structure ExactTypes :> EXACTTYPES =
struct

open Syntax
open Context
open PatternBind
open Unify

type context = asyncType Context.context

(* pat2syncType : pattern -> syncType *)
(*
fun pat2syncType (PTensor (p1, p2))  = TTensor (pat2syncType p1, pat2syncType p2)
  | pat2syncType (POne)             = TOne
  | pat2syncType (PDepPair (x, A, p)) = Exists (x, A, pat2syncType p)
  | pat2syncType (PVar (x, A))       = Async A
*)


(* checkKind : context * kind -> unit *)
fun checkKind (ctx, ki) = case Kind.prj ki of
	  Type => ()
	| KPi (x, A, K) => (checkType (ctx, A); checkKind (ctxPushUN (x, A, ctx), K))

(* checkType : context * asyncType -> unit *)
and checkType (ctx, ty) = case AsyncType.prj ty of
	  Lolli (A, B) => (checkType (ctx, A); checkType (ctx, B))
	| TPi (x, A, B) => (checkType (ctx, A); checkType (ctxPushUN (x, A, ctx), B))
	| AddProd (A, B) => (checkType (ctx, A); checkType (ctx, B))
	| Top => ()
	| TMonad S => checkSyncType (ctx, S)
	| TAtomic (a, S) => checkTypeSpine (ctx, S, Signatur.sigLookupKind a)
	| TAbbrev aA => ()

(* checkTypeSpine : context * typeSpine * kind -> unit *)
(* checks that the spine is : ki > Type *)
and checkTypeSpine (ctx, sp, ki) = case (TypeSpine.prj sp, Kind.prj ki) of
	  (TNil, Type) => ()
	| (TNil, KPi _) => raise Fail "Wrong kind; expected Type\n"
	| (TApp _, Type) => raise Fail "Wrong kind; cannot apply Type\n"
	| (TApp (N, S), KPi (_, A, K)) =>
			let val _ = checkObj (ctx, N, A)
			in checkTypeSpine (ctx, S, KClos (K, Subst.sub N)) end

(* checkSyncType : context * syncType -> unit *)
and checkSyncType (ctx, ty) = case SyncType.prj ty of
	  TTensor (S1, S2) => (checkSyncType (ctx, S1); checkSyncType (ctx, S2))
	| TOne => ()
	| Exists (x, A, S) => (checkType (ctx, A); checkSyncType (ctxPushUN (x, A, ctx), S))
	| Async A => checkType (ctx, A)

(* checkObj : context * obj * asyncType -> context * bool *)
and checkObj (ctx, ob, ty) = case (Obj.prj ob, Util.typePrjAbbrev ty) of
	  (LinLam (x, N), Lolli (A, B)) =>
			let val (ctxo, t) = checkObj (ctxPushLIN (x, A, ctx), N, TClos (B, Subst.shift 1))
			in (ctxPopLIN (t, ctxo), t) end
	| (Lam (x, N), TPi (_, A, B)) =>
			let val (ctxo, t) = checkObj (ctxPushUN (x, A, ctx), N, B)
			in (ctxPopUN ctxo, t) end
	| (AddPair (N1, N2), AddProd (A, B)) =>
			let val (ctxo1, t1) = checkObj (ctx, N1, A)
				val (ctxo2, t2) = checkObj (ctx, N2, B)
			in (ctxAddJoin (t1, t2) (ctxo1, ctxo2), t1 andalso t2) end
	| (Unit, Top) => (ctx, true)
	| (Monad E, TMonad S) => checkExp (ctx, E, S)
	| (Atomic (H, _, S), A) =>
			let val (ctxm, B) = inferHead (ctx, H)
				val (ctxo, t, A') = inferSpine (ctxm, S, B)
				fun errmsg () = "Object "^(PrettyPrint.printObj ob)
							^" has type:\n"^(PrettyPrint.printType A')
							^"\nbut expected:\n"^(PrettyPrint.printType ty)
				val () = unify (AsyncType.inj A, A', errmsg)
			in (ctxo, t) end
	| (Redex (N, B, S), A) =>
			let val B' = asyncTypeFromApx B
				val (ctxm, t1) = checkObj (ctx, N, B')
				val (ctxo, t2, A') = inferSpine (ctxm, S, B')
				fun errmsg () = "Object "^(PrettyPrint.printObj ob)
							^" has type:\n"^(PrettyPrint.printType A')
							^"\nbut expected:\n"^(PrettyPrint.printType ty)
				val () = unify (AsyncType.inj A, A', errmsg)
			in (ctxo, t1 orelse t2) end
	| (Constraint (N, A'), A) =>
			let val () = checkType (ctxDelLin ctx, A')
				fun errmsg () = "Object "^(PrettyPrint.printObj N)
							^" has ascribed type:\n"^(PrettyPrint.printType A')
							^"\nbut expected:\n"^(PrettyPrint.printType ty)
				val () = unify (AsyncType.inj A, A', errmsg)
			in checkObj (ctx, N, A') end
	| _ => raise Fail "Internal error match: checkObj\n"

(* inferHead : context * head -> context * asyncType *)
and inferHead (ctx, h) = case h of
	  Const c => (ctx, Signatur.sigLookupType c)
	| Var n => let val (ctxo, A) = ctxLookupNum (ctx, n) in (ctxo, TClos (A, Subst.shift n)) end
	| UCVar x =>
			(ctx, TClos (ImplicitVars.ucLookup x, (Subst.shift o length o ctx2list) ctx))
	| LogicVar {ty, s, ctx=rctx, ...} =>
			let fun calcCtx ss [] = emptyCtx
				  | calcCtx ss ((x, ty, mode)::G) =
						let val ss' = Subst.comp (Subst.shift 1, ss)
							val si = Subst.invert (Subst.shift 1)
						in if Subst.hdDef ss then
							let val ss'' = Subst.comp (ss', si)
							in ctxCons (x, TClos (ty, ss''), mode) (calcCtx ss'' G) end
						else (* mode <> LIN and hd wi = Undef *)
							calcCtx ss' G
						end
				val () = rctx := (SOME o calcCtx (Subst.invert s) o ctx2list o ctxDelLin) ctx
			in (ctx, TClos (ty, s)) end

(* inferSpine : context * spine * asyncType -> context * bool * asyncType *)
and inferSpine (ctx, sp, ty) = case (Spine.prj sp, Util.typePrjAbbrev ty) of
	  (Nil, A) => (ctx, false, ty)
	| (App (N, S), TPi (_, A, B)) =>
			let val _ = checkObj (ctxDelLin ctx, N, A)
				val (ctxo, t, tyo) = inferSpine (ctx, S, TClos (B, Subst.sub N))
			in (ctxo, t, tyo) end
	| (LinApp (N, S), Lolli (A, B)) =>
			let val (ctxm, t1) = checkObj (ctx, N, A)
				val (ctxo, t2, tyo) = inferSpine (ctxm, S, B)
			in (ctxo, t1 orelse t2, tyo) end
	| (ProjLeft S, AddProd (A, B)) => inferSpine (ctx, S, A)
	| (ProjRight S, AddProd (A, B)) => inferSpine (ctx, S, B)
	| _ => raise Fail "Internal error match: inferSpine\n"

(* checkExp : context * expObj * syncType -> context * bool *)
and checkExp (ctx, ex, ty) = case ExpObj.prj ex of
	  Let (p, N, E) =>
			let val S0 = checkPattern (ctxDelLin ctx, p)
				val (ctxm, t1) = checkObj (ctx, N, TMonad' S0)
				val ctxm' = patBind (fn x=>x) p ctxm
				val (ctxo', t2) = checkExp (ctxm', E, STClos (ty, Subst.shift (nbinds p)))
			in (patUnbind (p, ctxo', t2), t1 orelse t2) end
	| Mon M => checkMonadObj (ctx, M, ty)

(* checkPattern : context * pattern -> syncType *)
and checkPattern (ctx, p) = case Pattern.prj p of
	  PTensor (p1, p2) => TTensor' (checkPattern (ctx, p1), checkPattern (ctx, p2))
	| POne => TOne'
	| PDepPair (x, A, p) =>
			( checkType (ctx, A)
			; Exists' (x, A, checkPattern (ctxPushUN (x, A, ctx), p)) )
	| PVar (x, A) => (checkType (ctx, A); Async' A)

(* checkMonadObj : context * monadObj * syncType -> context * bool *)
and checkMonadObj (ctx, mob, ty) = case (MonadObj.prj mob, SyncType.prj ty) of
	  (Tensor (M1, M2), TTensor (S1, S2)) =>
			let val (ctxm, t1) = checkMonadObj (ctx, M1, S1)
				val (ctxo, t2) = checkMonadObj (ctxm, M2, S2)
			in (ctxo, t1 orelse t2) end
	| (One, TOne) => (ctx, false)
	| (DepPair (N, M), Exists (x, A, S)) =>
			let val _ = checkObj (ctxDelLin ctx, N, A)
			in checkMonadObj (ctx, M, STClos (S, Subst.sub N)) end
	| (Norm N, Async A) => checkObj (ctx, N, A)
	| _ => raise Fail "Internal error match: checkMonadObj\n"


fun checkKindEC ki = checkKind (emptyCtx, ki)
fun checkTypeEC ty = checkType (emptyCtx, ty)
fun checkObjEC (ob, ty) = ignore (checkObj (emptyCtx, Constraint' (ob, ty), ty))

end
