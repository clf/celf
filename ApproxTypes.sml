structure ApproxTypes :> APPROXTYPES =
struct

open Syntax
open Context
open Either

type context = apxAsyncType Context.context

exception ExnApxUnifyType of string

(* ucase : string -> bool *)
fun ucase x = x<>"" andalso Char.isUpper (String.sub (x, 0))

(* occur : typeLogicVar -> apxAsyncType -> unit *)
fun occur X ty = ApxAsyncTypeAuxDefs.fold
	(fn ApxTLogicVar X' => if X=X' then raise ExnApxUnifyType "Occurs check" else ()
	  | ApxTMonad S => occurSync X S
	  | _ => ()) ty
and occurSync X sty = ApxSyncTypeAuxDefs.fold
	(fn ApxExists (A, ()) => occur X A
	  | ApxAsync A => occur X A
	  | _ => ()) sty

(* occur : typeLogicVar -> apxAsyncType -> unit *)
(*
fun occur X ty = case ApxAsyncType.prj ty of
	  ApxTLogicVar X' =>
		if X=X' then raise ExnApxUnifyType "Occurs check"
		else ()
	| ApxLolli (A, B) => (occur X A; occur X B)
	| ApxTPi (A, B) => (occur X A; occur X B)
	| ApxAddProd (A, B) => (occur X A; occur X B)
	| ApxTop => ()
	| ApxTMonad S => occurSync X S
	| ApxTAtomic _ => () (* atomic types contain no logic vars *)
and occurSync X sty = case ApxSyncType.prj sty of
	  ApxTTensor (S1, S2) => (occurSync X S1; occurSync X S2)
	| ApxTOne => ()
	| ApxExists (A, S) => (occur X A; occurSync X S)
	| ApxAsync A => occur X A
*)

(* apxCopyType : asyncType -> asyncType *)
(*
fun apxCopyType (Lolli (A, B)) = Lolli (apxCopyType A, apxCopyType B)
  | apxCopyType (TPi (x, A, B)) = TPi (x, apxCopyType A, apxCopyType B)
  | apxCopyType (AddProd (A, B)) = AddProd (apxCopyType A, apxCopyType B)
  | apxCopyType Top = Top
  | apxCopyType (TMonad S) = TMonad (apxCopySyncType S)
  | apxCopyType (TAtomic (a, _, _)) = Signatur.sigNewTAtomic a
  | apxCopyType (X as TLogicVar (ref NONE)) = X
  | apxCopyType (TLogicVar (ref (SOME A))) = apxCopyType A (* continue to make new obj logic vars *)
and apxCopySyncType (TTensor (S1, S2)) = TTensor (apxCopySyncType S1, apxCopySyncType S2)
  | apxCopySyncType TOne = TOne
  | apxCopySyncType (Exists (x, A, S)) = Exists (x, apxCopyType A, apxCopySyncType S)
  | apxCopySyncType (Async A) = Async (apxCopyType A)
*)

(* apxUnifyType : apxAsyncType * apxAsyncType -> unit *)
fun apxUnifyType (ty1, ty2) = case (Util.apxTypePrjAbbrev ty1, Util.apxTypePrjAbbrev ty2) of
(*	  (ApxTLogicVar (ref (SOME A1)), A2) => apxUnifyType (A1, ApxAsyncType.inj A2)
	| (A1, ApxTLogicVar (ref (SOME A2))) => apxUnifyType (ApxAsyncType.inj A1, A2)*)
	  (ApxLolli (A1, B1), ApxLolli (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxTPi (A1, B1), ApxTPi (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxAddProd (A1, B1), ApxAddProd (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxTop, ApxTop) => ()
	| (ApxTMonad S1, ApxTMonad S2) => apxUnifySyncType (S1, S2)
	| (ApxTAtomic a1, ApxTAtomic a2) =>
			if a1 = a2 then () else raise ExnApxUnifyType (a1^" and "^a2^" differ")
	| (ApxTLogicVar X, A as ApxTLogicVar X') =>
			if X=X' then () else updLVar (X, ApxAsyncType.inj A)
	(*| (ApxTLogicVar X, A) => let val A' = ApxAsyncType.inj A in (occur X A'; updLVar (X, A')) end
	| (A, ApxTLogicVar X) => let val A' = ApxAsyncType.inj A in (occur X A'; updLVar (X, A')) end*)
	| (ApxTLogicVar X, _) => (occur X ty2; updLVar (X, ty2))
	| (_, ApxTLogicVar X) => (occur X ty1; updLVar (X, ty1))
	| (A1, A2) => raise ExnApxUnifyType
			((PrettyPrint.printType (asyncTypeFromApx ty1))^"\nand: "
						^(PrettyPrint.printType (asyncTypeFromApx ty2)))
and apxUnifySyncType (ty1, ty2) = case (ApxSyncType.prj ty1, ApxSyncType.prj ty2) of
	  (ApxTTensor (S1, T1), ApxTTensor (S2, T2)) =>
			(apxUnifySyncType (S1, S2); apxUnifySyncType (T1, T2))
	| (ApxTOne, ApxTOne) => ()
	| (ApxExists (A1, S1), ApxExists (A2, S2)) => (apxUnifyType (A1, A2); apxUnifySyncType (S1, S2))
	| (ApxAsync A1, ApxAsync A2) => apxUnifyType (A1, A2)
	| (S1, S2) => raise ExnApxUnifyType "stub: (S1, S2)"

fun apxUnify (ty1ty2 as (ty1, ty2)) = (apxUnifyType ty1ty2)
		(*handle (e as ExnApxUnifyType s) => (print ("ExnApxUnify: "^s^"\n") ; raise e)*)
		handle (e as ExnApxUnifyType s) => (print ("ExnApxUnify: "^
			(PrettyPrint.printType (asyncTypeFromApx ty1))^"\nand: "
						^(PrettyPrint.printType (asyncTypeFromApx ty2))^"\n") ; raise e)

(* nbinds : pattern -> int *)
(*
fun nbinds p = case Pattern.prj p of
	  PTensor (p1, p2) => nbinds p1 + nbinds p2
	| POne => 0
	| PDepPair (x, A, p) => 1 + nbinds p
	| PVar (x, A) => 1
*)

(* pat2apxSyncType : pattern -> apxSyncType *)
fun pat2apxSyncType p = case Pattern.prj p of
	  PTensor (p1, p2) => ApxTTensor' (pat2apxSyncType p1, pat2apxSyncType p2)
	| POne => ApxTOne'
	| PDepPair (x, A, p) => ApxExists' (asyncTypeToApx A, pat2apxSyncType p)
	| PVar (x, A) => ApxAsync' (asyncTypeToApx A)
(*
fun pat2syncType (PTensor (p1, p2))   = TTensor (pat2syncType p1, pat2syncType p2)
  | pat2syncType (POne)               = TOne
  | pat2syncType (PDepPair (x, A, p)) = Exists (x, A, pat2syncType p)
  | pat2syncType (PVar (x, A))        = Async A
  *)

(* patBind : pattern * context -> context *)
fun patBind (p, ctx) = case Pattern.prj p of
	  PTensor (p1, p2) => patBind (p2, patBind (p1, ctx)) (* S2[^|S1|] *)
	| POne => ctx
	| PDepPair (x, A, p) => patBind (p, ctxPushUN (x, asyncTypeToApx A, ctx))
	| PVar (x, A) => ctxPushLIN (x, asyncTypeToApx A, ctx)

(* patUnbind : pattern * context * bool -> context *)
fun patUnbind (p, ctx, t) = case Pattern.prj p of
	  PTensor (p1, p2) => patUnbind (p1, patUnbind (p2, ctx, t), t)
	| POne => ctx
	| PDepPair (x, _, p) => ctxPopUN (patUnbind (p, ctx, t))
	| PVar (x, _) => ctxPopLIN (t, ctx)

(* apxCheckKind : context * kind -> kind *)
fun apxCheckKind (ctx, ki) = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) =>
			let val A' = apxCheckType (ctx, A)
			in KPi' (x, A', apxCheckKind (ctxPushUN (x, asyncTypeToApx A', ctx), K)) end

(* apxCheckType : context * asyncType -> asyncType *)
and apxCheckType (ctx, ty) = case AsyncType.prj ty of
	  Lolli (A, B) => Lolli' (apxCheckType (ctx, A), apxCheckType (ctx, B))
	| TPi (x, A, B) =>
			let val A' = apxCheckType (ctx, A)
			in TPi' (x, A', apxCheckType (ctxPushUN (x, asyncTypeToApx A', ctx), B)) end
	| AddProd (A, B) => AddProd' (apxCheckType (ctx, A), apxCheckType (ctx, B))
	| Top => Top'
	| TMonad S => TMonad' (apxCheckSyncType (ctx, S))
	| TAtomic (a, _, S) =>
		(case Signatur.sigGetTypeAbbrev a of
			  SOME ty =>
				let val _ = apxCheckTypeSpine (ctx, S, ApxType')
				in TAbbrev' (a, ty) end
			| NONE =>
				let val K = Signatur.sigLookupApxKind a
				in TAtomic' (a, Signatur.sigNewImplicitsType a, apxCheckTypeSpine (ctx, S, K)) end)
	| TAbbrev _ => raise Fail "Internal error: TAbbrev cannot occur yet\n"
	| TUnknown => ty (* Important to return ty, since TUnknown cannot be injected *)

(* apxCheckTypeSpine : context * typeSpine * apxKind -> typeSpine *)
(* checks that the spine is : ki > Type *)
and apxCheckTypeSpine (ctx, sp, ki) = case (TypeSpine.prj sp, ApxKind.prj ki) of
	  (TNil, ApxType) => TNil'
	| (TNil, ApxKPi _) => raise Fail "Wrong kind; expected Type\n"
	| (TApp _, ApxType) => raise Fail "Wrong kind; cannot apply Type\n"
	| (TApp (N, S), ApxKPi (A, K)) =>
			let val (_, _, N') = apxCheckObj (ctx, N, A)
			in TApp' (N', apxCheckTypeSpine (ctx, S, K)) end

(* apxCheckSyncType : context * syncType -> syncType *)
and apxCheckSyncType (ctx, ty) = case SyncType.prj ty of
	  TTensor (S1, S2) => TTensor' (apxCheckSyncType (ctx, S1), apxCheckSyncType (ctx, S2))
	| TOne => TOne'
	| Exists (x, A, S) =>
			let val A' = apxCheckType (ctx, A)
			in Exists' (x, A', apxCheckSyncType (ctxPushUN (x, asyncTypeToApx A', ctx), S)) end
	| Async A => Async' (apxCheckType (ctx, A))

(* apxCheckObj : context * obj * apxAsyncType -> context * bool * obj *)
and apxCheckObj (ctx, ob, A) =
	let val (ctxo, t, N, A') = apxInferObj (ctx, ob)
	in apxUnify (A, A'); (ctxo, t, N) end

(* apxInferObj : context * obj -> context * bool * obj * apxAsyncType *)
and apxInferObj (ctx, ob) = case ObjAuxDefs.prj2 ob of
	  Redex (Redex (N, A, S1), _, S2) => apxInferObj (ctx, Redex' (N, A, Util.appendSpine (S1, S2)))
	| Redex (Atomic (H, A, S1), _, S2) => apxInferObj (ctx, Atomic' (H, A, Util.appendSpine (S1, S2)))
	| _ => case Obj.prj ob of
	  LinLam (x, N) =>
			let val A = newApxTVar()
				val (ctxo, t, N', B) = apxInferObj (ctxPushLIN (x, A, ctx), N)
			in (ctxPopLIN (t, ctxo), t, LinLam' (x, N'), ApxLolli' (A, B)) end
	| Lam (x, N) =>
			let val A = newApxTVar()
				val (ctxo, t, N', B) = apxInferObj (ctxPushUN (x, A, ctx), N)
			in (ctxPopUN ctxo, t, Lam' (x, N'), ApxTPi' (A, B)) end
	| AddPair (N1, N2) =>
			let val (ctxo1, t1, N1', A1) = apxInferObj (ctx, N1)
				val (ctxo2, t2, N2', A2) = apxInferObj (ctx, N2)
			in (ctxAddJoin (t1, t2) (ctxo1, ctxo2), t1 andalso t2, 
				AddPair' (N1', N2'), ApxAddProd' (A1, A2)) end
	| Unit => (ctx, true, Unit', ApxTop')
	| Monad E => (fn (c, t, e, s) => (c, t, Monad' e, ApxTMonad' s)) (apxInferExp (ctx, E))
	| Atomic (H, _, S) =>
			let val (ctxm, t1, H', A) = apxInferHead (ctx, H)
				val (ctxo, t2, S', B) = apxInferSpine (ctxm, S, A)
				fun atomRedex (LEFT h, ty, sp) = Atomic' (h, ty, sp)
				  | atomRedex (RIGHT h, ty, sp) = Redex' (h, ty, sp)
			in (ctxo, t1 orelse t2, atomRedex (H', A, S'), B) end
	| Redex (N, A, S) =>
			let val (ctxm, t1, N') = apxCheckObj (ctx, N, A)
				val (ctxo, t2, S', B) = apxInferSpine (ctxm, S, A)
			in (ctxo, t1 orelse t2, Redex' (N', A, S'), B) end
	| Constraint (N, A) =>
			let val A' = apxCheckType (ctxDelLin ctx, A)
				val apxA' = asyncTypeToApx A'
				val (ctxo, t, N') = apxCheckObj (ctx, N, apxA')
			in (ctxo, t, Constraint' (N', A'), apxA') end

(* apxInferHead : context * head -> context * bool * (head, obj) either * apxAsyncType *)
and apxInferHead (ctx, h) = case h of
	  Const (c, _) => (* set Top flag to true in case of Top type *)
			(case ctxLookupName (ctx, c) of
				  (SOME (n, A, ctxo)) => (ctxo, true, LEFT (Var n), A)
				| NONE =>
					if ucase c then
						(ctx, true, LEFT (UCVar c), ImplicitVars.apxUCLookup c)
					else (case Signatur.sigGetObjAbbrev c of
						  SOME (ob, ty) => (ctx, true, RIGHT ob, asyncTypeToApx ty)
						| NONE => (ctx, true, LEFT (Const (c, Signatur.sigNewImplicitsObj c)),
									Signatur.sigLookupApxType c)))
	| Var _ => raise Fail "de Bruijn indices shouldn't occur yet\n"
	| UCVar _ => raise Fail "Upper case variables shouldn't occur yet\n"
	| X as LogicVar (_, A, _, _, _, _) => (ctx, true, LEFT X, asyncTypeToApx A)

(* apxInferSpine : context * spine * apxAsyncType -> context * bool * spine * apxAsyncType *)
and apxInferSpine (ctx, sp, ty) = case Spine.prj sp of
	  Nil => (ctx, false, Nil', ty)
	| App (N, S) =>
			let val (_, _, N', A) = apxInferObj (ctxDelLin ctx, N)
				val B = newApxTVar ()
				val () = apxUnify (ty, ApxTPi' (A, B))
				val (ctxo, t, S', tyo) = apxInferSpine (ctx, S, B)
			in (ctxo, t, App' (N', S'), tyo) end
	| LinApp (N, S) =>
			let val (ctxm, t1, N', A) = apxInferObj (ctx, N)
				val B = newApxTVar ()
				val () = apxUnify (ty, ApxLolli' (A, B))
				val (ctxo, t2, S', tyo) = apxInferSpine (ctxm, S, B)
			in (ctxo, t1 orelse t2, LinApp' (N', S'), tyo) end
	| ProjLeft S =>
			let val A = newApxTVar ()
				val B = newApxTVar ()
				val () = apxUnify (ty, ApxAddProd' (A, B))
				val (ctxo, t, S', tyo) = apxInferSpine (ctx, S, A)
			in (ctxo, t, ProjLeft' S', tyo) end
	| ProjRight S =>
			let val A = newApxTVar ()
				val B = newApxTVar ()
				val () = apxUnify (ty, ApxAddProd' (A, B))
				val (ctxo, t, S', tyo) = apxInferSpine (ctx, S, B)
			in (ctxo, t, ProjRight' S', tyo) end

(* apxInferExp : context * expObj -> context * bool * expObj * apxSyncType *)
and apxInferExp (ctx, ex) = case ExpObj.prj ex of
	  Let (p, N, E) =>
			let val p' = apxCheckPattern (ctxDelLin ctx, p)
				val (ctxm, t1, N') = apxCheckObj (ctx, N, ApxTMonad' (pat2apxSyncType p'))
				val (ctxo', t2, E', S) = apxInferExp (patBind (p', ctxm), E)
			in (patUnbind (p', ctxo', t2), t1 orelse t2, Let' (p', N', E'), S) end
	| Mon M => (fn (ctxo, t, M', S) => (ctxo, t, Mon' M', S)) (apxInferMonadObj (ctx, M))

(* apxCheckPattern : context * pattern -> pattern *)
and apxCheckPattern (ctx, p) = case Pattern.prj p of
	  PTensor (p1, p2) => PTensor' (apxCheckPattern (ctx, p1), apxCheckPattern (ctx, p2))
	| POne => POne'
	| PDepPair (x, A, p) =>
			let val A' = apxCheckType (ctx, A)
			in PDepPair' (x, A', apxCheckPattern (ctxPushUN (x, asyncTypeToApx A', ctx), p)) end
	| PVar (x, A) => PVar' (x, apxCheckType (ctx, A))

(* apxInferMonadObj : context * monadObj -> context * bool * monadObj * apxSyncType *)
and apxInferMonadObj (ctx, mob) = case MonadObj.prj mob of
	  Tensor (M1, M2) =>
			let val (ctxm, t1, M1', S1) = apxInferMonadObj (ctx, M1)
				val (ctxo, t2, M2', S2) = apxInferMonadObj (ctxm, M2)
			in (ctxo, t1 orelse t2, Tensor' (M1', M2'), ApxTTensor' (S1, S2)) end
	| One => (ctx, false, One', ApxTOne')
	| DepPair (N, M) =>
			let val (_, _, N', A) = apxInferObj (ctxDelLin ctx, N)
				val (ctxo, t, M', S) = apxInferMonadObj (ctx, M)
			in (ctxo, t, DepPair' (N', M'), ApxExists' (A, S)) end
	| Norm N => (fn (ctxo, t, N', A) => (ctxo, t, Norm' N', ApxAsync' A)) (apxInferObj (ctx, N))


fun apxCheckKindEC ki = apxCheckKind (emptyCtx, ki)
fun apxCheckTypeEC ty = apxCheckType (emptyCtx, ty)
fun apxCheckObjEC (ob, ty) = case (Obj.prj o #3 o apxInferObj) (emptyCtx, Constraint' (ob, ty)) of
		  Constraint obty => obty
		| _ => raise Fail "Internal error: apxCheckObjEC\n"

end
