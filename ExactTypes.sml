structure ExactTypes :> EXACTTYPES =
struct

open Syntax
open Context
open Either

val outputUnify = true

type context = asyncType Context.context

exception ExnUnify of string

val constraints = ref []
val awakenedConstrs = ref []

(* resetConstrs : unit -> unit *)
fun resetConstrs () = (constraints := [])

fun constrToStr Solved = "Solved"
  | constrToStr (Eqn (o1, o2)) = (PrettyPrint.printObj o1)^" == "^(PrettyPrint.printObj o2)

(* noConstrs : unit -> unit *)
fun noConstrs () =
	let val leftOver = List.mapPartial (fn Solved => NONE | Eqn e => SOME e) (map ! (!constraints))
	in case leftOver of [] => ()
	| _::_ => (app (fn o1o2 => print ("Constr: "^(constrToStr (Eqn o1o2))^"\n")) leftOver
		; raise Fail "Leftover constraints\n") end

(* addConstraint : constr ref * constr ref list ref list -> unit *)
fun addConstraint (c, css) =
	( if outputUnify then print ("Adding constraint "^(constrToStr (!c))^"\n") else ()
	; app (fn cs => cs := c::(!cs)) (constraints::css) )

(* instantiate : obj option ref * obj * constr ref list ref * int -> unit *)
fun instantiate (ref (SOME _), _, _, _) = raise Fail "Internal error: double instantiation\n"
  | instantiate (r, rInst, ref cs, l) =
		( r := SOME rInst
		; if outputUnify then
			print ("Instantiating $"^(Int.toString l)^" = "^(PrettyPrint.printObj rInst)^"\n")
		  else ()
		; awakenedConstrs := cs @ (!awakenedConstrs))

(* lowerLVar : asyncType * spine * subst * context -> obj * obj objF *)
fun lowerLVar (ty, sp, s, ctx) = case (Util.typePrjAbbrev ty, Spine.prj sp) of
	  (Lolli (A, B), LinApp (N, S)) =>
			let val (rInst, Y) = lowerLVar (B, S, Subst.dot (N, s), ctxPushLIN ("", A, ctx))
			in (LinLam' ("", rInst), Y) end
	| (TPi (x, A, B), App (N, S)) =>
			let val (rInst, Y) = lowerLVar (B, S, Subst.dot (N, s), ctxPushUN (x, A, ctx))
			in (Lam' (x, rInst), Y) end
	| (AddProd (A, B), ProjLeft S) =>
			let val (rInst, Y) = lowerLVar (A, S, s, ctx)
			in (AddPair' (rInst, newLVarCtx (SOME ctx) B), Y) end
	| (AddProd (A, B), ProjRight S) =>
			let val (rInst, Y) = lowerLVar (B, S, s, ctx)
			in (AddPair' (newLVarCtx (SOME ctx) A, rInst), Y) end
	| (TAtomic _, Nil) =>
			let val X = newLVarCtx (SOME ctx) ty
			in (X, Obj.prj (Clos (X, s))) end
	| (TMonad _, Nil) =>
			let val X = newLVarCtx (SOME ctx) ty
			in (X, Obj.prj (Clos (X, s))) end
	| (TUnknown, _) => raise Fail "Ambiguous typing\n"
	| _ => raise Fail "Internal error: lowerLVar\n"

(* lowerObj : obj objF -> obj objF *)
fun lowerObj (N as Atomic (LogicVar (r, A, s, ref ctx, cs, l), _, S)) =
		(case Spine.prj S of Nil => N | _ =>
			let val (rInst, Y) = lowerLVar (A, S, s, valOf ctx)
			in instantiate (r, rInst, cs, l); Y end)
  | lowerObj N = N

(* patBind : pattern -> context -> context *)
fun patBind p ctx = case Pattern.prj p of
	  PTensor (p1, p2) => patBind (PClos (p2, Subst.shift (nbinds p1))) (patBind p1 ctx)
	| POne => ctx
	| PDepPair (x, A, p) => patBind p (ctxPushUN (x, A, ctx))
	| PVar (x, A) => ctxPushLIN (x, A, ctx)

(* patUnbind : pattern * context * bool -> context *)
fun patUnbind (p, ctx, t) = case Pattern.prj p of
	  PTensor (p1, p2) => patUnbind (p1, patUnbind (p2, ctx, t), t)
	| POne => ctx
	| PDepPair (x, _, p) => ctxPopUN (patUnbind (p, ctx, t))
	| PVar (x, _) => ctxPopLIN (t, ctx)

(* newMon : syncType * context -> monadObj *)
fun newMon (sTy, ctx) = case SyncType.prj sTy of
	  TTensor (S1, S2) => Tensor' (newMon (S1, ctx), newMon (S2, ctx))
	| TOne => One'
	| Exists (x, A, S) => DepPair' (newLVarCtx (SOME ctx) A, newMon (S, ctxPushUN (x, A, ctx)))
	| Async A => Norm' (newLVarCtx (SOME ctx) A)

(* newMonA : asyncType * context -> expObj *)
fun newMonA (A, ctx) = case AsyncType.prj A of
	  TMonad S => Mon' (newMon (S, ctx))
	| _ => raise Fail "Internal error: newMonA\n"

fun invAtomic (Atomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic\n"
val invAtomicP = invAtomic o Obj.prj

(* splitExp : obj option ref * expObj
		-> (head * monadObj, (expObj -> expObj) * monadObj * (context -> context) * int) Either *)
fun splitExp (rOccur, ex) =
	let fun splitExp' ex = case Whnf.whnfExp ex of
			  Let (p, N, E) =>
				if case #1 (invAtomicP N) of
					  LogicVar (r, _, _, _, _, _) => r=rOccur
					| _ => false
				then NONE
				else Option.map (fn (ef, M, ectx, n) =>
								(fn e => Let' (p, N, ef e), M, ectx o (patBind p), n + nbinds p))
							(splitExp' E)
			| Mon M => SOME (fn e => e, M, fn ctx => ctx, 0)
		fun pruneLetOccur foundL ex = case Whnf.whnfExp ex of
			  Mon M => (case foundL of
				  NONE => raise Fail "Internal error: pruneLet\n"
				| SOME L => (L, M))
			| Let (p, N, E) => (case (#1 o invAtomic o lowerObj o Obj.prj) N of
				  (L as LogicVar (r, A, s, ref G, cs, l)) =>
					if r = rOccur then
						if isSome foundL then
							raise ExnUnify "Double occurs check in let\n"
						else
							pruneLetOccur (SOME L) E
					else
						( instantiate (r, Monad' (newMonA (A, valOf G)), cs, l)
						; pruneLetOccur foundL (Let' (p, N, E)) )
				| _ => raise ExnUnify "Occurs check in let\n")
	in case splitExp' ex of
		  SOME eMcn => RIGHT eMcn
		| NONE => LEFT (pruneLetOccur NONE ex)
	end

(* objExists : bool -> obj option ref -> subst -> obj -> obj option *)
(* typeExists : bool -> obj option ref -> subst -> asyncType -> asyncType option *)
(*fun objExists prune rOccur s ob =*)
val (objExists, typeExists) =
	let exception ExnMayNotExist
		fun pruneCtx f wi [] = emptyCtx
		  | pruneCtx f wi ((x, A, mode)::G) =
				let val s = Subst.shift 1
					val si = Subst.invert s
				in if Subst.hdDef wi then
					let val wi' = Subst.comp (Subst.comp (s, wi), si)
						val A' = Util.objMapType (f (Subst.invert wi')) (TClos (A, wi'))
					in ctxCons (x, A', mode) (pruneCtx f wi' G) end
				else if mode = LIN then (* and hd wi = Undef *)
					raise Subst.ExnUndef
				else (* mode <> LIN and hd wi = Undef *)
					pruneCtx f (Subst.comp (s, wi)) G
				end
		fun f prune rOccur s ob = case lowerObj (Whnf.whnfObj ob) of
		  N as Atomic (LogicVar (rY, A, sY, ref G, cs, l), _, _ (* = Nil *)) =>
				if rY = rOccur then raise Subst.ExnUndef
				else if prune then
					let val weakenSub =
							SOME (Subst.fold
									(fn (ob, w) => case objExists false rOccur s ob of
										  SOME _ => Subst.dot1 w
										| NONE => Subst.comp (w, Subst.shift 1))
									(fn _ => Subst.id) sY)
							handle ExnMayNotExist => NONE
					in case weakenSub of
						  SOME w =>
							if Subst.isId w then N else
							let val wi = Subst.invert w
								val G' = Option.map
										(pruneCtx (f prune(*=true*) rOccur) wi o ctx2list) G
								val A' = Util.objMapType (f prune(*=true*) rOccur w) (TClos (A, wi))
								val Y'w = Clos (newLVarCtx G' A', w)
								val () = instantiate (rY, Y'w, cs, l)
							in Obj.prj (Clos (Y'w, sY)) end
						| NONE =>
							let val A' = Util.objMapType (f prune(*=true*) rOccur s) (TClos (A, sY))
								val Y' = newLVarCtx NONE A'
								val cnstr = ref (Eqn (Clos (Y', s), Clos (Obj.inj N, s)))
								val () = addConstraint (cnstr, [cs])
							in Obj.prj Y' end
					end
				else (* no pruning *)
					(Subst.fold
						(fn (ob, ()) => case objExists false rOccur s ob of
							SOME _ => () | NONE => raise ExnMayNotExist) ignore sY
					; N)
		| N => N
		and objExists prune rOccur s ob =
			(SOME (Util.objMapObj (f prune rOccur s) ob) handle Subst.ExnUndef => NONE)
		fun typeExists prune rOccur s ty =
			(SOME (Util.objMapType (f prune rOccur s) ty) handle Subst.ExnUndef => NONE)
	in (objExists, typeExists) end
	(*in SOME (Util.objMapObj f ob) handle Subst.ExnUndef => NONE end*)

fun unifyType (ty1, ty2) = case (Util.typePrjAbbrev ty1, Util.typePrjAbbrev ty2) of
	  (TUnknown, _) => raise Fail "Ambiguous typing\n"
	| (_, TUnknown) => raise Fail "Ambiguous typing\n"
	| (Lolli (A1, B1), Lolli (A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (TPi (x1, A1, B1), TPi (x2, A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (AddProd (A1, B1), AddProd (A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (Top, Top) => ()
	| (TMonad S1, TMonad S2) => unifySyncType (S1, S2)
	| (TAtomic (a1, impl1, S1), TAtomic (a2, impl2, S2)) =>
			if a1 <> a2 then raise Fail (a1^" and "^a2^" differ; shouldn't happen")
			else (ListPair.appEq (unifyObj NONE) (impl1, impl2); unifyTSpine (S1, S2))
	| (A1, A2) => raise Fail "Error shouldn't happen: unifyType\n"
and unifySyncType (ty1, ty2) = case (SyncType.prj ty1, SyncType.prj ty2) of
	  (TTensor (S1, T1), TTensor (S2, T2)) => (unifySyncType (S1, S2); unifySyncType (T1, T2))
	| (TOne, TOne) => ()
	| (Exists (x1, A1, S1), Exists (x2, A2, S2)) => (unifyType (A1, A2); unifySyncType (S1, S2))
	| (Async A1, Async A2) => unifyType (A1, A2)
	| (S1, S2) => raise Fail "Error shouldn't happen: unifySyncType\n"
and unifyTSpine (sp1, sp2) = case (TypeSpine.prj sp1, TypeSpine.prj sp2) of
	  (TNil, TNil) => ()
	| (TApp (N1, S1), TApp (N2, S2)) => (unifyObj NONE (N1, N2); unifyTSpine (S1, S2))
	| (S1, S2) => raise Fail "Error shouldn't happen: unifyTSpine\n"
and unifyObj dryRun (ob1, ob2) =
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	let val ob1' = lowerObj (Whnf.whnfObj ob1)
		val ob2' = lowerObj (Whnf.whnfObj ob2)
	in case (ob1', ob2') of
		  (LinLam (_, N1), LinLam (_, N2)) => unifyObj dryRun (N1, N2)
		| (Lam (_, N1), Lam (_, N2)) => unifyObj dryRun (N1, N2)
		| (AddPair (L1, N1), AddPair (L2, N2)) =>
				(unifyObj dryRun (L1, L2); unifyObj dryRun (N1, N2))
		| (Unit, Unit) => ()
		| (Monad E1, Monad E2) =>
				unifyExp dryRun (E1, E2)
		| (Atomic hAS1, Atomic hAS2) => unifyHead dryRun (hAS1, hAS2)
		| (N1, N2) => raise Fail "Internal error: unifyObj\n"
	end
and unifyHead dryRun (hAS1 as (h1, _, S1), hAS2 as (h2, _, S2)) = case (h1, h2) of
	  (Const (c1, impl1), Const (c2, impl2)) =>
			if c1 <> c2 then raise ExnUnify ("Constants "^c1^" and "^c2^" differ\n")
			else (ListPair.appEq (unifyObj dryRun) (impl1, impl2); unifySpine dryRun (S1, S2))
	| (UCVar x1, UCVar x2) =>
			if x1 <> x2 then raise ExnUnify ("Vars "^x1^" and "^x2^" differ\n")
			else unifySpine dryRun (S1, S2)
	| (Var n1, Var n2) =>
			if n1 <> n2 then raise ExnUnify "Vars differ\n"
			else unifySpine dryRun (S1, S2)
	| (LogicVar (r1, A1, s1, ref G1, cs1, l1), LogicVar (r2, _, s2, _, cs2, l2)) =>
			if isSome dryRun then (valOf dryRun) := false else
			if r1 = r2 then case Subst.patSub Eta.etaContract s1 of
				  NONE => addConstraint (ref (Eqn (Atomic' hAS2, Atomic' hAS1)), [cs1])
				| SOME s1' => (case Subst.patSub Eta.etaContract s2 of
					  NONE => addConstraint (ref (Eqn (Atomic' hAS1, Atomic' hAS2)), [cs1])
					| SOME s2' =>
						let val s' = Subst.intersection (s1', s2')
						in if Subst.isId s' then () else 
							let val si = Subst.invert s'
								val G' = raise Fail "stub: reduce context (G1,si)"
								(*val A' = case typeExists true (ref NONE) s' (TClos (A1, si)) of
									SOME ty => ty | NONE => raise ExnUnify "Unification failed\n"*)
								val A' = TClos (A1, si)
							in instantiate (r1, Clos (newLVarCtx G' A', s'), cs1, l1) end
						end)
			else (case Subst.patSub Eta.etaContract s1 of
				  SOME s' => unifyLVar (r1, l1, s', Atomic' hAS2, cs1)
				| NONE =>
					(case Subst.patSub Eta.etaContract s2 of
					  SOME s' => unifyLVar (r2, l2, s', Atomic' hAS1, cs2)
					| NONE => addConstraint (ref (Eqn (Atomic' hAS1, Atomic' hAS2)), [cs1, cs2])))
	| (LogicVar (r, _, s, _, cs, l), _) =>
			if isSome dryRun then (valOf dryRun) := false else
			(case Subst.patSub Eta.etaContract s of
				  SOME s' => unifyLVar (r, l, s', Atomic' hAS2, cs)
				| NONE => addConstraint (ref (Eqn (Atomic' hAS1, Atomic' hAS2)), [cs]))
	| (_, LogicVar _) => unifyHead dryRun (hAS2, hAS1)
	| _ => raise ExnUnify "h1 h2"
and unifyLVar (r, l, s, ob, cs) = (* LogicVar (r, _, s, _, cs, l) =unify= ob *)
	case objExists true r s (Clos (ob, Subst.invert s)) of
		  NONE => raise ExnUnify "Unification failed\n"
		| SOME N => instantiate (r, N, cs, l)
and unifySpine dryRun (sp1, sp2) = case (Spine.prj sp1, Spine.prj sp2) of
	  (Nil, Nil) => ()
	| (App (N1, S1), App (N2, S2)) => (unifyObj dryRun (N1, N2); unifySpine dryRun (S1, S2))
	| (LinApp (N1, S1), LinApp (N2, S2)) => (unifyObj dryRun (N1, N2); unifySpine dryRun (S1, S2))
	| (ProjLeft S1, ProjLeft S2) => unifySpine dryRun (S1, S2)
	| (ProjRight S1, ProjRight S2) => unifySpine dryRun (S1, S2)
	| _ => raise Fail "Internal error: unifySpine\n"
and unifyExp dryRun (e1, e2) = case (Whnf.whnfExp e1, Whnf.whnfExp e2) of
	  (Mon M1, Mon M2) => unifyMon dryRun (M1, M2)
	| (Let L1, Mon M2) => unifyLetMon dryRun (L1, M2)
	| (Mon M1, Let L2) => unifyLetMon dryRun (L2, M1)
	| (Let L1, Let L2) =>
			let val lVarCount = (ExpObjAuxDefs.fold
						(fn Mon _ => 0 | Let (_, N, n) =>
							(case Obj.prj N of Atomic (LogicVar _, _, _) => n+1
								| Atomic _ => n | _ => raise Fail "Internal error lVarCount")))
						o Whnf.whnfLetSpine
			in if isSome dryRun andalso (lVarCount (Let' L1) > 0 orelse lVarCount (Let' L2) > 0)
				then (valOf dryRun) := false
				else unifyLetLet dryRun (L1, L2)
			end
and unifyLetMon dryRun ((p, N, E), M) = case lowerObj (Obj.prj N) (* N is already in whnf *) of
	  Atomic (LogicVar (r, A, s, ref G, cs, l), _, _ (*=Nil*)) =>
			if isSome dryRun then (valOf dryRun) := false else (* stub? *)
			( instantiate (r, Monad' (newMonA (A, valOf G)), cs, l)
			; unifyExp NONE (Let' (p, N, E), Mon' M) )
	| Atomic _ => raise ExnUnify "let = mon\n"
	| _ => raise Fail "Internal error: unifyLetMon\n"
and unifyMon dryRun (m1, m2) = case (MonadObj.prj m1, MonadObj.prj m2) of
	  (Tensor (M11, M12), Tensor (M21, M22)) =>
			(unifyMon dryRun (M11, M21); unifyMon dryRun (M12, M22))
	| (One, One) => ()
	| (DepPair (N1, M1), DepPair (N2, M2)) => (unifyObj dryRun (N1, N2); unifyMon dryRun (M1, M2))
	| (Norm N1, Norm N2) => unifyObj dryRun (N1, N2)
	| _ => raise Fail "Internal error: unifyMon\n"
and unifyLetLet dryRun ((p1, ob1, E1), (p2, ob2, E2)) =
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	let val ob1' = lowerObj (Whnf.whnfObj ob1)
		val ob2' = lowerObj (Whnf.whnfObj ob2)
	in case (ob1', Whnf.whnfExp E1, ob2', Whnf.whnfExp E2) of
		  (Atomic (L1 as LogicVar (r, A, s, ref G, cs, l), A', S (*=Nil*)), Mon M1, _, E2') =>
			(case splitExp (r, Let' (p2, Obj.inj ob2', ExpObj.inj E2')) of
				  LEFT (L2, M2) =>
					( unifyHead NONE ((L1, A', S), (L2, A', S))
					; unifyMon NONE (M1, M2) )
				| RIGHT (e, M2, ectx, n) =>
					(case Subst.patSub Eta.etaContract s of
						  NONE => raise Fail "stub !!!"
						| SOME s' =>
							let val newM = EClos (newMonA (TClos (A, Subst.shift n),
													ectx (valOf G)), Subst.dotn n s')
							in
								( unifyExp NONE (Let' (PClos (p1, Subst.shift n), Monad' newM,
										Mon' (MClos (M1, Subst.dotn (nbinds p1) (Subst.shift n)))),
									Mon' M2)
								; unifyLVar (r, l, s', Monad' (e newM), cs) )
							end))
		| (_, E1', Atomic (LogicVar _, _, _), Mon M2) =>
			unifyLetLet NONE ((p2, Obj.inj ob2', Mon' M2), (p1, Obj.inj ob1', ExpObj.inj E1'))
		| (Atomic (LogicVar L1, _, _), E1', Atomic (LogicVar L2, _, _), E2') =>
			raise Fail "stub: postpone as constraint"
		| (Atomic hAS1, E1', Atomic (LogicVar L2, _, _), E2') =>
			let val E = Whnf.whnfLetSpine (Let' (p2, Obj.inj ob2', ExpObj.inj E2'))
				val E2rest = matchHeadInLet (hAS1, fn _ => fn e => e, 0, E, E, 0)
			in unifyExp NONE (ExpObj.inj E1', E2rest) end
		| (Atomic (LogicVar L1, _, _), E1', Atomic hAS2, E2') =>
			let val E = Whnf.whnfLetSpine (Let' (p1, Obj.inj ob1', ExpObj.inj E1'))
				val E1rest = matchHeadInLet (hAS2, fn _ => fn e => e, 0, E, E, 0)
			in unifyExp NONE (E1rest, ExpObj.inj E2') end
		| (Atomic hAS1, E1', Atomic hAS2, E2') =>
			let val E = Whnf.whnfLetSpine (Let' (p2, Obj.inj ob2', ExpObj.inj E2'))
				val E2rest = matchHeadInLet (hAS1, fn _ => fn e => e, 0, E, E, 0)
			in unifyExp dryRun (ExpObj.inj E1', E2rest) (*stub: on failure check reverse?*) end
		| _ => raise Fail "Internal error: unifyLetLet\n"
	end
and matchHeadInLet (hAS, e, nbe, E, EsX, nMaybe) = case (ExpObj.prj E, Whnf.whnfExp EsX) of
	  (Let (p, N, E'), Let (_, NsX, EsX')) =>
			let val nbp = nbinds p
				fun hAS' () = invAtomicP (Clos (Atomic' hAS, Subst.shift nbp))
				fun switchSub 0 = Subst.dotn nbe (Subst.shift nbp)
				  | switchSub q = Subst.dot (EtaTag (Unit', nbp+nbe+1-q), switchSub (q-1))
				val e' = fn s => fn E =>
							let val s' = Subst.dotn nbe s
							in e s (Let' (PClos (p, s'), Clos (N, s'), E)) end
				fun lVarSub 0 = Subst.shift nbp
				  | lVarSub n = Subst.dot (Util.blank (), lVarSub (n-1))
				fun isLVar (LogicVar _, _, _) = true
				  | isLVar _ = false
				fun EsX'' () = if isLVar (invAtomicP NsX) then EClos (EsX', lVarSub nbp) else EsX'
				val dryRun = ref true
			in
				case SOME (unifyHead (SOME dryRun) (hAS, invAtomicP NsX))
						handle ExnUnify _ => NONE of
				  SOME () =>
					if !dryRun then
						e (Subst.shift nbp) (EClos (E', switchSub nbp))
					else
						matchHeadInLet (hAS' (), e', nbe + nbp, E', EsX'' (), nMaybe + 1)
				| NONE =>
						matchHeadInLet (hAS' (), e', nbe + nbp, E', EsX'' (), nMaybe)
			end
	| (Mon _, Mon _) =>
			if nMaybe = 0 then raise ExnUnify "Monadic objects not unifiable\n"
			else if nMaybe = 1 then raise Fail "stub: should be able to let-float\n"
			else raise Fail "stub: multiple options"
	| _ => raise Fail "Internal error: matchHeadInLet\n"

(* solveConstr : constr ref -> unit *)
fun solveConstr c = case !c of Solved => () | Eqn ob1ob2 =>
	( if outputUnify then print ("Unifying leftover constraint: "^(constrToStr (!c))^"\n") else ()
	; c := Solved
	; unifyObj NONE ob1ob2 )

(* solveAwakened : unit -> unit *)
fun solveAwakened () = case !awakenedConstrs of [] => () | c::cs =>
	( awakenedConstrs := cs
	; solveConstr c
	; solveAwakened () )

val unifyProblemCounter = ref 0
fun unifyProblemCount () =
	( unifyProblemCounter := (!unifyProblemCounter) + 1
	; !unifyProblemCounter )

(* unify : asyncType * asyncType * (unit -> string) -> unit *)
fun unify (ty1, ty2, errmsg) =
	let val ty1 = Whnf.normalizeType ty1
		val ty2 = Whnf.normalizeType ty2
	in
	( awakenedConstrs := []
	; if outputUnify then
		( print "["
		; print (Int.toString (unifyProblemCount ()))
		; print "] Unifying "
		; print (PrettyPrint.printType ty1)
		; print " and "
		; print (PrettyPrint.printType ty2)
		; print "\n" )
	  else ()
	; unifyType (ty1, ty2)
	; solveAwakened () ) end
		handle (e as ExnUnify s) => (print ("ExnUnify: "^s^"\n"^(errmsg ())^"\n") ; raise e)

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
	| TAtomic (a, impl, S) =>
			let val K = Signatur.sigLookupKind a
				(*fun impl2sp [] = S
				  | impl2sp (N::Ns) = TApp' (N, impl2sp Ns)*)
			in checkTypeSpine (ctx, foldr TApp' S impl, K) end
	| TAbbrev aA => ()
	| TUnknown => raise Fail "Ambiguous typing\n"

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
	| (_, TUnknown) => raise Fail "Ambiguous typing\n"
	| _ => raise Fail "Internal error match: checkObj\n"

(* inferHead : context * head -> context * asyncType *)
and inferHead (ctx, h) = case h of
	  Const (c, impl) =>
			(ctx, #3 (inferSpine (ctxDelLin ctx, foldr App' Nil' impl, Signatur.sigLookupType c)))
	| Var n => let val (ctxo, A) = ctxLookupNum (ctx, n) in (ctxo, TClos (A, Subst.shift n)) end
	| UCVar x =>
			(ctx, TClos (ImplicitVars.ucLookup x, (Subst.shift o length o ctx2list) ctx))
	| LogicVar (_, A, s, rctx, _, _) =>
			let fun calcCtx ss [] = emptyCtx
				  | calcCtx ss ((x, A, mode)::G) =
						let val ss' = Subst.comp (Subst.shift 1, ss)
							val si = Subst.invert (Subst.shift 1)
						in if Subst.hdDef ss then
							let val ss'' = Subst.comp (ss', si)
							in ctxCons (x, TClos (A, ss''), mode) (calcCtx ss'' G) end
						else (* mode <> LIN and hd wi = Undef *)
							calcCtx ss' G
						end
				val () = rctx := (SOME o calcCtx (Subst.invert s) o ctx2list o ctxDelLin) ctx
			in (ctx, TClos (A, s)) end

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
	| (_, TUnknown) => raise Fail "Ambiguous typing\n"
	| _ => raise Fail "Internal error match: inferSpine\n"

(* checkExp : context * expObj * syncType -> context * bool *)
and checkExp (ctx, ex, ty) = case ExpObj.prj ex of
	  Let (p, N, E) =>
			let val S0 = checkPattern (ctxDelLin ctx, p)
				val (ctxm, t1) = checkObj (ctx, N, TMonad' S0)
				val ctxm' = patBind p ctxm
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
