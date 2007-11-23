structure Unify :> UNIFY =
struct

open VRef infix ::=
open Syntax
open Either
open Context
open PatternBind

val outputUnify = true

exception ExnUnify of string

val constraints = vref []
val awakenedConstrs = ref []

(* resetConstrs : unit -> unit *)
fun resetConstrs () = (constraints ::= [])

fun constrToStr Solved = "Solved"
  | constrToStr (Eqn (o1, o2)) = (PrettyPrint.printObj o1)^" == "^(PrettyPrint.printObj o2)

(* addConstraint : constr vref * constr vref list vref list -> unit *)
fun addConstraint (c, css) =
	( if outputUnify then print ("Adding constraint "^(constrToStr (!!c))^"\n") else ()
	; app (fn cs => cs ::= c::(!!cs)) (constraints::css) )

(* instantiate : obj option vref * obj * constr vref list vref * int -> unit *)
fun instantiate (r, rInst, cs, l) =
		if isSome (!! r) then raise Fail "Internal error: double instantiation\n" else
		( r ::= SOME rInst
		; if outputUnify then
			print ("Instantiating $"^(Int.toString l)^" = "^(PrettyPrint.printObj rInst)^"\n")
		  else ()
		; awakenedConstrs := !!cs @ !awakenedConstrs)

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
	| _ => raise Fail "Internal error: lowerLVar\n"

fun invAtomic (Atomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic\n"
val invAtomicP = invAtomic o Obj.prj

(* lowerAtomic : head * apxAsyncType * spine -> head * apxAsyncType * spine *)
fun lowerAtomic (N as (LogicVar {X, ty, s, ctx=ref ctx, cnstr=cs, tag}, _, S)) =
		(case Spine.prj S of Nil => N | _ =>
			let val (rInst, Y) = lowerLVar (ty, S, s, valOf ctx)
			in instantiate (X, rInst, cs, tag); invAtomic Y end)
  | lowerAtomic hAS = hAS

fun lowerObj (NfAtomic hAS) = NfAtomic (lowerAtomic hAS)
  | lowerObj N = N

fun whnf2obj (NfLinLam N) = LinLam N
  | whnf2obj (NfLam N) = Lam N
  | whnf2obj (NfAddPair N) = AddPair N
  | whnf2obj NfUnit = Unit
  | whnf2obj (NfMonad N) = Monad N
  | whnf2obj (NfAtomic N) = Atomic N

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

(* splitExp : obj option vref * expObj
		-> (head * monadObj, (expObj -> expObj) * monadObj * (context -> context) * int) Either *)
fun splitExp (rOccur, ex) =
	let fun splitExp' ex = case Whnf.whnfExp ex of
			  Let (p, N, E) =>
				if case #1 N of
					  LogicVar {X, ...} => eq (X, rOccur)
					| _ => false
				then NONE
				else Option.map (fn (ef, M, ectx, n) =>
								(fn e => Let' (p, Atomic' N, ef e), M,
									ectx o (patBind (fn x=>x) p), n + nbinds p))
							(splitExp' E)
			| Mon M => SOME (fn e => e, M, fn ctx => ctx, 0)
		fun pruneLetOccur foundL ex = case Whnf.whnfExp ex of
			  Mon M => (case foundL of
				  NONE => raise Fail "Internal error: pruneLet\n"
				| SOME L => (L, M))
			| Let (p, N, E) => (case (#1 o lowerAtomic) N of
				  (L as LogicVar {X, ty, ctx=ref G, cnstr=cs, tag, ...}) =>
					if eq (X, rOccur) then
						if isSome foundL then
							raise ExnUnify "Double occurs check in let\n"
							(* stub: might set all lvars to {M} --asn *)
						else
							pruneLetOccur (SOME L) E
					else
						( instantiate (X, Monad' (newMonA (ty, valOf G)), cs, tag)
						; pruneLetOccur foundL (Let' (p, Atomic' N, E)) )
				| _ => raise ExnUnify "Occurs check in let\n")
	in case splitExp' ex of
		  SOME eMcn => RIGHT eMcn
		| NONE => LEFT (pruneLetOccur NONE ex)
	end

(* objExists : bool -> obj option vref -> subst -> obj -> obj option *)
(* typeExists : bool -> obj option vref -> subst -> asyncType -> asyncType option *)
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
		fun f prune rOccur s ob = case whnf2obj (lowerObj (Whnf.whnfObj ob)) of
		  N as Atomic (LogicVar {X=rY, ty=A, s=sY, ctx=ref G, cnstr=cs, tag}, _, _ (* = Nil *)) =>
				if eq (rY, rOccur) then raise Subst.ExnUndef
				else let fun subObjExists Undef = false
				           | subObjExists (Idx _) = true
				           | subObjExists (Ob ob) = isSome (objExists false rOccur s ob)
				in if prune then
					let val weakenSub =
							SOME (Subst.fold
									(fn (ob, w) => if subObjExists ob
										then Subst.dot1 w
										else Subst.comp (w, Subst.shift 1))
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
								val () = instantiate (rY, Y'w, cs, tag)
							in Obj.prj (Clos (Y'w, sY)) end
						| NONE =>
							let val A' = Util.objMapType (f prune(*=true*) rOccur s) (TClos (A, sY))
								val Y' = newLVarCtx NONE A'
								val cnstr = vref (Eqn (Clos (Y', s), Clos (Obj.inj N, s)))
								val () = addConstraint (cnstr, [cs])
							in Obj.prj Y' end
					end
				else (* no pruning *)
					(Subst.fold
						(fn (ob, ()) => if subObjExists ob then () else raise ExnMayNotExist)
						ignore sY
					; N)
				end
		| N => N
		and objExists prune rOccur s ob =
			(SOME (Util.objMapObj (f prune rOccur s) ob) handle Subst.ExnUndef => NONE)
		fun typeExists prune rOccur s ty =
			(SOME (Util.objMapType (f prune rOccur s) ty) handle Subst.ExnUndef => NONE)
	in (objExists, typeExists) end
	(*in SOME (Util.objMapObj f ob) handle Subst.ExnUndef => NONE end*)

fun unifyType (ty1, ty2) = case (Util.typePrjAbbrev ty1, Util.typePrjAbbrev ty2) of
	  (Lolli (A1, B1), Lolli (A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (TPi (x1, A1, B1), TPi (x2, A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (AddProd (A1, B1), AddProd (A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (Top, Top) => ()
	| (TMonad S1, TMonad S2) => unifySyncType (S1, S2)
	| (TAtomic (a1, S1), TAtomic (a2, S2)) =>
			if a1 <> a2 then raise Fail (a1^" and "^a2^" differ; shouldn't happen")
			else unifyTSpine (S1, S2)
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
		  (NfLinLam (_, N1), NfLinLam (_, N2)) => unifyObj dryRun (N1, N2)
		| (NfLam (_, N1), NfLam (_, N2)) => unifyObj dryRun (N1, N2)
		| (NfAddPair (L1, N1), NfAddPair (L2, N2)) =>
				(unifyObj dryRun (L1, L2); unifyObj dryRun (N1, N2))
		| (NfUnit, NfUnit) => ()
		| (NfMonad E1, NfMonad E2) =>
				unifyExp dryRun (E1, E2)
		| (NfAtomic hAS1, NfAtomic hAS2) => unifyHead dryRun (hAS1, hAS2)
		| (N1, N2) => raise Fail "Internal error: unifyObj\n"
	end
and unifyHead dryRun (hAS1 as (h1, _, S1), hAS2 as (h2, _, S2)) = case (h1, h2) of
	  (Const c1, Const c2) =>
			if c1 <> c2 then raise ExnUnify ("Constants "^c1^" and "^c2^" differ\n")
			else unifySpine dryRun (S1, S2)
	| (UCVar x1, UCVar x2) =>
			if x1 <> x2 then raise ExnUnify ("Vars "^x1^" and "^x2^" differ\n")
			else unifySpine dryRun (S1, S2)
	| (Var n1, Var n2) =>
			if n1 <> n2 then raise ExnUnify "Vars differ\n"
			else unifySpine dryRun (S1, S2)
	| (LogicVar {X=r1, ty=A1, s=s1, ctx=ref G1, cnstr=cs1, tag=tag1},
		LogicVar {X=r2, s=s2, cnstr=cs2, tag=tag2, ...}) =>
			if isSome dryRun then (valOf dryRun) := false else
			if eq (r1, r2) then case Subst.patSub Eta.etaContract s1 of
				  NONE => addConstraint (vref (Eqn (Atomic' hAS2, Atomic' hAS1)), [cs1])
				| SOME s1' => (case Subst.patSub Eta.etaContract s2 of
					  NONE => addConstraint (vref (Eqn (Atomic' hAS1, Atomic' hAS2)), [cs1])
					| SOME s2' =>
						let val s' = Subst.intersection (s1', s2')
						in if Subst.isId s' then () else 
							let val si = Subst.invert s'
								val G' = raise Fail "stub: reduce context (G1,si)"
								(*val A' = case typeExists true (ref NONE) s' (TClos (A1, si)) of
									SOME ty => ty | NONE => raise ExnUnify "Unification failed\n"*)
								val A' = TClos (A1, si)
							in instantiate (r1, Clos (newLVarCtx G' A', s'), cs1, tag1) end
						end)
			else (case Subst.patSub Eta.etaContract s1 of
				  SOME s' => unifyLVar (r1, tag1, s', Atomic' hAS2, cs1)
				| NONE =>
					(case Subst.patSub Eta.etaContract s2 of
					  SOME s' => unifyLVar (r2, tag2, s', Atomic' hAS1, cs2)
					| NONE => addConstraint (vref (Eqn (Atomic' hAS1, Atomic' hAS2)), [cs1, cs2])))
	| (LogicVar {X, s, cnstr=cs, tag, ...}, _) =>
			if isSome dryRun then (valOf dryRun) := false else
			(case Subst.patSub Eta.etaContract s of
				  SOME s' => unifyLVar (X, tag, s', Atomic' hAS2, cs)
				| NONE => addConstraint (vref (Eqn (Atomic' hAS1, Atomic' hAS2)), [cs]))
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
			let fun lVarCount (Let (_, (LogicVar _, _, _), E)) = 1 + lVarCount (Whnf.whnfExp E)
				  | lVarCount (Let (_, _, E)) = lVarCount (Whnf.whnfExp E)
				  | lVarCount (Mon _) = 0
			in if isSome dryRun andalso (lVarCount (Let L1) > 0 orelse lVarCount (Let L2) > 0)
				then (valOf dryRun) := false
				else unifyLetLet dryRun (L1, L2)
			end
and unifyLetMon dryRun ((p, hAS, E), M) = case lowerAtomic hAS of
	  (LogicVar {X, ty, s, ctx=ref G, cnstr=cs, tag}, _, _ (*=Nil*)) =>
			if isSome dryRun then (valOf dryRun) := false else (* stub? *)
			( instantiate (X, Monad' (newMonA (ty, valOf G)), cs, tag)
			; unifyExp NONE (Let' (p, Atomic' hAS, E), Mon' M) )
	| _ => raise ExnUnify "let = mon\n"
and unifyMon dryRun (m1, m2) = case (MonadObj.prj m1, MonadObj.prj m2) of
	  (Tensor (M11, M12), Tensor (M21, M22)) =>
			(unifyMon dryRun (M11, M21); unifyMon dryRun (M12, M22))
	| (One, One) => ()
	| (DepPair (N1, M1), DepPair (N2, M2)) => (unifyObj dryRun (N1, N2); unifyMon dryRun (M1, M2))
	| (Norm N1, Norm N2) => unifyObj dryRun (N1, N2)
	| _ => raise Fail "Internal error: unifyMon\n"
and unifyLetLet dryRun ((p1, ob1, E1), (p2, ob2, E2)) =
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	let val ob1' = lowerAtomic ob1
		val ob2' = (invAtomic o whnf2obj o lowerObj o Whnf.whnfObj o Atomic') ob2
		val expWhnfInj = ExpObj.inj o (ExpObj.Fmap ((Atomic', fn x=>x, fn x=>x), fn x=>x))
	in case (ob1', Whnf.whnfExp E1, ob2', Whnf.whnfExp E2) of
		  ((L1 as LogicVar {X, ty, s, ctx=ref G, cnstr=cs, tag}, A', S (*=Nil*)), Mon M1, _, E2') =>
			(case splitExp (X, Let' (p2, Atomic' ob2', expWhnfInj E2')) of
				  LEFT (L2, M2) =>
					( unifyHead NONE ((L1, A', S), (L2, A', S))
					; unifyMon NONE (M1, M2) )
				| RIGHT (e, M2, ectx, n) =>
					(case Subst.patSub Eta.etaContract s of
						  NONE => raise Fail "stub !!!"
						| SOME s' =>
							let val newM = EClos (newMonA (TClos (ty, Subst.shift n),
													ectx (valOf G)), Subst.dotn n s')
							in
								( unifyExp NONE (Let' (PClos (p1, Subst.shift n), Monad' newM,
										Mon' (MClos (M1, Subst.dotn (nbinds p1) (Subst.shift n)))),
									Mon' M2)
								; unifyLVar (X, tag, s', Monad' (e newM), cs) )
							end))
		| (_, E1', (LogicVar _, _, _), Mon M2) =>
			unifyLetLet NONE ((p2, ob2', Mon' M2), (p1, ob1', expWhnfInj E1'))
		| ((LogicVar L1, _, _), E1', (LogicVar L2, _, _), E2') =>
			raise Fail "stub: postpone as constraint"
		| (hAS1, E1', (LogicVar L2, _, _), E2') =>
			let val E = Util.whnfLetSpine (Let' (p2, Atomic' ob2', expWhnfInj E2'))
				val E2rest = matchHeadInLet (hAS1, fn _ => fn e => e, 0, E, E, 0)
			in unifyExp NONE (expWhnfInj E1', E2rest) end
		| ((LogicVar L1, _, _), E1', hAS2, E2') =>
			let val E = Util.whnfLetSpine (Let' (p1, Atomic' ob1', expWhnfInj E1'))
				val E1rest = matchHeadInLet (hAS2, fn _ => fn e => e, 0, E, E, 0)
			in unifyExp NONE (E1rest, expWhnfInj E2') end
		| (hAS1, E1', hAS2, E2') =>
			let val E = Util.whnfLetSpine (Let' (p2, Atomic' ob2', expWhnfInj E2'))
				val E2rest = matchHeadInLet (hAS1, fn _ => fn e => e, 0, E, E, 0)
			in unifyExp dryRun (expWhnfInj E1', E2rest) (*stub: on failure check reverse?*) end
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
				fun EsX'' () = if isLVar NsX then EClos (EsX', lVarSub nbp) else EsX'
				val dryRun = ref true
			in
				case SOME (unifyHead (SOME dryRun) (hAS, NsX))
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

(* solveConstr : constr vref -> unit *)
fun solveConstr c = case !!c of Solved => () | Eqn ob1ob2 =>
	( if outputUnify then print ("Unifying leftover constraint: "^(constrToStr (!!c))^"\n") else ()
	; c ::= Solved
	; unifyObj NONE ob1ob2 )

(* solveAwakened : unit -> unit *)
fun solveAwakened () = case !awakenedConstrs of [] => () | c::cs =>
	( awakenedConstrs := cs
	; solveConstr c
	; solveAwakened () )

(* noConstrs : unit -> unit *)
fun noConstrs () =
	let val () = awakenedConstrs := !!constraints
		val () = solveAwakened ()
		val leftOver = List.mapPartial (fn Solved => NONE | Eqn e => SOME e)
						(map !! (!!constraints))
	in case leftOver of [] => ()
	| _::_ => (app (fn o1o2 => print ("Constr: "^(constrToStr (Eqn o1o2))^"\n")) leftOver
		; raise Fail "Leftover constraints\n") end

val unifyProblemCounter = ref 0
fun unifyProblemCount () =
	( unifyProblemCounter := (!unifyProblemCounter) + 1
	; !unifyProblemCounter )

(* unifyOpt : asyncType * asyncType -> exn option *)
fun unifyOpt (ty1, ty2) =
	let val ty1 = Util.forceNormalizeType ty1
		val ty2 = Util.forceNormalizeType ty2
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
	; solveAwakened ()
	; NONE ) end
		handle (e as ExnUnify _) => SOME e

(* unifiable : asyncType * asyncType -> bool *)
val unifiable = not o isSome o unifyOpt

(* unify : asyncType * asyncType * (unit -> string) -> unit *)
fun unify (ty1, ty2, errmsg) = case unifyOpt (ty1, ty2) of
	  NONE => ()
	| SOME (e as ExnUnify s) => (print ("ExnUnify: "^s^"\n"^(errmsg ())^"\n") ; raise e)
	| SOME e => raise e

end
