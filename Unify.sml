(*  Celf
 *  Copyright (C) 2008 Anders Schack-Nielsen and Carsten Schürmann
 *
 *  This file is part of Celf.
 *
 *  Celf is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Celf is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Celf.  If not, see <http://www.gnu.org/licenses/>.
 *)

signature TLU_Unify = TOP_LEVEL_UTIL
structure Unify :> UNIFY =
struct

open VRef infix ::=
open Syntax infix with's
open Context
open PatternBind

val outputUnify = ref false

exception ExnUnify of string

val constraints = vref [] : constr vref list vref
val awakenedConstrs = ref [] : constr vref list ref

(* resetConstrs : unit -> unit *)
fun resetConstrs () = (constraints ::= [])

fun constrToStr Solved = "Solved"
  | constrToStr (Eqn (o1, o2)) = (PrettyPrint.printObj o1)^" == "^(PrettyPrint.printObj o2)
  | constrToStr (Exist o1) = "EXIST: "^(PrettyPrint.printObj o1)

(* addConstraint : constr vref * constr vref list vref list -> unit *)
fun addConstraint (c, css) =
	( if !outputUnify then print ("Adding constraint "^(constrToStr (!!c))^"\n") else ()
	; app (fn cs => cs ::= c::(!!cs)) (constraints::css) )

(* instantiate : obj option vref * obj * constr vref list vref * word -> unit *)
fun instantiate (r, rInst, cs, l) =
		if isSome (!! r) then raise Fail "Internal error: double instantiation\n" else
		( r ::= SOME rInst
		; if !outputUnify then
			print ("Instantiating $"^(Word.toString l)^" = "^(PrettyPrint.printObj rInst)^"\n")
		  else ()
		; awakenedConstrs := !!cs @ !awakenedConstrs)

(* lowerLVar : asyncType * spine * subst * context -> obj * obj objF *)
fun lowerLVar (ty, sp, s, ctx) = case (Util.typePrjAbbrev ty, Spine.prj sp) of
	  (Lolli (A, B), LinApp (N, S)) =>
			let val (rInst, Y) = lowerLVar (B, S, Subst.dot (LIN, N, s), ctxPushLIN ("", A, ctx))
			in (LinLam' ("", rInst), Y) end
	| (TPi (x, A, B), App (N, S)) =>
			let val x' = getOpt (x, "")
				val (rInst, Y) = lowerLVar (B, S, Subst.dot (INT, N, s), ctxPushINT (x', A, ctx))
			in (Lam' (x', rInst), Y) end
	| (AddProd (A, B), ProjLeft S) =>
			let val (rInst, Y) = lowerLVar (A, S, s, ctx)
			in (AddPair' (rInst, newLVarCtx (SOME ctx) B), Y) end
	| (AddProd (A, B), ProjRight S) =>
			let val (rInst, Y) = lowerLVar (B, S, s, ctx)
			in (AddPair' (newLVarCtx (SOME ctx) A, rInst), Y) end
	| (TAtomic _, Nil) =>
			let val X = newLVarCtx (SOME ctx) ty
			in (X, Obj.prj $ Clos (X, s)) end
	| (TMonad _, Nil) =>
			let val X = newLVarCtx (SOME ctx) ty
			in (X, Obj.prj $ Clos (X, s)) end
	| _ => raise Fail "Internal error: lowerLVar\n"

fun invAtomic (Atomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic\n"
val invAtomicP = invAtomic o Obj.prj

(* lowerAtomic : head * apxAsyncType * spine -> head * apxAsyncType * spine *)
fun lowerAtomic (N as (LogicVar {X, ty, s, ctx=ref ctx, cnstr=cs, tag}, S)) =
		(case Spine.prj S of Nil => N | _ =>
			let val (rInst, Y) = lowerLVar (ty, S, s, valOf ctx)
			in instantiate (X, rInst, cs, tag); invAtomic Y end)
  | lowerAtomic hS = hS

fun lowerObj (NfAtomic hS) = NfAtomic (lowerAtomic hS)
  | lowerObj N = N

fun whnf2obj (NfLinLam N) = LinLam N
  | whnf2obj (NfLam N) = Lam N
  | whnf2obj (NfAddPair N) = AddPair N
  | whnf2obj NfUnit = Unit
  | whnf2obj (NfMonad N) = Monad N
  | whnf2obj (NfAtomic N) = Atomic N

(* newMon (S, G) = M  :  G |- M : S *)
(* newMon : syncType * context -> monadObj *)
fun newMon _ = raise Fail "stub newMon"
(*
context split
fun newMon (sTy, ctx) = case SyncType.prj sTy of
	  TTensor (S1, S2) => Tensor' (newMon (S1, ctx), newMon (S2, ctx))
	| TOne => One'
	| Exists (x, A, S) =>
		let val N = newLVarCtx (SOME ctx) A
			val S' = if isSome x then STClos (S, Subst.sub N) else S
		in DepPair' (N, newMon (S', ctx)) end (* bugfix 27/11-07 --asn *)
	| Async A => Norm' (newLVarCtx (SOME ctx) A)
*)

(* newMonA : asyncType * context -> expObj *)
fun newMonA (A, ctx) = case AsyncType.prj A of
	  TMonad S => Mon' (newMon (S, ctx))
	| _ => raise Fail "Internal error: newMonA\n"

(* splitExp : obj option vref * expObj
		-> (head * monadObj, (expObj -> expObj) * monadObj * (context -> context) * int) sum *)
(* if X doesn't occur in let-head-position in E then
 *   splitExp (X, E) = INR (E'[], M, G[], n) 
 * where E=E'[M], n=nbinds(E') and G'|-E implies G[G']|-M
 *
 * if X does occur a single time and lvars can be instantiated such that
 * E=let {p}=X[s] in M then
 *   splitExp (X, E) = INL (X[s], M)
 * otherwise ExnUnify is raised.
 *)
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
			| Let (p, N, E) => (case #1 $ lowerAtomic N of
				  (L as LogicVar {X, ty, ctx=ref G, cnstr=cs, tag, ...}) =>
					if eq (X, rOccur) then
						if isSome foundL then
							(*raise ExnUnify "Double occurs check in let\n"*)
							(* stub: might set all lvars to {M} --asn *)
							raise Fail "stub: set X to {M}"
						else
							pruneLetOccur (SOME L) E
					else
						( instantiate (X, Monad' (newMonA (ty, valOf G)), cs, tag)
						; pruneLetOccur foundL (Let' (p, Atomic' N, E)) )
				| _ => raise ExnUnify "Occurs check in let\n")
	in case splitExp' ex of
		  SOME eMcn => INR eMcn
		| NONE => INL (pruneLetOccur NONE ex)
	end

(* pruneCtx : exn -> (asyncType -> asyncType) -> subst -> asyncType context -> asyncType context *)
(* pruneCtx calculates G' such that
   G' |- ss : G
   for a strengthening substitution ss
   raises e if ss is not well-typed due to linearity
*)
fun pruneCtx e pruneType ss G =
	let fun pruneCtx' ss [] = emptyCtx
		  | pruneCtx' ss ((x, A, mode)::G) =
				if Subst.hdDef ss then
					let val si = Subst.invert (Subst.shift 1)
						val ss' = Subst.comp (Subst.comp (Subst.shift 1, ss), si)
						val A' = pruneType (TClos (A, ss'))
					in ctxCons (x, A', mode) (pruneCtx' ss' G) end
				else if mode = SOME LIN then (* and hd ss = Undef *)
					raise e
				else (* mode <> LIN and hd ss = Undef *)
					pruneCtx' (Subst.comp (Subst.shift 1, ss)) G
	in pruneCtx' ss (ctx2list G) end

exception ExnOccur
(* objExists : obj option vref -> obj -> obj option *)
(* typeExists : obj option vref -> asyncType -> asyncType option *)
val (objExists, typeExists) =
	let fun allowPrune nprune = not $ isSome nprune
		fun xExists NONE f x = (SOME (f x) handle Subst.ExnUndef => NONE)
		  | xExists (SOME (npR as ref np)) f x =
				(SOME (f x) handle Subst.ExnUndef => (npR := np; NONE))
		fun f nprune rOccur srig ob = case whnf2obj $ lowerObj $ Whnf.whnfObj ob of
		  Atomic (LogicVar {ctx=ref NONE, tag, ...}, _) =>
				raise Fail ("Internal error: no context on $"^Word.toString tag)
		| Atomic (LogicVar (Y as {X=rY, ty=A, s=sY, ctx=ref (SOME G), cnstr=cs, tag}), _) =>
				if eq (rY, rOccur) then
					(* X = H . S{X[p]} --> X = H . S{_}   if p is pattern
					 * X = H . S_srig{X[s]} --> _         with H <> lvar and H <> var
					 * To simply raise ExnUndef is a completeness bug.  We must either
					 * be in a strongly rigid context or have sY preserve size, i.e.:
					 * For all ground R, |R| >= |R[sY]|
					 *)
					if srig andalso allowPrune nprune then raise Subst.ExnUndef
					else if isSome $ Subst.patSub Eta.etaContract sY (ctxMap asyncTypeToApx G)
						then raise Subst.ExnUndef
					else raise ExnOccur
				else let
					val needSubPrune = ref false
					fun getOptUndef (SOME ob) = ob
					  | getOptUndef NONE = raise Subst.ExnUndef
					val sY' = Subst.map (getOptUndef o objExistsP (SOME needSubPrune) rOccur) sY
					val w = Subst.fold (* calculate weakening substitution *)
								(fn (Undef, w) => Subst.comp (w, Subst.shift 1)
								  | (_, w) => Subst.dot1 w)
								(fn _ => Subst.id) sY'
					val needPrune = not $ Subst.isId w
					val N' = if allowPrune nprune andalso needPrune then
								let val wi = Subst.invert w
									val pruneType = Util.objSRigMapType (f NONE rOccur) srig
									val G' = pruneCtx Subst.ExnUndef pruneType wi G
									val A' = pruneType (TClos (A, wi))
									val Y'w = Clos (newLVarCtx (SOME G') A', w)
									val () = instantiate (rY, Y'w, cs, tag)
								in Obj.prj $ Clos (Y'w, sY') end
							else Atomic (LogicVar (Y with's sY'), Nil')
					val () = if allowPrune nprune andalso !needSubPrune then
								case N' of Atomic (LogicVar {cnstr, ...}, _) =>
									addConstraint (vref (Exist (Obj.inj N')), [cnstr])
								| _ => raise Fail "Internal error: no lvar"
							else ()
					val () = Option.app
							(fn p => p := (!p orelse needPrune orelse !needSubPrune)) nprune
				in N' end
		| N => N
		and objExistsP nprune rOccur ob =
			xExists nprune (Util.objSRigMapObj (f nprune rOccur) true) ob
		fun typeExistsP nprune rOccur ty =
			xExists nprune (Util.objSRigMapType (f nprune rOccur) true) ty
	in (objExistsP NONE, typeExistsP NONE) end

(*
fun lPrLookup (n, pl) = if n>0 then List.find (fn (m, _) => m=n) pl else NONE

fun linPruneObj (ob, n, pl) = case lowerObj $ Whnf.whnfObj ob of
	  NfLinLam (x, N) => map1 (fn N' => LinLam' (x, N')) $ linPruneObj (N, n+1, pl)
	| NfLam (x, N) => map1 (fn N' => Lam' (x, N')) $ linPruneObj (N, n+1, pl)
	| NfAddPair (N1, N2) =>
	| NfUnit => (Unit', (true, #2 pl))
	| NfMonad E => map1 Monad' $ linPruneExp (E, n, pl)
	| NfAtomic (H, S) => linPruneSpine (S, n, linPruneHead (H, n, pl))
and linPruneHead (H, n, pl) = case H of
	  Var (INT, m) => (case lPrLookup (m-n, #2 pl) of
		  NONE => pl
		| SOME NONE => raise Subst.ExnUndef
		| SOME (SOME ls) =>)
	| LogicVar X =>
	| _ => pl (* Const, UCVar, Var (LIN, _) *)
and linPruneSpine (sp, n, pl) = case Spine.prj sp of
	  Nil => (Nil', pl)
	| App (N, S) => map1 (fn S' => App' (Clos (N, _), S')) $ linPruneSpine (S, n, pl)
	| LinApp (N, S) => linPruneSpine (S, n, linPruneObj (N, n, pl))
	| ProjLeft S => map1 ProjLeft' $ linPruneSpine (S, n, pl)
	| ProjRight S => map1 ProjRight' $ linPruneSpine (S, n, pl)
*)

fun qsort [] a = a
  | qsort (x::xs) a =
		let val (l, g) = List.partition (fn y => y<x) xs
		in qsort l (x :: qsort g a) end

fun linPrune (ob, pl) =
	let val pl' = qsort pl
		open Subst
		fun convSub [] = id
		  | convSub (1::ps) = dot (INT, Atomic' (Var (LIN, 1), Nil'), comp (convSub ps, shift 1))
		  | convSub (n::ps) = dot1 $ convSub (n-1 :: ps)
		datatype lv = LV of obj * int | T | MULT of lv * lv | ADD of lv * lv
(*		fun fo 
		val u = ignore
		val ff = {fki=u, faTy=u, ftyS=u, fsTy=u, fo=fo, fsp=fsp, fe=fe, fm=fm, fp=u}
		*)
	in 0 end

fun unifyType (ty1, ty2) = case (Util.typePrjAbbrev ty1, Util.typePrjAbbrev ty2) of
	  (Lolli (A1, B1), Lolli (A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (TPi (x1, A1, B1), TPi (x2, A2, B2)) =>
			let val B1' = if isSome x1 then B1 else TClos (B1, Subst.shift 1)
				val B2' = if isSome x2 then B2 else TClos (B2, Subst.shift 1)
			in (unifyType (A1, A2); unifyType (B1', B2')) end
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
	| (Exists (x1, A1, S1), Exists (x2, A2, S2)) =>
			let val S1' = if isSome x1 then S1 else STClos (S1, Subst.shift 1)
				val S2' = if isSome x2 then S2 else STClos (S2, Subst.shift 1)
			in (unifyType (A1, A2); unifySyncType (S1', S2')) end
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
		fun invLam' M ap hS =
			redex (Clos (Atomic' hS, Subst.shift 1),
					ap (Atomic' (Var (M, 1), Nil'), Nil'))
		fun invLam LIN hS = invLam' LIN LinApp' hS
		  | invLam INT hS = invLam' INT App' hS
		fun invPair p hS = redex (Atomic' hS, p Nil')
	in case (ob1', ob2') of
		  (NfLinLam (_, N1), NfLinLam (_, N2)) => unifyObj dryRun (N1, N2)
		| (NfLinLam (_, N1), NfAtomic hS2) => unifyObj dryRun (N1, invLam LIN hS2)
		| (NfAtomic hS1, NfLinLam (_, N2)) => unifyObj dryRun (invLam LIN hS1, N2)
		| (NfLam (_, N1), NfLam (_, N2)) => unifyObj dryRun (N1, N2)
		| (NfLam (_, N1), NfAtomic hS2) => unifyObj dryRun (N1, invLam INT hS2)
		| (NfAtomic hS1, NfLam (_, N2)) => unifyObj dryRun (invLam INT hS1, N2)
		| (NfAddPair (L1, N1), NfAddPair (L2, N2)) =>
				( unifyObj dryRun (L1, L2)
				; unifyObj dryRun (N1, N2) )
		| (NfAddPair (L1, N1), NfAtomic hS2) =>
				( unifyObj dryRun (L1, invPair ProjLeft' hS2)
				; unifyObj dryRun (N1, invPair ProjRight' hS2) )
		| (NfAtomic hS1, NfAddPair (L2, N2)) =>
				( unifyObj dryRun (invPair ProjLeft' hS1, L2)
				; unifyObj dryRun (invPair ProjRight' hS1, N2) )
		| (NfUnit, NfUnit) => ()
		| (NfAtomic _, NfUnit) => ()
		| (NfUnit, NfAtomic _) => ()
		| (NfMonad E1, NfMonad E2) => unifyExp dryRun (E1, E2)
		| (NfAtomic _, NfMonad E2) => raise Fail "stub !!!"
		| (NfMonad E1, NfAtomic _) => raise Fail "stub !!!"
		| (NfAtomic hS1, NfAtomic hS2) => unifyHead dryRun (hS1, hS2)
		| (N1, N2) => raise Fail "Internal error: unifyObj\n"
	end
and unifyHead dryRun (hS1 as (h1, S1), hS2 as (h2, S2)) = case (h1, h2) of
	  (Const c1, Const c2) =>
			if c1 <> c2 then raise ExnUnify ("Constants "^c1^" and "^c2^" differ\n")
			else unifySpine dryRun (S1, S2)
	| (UCVar x1, UCVar x2) =>
			if x1 <> x2 then raise ExnUnify ("Vars "^x1^" and "^x2^" differ\n")
			else unifySpine dryRun (S1, S2)
	| (Var n1, Var n2) =>
			if n1 <> n2 then raise ExnUnify "Vars differ\n"
			else unifySpine dryRun (S1, S2)
	| (LogicVar (X1 as {X=r1, ty=A1, s=s1, ctx=ref (SOME G1), cnstr=cs1, tag=tag1}),
		LogicVar (X2 as {X=r2, s=s2, cnstr=cs2, ...})) =>
			if eq (r1, r2) then
				let val dryRunIntersect = ref true
					exception ExnUnifyMaybe
					fun conv ob1ob2 = case SOME (unifyObj (SOME dryRunIntersect) ob1ob2)
							handle ExnUnify _ => NONE of
						  SOME () => if !dryRunIntersect then true
								else raise ExnUnifyMaybe
						| NONE => false
					fun conv' (INL n, ob2) = conv (Atomic' (Var n, Nil'), ob2) (* stub eta --asn *)
					  | conv' (INR ob1, ob2) = conv (ob1, ob2)
				in case SOME (Subst.intersection conv' (s1, s2)) handle ExnUnifyMaybe => NONE of
					  NONE => if isSome dryRun then (valOf dryRun) := false else
							addConstraint (vref (Eqn (Atomic' hS1, Atomic' hS2)), [cs1])
					| SOME w => if Subst.isId w then () else 
							if isSome dryRun then (valOf dryRun) := false else
							let val wi = Subst.invert w
								fun pruneType ty = case typeExists (vref NONE) ty of
										  SOME ty' => ty'
										| NONE => raise ExnUnify "pruneType in intersection"
								val A' = pruneType $ TClos (A1, wi)
								val G' = pruneCtx (ExnUnify "intersect:pruneCtx") pruneType wi G1
							in instantiate (r1, Clos (newLVarCtx (SOME G') A', w), cs1, tag1) end
				end
			else if isSome dryRun then (valOf dryRun) := false
			else let val apxG1 = ctxMap asyncTypeToApx G1
			in case Subst.patSub Eta.etaContract s1 apxG1 of
				  SOME (p, s') => unifyLVar (X1 with's s', Atomic' hS2, p, s1)
				| NONE =>
					(case Subst.patSub Eta.etaContract s2 apxG1 of
					  SOME (p, s') => unifyLVar (X2 with's s', Atomic' hS1, p, s2)
					| NONE => addConstraint (vref (Eqn (Atomic' hS1, Atomic' hS2)), [cs1, cs2]))
			end
	| (LogicVar (X as {s, ctx=ref (SOME G), cnstr=cs, ...}), _) =>
			if isSome dryRun then (valOf dryRun) := false else
			(case Subst.patSub Eta.etaContract s (ctxMap asyncTypeToApx G) of
				  SOME (p, s') => unifyLVar (X with's s', Atomic' hS2, p, s)
				| NONE => addConstraint (vref (Eqn (Atomic' hS1, Atomic' hS2)), [cs]))
	| (LogicVar {ctx=ref NONE, tag, ...}, _) =>
			raise Fail ("Internal error: no context on $"^Word.toString tag)
	| (_, LogicVar _) => unifyHead dryRun (hS2, hS1)
	| _ => raise ExnUnify "h1 h2"
and unifyLVar (X as {cnstr=cs, ...}, ob, _::_, s) =
		addConstraint (vref (Eqn (Atomic' (LogicVar (X with's s), Nil'), ob)), [cs])
  | unifyLVar (X as {X=r, s, cnstr=cs, tag, ...}, ob, [], _) =
	(case objExists r (Clos (ob, Subst.invert s)) of
		  NONE => raise ExnUnify "Unification failed\n"
		| SOME N => instantiate (r, N, cs, tag))
			handle ExnOccur => addConstraint (vref (Eqn (Atomic' (LogicVar X, Nil'), ob)), [cs])
and unifySpine dryRun (sp1, sp2) = case (Spine.prj sp1, Spine.prj sp2) of
	  (Nil, Nil) => ()
	| (App (N1, S1), App (N2, S2)) => (unifyObj dryRun (N1, N2); unifySpine dryRun (S1, S2))
	| (LinApp (N1, S1), LinApp (N2, S2)) => (unifyObj dryRun (N1, N2); unifySpine dryRun (S1, S2))
	| (ProjLeft S1, ProjLeft S2) => unifySpine dryRun (S1, S2)
	| (ProjRight S1, ProjRight S2) => unifySpine dryRun (S1, S2)
	| (ProjLeft _, ProjRight _) => raise ExnUnify "Projections differ\n"
	| (ProjRight _, ProjLeft _) => raise ExnUnify "Projections differ\n"
	| _ => raise Fail "Internal error: unifySpine\n"
and unifyExp dryRun (e1, e2) = case (Whnf.whnfExp e1, Whnf.whnfExp e2) of
	  (Mon M1, Mon M2) => unifyMon dryRun (M1, M2)
	| (Let L1, Mon M2) => unifyLetMon dryRun (L1, M2)
	| (Mon M1, Let L2) => unifyLetMon dryRun (L2, M1)
	| (Let L1, Let L2) =>
			let fun lVarCount (Let (_, (LogicVar _, _), E)) = 1 + lVarCount (Whnf.whnfExp E)
				  | lVarCount (Let (_, _, E)) = lVarCount (Whnf.whnfExp E)
				  | lVarCount (Mon _) = 0
			in if isSome dryRun andalso (lVarCount (Let L1) > 0 orelse lVarCount (Let L2) > 0)
				then (valOf dryRun) := false
				else unifyLetLet dryRun (L1, L2)
			end
and unifyLetMon dryRun ((p, hS, E), M) = case lowerAtomic hS of
	  (LogicVar {X, ty, s, ctx=ref G, cnstr=cs, tag}, _ (*=Nil*)) =>
			if isSome dryRun then (valOf dryRun) := false else (* stub? *)
			( instantiate (X, Monad' (newMonA (ty, valOf G)), cs, tag)
			; unifyExp NONE (Let' (p, Atomic' hS, E), Mon' M) )
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
		val ob2' = invAtomic $ whnf2obj $ lowerObj $ Whnf.whnfObj $ Atomic' ob2
		val expWhnfInj = ExpObj.inj o (ExpObj.Fmap ((Atomic', fn x=>x, fn x=>x), fn x=>x))
	in case (ob1', Whnf.whnfExp E1, ob2', Whnf.whnfExp E2) of
		  ((L1 as LogicVar (X1 as {X, ty, s, ctx=ref G, ...}), S (*=Nil*)), Mon M1, _, E2') =>
			(case splitExp (X, Let' (p2, Atomic' ob2', expWhnfInj E2')) of
				  INL (L2, M2) =>
					( unifyHead NONE ((L1, S), (L2, S))
					; unifyMon NONE (M1, M2) )
				| INR (e, M2, ectx, n) =>
					(case Subst.patSub Eta.etaContract s (ctxMap asyncTypeToApx $ valOf G) of
						  NONE => raise Fail "stub !!!"
						| SOME (p, s') =>
							let val newM = EClos (newMonA (TClos (ty, Subst.shift n),
													ectx $ valOf G), Subst.dotn n s')
							in
								( unifyExp NONE (Let' (PClos (p1, Subst.shift n), Monad' newM,
										Mon' (MClos (M1, Subst.dotn (nbinds p1) (Subst.shift n)))),
									Mon' M2)
								; unifyLVar (X1 with's s', Monad' (e newM), p, s) )
							end))
		| (_, E1', (LogicVar _, _), Mon M2) =>
			unifyLetLet NONE ((p2, ob2', Mon' M2), (p1, ob1', expWhnfInj E1'))
		| ((LogicVar L1, _), E1', (LogicVar L2, _), E2') =>
			raise Fail "stub: postpone as constraint"
			(* or search E1' and E2' for heads that can be moved to front *)
		| (_ (* ob1' <> LVar *), E1', (LogicVar L2, _), E2') =>
			let val E = Util.whnfLetSpine (Let' (p2, Atomic' ob2', expWhnfInj E2'))
				val E2rest = matchHeadInLet NONE (ob1', fn _ => fn e => e, 0, E, E, 0)
			in unifyExp NONE (expWhnfInj E1', E2rest) end
		| ((LogicVar L1, _), E1', _ (* ob2' <> LVar *), E2') =>
			let val E = Util.whnfLetSpine (Let' (p1, Atomic' ob1', expWhnfInj E1'))
				val E1rest = matchHeadInLet NONE (ob2', fn _ => fn e => e, 0, E, E, 0)
			in unifyExp NONE (E1rest, expWhnfInj E2') end
		| (_ (* ob1' <> LVar *), E1', _ (* ob2' <> LVar *), E2') => let exception ExnTryRev in
			let val E = Util.whnfLetSpine (Let' (p2, Atomic' ob2', expWhnfInj E2'))
				val E2rest = matchHeadInLet (SOME ExnTryRev) (ob1', fn _ => fn e => e, 0, E, E, 0)
			in unifyExp dryRun (expWhnfInj E1', E2rest) end handle ExnTryRev =>
			let val E = Util.whnfLetSpine (Let' (p1, Atomic' ob1', expWhnfInj E1'))
				val E1rest = matchHeadInLet NONE (ob2', fn _ => fn e => e, 0, E, E, 0)
			in unifyExp dryRun (E1rest, expWhnfInj E2') end end
	end
and matchHeadInLet revExn (hS, e, nbe, E, EsX, nMaybe) = case (ExpObj.prj E, Whnf.whnfExp EsX) of
	  (Let (p, N, E'), Let (_, NsX, EsX')) =>
			let val nbp = nbinds p
				fun hS' () = invAtomicP (Clos (Atomic' hS, Subst.shift nbp))
				val e' = fn s => fn E =>
							let val s' = Subst.dotn nbe s
							in e s (Let' (PClos (p, s'), Clos (N, s'), E)) end
				fun lVarSub 0 = Subst.shift nbp
				  | lVarSub n = Subst.dot (raise Fail "stub lVarSub", Util.blank (), lVarSub (n-1))
				fun isLVar (LogicVar _, _) = true
				  | isLVar _ = false
				fun EsX'' () = if isLVar NsX then EClos (EsX', lVarSub nbp) else EsX'
				val dryRun = ref true
			in
				case SOME (unifyHead (SOME dryRun) (hS, NsX))
						handle ExnUnify _ => NONE of
				  SOME () =>
					if !dryRun then (* unify success *)
						e (Subst.shift nbp) (EClos (E', Subst.switchSub (nbp, nbe)))
					else (* unify maybe *)
						matchHeadInLet revExn (hS' (), e', nbe + nbp, E', EsX'' (), nMaybe + 1)
				| NONE => (* unify failure *)
						matchHeadInLet revExn (hS' (), e', nbe + nbp, E', EsX'' (), nMaybe)
			end
	| (Mon _, Mon _) =>
			if nMaybe = 0 then raise ExnUnify "Monadic objects not unifiable\n"
			else if isSome revExn then raise valOf revExn
			else if nMaybe = 1 then raise Fail "stub: should be able to let-float\n"
			else raise Fail "stub: multiple options"
	| _ => raise Fail "Internal error: matchHeadInLet\n"

(* solveConstr : constr vref -> unit *)
fun solveConstr c = case !!c of
	  Solved => ()
	| Eqn ob1ob2 =>
		( if !outputUnify then
			print ("Solving leftover constraint: "^(constrToStr (!!c))^"\n") else ()
		; c ::= Solved
		; unifyObj NONE ob1ob2 )
	| Exist ob1 =>
		( if !outputUnify then
			print ("Solving leftover constraint: "^(constrToStr (!!c))^"\n") else ()
		; c ::= Solved
		; if isSome $ objExists (vref NONE) ob1 then ()
			else raise ExnUnify "Exist constraint failed" )

(* solveAwakened : unit -> unit *)
fun solveAwakened () = case !awakenedConstrs of [] => () | c::cs =>
	( awakenedConstrs := cs
	; solveConstr c
	; solveAwakened () )

(* noConstrs : unit -> unit *)
fun noConstrs () =
	let val () = awakenedConstrs := !!constraints
		val () = solveAwakened ()
		val leftOver = List.mapPartial (fn Solved => NONE | e => SOME e)
						(map !! (!!constraints))
	in case leftOver of [] => ()
	| _::_ => (app (fn c => print ("Constr: "^(constrToStr c)^"\n")) leftOver
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
	; if !outputUnify then
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
