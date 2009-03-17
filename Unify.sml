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
  | constrToStr (Eqn (o1, o2)) =
		(PrettyPrint.printObj $ unnormalizeObj o1)^" == "
		^(PrettyPrint.printObj $ unnormalizeObj o2)
  | constrToStr (Exist o1) = "EXIST: "^(PrettyPrint.printObj $ unnormalizeObj o1)

(* addConstraint : constr vref * constr vref list vref list -> unit *)
fun addConstraint (c, css) =
	( if !outputUnify then print ("Adding constraint "^(constrToStr (!!c))^"\n") else ()
	; app (fn cs => cs ::= c::(!!cs)) (constraints::css) )

(* instantiate : nfObj option vref * nfObj * constr vref list vref * word -> unit *)
fun instantiate (r, rInst, cs, l) =
		if isSome (!! r) then raise Fail "Internal error: double instantiation\n" else
		( r ::= SOME rInst
		; if !outputUnify then
			print ("Instantiating $"^(Word.toString l)^" = "
				^(PrettyPrint.printObj $ unnormalizeObj rInst)^"\n")
		  else ()
		; awakenedConstrs := !!cs @ !awakenedConstrs)

(* lowerLVar : nfAsyncType * nfSpine * subst * context -> nfObj * nfObj nfObjF *)
(* Invariant:
 * lowerLVar (ty, sp, s, G) = (rInst, Y)
 * G |- rInst : ty
 * G1' |- s : G
 * G2' |- sp : ty[s] > a
 * G1'+G2' |- Y = rInst[s] sp : a
 *)
fun lowerLVar (ty, sp, s, ctx) = case (Util.nfTypePrjAbbrev ty, NfSpine.prj sp) of
	  (TLPi (p, A, B), LApp (M, S)) =>
			let val p' = Util.patternT2O p
				val (rInst, Y) = lowerLVar (B, S, Subst.dotMonad (M, s), opatBindNf (p', A) ctx)
			in (NfLLam' (p', rInst), Y) end
	| (AddProd (A, B), ProjLeft S) =>
			let val (rInst, Y) = lowerLVar (A, S, s, ctx)
			in (NfAddPair' (rInst, newNfLVarCtx (SOME ctx) B), Y) end
	| (AddProd (A, B), ProjRight S) =>
			let val (rInst, Y) = lowerLVar (B, S, s, ctx)
			in (NfAddPair' (newNfLVarCtx (SOME ctx) A, rInst), Y) end
	| (TAtomic _, Nil) =>
			let val X = newNfLVarCtx (SOME ctx) ty
			in (X, NfObj.prj $ NfClos (X, s)) end
	| (TMonad _, Nil) =>
			let val X = newNfLVarCtx (SOME ctx) ty
			in (X, NfObj.prj $ NfClos (X, s)) end
	| _ => raise Fail "Internal error: lowerLVar\n"

fun invAtomic (NfAtomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic\n"
val invAtomicP = invAtomic o NfObj.prj

(* lowerAtomic : nfHead * nfSpine -> nfHead * nfSpine *)
fun lowerAtomic (N as (LogicVar {X, ty, s, ctx=ref ctx, cnstr=cs, tag}, S)) =
		(case NfSpine.prj S of Nil => N | _ =>
			let val (rInst, Y) = lowerLVar (ty, S, s, valOf ctx)
			in instantiate (X, rInst, cs, tag); invAtomic Y end)
  | lowerAtomic hS = hS

fun lowerObj (NfAtomic hS) = NfAtomic (lowerAtomic hS)
  | lowerObj N = N

fun lowerExp (NfLet (p, hS, E)) = NfLet (p, lowerAtomic hS, E)
  | lowerExp E = E

(*
fun whnf2obj (NfLinLam N) = LinLam N
  | whnf2obj (NfLam N) = Lam N
  | whnf2obj (NfAddPair N) = AddPair N
  | whnf2obj (NfMonad N) = Monad N
  | whnf2obj (NfAtomic N) = Atomic N
*)

(* newMon (S, G) = M  :  G |- M : S *)
(* newMon : nfSyncType * context -> nfMonadObj *)
fun newMon _ = raise Fail "FIXME newMon"
(*
context split
fun newMon (sTy, ctx) = case SyncType.prj sTy of
	  LExists (p, S1, S2) =>
		let fun splitCtx G =
				if List.all (fn (_, _, m) => m = SOME INT orelse m = NONE) $ ctx2list G
				then (G, G)
				else raise Fail "FIXME: need context split"
			val (ctx1, ctx2) = splitCtx ctx
			val M1 = newMon (S1, ctx1)
		in DeepPair' (M1, newMon (STClos (S2, Subst.subM M1), ctx2)) end
	| TOne => One'
	| TDown A => Down' (newLVarCtx (SOME ctx) A)
	| TAffi A => Affi' (newLVarCtx (SOME ctx) A)  -- only aff and int
	| TBang A => Bang' (newLVarCtx (SOME ctx) A)  -- only int
	*)

(* newMonA : nfAsyncType * context -> nfExpObj *)
fun newMonA (A, ctx) = case NfAsyncType.prj A of
	  TMonad S => NfMon' (newMon (S, ctx))
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
fun splitExp (rOccur, ex) = raise Fail "FIXME2 splitExp"
(*
fun splitExp (rOccur, ex) =
	let fun splitExp' ex = case NfExpObj.prj ex of
			  NfLet (p, N, E) =>
				if case #1 N of
					  LogicVar {X, ...} => eq (X, rOccur)
					| _ => false
				then NONE
				else Option.map (fn (ef, M, ectx, n) =>
								(fn e => NfLet' (p, N, ef e), M,
									ectx o (patBind (fn x=>x) p), n + nbinds p))
							(splitExp' E)
			| NfMon M => SOME (fn e => e, M, fn ctx => ctx, 0)
		fun pruneLetOccur foundL ex = case NfExpObj.prj ex of
			  Mon M => (case foundL of
				  NONE => raise Fail "Internal error: pruneLet\n"
				| SOME L => (L, M))
			| Let (p, N, E) => (case #1 $ lowerAtomic N of
				  (L as LogicVar {X, ty, ctx=ref G, cnstr=cs, tag, ...}) =>
					if eq (X, rOccur) then
						if isSome foundL then
							(*raise ExnUnify "Double occurs check in let\n"*)
							(* FIXME: might set all lvars to {M} *)
							raise Fail "FIXME: set X to {M}"
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
*)

(* pruneCtx : exn -> (nfAsyncType -> nfAsyncType) -> subst -> nfAsyncType context -> nfAsyncType context *)
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
						val A' = pruneType (NfTClos (A, ss'))
					in ctxCons (x, A', mode) (pruneCtx' ss' G) end
				else if mode = SOME LIN then (* and hd ss = Undef *)
					raise e
				else (* mode <> LIN and hd ss = Undef *)
					pruneCtx' (Subst.comp (Subst.shift 1, ss)) G
	in pruneCtx' ss (ctx2list G) end

exception ExnOccur
fun patSub rOccur s G = Subst.patSub (checkExistObj rOccur) Eta.etaContract s G
and checkExistObj rOccur ob =
	let val nestedUndef = ref false
		val undefined = NfClos (normalizeObj (EtaTag (Atomic' (Var (INT, 1), Nil'), (INT, 1))),
							Subst.invert (Subst.shift 1))
		fun catch f x =
			let val nu = !nestedUndef
			in SOME (f x) handle Subst.ExnUndef => (nestedUndef := nu; NONE) end
		fun ctrlBind p (lv : bool) [] = [(p, lv)]
		  | ctrlBind p lv ((p', lv')::lvCtrlCtx) =
				if lv = lv' then (p+p', lv)::lvCtrlCtx
				else (p, lv)::(p', lv')::lvCtrlCtx
		fun isLvarCtrl n [] = false
		  | isLvarCtrl n ((p, lv)::lvCtrlCtx) =
				if n <= p then lv else isLvarCtrl (n-p) lvCtrlCtx
		fun chHead lvCtrlCtx (h as Const _) = (h, false)
		  | chHead lvCtrlCtx (h as UCVar _) = (h, false)
		  | chHead lvCtrlCtx (h as Var (_, n)) = (h, isLvarCtrl n lvCtrlCtx)
		  | chHead lvCtrlCtx (LogicVar {ctx=ref NONE, tag, ...}) =
				raise Fail ("Internal error: no context on $"^Word.toString tag)
		  | chHead lvCtrlCtx (LogicVar (Y as {X=rY, s=sY, ctx=ref (SOME G), ...})) =
				if eq (rY, rOccur) then (* X = H . S{X[p]} --> X = H . S{_}  if p is pattern *)
					if isSome $ patSub rOccur sY (ctxMap nfAsyncTypeToApx G) then
						raise Subst.ExnUndef
					else raise ExnOccur
				else
					let val sY' = Subst.map (chOb true lvCtrlCtx) sY
						val () = Subst.fold (fn (Undef, ()) => nestedUndef := true | _ => ())
								(fn _ => ()) sY'
					in (LogicVar (Y with's sY'), true) end
		and chOb lvArg lvCtrlCtx x = case lowerObj $ NfObj.prj x of
			  NfLLam (p, N) => NfLLam' (p, (chOb lvArg (ctrlBind (nbinds p) lvArg lvCtrlCtx) N)) 
			| NfAddPair (N1, N2) =>
				let val ch = if lvArg then catch (chOb lvArg lvCtrlCtx)
						else SOME o chOb lvArg lvCtrlCtx
				in case (ch N1, ch N2) of
					  (NONE, NONE) => raise Subst.ExnUndef
					| (SOME x, NONE) => (nestedUndef:=true; NfAddPair' (x, undefined))
					| (NONE, SOME x) => (nestedUndef:=true; NfAddPair' (undefined, x))
					| (SOME x1, SOME x2) => NfAddPair' (x1, x2)
				end
			| NfMonad E => NfMonad' (chEx lvArg lvCtrlCtx E)
			| NfAtomic (H, S) =>
				let val (H', lv) = chHead lvCtrlCtx H
				in NfAtomic' (H', chSp lv lvCtrlCtx S) end
		and chSp lvArg lvCtrlCtx x = Util.NfSpineRec.map (chMo lvArg lvCtrlCtx) x
		and chEx lvArg lvCtrlCtx x = case NfExpObj.prj x of
			  NfLet (p, hS, E) =>
				let val (H, S) = lowerAtomic hS
					val (H', lv) = chHead lvCtrlCtx H
				in NfLet' (p, (H', chSp lv lvCtrlCtx S),
						chEx lvArg (ctrlBind (nbinds p) lv lvCtrlCtx) E)
				end
			| NfMon M => NfMon' (chMo lvArg lvCtrlCtx M)
		and chMo false lvCtrlCtx x = Util.NfMonadObjRec.map (chOb false lvCtrlCtx) x
		  | chMo true lvCtrlCtx x = Util.NfMonadObjRec.fold (catch (chOb true lvCtrlCtx))
			(fn Down NONE => raise Subst.ExnUndef
			  | Affi NONE => (nestedUndef:=true; NfInj.Affi' undefined)
			  | Bang NONE => (nestedUndef:=true; NfInj.Bang' undefined)
			  | M => NfMonadObj.inj (Util.NfMonadObjRec.Fmap1 valOf M)) x
		val ob' = chOb true [] ob
	in (ob', not $ !nestedUndef) end

(* objExists : nfObj option vref -> nfObj -> nfObj option *)
(* typeExists : nfObj option vref -> nfAsyncType -> nfAsyncType option *)
val (objExists, typeExists) =
	let open Util
		fun pair r x = (r, x)
		(* FIXME: Remove occurs check from pruneType? *)
		fun pruneType rOccur x = NfAsyncTypeRec.map (pruneTypeSpine rOccur, pruneSyncType rOccur) x
		and pruneTypeSpine rOccur x = NfTypeSpineRec.map (pruneObj rOccur true) x
		and pruneSyncType rOccur x = NfSyncTypeRec.map (pruneType rOccur) x
		and pruneSpine rOccur (srig, x) = NfSpineRec.map (pruneMonad rOccur srig) x
		and pruneMonad rOccur srig x = NfMonadObjRec.map (pruneObj rOccur srig) x
		and pruneMonad' rOccur (srig, x) = pruneMonad rOccur srig x
		and pruneObj rOccur srig x = NfObjRec.unfold (pruneSpine rOccur, pruneExp rOccur)
			(fn (srig, ob) => case lowerObj $ NfObj.prj ob of
				  NfAtomic hS => NfAtomic $ pruneAtomic rOccur srig hS
				| N => NfObj.Fmap ((pair srig, pair srig), pair srig) N)
			(srig, x)
		and pruneExp rOccur (srig, x) = NfExpObjRec.unfold (pruneSpine rOccur, pruneMonad' rOccur)
			(fn (srig, ex) => case lowerExp $ NfExpObj.prj ex of
				  NfLet (p, hS, E) => NfLet (p, pruneAtomic rOccur srig hS, (srig, E))
				| NfMon M => NfMon (srig, M))
			(srig, x)
		and pruneAtomic rOccur srig (v as Var _, S) = (v, (false, S))
		  | pruneAtomic rOccur srig (c as Const _, S) = (c, (srig, S))
		  | pruneAtomic rOccur srig (c as UCVar _, S) = (c, (srig, S))
		  | pruneAtomic rOccur srig (LogicVar {ctx=ref NONE, tag, ...}, _) =
				raise Fail ("Internal error: no context on $"^Word.toString tag)
		  | pruneAtomic rOccur srig
			(LogicVar (Y as {X=rY, ty=A, s=sY, ctx=ref (SOME G), cnstr=cs, tag}), _) =
				if eq (rY, rOccur) then
					(* X = H . S{X[p]} --> X = H . S{_}   if p is pattern
					 * X = H . S_srig{X[s]} --> _         with H <> lvar and H <> var
					 * To simply raise ExnUndef is a completeness bug.  We must either
					 * be in a strongly rigid context or have sY preserve size, i.e.:
					 * For all ground R, |R| >= |R[sY]|
					 *)
					if srig then raise Subst.ExnUndef
					else if isSome $ patSub rOccur sY (ctxMap nfAsyncTypeToApx G)
						then raise Subst.ExnUndef
					else raise ExnOccur
				else let
					val noNestedUndef = ref true
					fun f (ob, nnu) = ( noNestedUndef := (!noNestedUndef andalso nnu) ; ob )
					val sY' = Subst.map (f o checkExistObj rOccur) sY
					val Y' = LogicVar (Y with's sY')
					val w = Subst.fold (* calculate weakening substitution *)
								(fn (Undef, w) => Subst.comp (w, Subst.shift 1)
								  | (_, w) => Subst.dot1 w)
								(fn _ => Subst.id) sY'
				in if Subst.isId w andalso !noNestedUndef then
					(Y', (false, NfInj.Nil'))
				else if !noNestedUndef andalso
						isSome $ Subst.patSub (fn x => (x, true))
								Eta.etaContract sY' (ctxMap nfAsyncTypeToApx G) then
					let val wi = Subst.invert w
						val G' = pruneCtx Subst.ExnUndef (pruneType (vref NONE)) wi G
						val A' = pruneType (vref NONE) (NfTClos (A, wi))
						val Y'w = NfClos (newNfLVarCtx (SOME G') A', w)
						val () = instantiate (rY, Y'w, cs, tag)
					in (#1 $ invAtomicP $ NfClos (Y'w, sY'), (false, NfInj.Nil')) end
				else
					( addConstraint (vref (Exist (NfAtomic' (Y', NfInj.Nil'))), [cs])
					; (Y', (false, NfInj.Nil')) )
				end
		fun objExists1 rOccur ob = SOME (pruneObj rOccur true ob) handle Subst.ExnUndef => NONE
		fun typeExists1 rOccur ty = SOME (pruneType rOccur ty) handle Subst.ExnUndef => NONE
	in (objExists1, typeExists1) end

(*
fun lPrLookup (n, pl) = if n>0 then List.find (fn (m, _) => m=n) pl else NONE

fun linPruneObj (ob, n, pl) = case lowerObj $ Whnf.whnfObj ob of
	  NfLinLam (x, N) => map1 (fn N' => LinLam' (x, N')) $ linPruneObj (N, n+1, pl)
	| NfLam (x, N) => map1 (fn N' => Lam' (x, N')) $ linPruneObj (N, n+1, pl)
	| NfAddPair (N1, N2) =>
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
(*		  | convSub (1::ps) = dot (INT, NfAtomic' (Var (LIN, 1), NfInj.Nil'), comp (convSub ps, shift 1))*)
		  | convSub (n::ps) = dot1 $ convSub (n-1 :: ps)
		datatype lv = LV of obj * int | T | MULT of lv * lv | ADD of lv * lv
(*		fun fo 
		val u = ignore
		val ff = {fki=u, faTy=u, ftyS=u, fsTy=u, fo=fo, fsp=fsp, fe=fe, fm=fm, fp=u}
		*)
	in 0 end

fun unifyType (ty1, ty2) = case (Util.nfTypePrjAbbrev ty1, Util.nfTypePrjAbbrev ty2) of
	  (TLPi (_, A1, B1), TLPi (_, A2, B2)) => (unifySyncType (A1, A2); unifyType (B1, B2))
	| (AddProd (A1, B1), AddProd (A2, B2)) => (unifyType (A1, A2); unifyType (B1, B2))
	| (TMonad S1, TMonad S2) => unifySyncType (S1, S2)
	| (TAtomic (a1, S1), TAtomic (a2, S2)) =>
			if a1 <> a2 then raise Fail (a1^" and "^a2^" differ; shouldn't happen")
			else unifyTSpine (S1, S2)
	| (A1, A2) => raise Fail "Error shouldn't happen: unifyType\n"
and unifySyncType (ty1, ty2) = case (NfSyncType.prj ty1, NfSyncType.prj ty2) of
	  (LExists (_, S1, T1), LExists (_, S2, T2)) => (unifySyncType (S1, S2); unifySyncType (T1, T2))
	| (TOne, TOne) => ()
	| (TDown A1, TDown A2) => unifyType (A1, A2)
	| (TAffi A1, TAffi A2) => unifyType (A1, A2)
	| (TBang A1, TBang A2) => unifyType (A1, A2)
	| (S1, S2) => raise Fail "Error shouldn't happen: unifySyncType\n"
and unifyTSpine (sp1, sp2) = case (NfTypeSpine.prj sp1, NfTypeSpine.prj sp2) of
	  (TNil, TNil) => ()
	| (TApp (N1, S1), TApp (N2, S2)) => (unifyObj NONE (N1, N2); unifyTSpine (S1, S2))
	| (S1, S2) => raise Fail "Error shouldn't happen: unifyTSpine\n"
and unifyObj dryRun (ob1, ob2) =
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	let val ob1' = lowerObj (NfObj.prj ob1)
		val ob2' = lowerObj (NfObj.prj ob2)
		open NfInj
		fun pat2mon p n = case Pattern.prj p of
			  PDepTensor (p1, p2) => DepPair' (pat2mon p1 (n + nbinds p2), pat2mon p2 n)
			| POne => One'
			| PDown _ => Down' (NfAtomic' (Var (LIN, n), Nil'))
			| PAffi _ => Affi' (NfAtomic' (Var (AFF, n), Nil'))
			| PBang _ => Bang' (NfAtomic' (Var (INT, n), Nil'))
		fun invLam p hS = nfredex (NfClos (NfAtomic' hS, Subst.shift $ nbinds p),
				LApp' (pat2mon p 1, Nil'))
		fun invPair p hS = nfredex (NfAtomic' hS, p Nil')
	in case (ob1', ob2') of
		  (NfLLam (_, N1), NfLLam (_, N2)) => unifyObj dryRun (N1, N2)
		| (NfLLam (p, N1), NfAtomic hS2) => unifyObj dryRun (N1, invLam p hS2)
		| (NfAtomic hS1, NfLLam (p, N2)) => unifyObj dryRun (invLam p hS1, N2)
		| (NfAddPair (L1, N1), NfAddPair (L2, N2)) =>
				( unifyObj dryRun (L1, L2)
				; unifyObj dryRun (N1, N2) )
		| (NfAddPair (L1, N1), NfAtomic hS2) =>
				( unifyObj dryRun (L1, invPair ProjLeft' hS2)
				; unifyObj dryRun (N1, invPair ProjRight' hS2) )
		| (NfAtomic hS1, NfAddPair (L2, N2)) =>
				( unifyObj dryRun (invPair ProjLeft' hS1, L2)
				; unifyObj dryRun (invPair ProjRight' hS1, N2) )
		| (NfMonad E1, NfMonad E2) => unifyExp dryRun (E1, E2)
		| (NfAtomic _, NfMonad E2) => raise Fail "FIXME !!!"
		| (NfMonad E1, NfAtomic _) => raise Fail "FIXME !!!"
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
					fun conv' (INL n, ob2) = conv (NfAtomic' (Var n, NfInj.Nil'), ob2) (* FIXME eta *)
					  | conv' (INR ob1, ob2) = conv (ob1, ob2)
				in case SOME (Subst.intersection conv' (s1, s2)) handle ExnUnifyMaybe => NONE of
					  NONE => if isSome dryRun then (valOf dryRun) := false else
							addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2)), [cs1])
					| SOME w => if Subst.isId w then () else 
							if isSome dryRun then (valOf dryRun) := false else
							let val wi = Subst.invert w
								fun pruneType ty = case typeExists (vref NONE) ty of
										  SOME ty' => ty'
										| NONE => raise ExnUnify "pruneType in intersection"
								val A' = pruneType $ NfTClos (A1, wi)
								val G' = pruneCtx (ExnUnify "intersect:pruneCtx") pruneType wi G1
							in instantiate (r1, NfClos (newNfLVarCtx (SOME G') A', w), cs1, tag1) end
				end
			else if isSome dryRun then (valOf dryRun) := false
			else let val apxG1 = ctxMap nfAsyncTypeToApx G1
			in case patSub (vref NONE) s1 apxG1 of
				  SOME (p, s') => unifyLVar (X1 with's s', NfAtomic' hS2, p, s1)
				| NONE =>
					(case patSub (vref NONE) s2 apxG1 of
					  SOME (p, s') => unifyLVar (X2 with's s', NfAtomic' hS1, p, s2)
					| NONE => addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2)), [cs1, cs2]))
			end
	| (LogicVar (X as {s, ctx=ref (SOME G), cnstr=cs, ...}), _) =>
			if isSome dryRun then (valOf dryRun) := false else
			(case patSub (vref NONE) s (ctxMap nfAsyncTypeToApx G) of
				  SOME (p, s') => unifyLVar (X with's s', NfAtomic' hS2, p, s)
				| NONE => addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2)), [cs]))
	| (LogicVar {ctx=ref NONE, tag, ...}, _) =>
			raise Fail ("Internal error: no context on $"^Word.toString tag)
	| (_, LogicVar _) => unifyHead dryRun (hS2, hS1)
	| _ => raise ExnUnify "h1 h2"
and unifyLVar (X as {cnstr=cs, ...}, ob, _::_, s) =
		addConstraint (vref (Eqn (NfAtomic' (LogicVar (X with's s), NfInj.Nil'), ob)), [cs])
  | unifyLVar (X as {X=r, s, cnstr=cs, tag, ...}, ob, [], _) =
	(case objExists r (NfClos (ob, Subst.invert s)) of
		  NONE => raise ExnUnify "Unification failed\n"
		| SOME N => instantiate (r, N, cs, tag))
			handle ExnOccur => addConstraint (vref (Eqn (NfAtomic' (LogicVar X, NfInj.Nil'), ob)), [cs])
and unifySpine dryRun (sp1, sp2) = case (NfSpine.prj sp1, NfSpine.prj sp2) of
	  (Nil, Nil) => ()
	| (LApp (M1, S1), LApp (M2, S2)) => (unifyMon dryRun (M1, M2); unifySpine dryRun (S1, S2))
	| (ProjLeft S1, ProjLeft S2) => unifySpine dryRun (S1, S2)
	| (ProjRight S1, ProjRight S2) => unifySpine dryRun (S1, S2)
	| (ProjLeft _, ProjRight _) => raise ExnUnify "Projections differ\n"
	| (ProjRight _, ProjLeft _) => raise ExnUnify "Projections differ\n"
	| _ => raise Fail "Internal error: unifySpine\n"
and unifyExp dryRun (e1, e2) = case (NfExpObj.prj e1, NfExpObj.prj e2) of
	  (NfMon M1, NfMon M2) => unifyMon dryRun (M1, M2)
	| (NfLet L1, NfMon M2) => unifyLetMon dryRun (L1, M2)
	| (NfMon M1, NfLet L2) => unifyLetMon dryRun (L2, M1)
	| (NfLet L1, NfLet L2) =>
			let fun lVarCount (NfLet (_, (LogicVar _, _), E)) = 1 + lVarCount (NfExpObj.prj E)
				  | lVarCount (NfLet (_, _, E)) = lVarCount (NfExpObj.prj E)
				  | lVarCount (NfMon _) = 0
			in if isSome dryRun andalso (lVarCount (NfLet L1) > 0 orelse lVarCount (NfLet L2) > 0)
				then (valOf dryRun) := false
				else unifyLetLet dryRun (L1, L2)
			end
and unifyLetMon dryRun ((p, hS, E), M) = case lowerAtomic hS of
	  (LogicVar {X, ty, s, ctx=ref G, cnstr=cs, tag}, _ (*=Nil*)) =>
			if isSome dryRun then (valOf dryRun) := false else (* FIXME? *)
			( instantiate (X, NfMonad' (newMonA (ty, valOf G)), cs, tag)
			; unifyExp NONE (NfLet' (p, hS, E), NfMon' M) )
	| _ => raise ExnUnify "let = mon\n"
and unifyMon dryRun (m1, m2) = case (NfMonadObj.prj m1, NfMonadObj.prj m2) of
	  (DepPair (M11, M12), DepPair (M21, M22)) =>
			(unifyMon dryRun (M11, M21); unifyMon dryRun (M12, M22))
	| (One, One) => ()
	| (Down N1, Down N2) => unifyObj dryRun (N1, N2)
	| (Affi N1, Affi N2) => unifyObj dryRun (N1, N2)
	| (Bang N1, Bang N2) => unifyObj dryRun (N1, N2)
	| (MonUndef, _) => raise Fail "Internal error: unifyMon: MonUndef\n"
	| (_, MonUndef) => raise Fail "Internal error: unifyMon: MonUndef\n"
	| _ => raise Fail "Internal error: unifyMon\n"
and unifyLetLet dryRun ((p1, ob1, E1), (p2, ob2, E2)) = raise Fail "FIXME2 unifyLetLet"
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	(*
	let val ob1' = lowerAtomic ob1
		val ob2' = invAtomic $ whnf2obj $ lowerObj $ NfObj.prj $ Atomic' ob2
		val expWhnfInj = ExpObj.inj o (ExpObj.Fmap ((Atomic', fn x=>x, fn x=>x), fn x=>x))
	in case (ob1', NfExpObj.prj E1, ob2', NfExpObj.prj E2) of
		  ((L1 as LogicVar (X1 as {X, ty, s, ctx=ref G, ...}), S (*=Nil*)), Mon M1, _, E2') =>
			(case splitExp (X, Let' (p2, Atomic' ob2', expWhnfInj E2')) of
				  INL (L2, M2) =>
					( unifyHead NONE ((L1, S), (L2, S))
					; unifyMon NONE (M1, M2) )
				| INR (e, M2, ectx, n) =>
					(case Subst.patSub Eta.etaContract s (ctxMap asyncTypeToApx $ valOf G) of
						  NONE => raise Fail "FIXME !!!"
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
			raise Fail "FIXME: postpone as constraint"
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
	end*)
and matchHeadInLet revExn (hS, e, nbe, E, EsX, nMaybe) = raise Fail "FIXME2 matchHeadInLet"
(*and matchHeadInLet revExn (hS, e, nbe, E, EsX, nMaybe) = case (ExpObj.prj E, NfExpObj.prj EsX) of
	  (Let (p, N, E'), Let (_, NsX, EsX')) =>
			let val nbp = nbinds p
				fun hS' () = invAtomicP (Clos (Atomic' hS, Subst.shift nbp))
				val e' = fn s => fn E =>
							let val s' = Subst.dotn nbe s
							in e s (Let' (PClos (p, s'), Clos (N, s'), E)) end
				fun lVarSub 0 = Subst.shift nbp
				  | lVarSub n = Subst.dot (raise Fail "FIXME lVarSub", Util.blank (), lVarSub (n-1))
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
			else if nMaybe = 1 then raise Fail "FIXME: should be able to let-float\n"
			else raise Fail "FIXME: multiple options"
	| _ => raise Fail "Internal error: matchHeadInLet\n"
*)

(* solveConstr : constr vref -> unit *)
fun solveConstr c = case !!c of
	  Solved => ()
	| Eqn (ob1, ob2) =>
		( if !outputUnify then
			print ("Solving leftover constraint: "^(constrToStr (!!c))^"\n") else ()
		; c ::= Solved
		; unifyObj NONE (ob1, ob2) )
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
	; unifyType (normalizeType ty1, normalizeType ty2)
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
