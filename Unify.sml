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
val monConstrs = vref [] : constr vref list vref

(* resetConstrs : unit -> unit *)
fun resetConstrs () = (constraints ::= [])

fun constrToStr Solved = "Solved"
  | constrToStr (Eqn (o1, o2, _)) =
		(PrettyPrint.printObj $ unnormalizeObj o1)^" == "
		^(PrettyPrint.printObj $ unnormalizeObj o2)
  | constrToStr (Exist (o1, _)) = "EXIST: "^(PrettyPrint.printObj $ unnormalizeObj o1)

(* addConstraint : constr vref * constr vref list vref list -> unit *)
fun addConstraint (c, css) =
	( if !outputUnify then print ("Adding constraint "^(constrToStr (!!c))^"\n") else ()
	; app (fn cs => cs ::= c::(!!cs)) (constraints::css) )

(* addLiveConstraint : constr vref * constr vref list vref list -> unit *)
(*fun addLiveConstraint (c, css) =
	( addConstraint (c, css)
	; awakenedConstrs := c :: !awakenedConstrs )*)

(* instantiate : nfObj option vref * nfObj * constr vref list vref * word -> unit *)
fun instantiate (r, rInst, cs, l) =
	if isSome (!! r) then raise Fail "Internal error: double instantiation" else
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
	| _ => raise Fail "Internal error: lowerLVar"

fun invAtomic (NfAtomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic"
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

fun isLVar (LogicVar _, _) = true
  | isLVar _ = false

fun invLVar (LogicVar Z, _) = Z
  | invLVar _ = raise Fail "Internal error: invLVar"

fun pat2mon p =
	let open NfInj
		fun pat2mon' p n = case Pattern.prj p of
			  PDepTensor (p1, p2) => DepPair' (pat2mon' p1 (n + nbinds p2), pat2mon' p2 n)
			| POne => One'
			| PDown _ => Down' (NfAtomic' (Var (LIN, n), Nil'))
			| PAffi _ => Affi' (NfAtomic' (Var (AFF, n), Nil'))
			| PBang _ => Bang' (NfAtomic' (Var (INT, n), Nil'))
	in pat2mon' p 1 end

(* ctx2int G = (p, G_I)
 * computes the maximal linear-changing substitution
 * G_I |- lcis2sub(p) : G *)
(* ctx2int : context -> (subMode * int) list * context *)
fun ctx2int G =
	let val G' = ctx2list G
		fun ctx2int' n [] = ([], emptyCtx)
		  | ctx2int' n ((x, A, m)::ctx) =
			let val (p, ctx') = ctx2int' (n+1) ctx
				val (p', m') = case m of
					  NONE => (p, NONE)
					| SOME INT => (p, SOME INT)
					| SOME AFF => ((INT4AFF, n)::p, SOME INT)
					| SOME LIN => ((INT4LIN, n)::p, SOME INT)
			in (p', ctxCons (x, A, m') ctx') end
	in ctx2int' 1 G' end

(* newMonI (S, G) = M
 * G |- M : S  assuming G is entirely intuitionistic *)
(* newMonI : nfSyncType * context -> nfMonadObj *)
fun newMonI (sTy, ctx) = case NfSyncType.prj sTy of
	  LExists (p, S1, S2) =>
		let val M1 = newMonI (S1, ctx)
		in NfInj.DepPair' (M1, newMonI (NfSTClos (S2, Subst.subM M1), ctx)) end
	| TOne => NfInj.One'
	| TDown A => NfInj.Down' (newNfLVarCtx (SOME ctx) A)
	| TAffi A => NfInj.Affi' (newNfLVarCtx (SOME ctx) A)
	| TBang A => NfInj.Bang' (newNfLVarCtx (SOME ctx) A)

(* newMon (S, G) = (p, M)
 * G_I |- lcis2sub(p) : G
 * G_I |- M : S           *)
(* newMon : nfSyncType * context -> (subMode * int) list * nfMonadObj *)
fun newMon (S, G) =
	let val (p, GI) = ctx2int G
	in (p, newMonI (S, GI)) end

(* newMonA : nfAsyncType * context -> (subMode * int) list * nfObj *)
fun newMonA (A, ctx) = case NfAsyncType.prj A of
	  TMonad S => map2 (NfMonad' o NfMon') (newMon (S, ctx))
	| _ => raise Fail "Internal error: newMonA"

(* headCountExp obj option vref * nfExpObj -> int *)
fun headCountExp (rOccur, ex) = case NfExpObj.prj ex of
	  NfLet (_, (LogicVar {X, ...}, _), E) =>
		if eq (X, rOccur) then 1 + headCountExp (rOccur, E) else headCountExp (rOccur, E)
	| NfLet (_, _, E) => headCountExp (rOccur, E)
	| NfMon _ => 0

structure NS = NatSet

fun occurObj ob = case SOME (lowerObj (NfObj.prj ob)) handle Subst.ExnUndef => NONE of
	  NONE => NS.empty
	| SOME (NfLLam (p, N)) => NS.decrn (nbinds p) (occurObj N)
	| SOME (NfAddPair (N1, N2)) => NS.union (occurObj N1, occurObj N2)
	| SOME (NfMonad E) => occurExp E
	| SOME (NfAtomic (H, S)) => NS.union (occurHead H, occurSpine S)
and occurHead h = case h of
	  Const _ => NS.empty
	| Var (_, n) => NS.singleton n
	| UCVar _ => NS.empty
	| LogicVar {ctx=ref NONE, ...} => raise Fail "Internal error: occurHead: no ctx"
	| LogicVar {ctx=ref (SOME G), s, ...} => occurSub G s
and occurSub ctx s =
	let val () = if List.all (isSome o #3) $ ctx2list ctx then () else
					raise Fail "Internal error: occurSub: lvar with non-pruned ctx"
		val ctxL = ctxLength ctx
		val subL = Subst.fold (fn (_, n) => n+1) (fn _ => 0) s
		fun occurSubOb Undef = NS.empty
		  | occurSubOb (Ob (_, ob)) = occurObj ob
		  | occurSubOb (Idx (_, n)) = NS.singleton n
	in Subst.fold (NS.union o (map1 occurSubOb)) (fn m => NS.occurFromTo (m+1) (ctxL-subL+m)) s end
and occurSpine sp = case NfSpine.prj sp of
	  Nil => NS.empty
	| LApp (M, S) => NS.union (occurMonadObj M, occurSpine S)
	| ProjLeft S => occurSpine S
	| ProjRight S => occurSpine S
and occurExp e = case NfExpObj.prj e of
	  NfLet (p, (H, S), E) =>
		NS.union (occurHead H, NS.union (occurSpine S, NS.decrn (nbinds p) (occurExp E)))
	| NfMon M => occurMonadObj M
and occurMonadObj m = case NfMonadObj.prj m of
	  DepPair (M1, M2) => NS.union (occurMonadObj M1, occurMonadObj M2)
	| One => NS.empty
	| Down N => occurObj N
	| Affi N => occurObj N
	| Bang N => occurObj N
	| MonUndef => raise Fail "Internal error: occurMonadObj: MonUndef"

fun ctxSubList ctx [] = ctx
  | ctxSubList ctx (n::ns) = ctxSubList (#1 $ ctxLookupNum (ctx, n)) ns
fun ctxSubSet ctx ns = ctxSubList ctx (NS.toList ns)

fun synthHead ctx h = case h of
	  Const c => (ctx, normalizeType $ Signatur.sigLookupType c)
	| Var (m, n) =>
		let val (ctxo, m', A) = ctxLookupNum (ctx, n)
			val () = if m=m' then () else raise Fail "Internal error: Linearity mismatch"
		in (ctxo, NfTClos (A, Subst.shift n)) end
	| UCVar x =>
		(ctx, NfTClos (normalizeType $ ImplicitVars.ucLookup x,
				Subst.shift $ ctxLength ctx))
	| LogicVar {ctx=ref NONE, ...} => raise Fail "Internal error: synthHead: no ctx"
	| LogicVar {X, ty, s, ctx=ref (SOME G), ...} =>
		(ctxSubSet ctx (occurSub G s), NfTClos (ty, s))
fun synthSpine ctx sp ty = case (NfSpine.prj sp, Util.nfTypePrjAbbrev ty) of
	  (Nil, _) => (ctx, ty)
	| (LApp (M, S), TLPi (_, _, B)) =>
		synthSpine (ctxSubSet ctx (occurMonadObj M)) S (NfTClos (B, Subst.subM M))
	| (ProjLeft S, AddProd (A, _)) => synthSpine ctx S A
	| (ProjRight S, AddProd (_, B)) => synthSpine ctx S B
	| _ => raise Fail "Internal error: synthSpine match"
fun synthAtomic ctx (H, S) =
	let val (ctx1, ty1) = synthHead ctx H
	in synthSpine ctx1 S ty1 end

exception ExnOccur  (* occurs check failure outside the pattern fragment *)

fun patSubOcc rOccur s = Subst.patSub (checkExistObj rOccur) Eta.etaContract s
(* checkExistObj : nfObj option vref -> nfObj -> nfObj * bool *)
(* check whether ob exists while performing occurs check
 * possible return values:
 *  (ob, true)  - ob exists
 *  (ob, false) - ob has nested Undefs inside
 *  ExnUndef    - ob does not exist
 *  ExnOccur    - don't know due to occurs check failure outside the pattern fragment *)
and checkExistObj rOccur ob =
	let val nestedUndef = ref false
		val undefined = NfClos (normalizeObj (EtaTag (Atomic' (Var (INT, 1), Nil'), (INT, 1))),
							Subst.invert (Subst.shift 1))
		fun catch f x =
			let val nu = !nestedUndef
			in SOME (f x) handle Subst.ExnUndef => (nestedUndef := nu; NONE) end
		(* To know whether we can reduce H . S{_} to _ we need to know
		 * whether H is a logicvar or a var "controlled" by a logicvar,
		 * i.e. whether a logicvar could potentially be substituted for H.
		 * This reduction normally happens automatically since _ in terms
		 * is represented by ExnUndef, so we need to stop it with catch.
		 *)
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
		  | chHead lvCtrlCtx (LogicVar (Y as {X=rY, s=sY, ...})) =
				if eq (rY, rOccur) then (* X = H . S{X[p]} --> X = H . S{_}  if p is pattern *)
					if isSome $ patSubOcc rOccur sY then
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

fun patSub s = patSubOcc (vref NONE) s

(* pruneCtx : exn -> (nfAsyncType -> nfAsyncType) -> pat_Subst -> nfAsyncType context -> nfAsyncType context *)
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

(* objExists : (unit -> string) -> nfObj option vref -> nfObj -> nfObj option *)
(* typeExists : (unit -> string) -> nfAsyncType -> nfAsyncType option *)
(* Force the existence of ob/ty while performing occurs check and pruning.
 * Subterms outside the pattern fragment with nested undefs get postponed
 * as Exists-constraints.
 * Possible return values:
 *  SOME ob  - ob exists
 *  NONE     - ob does not exist
 *  ExnOccur - don't know due to occurs check failure outside the pattern fragment *)
val (objExists, typeExists) =
	let open Util
		fun pair r x = (r, x)
		fun pruneType em x = NfAsyncTypeRec.map (pruneTypeSpine em, pruneSyncType em) x
		and pruneTypeSpine em x = NfTypeSpineRec.map (pruneObj em (vref NONE) true) x
		and pruneSyncType em x = NfSyncTypeRec.map (pruneType em) x
		and pruneSpine em rOccur (srig, x) = NfSpineRec.map (pruneMonad em rOccur srig) x
		and pruneMonad em rOccur srig x = NfMonadObjRec.map (pruneObj em rOccur srig) x
		and pruneMonad' em rOccur (srig, x) = pruneMonad em rOccur srig x
		and pruneObj em rOccur srig x = NfObjRec.unfold (pruneSpine em rOccur, pruneExp em rOccur)
			(fn (srig, ob) => case lowerObj $ NfObj.prj ob of
				  NfAtomic hS => NfAtomic $ pruneAtomic em rOccur srig hS
				| N => NfObj.Fmap ((pair srig, pair srig), pair srig) N)
			(srig, x)
		and pruneExp em rOccur (srig, x) = NfExpObjRec.unfold (pruneSpine em rOccur, pruneMonad' em rOccur)
			(fn (srig, ex) => case lowerExp $ NfExpObj.prj ex of
				  NfLet (p, hS, E) => NfLet (p, pruneAtomic em rOccur srig hS, (srig, E))
				| NfMon M => NfMon (srig, M))
			(srig, x)
		and pruneAtomic _ rOccur srig (v as Var _, S) = (v, (false, S))
		  | pruneAtomic _ rOccur srig (c as Const _, S) = (c, (srig, S))
		  | pruneAtomic _ rOccur srig (c as UCVar _, S) = (c, (srig, S))
		  | pruneAtomic _ rOccur srig (LogicVar {ctx=ref NONE, tag, ...}, _) =
				raise Fail ("Internal error: no context on $"^Word.toString tag)
		  | pruneAtomic errmsg rOccur srig
			(LogicVar (Y as {X=rY, ty=A, s=sY, ctx=ref (SOME G), cnstr=cs, tag}), _) =
				if eq (rY, rOccur) then
					(* X = H . S{X[p]} --> X = H . S{_}   if p is pattern
					 * X = H . S_srig{X[s]} --> _         with H <> lvar and H <> var
					 * To simply raise ExnUndef would be a completeness bug.  We must
					 * either be in a strongly rigid context or have sY preserve size,
					 * i.e.: For all ground R, |R| >= |R[sY]|
					 *)
					if srig then raise Subst.ExnUndef
					else if isSome $ patSubOcc rOccur sY then raise Subst.ExnUndef
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
						isSome $ Subst.patSub (fn x => (x, true)) Eta.etaContract sY' then
					let val wi = Subst.invert w
						val G' = pruneCtx Subst.ExnUndef (pruneType errmsg) wi G
						val A' = pruneType errmsg (NfTClos (A, wi))
						val Y'w = NfClos (newNfLVarCtx (SOME G') A', w)
						val () = instantiate (rY, Y'w, cs, tag)
					in map2 (pair false) $ invAtomicP $ NfClos (Y'w, sY') end
				else
					( addConstraint (vref (Exist (NfAtomic' (Y', NfInj.Nil'), errmsg)), [cs])
					; (Y', (false, NfInj.Nil')) )
				end
		fun objExists1 em rOccur ob = SOME (pruneObj em rOccur true ob) handle Subst.ExnUndef => NONE
		fun typeExists1 em ty = SOME (pruneType em ty) handle Subst.ExnUndef => NONE
	in (objExists1, typeExists1) end

(* pruneLVar : nfHead -> unit
 * prunes away linear and affine vars not occuring in the context *)
fun pruneLVar (LogicVar {X, ty, ctx=ref (SOME G), cnstr, tag, ...}) =
	let val weakenSub = foldr (fn ((_, _, NONE), w) => Subst.comp (w, Subst.shift 1)
		                        | ((_, _, SOME _), w) => Subst.dot1 w)
		                Subst.id (ctx2list G)
	in if Subst.isId weakenSub then () else
	let val ss = Subst.invert weakenSub
		val G' = SOME $ pruneCtx (Fail "Internal error: pruneLVar: pruning lin") (fn A => A) ss G
		val ty' = NfTClos (ty, ss)
	in instantiate (X, NfClos (newNfLVarCtx G' ty', weakenSub), cnstr, tag) end end
  | pruneLVar _ = raise Fail "Internal error: pruneLVar: no lvar"

(* linPrune : (unit -> string) -> nfObj * (subMode * int) list -> nfObj option *)
(* tries to solve X[lcis2sub pl] = ob by linearity pruning,
 * returns the solution to X if successful *)
fun linPrune errmsg (ob, pl) =
	let datatype occ = No | Rigid | FlexMult | FlexUniq
		val doexists = ref false
		val postpone = ref false
		fun np occ = (occ, Subst.id, Subst.id)
		fun swap (occ, s1, s2) = (occ, s2, s1)
		fun additiveOcc _ ID      _ _ = raise Fail "Internal error: linPrune: ID"
		  | additiveOcc _ _       No No = np No
		  | additiveOcc n m       o1 No = swap $ additiveOcc n m No o1
		  | additiveOcc _ INT4AFF No Rigid = np Rigid
		  | additiveOcc _ _       No Rigid = raise ExnUnify "Implied linear var missing"
		(*| additiveOcc _ AFF4LIN No o2 = raise Fail "Internal error: A->L flex"*)
		(* "AFF4LIN No FlexMult" can occur if there is affine occurrences in a non-pattern sub *)
		  | additiveOcc _ AFF4LIN No o2 = raise ExnUnify "Implied linear var missing"
		  | additiveOcc _ INT4AFF No o2 = np o2
		  | additiveOcc n INT4LIN No o2 = (No, Subst.id, Subst.pruningsub [((), n)])
		  | additiveOcc _ _       Rigid Rigid = np Rigid
		  | additiveOcc n m       o1 Rigid = swap $ additiveOcc n m Rigid o1
		  | additiveOcc _ _       Rigid FlexUniq = np Rigid
		  | additiveOcc _ _       Rigid FlexMult = (postpone:=true; np Rigid)
		  | additiveOcc _ _       FlexUniq FlexUniq = np FlexUniq
		  | additiveOcc _ _       FlexMult _ = np FlexMult
		  | additiveOcc _ _       _ FlexMult = np FlexMult
		fun multOcc _ ID _ _ = raise Fail "Internal error: linPrune: ID"
		  | multOcc _ _ No o2 = np o2
		  | multOcc _ _ o1 No = np o1
		  | multOcc _ _ Rigid Rigid = raise ExnUnify "Implied linear/affine var occurring twice"
		  | multOcc n _ Rigid _ = (Rigid, Subst.id, Subst.pruningsub [((), n)])
		  | multOcc n _ _ Rigid = (Rigid, Subst.pruningsub [((), n)], Subst.id)
		  | multOcc _ _ _ _ = np FlexMult
		fun occMap _ ([], [], []) = np []
		  | occMap f ((m, n)::p, o1::occ1, o2::occ2) =
				let val (occ, s1, s2) = f n m o1 o2
					val (occs, s1', s2') = occMap f (p, occ1, occ2)
				in (occ::occs, Subst.comp (s1, s1'), Subst.comp (s2, s2')) end
		  | occMap _ _ = raise Fail "Internal error: additiveOccs: Unequal lengths"
		val additiveOccs = occMap additiveOcc
		val multOccs = occMap multOcc
		fun pClos clo n s N = if Subst.isId s then N else
			( doexists := true
			; clo (N, Subst.dotn n s) )
		fun pObj p n ob = case NfObj.prj ob of (* lowering is done in pAtomic *)
			  NfLLam (pa, N) => map1 (fn N' => NfLLam' (pa, N')) (pObj p (n + nbinds pa) N)
			| NfAddPair (N1, N2) =>
				let val (N1', occ1) = pObj p n N1
					val (N2', occ2) = pObj p n N2
					val (occ, s1, s2) = additiveOccs (p, occ1, occ2)
				in (NfAddPair' (pClos NfClos n s1 N1', pClos NfClos n s2 N2'), occ) end
			| NfMonad E => map1 NfMonad' (pExp p n E)
			| NfAtomic hs => map1 NfAtomic' (pAtomic p n hs)
		and pAtomic p n hs =
			let fun lookup k p = case List.filter (fn (_, j : int) => j=k) p of
					  [] => ID
					| [(ID, _)] => raise Fail "Internal error: linPrune: lin mismatch"
					| [(m, _)] => m
					| (_::_::_) => raise Fail "Internal error: linPrune: double var"
			in case lowerAtomic hs of
			  (Const c, S) => map1 (fn s => (Const c, s)) (pSpine p n S)
			| (UCVar v, S) => map1 (fn s => (UCVar v, s)) (pSpine p n S)
			| (Var (m, k), S) =>
				let val m' = case (m, lookup (k-n) p) of
						  (_, ID) => m
						| (INT, INT4AFF) => AFF
						| (AFF, AFF4LIN) => LIN
						| (INT, INT4LIN) => AFF
						| _ => raise Fail "Internal error: linPrune: linearity mismatch"
					val occ1 = map (fn (_, j) => if j+n=k then Rigid else No) p
					val (S', occ2) = pSpine p n S
					val (occ, s1, s2) = multOccs (p, occ1, occ2)
					val () = if Subst.isId s1 then () else raise Fail "Internal error: lprune var"
				in ((Var (m', k), pClos NfSClos n s2 S'), occ) end
			| (LogicVar {ctx=ref NONE, ...}, _) => raise Fail "Internal error: linPrune: no ctx"
			| (LogicVar (X1 as {X=r, ty=A, s, ctx=ref (SOME G), cnstr=cs, tag}), _) =>
				let val () = if List.all (isSome o #3) $ ctx2list G then () else
								raise Fail "Internal error: pAtomic: lvar with non-pruned ctx"
				in case patSub s of
				  SOME (p1, s1) =>
					let val s2 = Subst.comp (Subst.coerce2s s1, Subst.lcis2sub p1)
						val (s3, pp, occ) = Subst.fold
							(fn (Ob _, _) => raise Fail "Internal error: not patsub"
							  | (Undef, (s, pp, occ)) => (Subst.Dot (Undef, s), pp, occ)
							  | (Idx (m, k), (s, pp, occ)) =>
								let val (m', pp1, occ1) = case (m, lookup (k-n) p) of
								  (_, ID) => (m, [], [])
								| (ID, INT4AFF) => (ID, [(INT4AFF, k)], [(k, FlexUniq)])
								| (ID, AFF4LIN) => (ID, [(AFF4LIN, k)], [(k, Rigid)])
								| (ID, INT4LIN) => (ID, [(INT4AFF, k)], [(k, FlexUniq)])
								| (INT4AFF, INT4AFF) => (ID, [], [(k, FlexUniq)])
								| (INT4AFF, INT4LIN) => (ID, [], [(k, FlexUniq)])
								| (AFF4LIN, AFF4LIN) => (ID, [], [(k, Rigid)])
								| (INT4LIN, INT4AFF) => (AFF4LIN, [], [(k, Rigid)])
								| (INT4LIN, INT4LIN) => (AFF4LIN, [], [(k, Rigid)])
								| _ => raise Fail "Internal error: linPrune: lin mismatch"
								in (Subst.Dot (Idx (m', k), s), pp1 @ pp, occ1 @ occ) end)
							(fn l =>
								let val p' = List.filter (fn (_, j) => j > l-n) p
								in (Subst.shift l,
									map (fn (INT4LIN, j) => (INT4AFF, j+n)
										  | (m, j) => (m, j+n)) p',
									map (fn (AFF4LIN, j) => (j+n, Rigid)
										  | (_, j) => (j+n, FlexUniq)) p')
								end)
							s2
						val occ' = map (fn (_, j) =>
								case List.filter (fn (k, _) => k-n=j) occ of
								  [] => No
								| [(_, oc)] => oc
								| (_::_::_) => raise Fail "Internal error: lp: not patsub") p
						val Y = if null pp then X1 else
								let fun pType pp A =
										let val ps = Subst.pruningsub $
												List.filter (fn (m, _) => m <> AFF4LIN) pp
										in if Subst.isId ps then A
										else case typeExists errmsg (NfTClos (A, ps)) of
											  NONE => raise ExnUnify "Implied A/L var in type"
											| SOME A' => A' end
									fun sub1 ((_, 1)::pp) = map (fn (m, x) => (m, x-1)) pp
									  | sub1 pp = map (fn (m, x) => (m, x-1)) pp
									fun addM 1 (SOME INT) = SOME AFF
									  | addM 1 (SOME AFF) = SOME LIN
									  | addM 1 _ = raise Fail "Internal error: addM"
									  | addM _ m = m
									fun pCtx (G, []) = list2ctx G
									  | pCtx ([], _::_) = raise Fail "Internal error: pCtx"
									  | pCtx ((x, A, m)::G, pp as (_, j)::_) =
										let val pp' = sub1 pp
										in ctxCons (x, pType pp' A, addM j m) (pCtx (G, pp')) end
									val pp' = Subst.lcisComp (pp, Subst.invert s1)
									val A' = pType pp' A
									val G' = pCtx (ctx2list G, pp')
									val Y = newNfLVarCtx (SOME G') A'
									val () = instantiate (r, NfClos (Y, Subst.lcis2sub pp'), cs, tag)
								in invLVar $ invAtomicP Y end
					in ((LogicVar (Y with's s3), NfInj.Nil'), occ') end
				| NONE =>
					let val occSubAll = NS.decrn n (occurSub G s)
						fun occurs j = NS.member j occSubAll
						val occ = map (fn (m, j) => if occurs j then FlexMult else No) p
					in ((LogicVar X1, NfInj.Nil'), occ) end
				end
			end
		and pSpine p n sp = case NfSpine.prj sp of
			  Nil => (NfInj.Nil', map (fn _ => No) p)
			| LApp (M, S) =>
				let val (M', occ1) = pMonadObj p n M
					val (S', occ2) = pSpine p n S
					val (occ, s1, s2) = multOccs (p, occ1, occ2)
				in (NfInj.LApp' (pClos NfMClos n s1 M', pClos NfSClos n s2 S'), occ) end
			| ProjLeft S => map1 NfInj.ProjLeft' (pSpine p n S)
			| ProjRight S => map1 NfInj.ProjRight' (pSpine p n S)
		and pExp p n ex = case lowerExp $ NfExpObj.prj ex of
			  NfLet (pa, hs, E) =>
				let val (hs', occ1) = pAtomic p n hs
					val (E', occ2) = pExp p (n + nbinds pa) E
					val (occ, s1, s2) = multOccs (p, occ1, occ2)
					fun hsClos (hs, s) = (case NfObj.prj (NfClos (NfAtomic' hs, s)) of
						  NfAtomic hs' => hs'
						| _ => raise Fail "Internal error: pExp: no atomic")
							handle Subst.ExnUndef => raise Fail "Internal error: pExp: prune var"
				in (NfLet' (pa, pClos hsClos n s1 hs', pClos NfEClos n s2 E'), occ) end
			| NfMon M => map1 NfMon' (pMonadObj p n M)
		and pMonadObj p n mo = case NfMonadObj.prj mo of
			  DepPair (M1, M2) =>
				let val (M1', occ1) = pMonadObj p n M1
					val (M2', occ2) = pMonadObj p n M2
					val (occ, s1, s2) = multOccs (p, occ1, occ2)
				in (NfInj.DepPair' (pClos NfMClos n s1 M1', pClos NfMClos n s2 M2'), occ) end
			| One => (NfInj.One', map (fn _ => No) p)
			| Down N => map1 NfInj.Down' (pObj p n N)
			| Affi N =>
				let val (pI2A, p2L) = List.partition (fn (m, _) => m = INT4AFF) p
					val (N', occ1) = if null pI2A then (N, []) else pObj pI2A n N
					val occ2 = map (fn (_, j) => (No, j)) p2L
					val occ = map #1 $ Subst.qsort2 (occ2 @ listPairMapEq (map2 #2) (occ1, pI2A))
				in (NfInj.Affi' (pClos NfClos n (Subst.pruningsub p2L) N'), occ) end
			| Bang N => (NfInj.Bang' (pClos NfClos n (Subst.pruningsub p) N), map (fn _ => No) p)
			| MonUndef => raise Fail "Internal error: MonUndef"
		fun finish p occ = additiveOccs (p, occ, map (fn _ => Rigid) p)
		fun pruneObj [] ob = SOME ob
		  | pruneObj p ob =
			let val () = doexists := false
				val () = postpone := false
				val (ob1, occ) = pObj p 0 ob
				val _ = finish p occ
				val ob2 = if !doexists then case objExists errmsg (vref NONE) ob1 of
							  NONE => raise ExnUnify "Impossible occurrences of implied A/L var"
							| SOME ob2 => ob2
						else ob1
			in if !postpone then NONE else SOME ob2 end
		val pl1 = Subst.qsort2 pl
		val pl2 = List.mapPartial (fn (INT4LIN, j) => SOME (AFF4LIN, j) | _ => NONE) pl1
	in Option.mapPartial (pruneObj pl2) (pruneObj pl1 ob) end

fun unifyType em (ty1, ty2) = case (Util.nfTypePrjAbbrev ty1, Util.nfTypePrjAbbrev ty2) of
	  (TLPi (_, A1, B1), TLPi (_, A2, B2)) => (unifySyncType em (A1, A2); unifyType em (B1, B2))
	| (AddProd (A1, B1), AddProd (A2, B2)) => (unifyType em (A1, A2); unifyType em (B1, B2))
	| (TMonad S1, TMonad S2) => unifySyncType em (S1, S2)
	| (TAtomic (a1, S1), TAtomic (a2, S2)) =>
			if a1 <> a2 then raise Fail ("Internal error: "^a1^" and "^a2^" differ")
			else unifyTSpine em (S1, S2)
	| (A1, A2) => raise Fail "Internal error: unifyType"
and unifySyncType em (ty1, ty2) = case (NfSyncType.prj ty1, NfSyncType.prj ty2) of
	  (LExists (_, S1, T1), LExists (_, S2, T2)) => (unifySyncType em (S1, S2); unifySyncType em (T1, T2))
	| (TOne, TOne) => ()
	| (TDown A1, TDown A2) => unifyType em (A1, A2)
	| (TAffi A1, TAffi A2) => unifyType em (A1, A2)
	| (TBang A1, TBang A2) => unifyType em (A1, A2)
	| (S1, S2) => raise Fail "Internal error: unifySyncType"
and unifyTSpine em (sp1, sp2) = case (NfTypeSpine.prj sp1, NfTypeSpine.prj sp2) of
	  (TNil, TNil) => ()
	| (TApp (N1, S1), TApp (N2, S2)) => (unifyObj em NONE (N1, N2); unifyTSpine em (S1, S2))
	| (S1, S2) => raise Fail "Internal error: unifyTSpine"
and unifyObj em dryRun (ob1, ob2) =
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	let val ob1' = lowerObj (NfObj.prj ob1)
		val ob2' = lowerObj (NfObj.prj ob2)
		open NfInj
		fun invLam p hS = nfredex (NfClos (NfAtomic' hS, Subst.shift $ nbinds p),
				LApp' (pat2mon p, Nil'))
		fun invPair p hS = nfredex (NfAtomic' hS, p Nil')
	in case (ob1', ob2') of
		  (NfLLam (_, N1), NfLLam (_, N2)) => unifyObj em dryRun (N1, N2)
		| (NfLLam (p, N1), NfAtomic hS2) => unifyObj em dryRun (N1, invLam p hS2)
		| (NfAtomic hS1, NfLLam (p, N2)) => unifyObj em dryRun (invLam p hS1, N2)
		| (NfAddPair (L1, N1), NfAddPair (L2, N2)) =>
				( unifyObj em dryRun (L1, L2)
				; unifyObj em dryRun (N1, N2) )
		| (NfAddPair (L1, N1), NfAtomic hS2) =>
				( unifyObj em dryRun (L1, invPair ProjLeft' hS2)
				; unifyObj em dryRun (N1, invPair ProjRight' hS2) )
		| (NfAtomic hS1, NfAddPair (L2, N2)) =>
				( unifyObj em dryRun (invPair ProjLeft' hS1, L2)
				; unifyObj em dryRun (invPair ProjRight' hS1, N2) )
		| (NfMonad E1, NfMonad E2) =>
				(case (Eta.etaContractLetMon E1, Eta.etaContractLetMon E2) of
					  (NONE, NONE) => unifyExp em dryRun (E1, E2)
					| (SOME hS1, NONE) => unifyAtomicExp em dryRun ((lowerAtomic hS1, SOME E1), E2)
					| (NONE, SOME hS2) => unifyAtomicExp em dryRun ((lowerAtomic hS2, SOME E2), E1)
					| (SOME hS1, SOME hS2) =>
						let val hS1' = lowerAtomic hS1
							val hS2' = invAtomic $ lowerObj $ NfObj.prj $ NfAtomic' hS2
						in unifyHead em dryRun (hS1', hS2') end)
		| (NfMonad E, NfAtomic hS) =>
				unifyObj em dryRun (NfAtomic' hS, NfMonad' E)
		| (NfAtomic hS, NfMonad E) =>
				(case Eta.etaContractLetMon E of
					  NONE => unifyAtomicExp em dryRun ((hS, NONE), E)
					| SOME hS2 => unifyHead em dryRun (hS, lowerAtomic hS2))
(*		| (NfAtomic hS, NfMonad E) =>
				(case case #1 hS of LogicVar (X as {X=r, ...}) =>
					if headCountExp (r, E) = SOME 0 then SOME X else NONE | _ => NONE of
					  SOME (X as {s, ctx=ref (SOME G), cnstr=cs, ...}) =>
						if isSome dryRun then (valOf dryRun) := false else
						(case patSub s of
							  SOME (p, s') => unifyLVar (X with's s', NfMonad' E, p)
							| NONE => addConstraint (vref (Eqn (NfObj.inj ob1', NfMonad' E)), [cs]))
					| SOME {ctx=ref NONE, ...} => raise Fail "Internal error: no ctx"
					| NONE =>
						let val (p, Mf) = etaMimicExp E
						in unifyExp dryRun (NfLet' (p, hS, NfMon' $ Mf 1), E) end)*)
		| (NfAtomic hS1, NfAtomic hS2) => unifyHead em dryRun (hS1, hS2)
		| (N1, N2) => raise Fail "Internal error: unifyObj"
	end
and unifyHead errmsg dryRun (hS1 as (h1, S1), hS2 as (h2, S2)) = case (h1, h2) of
	  (Const c1, Const c2) =>
			if c1 <> c2 then raise ExnUnify ("Constants "^c1^" and "^c2^" differ")
			else unifySpine errmsg dryRun (S1, S2)
	| (UCVar x1, UCVar x2) =>
			if x1 <> x2 then raise ExnUnify ("Vars "^x1^" and "^x2^" differ")
			else unifySpine errmsg dryRun (S1, S2)
	| (Var n1, Var n2) =>
			if n1 <> n2 then raise ExnUnify "Vars differ"
			else unifySpine errmsg dryRun (S1, S2)
	| (LogicVar (X1 as {X=r1, ty=A1, s=s1, ctx=ref (SOME G1), cnstr=cs1, tag=tag1}),
		LogicVar (X2 as {X=r2, s=s2, cnstr=cs2, ...})) =>
			if eq (r1, r2) then
				case (patSub s1, patSub s2) of
				  (NONE, NONE) => (* FIXME: code restructuring? *)
					let val dryRunIntersect = ref true
						exception ExnUnifyMaybe
						fun conv ob1ob2 = case SOME (unifyObj errmsg (SOME dryRunIntersect) ob1ob2)
								handle ExnUnify _ => NONE of
							  SOME () => if !dryRunIntersect then true else raise ExnUnifyMaybe
							| NONE => false
						fun conv' (INL n, ob2) = conv (NfAtomic' (Var n, NfInj.Nil'), ob2) (* eta *)
						  | conv' (INR ob1, ob2) = conv (ob1, ob2)
					in if Subst.isId (Subst.intersection conv' (s1, s2))
							handle ExnUnifyMaybe => false then ()
					else if isSome dryRun then (valOf dryRun) := false else
						addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)), [cs1])
					end
				| (SOME (p, s1'), NONE) =>
					if isSome dryRun then (valOf dryRun) := false else
						addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)), [cs1])
				| (NONE, SOME (p, s2')) =>
					if isSome dryRun then (valOf dryRun) := false else
						addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)), [cs1])
				| (SOME (_, s1'), SOME (_, s2')) => (* we can disregard linear changing subs *)
					let val s12 = Subst.comp (s1', Subst.invert s2')
						val w = Subst.coerce2p_ (Subst.intersect s12)
						val wi = Subst.invert w
						val sp = Subst.comp (w, Subst.comp (s12, wi))
					in if Subst.isId w then
						if Subst.isId sp then ()
						else if isSome dryRun then (valOf dryRun) := false else
							addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)), [cs1])
					else if isSome dryRun then (valOf dryRun) := false else
						let fun pruneType ty = case typeExists errmsg ty of
									  SOME ty' => ty'
									| NONE => raise ExnUnify "pruneType in intersection"
							val A' = pruneType $ NfTClos (A1, wi)
							val G' = pruneCtx (ExnUnify "intersect:pruneCtx") pruneType wi G1
							val Y = newNfLVarCtx (SOME G') A'
							val () = instantiate (r1, NfClos (Y, w), cs1, tag1)
						in if Subst.isId sp then () else
							addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)),
								[case NfObj.prj Y of NfAtomic (LogicVar {cnstr=cs, ...}, _) => cs
									| _ => raise Fail "Internal error: intersect: no lvar"])
						end
					end
			else if isSome dryRun then (valOf dryRun) := false
			else (case patSub s1 of
				  SOME (p, s') => unifyLVar errmsg (X1 with's s', NfAtomic' hS2, p)
				| NONE =>
					(case patSub s2 of
					  SOME (p, s') => unifyLVar errmsg (X2 with's s', NfAtomic' hS1, p)
					| NONE => addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)), [cs1, cs2])))
	| (LogicVar (X as {s, cnstr=cs, ...}), _) =>
			if isSome dryRun then (valOf dryRun) := false else
			(case patSub s of
				  SOME (p, s') => unifyLVar errmsg (X with's s', NfAtomic' hS2, p)
				| NONE => addConstraint (vref (Eqn (NfAtomic' hS1, NfAtomic' hS2, errmsg)), [cs]))
	| (_, LogicVar _) => unifyHead errmsg dryRun (hS2, hS1)
	| _ => raise ExnUnify "Heads differ"
and unifyLVar errmsg (X as {X=r, s, cnstr=cs, tag, ...}, ob, p) =
	let val si = Subst.invert s
	in case objExists errmsg r (NfClos (ob, si)) of
		  NONE => raise ExnUnify "Cannot prune"
		| SOME N => if null p then instantiate (r, N, cs, tag) else
			let val p' = Subst.lcisComp (p, si)
			in case linPrune errmsg (N, p') of
				  NONE => addConstraint (vref (Eqn
						(NfAtomic' (LogicVar (X with's (Subst.lcis2sub p')), NfInj.Nil'), N, errmsg)), [cs])
				| SOME N' => instantiate (r, N', cs, tag)
			end
	end handle ExnOccur =>
		addConstraint (vref (Eqn (NfAtomic' (LogicVar
				(X with's (Subst.comp (Subst.coerce2s s, Subst.lcis2sub p))), NfInj.Nil'), ob, errmsg)), [cs])
and unifySpine em dryRun (sp1, sp2) = case (NfSpine.prj sp1, NfSpine.prj sp2) of
	  (Nil, Nil) => ()
	| (LApp (M1, S1), LApp (M2, S2)) => (unifyMon em dryRun (M1, M2); unifySpine em dryRun (S1, S2))
	| (ProjLeft S1, ProjLeft S2) => unifySpine em dryRun (S1, S2)
	| (ProjRight S1, ProjRight S2) => unifySpine em dryRun (S1, S2)
	| (ProjLeft _, ProjRight _) => raise ExnUnify "Projections differ"
	| (ProjRight _, ProjLeft _) => raise ExnUnify "Projections differ"
	| _ => raise Fail "Internal error: unifySpine"
and unifyAtomicExp errmsg dryRun ((hS, e1), e2) =
	let open NfInj
		fun etaMimicMon m = case NfMonadObj.prj m of
			  DepPair (M1, M2) =>
				let val (p2, Mf2) = etaMimicMon M2
					val (p1, Mf1) = etaMimicMon M1
				in (PDepTensor' (p1, p2), fn n => DepPair' (Mf1 (n + nbinds p2), Mf2 n)) end
			| One => (POne', fn _ => One')
			| Down _ => (PDown' "", fn n => Down' $ NfAtomic' (Var (LIN, n), Nil'))
			| Affi _ => (PAffi' "", fn n => Affi' $ NfAtomic' (Var (AFF, n), Nil'))
			| Bang _ => (PBang' "", fn n => Bang' $ NfAtomic' (Var (INT, n), Nil'))
			| MonUndef => raise Fail "Internal error: etaMimicMon: MonUndef"
		fun etaMimicExp e = case NfExpObj.prj e of
			  NfLet (_, _, E) => etaMimicExp E
			| NfMon M => etaMimicMon M
		fun e1' () = case e1 of SOME e => e | NONE =>
			let val (p, Mf) = etaMimicExp e2
			in NfLet' (p, hS, NfMon' $ Mf 1) end
	in case hS of
	  (LogicVar (X as {X=r, s, cnstr=cs, ...}), _) =>
		if headCountExp (r, e2) = 0 then
			if isSome dryRun then (valOf dryRun) := false else
			case patSub s of
			  SOME (p, s') => unifyLVar errmsg (X with's s', NfMonad' e2, p)
			| NONE => addConstraint (vref (Eqn (NfAtomic' hS, NfMonad' e2, errmsg)), [cs])
		else unifyExp errmsg dryRun (e1' (), e2)
	| _ => unifyExp errmsg dryRun (e1' (), e2)
	end
and unifyExp em dryRun (e1, e2) = case (NfExpObj.prj e1, NfExpObj.prj e2) of
	  (NfMon M1, NfMon M2) => unifyMon em dryRun (M1, M2)
	| (NfLet L1, NfMon M2) => unifyLetMon em dryRun (L1, M2)
	| (NfMon M1, NfLet L2) => unifyLetMon em dryRun (L2, M1)
	| (NfLet L1, NfLet L2) => unifyLetLet em dryRun (L1, L2)
			(*let fun lVarCount (NfLet (_, (LogicVar _, _), E)) = 1 + lVarCount (NfExpObj.prj E)
				  | lVarCount (NfLet (_, _, E)) = lVarCount (NfExpObj.prj E)
				  | lVarCount (NfMon _) = 0
			in if isSome dryRun andalso (lVarCount (NfLet L1) > 0 orelse lVarCount (NfLet L2) > 0)
				then (valOf dryRun) := false
				else unifyLetLet dryRun (L1, L2)
			end*)
and unifyLetMon errmsg dryRun ((pa, hS, E), M) = case lowerAtomic hS of
	  (LogicVar (X as {X=r, ty, s, ctx=ref (SOME G), cnstr=cs, tag}), _ (*=Nil*)) =>
			if isSome dryRun then (valOf dryRun) := false else
			(case patSub s of
				  NONE => addConstraint (vref (Eqn
						(NfMonad' $ NfLet' (pa, hS, E), NfMonad' $ NfMon' M, errmsg)), [cs])
				| SOME (p', s') =>
					let val () = if List.all (isSome o #3) $ ctx2list G then () else
								raise Fail "Internal error: unifyLetMon: lvar with non-pruned ctx"
						open Subst
						val (p, newM) = newMonA (ty, G)
						val lcis = lcis2sub $ lcisComp (lcisDiff (p, lcisComp (p', invert s')), s')
					in ( unifyLVar errmsg (X with's id, newM, p)
					   ; unifyExp errmsg NONE (nfletredex (pa, NfClos (newM, s'), E), (* E = E[lcis] *)
							NfMon' $ NfMClos (M, lcis)) )
					end)
	| (LogicVar {ctx=ref NONE, tag, ...}, _) =>
			raise Fail ("Internal error: no context on $"^Word.toString tag)
	| _ => raise ExnUnify "let sequences have different lengths"
and unifyMon em dryRun (m1, m2) = case (NfMonadObj.prj m1, NfMonadObj.prj m2) of
	  (DepPair (M11, M12), DepPair (M21, M22)) =>
			(unifyMon em dryRun (M11, M21); unifyMon em dryRun (M12, M22))
	| (One, One) => ()
	| (Down N1, Down N2) => unifyObj em dryRun (N1, N2)
	| (Affi N1, Affi N2) => unifyObj em dryRun (N1, N2)
	| (Bang N1, Bang N2) => unifyObj em dryRun (N1, N2)
	| (MonUndef, _) => raise Fail "Internal error: unifyMon: MonUndef"
	| (_, MonUndef) => raise Fail "Internal error: unifyMon: MonUndef"
	| _ => raise Fail "Internal error: unifyMon"
and unifyLetLet errmsg dryRun ((p1, ob1, E1), (p2, ob2, E2)) =
	(* In the case of two equal LVars, the lowering of ob1 affects the whnf of ob2 *)
	let val ob1' = lowerAtomic ob1
		val ob2' = invAtomic $ lowerObj $ NfObj.prj $ NfAtomic' ob2
		fun postpone css = addConstraint (vref (Eqn
				(NfMonad' $ NfLet' (p1, ob1', E1),
				 NfMonad' $ NfLet' (p2, ob2', E2), errmsg)), css)
	in case (ob1', NfExpObj.prj E1, ob2', NfExpObj.prj E2) of
		  ((LogicVar {cnstr=cs1, ...}, _), E1', (LogicVar {cnstr=cs2, ...}, _), E2') =>
			(* even {let {[x,y]}=X in [x,y]} = {let {[x,y]}=X in [y,x]} has solutions *)
			if isSome dryRun then (valOf dryRun) := false else postpone [cs1, cs2]
		| (_, E1', (LogicVar _, _), NfMon M2) =>
			unifyLetLet errmsg dryRun ((p2, ob2', NfMon' M2), (p1, ob1', NfExpObj.inj E1'))
		| ((LogicVar (X1 as {X, ty, s, ...}), _ (*=Nil*)), NfMon M1, _, E2') =>
			if isSome dryRun then (valOf dryRun) := false else
			(case patSub s of
			  NONE => postpone [#cnstr X1]
			| SOME (p, s') =>
				if headCountExp (X, NfLet' (p2, ob2', NfExpObj.inj E2')) = 0 then
					let val (Y, qn, E2rest) = unifyLVarLetPrefix errmsg (p1, X1 with's s', p,
											NfLet' (p2, ob2', E2))
						val rest1 = NfLet' (p1, invAtomicP Y,
									NfMon' $ NfMClos (M1, Subst.dotn (nbinds p1) (Subst.shift qn)))
					in unifyExp errmsg NONE (rest1, E2rest) end
				else postpone [#cnstr X1])
		| ((LogicVar _, _), _, _ (* ob2' <> LVar *), _) =>
			unifyLetLet errmsg dryRun ((p2, ob2', E2), (p1, ob1', E1))
		| _ (* ob1' <> LVar *) =>
			let val E2t = NfLet' (p2, ob2', E2)
			in case matchHeadInLet (ob1', E2t) of
			  INL E2rest => unifyExp errmsg dryRun (E1, E2rest)
			| INR m2 =>
				let val E1t = NfLet' (p1, ob1', E1)
				in case matchHeadInLet (ob2', E1t) of
				  INL E1rest => unifyExp errmsg dryRun (E1rest, E2)
				| INR m1 => if isSome dryRun then (valOf dryRun) := false else
					let fun notLvar (LogicVar _, _) = false
						  | notLvar _ = true
						fun lvarFreeN Et (_, 0) = true
						  | lvarFreeN Et (E, n) = case NfExpObj.prj E of
							  NfLet (_, (LogicVar {X, s, ...}, _), E') =>
								n=1 andalso isSome (patSub s) andalso headCountExp (X, Et) = 0
							| NfLet (_, _, E') => lvarFreeN Et (E', n-1)
							| NfMon _ => raise Fail "Internal error: lvarFreeN"
					in if isSome m2 andalso lvarFreeN E1t (E2t, valOf m2) andalso notLvar ob1' then
						unifyExp errmsg dryRun (E1, matchHeadInLetFixedPos errmsg (p1, ob1', E2t, valOf m2))
					else if isSome m1 andalso lvarFreeN E2t (E1t, valOf m1) andalso notLvar ob2' then
						unifyExp errmsg dryRun (matchHeadInLetFixedPos errmsg (p2, ob2', E1t, valOf m1), E2)
					else addConstraint (vref (Eqn
							(NfMonad' $ NfLet' (p1, ob1', E1),
							 NfMonad' $ NfLet' (p2, ob2', E2), errmsg)), [monConstrs])
					end
				end
			end
	end
(* unifyLVarLetPrefix errmsg (p1, X1[s], p, E2)
 * with E2 = let {q1} = N1 in ... let {qn} = Nn in E3,
 * E3 is either a monadic object M or let {q} = Z[t] in E4,
 * n>=1, Ni not logic variables, and s a pattern sub
 * set X1[s][lcis2sub p] =
 *   {let {q1} = N1 in ... let {qn} = Nn in
 *    let {p1} = Y[s'] in p1}
 * where s' = dotn (q1+...+qn) s
 * return (Y[s'], q1+...+qn, E3) *)
and unifyLVarLetPrefix em (p1, X1 as {X, ty, s, ctx=ref G, ...}, p, E2) =
	let fun buildY ctx qn ex =
			let val Y = newNfLVarCtx (SOME ctx) (NfTClos (ty, Subst.shift qn))
				val Y' = invAtomicP Y
				val () = pruneLVar $ #1 Y'
				val p1m = pat2mon p1
			in (NfLet' (p1, Y', NfMon' p1m), (Y, qn, ex)) end
		fun splitLet ctx si ex qn = case NfExpObj.prj ex of
			  NfMon _ => buildY ctx qn ex
			| NfLet (_, (LogicVar _, _), _) => buildY ctx qn ex
			| NfLet (q, hs, E) =>
				let fun prunehs' rX = (case objExists em rX (NfClos (NfAtomic' hs, si)) of
							  SOME ob => invAtomicP ob
							| NONE => raise ExnUnify "Can't prune")
					val hs' = prunehs' X handle ExnOccur => prunehs' (vref NONE)
					(* ExnOccur: If the occurs check fails outside the pattern
					 * fragment we postpone its treatment to the call to
					 * unifyLVar below where it will be reraised *)
					val (ctx', A) = synthAtomic ctx hs'
					val sty = case Util.nfTypePrjAbbrev A of TMonad sty => sty
							| _ => raise Fail "Internal error: sync type expected"
					val ctx'' = opatBindNf (q, sty) ctx'
					val si' = Subst.dotn (nbinds q) si
					val (E', y) = splitLet ctx'' si' E (qn + nbinds q)
				in (NfLet' (q, hs', E'), y) end
		val si = Subst.invert s
		val p' = Subst.lcisComp (p, si) (* X[s][lcis2sub p] = X[lcis2sub p'][s] *)
		(* FIXME: use ralist lookup *)
		fun changeMode ((INT4LIN, 1), (x, A, SOME LIN)::G) = (x, A, SOME INT)::G
		  | changeMode ((AFF4LIN, 1), (x, A, SOME LIN)::G) = (x, A, SOME AFF)::G
		  | changeMode ((INT4AFF, 1), (x, A, SOME AFF)::G) = (x, A, SOME INT)::G
		  | changeMode ((_, 1), _) = raise Fail "Internal error: changeMode: 1"
		  | changeMode ((m, j), x::G) = x :: changeMode ((m, j-1), G)
		  | changeMode (_, []) = raise Fail "Internal error: changeMode: []"
		(* G |- X, G' |- X[lcis2sub p'] *)
		val G' = list2ctx $ foldl changeMode (ctx2list $ valOf G) p'
		val (E2Y, (Y, qn, M2)) = splitLet G' si E2 0
		val () = case Util.NfExpObjAuxDefs.prj2 E2Y of
			  NfLet (_, _, NfLet _) => ()
			| _ => raise Fail "Internal error: unifyLVarLetPrefix: no progress"
		val () = unifyLVar em (X1 with's Subst.id, NfMonad' E2Y, p')
	in (NfClos (Y, Subst.dotn qn s), qn, M2) end
and matchHeadInLet (hS, E) =
	let (* None n : No match found, looking at let number n
		 * One n : One possible match found at let number n
		 * More : Several possible matches found *)
		datatype maybeMatch = None of int | One of int | More
		fun advance (None l) = None (l+1)
		  | advance mm = mm
		fun foundOne (None l) = One l
		  | foundOne (One _) = More
		  | foundOne More = More
		fun matchHead (hS, e, nbe, E, EsX, nMaybe) = case (NfExpObj.prj E, NfExpObj.prj EsX) of
			  (NfLet (p, N, E'), NfLet (_, NsX, EsX')) =>
				let val nbp = nbinds p
					fun AtClos (a, s) = invAtomicP (NfClos (NfAtomic' a, s))
					fun hS' () = AtClos (hS, Subst.shift nbp)
					val e' = fn s => fn E =>
								let val s' = Subst.dotn nbe s
								in e s (NfLet' (p, AtClos (N, s'), E)) end
					fun lVarSub (p, s) = case Pattern.prj p of
						  PDepTensor (p1, p2) => lVarSub (p2, lVarSub (p1, s))
						| POne => s
						| PDown _ => Subst.Dot (Ob (LIN, normalizeObj $ Parse.blank ()), s)
						| PAffi _ => Subst.Dot (Ob (AFF, normalizeObj $ Parse.blank ()), s)
						| PBang _ => Subst.Dot (Ob (INT, normalizeObj $ Parse.blank ()), s)
					fun lVarSub' () = lVarSub (p, Subst.shift nbp)
					fun EsX'' () = if isLVar NsX then NfEClos (EsX', lVarSub' ()) else EsX'
					val dryRun = ref true
				in
					case SOME (unifyHead (fn () => "") (SOME dryRun) (hS, NsX))
							handle ExnUnify _ => NONE of
					  SOME () =>
						if !dryRun andalso nbp = 0 then (* unify success *)
							INL $ e (Subst.shift nbp) (NfEClos (E', Subst.switchSub (nbp, nbe)))
						else (* unify maybe *)
							matchHead (hS' (), e', nbe + nbp, E', EsX'' (), foundOne nMaybe)
					| NONE => (* unify failure *)
							matchHead (hS' (), e', nbe + nbp, E', EsX'' (), advance nMaybe)
				end
			| (NfMon _, NfMon _) =>
				(case nMaybe of
					  None _ => raise ExnUnify "Monadic objects not unifiable"
					| One l => INR (SOME l)
					| More => INR NONE)
			| _ => raise Fail "Internal error: matchHeadInLet"
	in matchHead (hS, fn _ => fn e => e, 0, E, E, None 1) end
and matchHeadInLetFixedPos em (q, hS, E, pos) =
	let val () = if isLVar hS then raise Fail "Internal error: mHILFP: lvar1" else ()
		fun matchHead (hS, e, nbe, E, pos) = case NfExpObj.prj E of
			  NfLet (p, N, E') =>
				let val nbp = nbinds p
					fun AtClos (a, s) = invAtomicP (NfClos (NfAtomic' a, s))
					fun hS' () = AtClos (hS, Subst.shift nbp)
					val e' = fn s => fn E =>
								let val s' = Subst.dotn nbe s
								in e s (NfLet' (p, AtClos (N, s'), E)) end
					val () = if pos > 1 andalso isLVar N then
								raise Fail "Internal error: mHILFP: lvar2" else ()
				in if pos = 1 then if isLVar N then
					let val (X as {s, ...}) = invLVar N
						val (p', s') = valOf $ patSub s
						val (Y, qn, _) = unifyLVarLetPrefix em (p, X with's s', p',
								NfLet' (q, hS, NfMon' NfInj.One'))
						val E'' = NfLet' (p, invAtomicP Y,
								NfEClos (E', Subst.dotn nbp (Subst.shift qn)))
					in e (Subst.shift qn) (NfEClos (E'', Subst.switchSub (qn, nbe))) end
				else (* pos = 1 andalso not LVar *)
					( unifyHead em NONE (hS, N)
					; e (Subst.shift nbp) (NfEClos (E', Subst.switchSub (nbp, nbe))) )
				else matchHead (hS' (), e', nbe + nbp, E', pos - 1)
				end
			| NfMon _ => raise Fail "Internal error: mHILFP: wrong pos"
	in matchHead (hS, fn _ => fn e => e, 0, E, pos) end

fun matchHeadInLetBranch em (same, q, hS, E, sc) =
	let val () = if isLVar hS then raise Fail "Internal error: mHILBranch: lvar" else ()
		fun matchHead (hS, e, nbe, E) = case lowerExp $ NfExpObj.prj E of
			  NfLet (p, N, E') =>
				let val nbp = nbinds p
					fun AtClos (a, s) = invAtomicP (NfClos (NfAtomic' a, s))
					fun hS' () = AtClos (hS, Subst.shift nbp)
					val e' = fn s => fn E =>
								let val s' = Subst.dotn nbe s
								in e s (NfLet' (p, AtClos (N, s'), E)) end
					fun assertMon () = case NfExpObj.prj E' of NfMon _ => () | _ =>
							raise Fail "Internal error: matchHeadInLetBranch: assertMon"
				in if isLVar N then (assertMon () ; if same then () else
				BackTrack.backtrack (fn () =>
					let val (X as {s, ...}) = invLVar N
						fun valOf' (SOME x) = x
						  | valOf' NONE = raise Fail "Internal error: not patsub in mHILBranch"
						val (p', s') = valOf' $ patSub s
					in case SOME (unifyLVarLetPrefix em (p, X with's s', p',
								NfLet' (q, hS, NfMon' NfInj.One'))) handle ExnUnify _ => NONE of
						  NONE => ()
						| SOME (Y, qn, _) =>
							let val E'' = NfLet' (p, invAtomicP Y,
											NfEClos (E', Subst.dotn nbp (Subst.shift qn)))
							in sc (e (Subst.shift qn) (NfEClos (E'', Subst.switchSub (qn, nbe))))
							end
					end))
				else
				( BackTrack.backtrack (fn () =>
					case SOME (unifyHead em NONE (hS, N)) handle ExnUnify _ => NONE of
					  SOME () => sc (e (Subst.shift nbp) (NfEClos (E', Subst.switchSub (nbp, nbe))))
					| NONE => ())
				; matchHead (hS' (), e', nbe + nbp, E') )
				end
			| NfMon _ => ()
	in matchHead (hS, fn _ => fn e => e, 0, E) end
fun unifyExpCont em e1e2 sc = case SOME (unifyExp em NONE e1e2) handle ExnUnify _ => NONE of
		SOME () => sc () | NONE => ()
fun unifyBranchExp errmsg (_, 0, e1, e2, sc) =
	(case Util.NfExpObjAuxDefs.prj2 e1 of
		  NfLet (_, (LogicVar _, _), NfMon _) => unifyExpCont errmsg (e1, e2) sc
		| NfMon _ => unifyExpCont errmsg (e1, e2) sc
		| _ => ( addConstraint (vref (Eqn (NfMonad' e1, NfMonad' e2, errmsg)), []) ; sc () ))
  | unifyBranchExp errmsg (same, n, e1, e2, sc) =
	let fun invLet e = case NfExpObj.prj e of NfLet pNE => pNE
				| NfMon _ => raise Fail "Internal error: invLet"
		val (p, N, E) = invLet e1
	in matchHeadInLetBranch errmsg (same, p, N, e2,
			fn e2rest => unifyBranchExp errmsg (same, n-1, E, e2rest, sc))
	end
fun unifyBranch errmsg (ob1, ob2, sc) = case (NfObj.prj ob1, NfObj.prj ob2) of
	  (NfMonad E1, NfMonad E2) =>
		let fun checkLet (n, css, E) = case Util.NfExpObjAuxDefs.T.Fmap NfExpObj.prj E of
				  NfLet (_, (LogicVar {cnstr, ...}, _), E' as NfLet _) =>
					checkLet (n, cnstr::css, E')
				| NfLet (_, (LogicVar X, _), E' as NfMon _) =>
					if null css then INL (n, SOME X) else INR css
				| NfLet (_, _, E') => checkLet (n+1, css, E')
				| NfMon _ => if null css then INL (n, NONE) else INR css
			fun checkLet' E = checkLet (0, [], NfExpObj.prj E)
			fun join (INR css1, INL _) = INR css1
			  | join (INL _, INR css2) = INR css2
			  | join (INR css1, INR css2) = INR (css1 @ css2)
			  | join (INL l1, INL l2) = INL (l1, l2)
		in case join (checkLet' E1, checkLet' E2) of
			  INR css =>
				( addConstraint (vref (Eqn (NfMonad' E1, NfMonad' E2, errmsg)), css)
				; sc () )
			| INL ((n1, SOME {X=r1, s=s1, cnstr=cs1, ...}),
					(n2, SOME {X=r2, s=s2, cnstr=cs2, ...})) =>
				if eq (r1, r2) andalso n1<>n2 then () else
				(case (patSub s1, patSub s2) of
					  (SOME _, SOME _) =>
						if n1 <= n2 then unifyBranchExp errmsg (eq (r1, r2), n1, E1, E2, sc)
						else unifyBranchExp errmsg (eq (r1, r2), n2, E2, E1, sc)
					| (SOME _, NONE) => unifyBranchExp errmsg (eq (r1, r2), n2, E2, E1, sc)
					| (NONE, SOME _) => unifyBranchExp errmsg (eq (r1, r2), n1, E1, E2, sc)
					| (NONE, NONE) =>
						( addConstraint (vref (Eqn (NfMonad' E1, NfMonad' E2, errmsg)), [cs1, cs2])
						; sc () ))
			| INL ((n1, SOME X1), (n2, NONE)) =>
				if n1 > n2 then () else unifyBranchExp errmsg (false, n1, E1, E2, sc)
			| INL ((n1, NONE), (n2, SOME X2)) =>
				if n1 < n2 then () else unifyBranchExp errmsg (false, n2, E2, E1, sc)
			| INL ((n1, NONE), (n2, NONE)) =>
				if n1 <> n2 then () else unifyBranchExp errmsg (false, n1, E1, E2, sc)
		end
	| _ => raise Fail "Internal error: unifyBranch: not monad"

(* solveConstr : constr vref -> (string * (unit -> string)) option *)
fun solveConstr c = case !!c of
	  Solved => NONE
	| Eqn (ob1, ob2, errmsg) =>
		(( if !outputUnify then
			print ("Solving leftover constraint: "^(constrToStr (!!c))^"\n") else ()
		; c ::= Solved
		; unifyObj errmsg NONE (ob1, ob2)
		; NONE ) handle ExnUnify s => SOME (s, errmsg) )
	| Exist (ob1, errmsg) =>
		( if !outputUnify then
			print ("Solving leftover constraint: "^(constrToStr (!!c))^"\n") else ()
		; c ::= Solved
		; if isSome $ objExists errmsg (vref NONE) ob1 then NONE
			else SOME ("Exist constraint failed", errmsg) )

(* solveAwakened : unit -> (string * (unit -> string)) option *)
fun solveAwakened () = case !awakenedConstrs of [] => NONE | c::cs =>
	let val () = awakenedConstrs := cs
		val unifExn = solveConstr c
	in if isSome unifExn then unifExn else solveAwakened () end

(* solveLeftoverConstrOpt : obj option -> (string * (unit -> string)) option *)
fun solveLeftoverConstrOpt N =
	let val () = awakenedConstrs := !!constraints
		val unifExn = solveAwakened ()
		val leftOver = List.mapPartial (fn Solved => NONE | e => SOME e)
						(map !! (!!constraints))
		fun noLeftOver () = case leftOver of [] => NONE
			| _::_ => raise ExnDeclError (TypeErr, "Leftover constraints:\n"
			^ concat (map (fn c => "Constr: "^constrToStr c^"\n") leftOver)
			^ (case N of NONE => "" | SOME N =>
				"\nduring construction of:\n  " ^ PrettyPrint.printObj N ^ "\n"))
	in if isSome unifExn then unifExn else noLeftOver ()
	end

fun exportError NONE = ()
  | exportError (SOME (s, errmsg)) =
		raise ExnDeclError (TypeErr, "Unification failed: " ^ s ^ "\n" ^ errmsg ())

(* constrsSolvable : obj -> bool *)
fun constrsSolvable N = not $ isSome $ solveLeftoverConstrOpt (SOME N)

(* solveLeftoverConstr : unit -> unit *)
fun solveLeftoverConstr () = exportError $ solveLeftoverConstrOpt NONE

fun branchConstr (c, sc) = case !!c of
	  Solved => sc ()
	| Eqn (ob1, ob2, errmsg) =>
		( if !outputUnify then
			print ("Branching on leftover constraint: "^(constrToStr (!!c))^"\n") else ()
		; c ::= Solved
		; unifyBranch errmsg (ob1, ob2, sc) )
	| Exist _ => raise Fail "Internal error: branchConstr: branch on exist-constraint"

val unifyProblemCounter = ref 0
fun unifyProblemCount () =
	( unifyProblemCounter := (!unifyProblemCounter) + 1
	; !unifyProblemCounter )

(* unifyOpt : asyncType * asyncType -> (string * (unit -> string)) option *)
fun unifyOpt (ty1, ty2, errmsg) =
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
	; unifyType errmsg (normalizeType ty1, normalizeType ty2)
	; solveAwakened () ) end
		handle ExnUnify s => SOME (s, errmsg)

(* unifiable : asyncType * asyncType -> bool *)
fun unifiable (ty1, ty2) = not $ isSome $ unifyOpt (ty1, ty2, fn () => "")

(* unify : asyncType * asyncType * (unit -> string) -> unit *)
fun unify ty1ty2errmsg = exportError $ unifyOpt ty1ty2errmsg

(* solveConstrBacktrack : (unit -> unit) -> unit
 * Branch on all ambiguous let-constraints and call sc on all successful leaves *)
fun solveConstrBacktrack sc =
	let fun sc' () = if isSome $ solveAwakened () then () else
			BackTrack.backtrack (fn () => case !!monConstrs of
				  [] => sc ()
				| c::cs => ( monConstrs ::= cs ; branchConstr (c, sc') ))
	in sc' () end

(* unifyAndBranch : asyncType * asyncType * (unit -> unit) -> unit *)
fun unifyAndBranch (ty1, ty2, sc) =
	if unifiable (ty1, ty2) then solveConstrBacktrack sc else ()

end
