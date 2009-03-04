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

signature TLU_OpSem = TOP_LEVEL_UTIL
structure OpSem :> OPSEM =
struct

open Syntax
open Context
open PatternBind
open SignaturTable

val traceSolve = ref false

val fcLimit = ref NONE : int option ref

type context = (asyncType * (lr list * headType) list) context
type lcontext = int list (* must-occur context: list of indices *)

val pBindCtx = depPatBind {dep = fn A => (A, []), nodep = fn A => (A, heads A)}

fun pBindLCtx p l =
	let fun bind (n, p, l) = case Pattern.prj p of
			  PDepTensor (p1, p2) => bind (n, p2, bind (n + nbinds p2, p1, l))
			| PDown _ => n::l
			| _ => l (* POne, PAffi, PBang *)
	in bind (1, p, map (fn k => k + nbinds p) l) end

fun pBind (p, sty) (l, ctx) = (pBindLCtx p l, pBindCtx (p, sty) ctx)

fun linDiff ctxs =
	let fun f (SOME INT, SOME INT) = SOME INT
		  | f (SOME AFF, _) = SOME AFF
		  | f (NONE, NONE) = NONE
		  | f (SOME LIN, SOME LIN) = NONE
		  | f (SOME LIN, NONE) = SOME LIN
		  | f _ = raise Fail "Internal error: linDiff"
		fun g ((x, A, m1), (_, _, m2)) = (x, A, f (m1, m2))
		val diffctx = listPairMapEq g $ map12 ctx2list ctx2list ctxs
		fun allLin (_, []) = []
		  | allLin (n, (_, _, SOME LIN)::ctx) = n :: allLin (n+1, ctx)
		  | allLin (n, _::ctx) = allLin (n+1, ctx)
	in (allLin (1, diffctx), list2ctx diffctx) end

fun removeHyp ((l, ctx), k) = (List.filter (fn n => n<>k) l, #1 $ ctxLookupNum (ctx, k))

fun linIntersect' (n, k::l, (x, A, m)::G) =
		if n=k then
			if m=SOME LIN then k :: linIntersect' (n+1, l, G)
			else linIntersect' (n+1, l, G)
		else linIntersect' (n+1, k::l, G)
  | linIntersect' (_, [], _) = []
  | linIntersect' (_, _::_, []) = raise Fail "Internal error: linIntersect: malformed lctx"
fun linIntersect (l, ctx) = (linIntersect' (1, l, ctx2list ctx), ctx)

fun cannotConsumeLin sty = case SyncType.prj sty of
	  LExists (_, S1, S2) => cannotConsumeLin S1 andalso cannotConsumeLin S2
	| TDown _ => false
	| _ => true (* TOne, TAffi, TBang *)

fun multSplit sty2 =
	if cannotConsumeLin sty2 then
		{ fst = fn (l, ctx) => (l, ctx),
		  snd = fn (_, ctxm) => ([], ctxm) }
	else
		{ fst = fn (_, ctx) => ([], ctx),
		  snd = fn (l, ctxm) => linIntersect (l, ctxm) }


fun genMon (ctx : context, p, sty) =
	let val intCtx = ref NONE
		fun getIntCtx () = case !intCtx of
			  SOME G => SOME G
			| NONE => ( intCtx := (SOME $ ctxIntPart $ ctxMap #1 ctx) ; getIntCtx () )
		fun gen (p, sty) = case (Pattern.prj p, SyncType.prj sty) of
			  (PDepTensor (p1, p2), LExists (p1', S1, S2)) =>
					DepPair' (gen (Util.patternAddDep (p1, p1'), S1), gen (p2, S2))
			| (POne, TOne) => One'
			| (PDown (), TDown _) => MonUndef'
			| (PAffi (), TAffi _) => MonUndef'
			| (PBang NONE, TBang _) => MonUndef'
			| (PBang (SOME x), TBang A) => Bang' (newLVarCtx (getIntCtx ()) A)
			| _ => raise Fail "Internal error: genMon"
		fun gen' sty = case SyncType.prj sty of
			  LExists (p, S1, S2) => DepPair' (gen (p, S1), gen' S2)
			| TOne => One'
			| _ => MonUndef'
	in case p of NONE => gen' sty | SOME p => gen (p, sty) end


(* solve : (lcontext * context) * asyncType * (obj * context -> unit) -> unit *)
(* Right Inversion : Gamma;Delta => A *)
fun solve (ctx, ty, sc) =
	( if !traceSolve then
		print ("Right Invert ("^PrettyPrint.printType ty^")\n")
	  else ()
	; solve' (ctx, ty, sc) )
and solve' (ctx, ty, sc) = case Util.typePrjAbbrev ty of
	  TLPi (p, S, A) => solve (pBind (p, S) ctx, A,
			fn (N, ctxo) => let val p' = Util.patternT2O p in
				(*Option.app (fn ctxo' => sc (LLam' (p', N), ctxo')) (patUnbindOpt (p', ctxo))*)
				sc (LLam' (p', N), patUnbind (p', ctxo)) end)
	(*| AddProd (A, B) => solve (ctx, A,
			fn (N1, ctxo1) => solve (ctx, B,
			fn (N2, ctxo2) => Option.app (fn ctxo => sc (AddPair' (N1, N2), ctxo))
				(ctxAddJoinOpt (ctxo1, ctxo2))))*)
	| AddProd (A, B) => solve (ctx, A,
			fn (N1, ctxo1) => solve (linDiff (#2 ctx, ctxo1), B,
			fn (N2, ctxo2) => sc (AddPair' (N1, N2),
					ctxAddJoin (ctxo1, ctxJoinAffLin (ctxo2, ctxo1)))))
	| TMonad S => forwardChain (!fcLimit, ctx, S, fn (E, ctxo) => sc (Monad' E, ctxo))
	| P as TAtomic _ => matchAtom (ctx, P, sc)
	| TAbbrev _ => raise Fail "Internal error solve: TAbbrev\n"

(* matchAtom : (lcontext * context) * asyncType asyncTypeF * (obj * context -> unit) -> unit *)
(* Choice point: choose hypothesis and switch from Right Inversion to Left Focusing *)
and matchAtom (ctx, P, sc) =
	( if !traceSolve then
		print ("MatchAtom ("^PrettyPrint.printType (AsyncType.inj P)^")\n")
	  else ()
	; matchAtom' (ctx, P, sc) )
and matchAtom' (ctx, P, sc) =
	let val aP = (case P of TAtomic (a, _) => a
					| _ => raise Fail "Internal error: wrong argument to matchAtom!\n")
		val P' = AsyncType.inj P
		fun lFocus (ctx', lr, A, h) = fn () => leftFocus (lr, ctx', P', A, fn (S, ctxo) =>
										sc (Atomic' (h, S), ctxo))
		fun matchSig (c, lr, A) = BackTrack.backtrack (lFocus (ctx, lr, A, Const c))
		fun matchCtx ([], _) = ()
		  | matchCtx ((_, _, NONE)::G, k) = matchCtx (G, k+1)
		  | matchCtx ((x, (A, hds), SOME mode)::G, k) =
		  		let val ctx' = if mode=INT then ctx else removeHyp (ctx, k)
					val A' = TClos (A, Subst.shift k)
					val h = Var (mode, k)
					val () = app (fn (lr, _) => BackTrack.backtrack (lFocus (ctx', lr, A', h)))
							(List.filter (fn (_, HdAtom a) => a=aP | _ => false) hds)
				in matchCtx (G, k+1) end
	in
	  matchCtx (ctx2list $ #2 ctx, 1)
	; app matchSig (getCandAtomic aP)
	end

(* forwardChain : int * (lcontext * context) * syncType * (expObj * context -> unit) -> unit *)
and forwardChain (fcLim, ctx, S, sc) =
	( if !traceSolve then
		print ("ForwardChain ("^PrettyPrint.printType (TMonad' S)^")\n")
	  else ()
	; forwardChain' (fcLim, ctx, S, sc) )
and forwardChain' (fcLim, (l, ctx), S, sc) =
	let fun mlFocus (ctx', lr, A, h) = fn commitExn =>
					monLeftFocus (lr, ([], ctx'), A, fn (S, sty, ctxo) =>
						raise commitExn ((h, S), sty, ctxo))
		fun matchSig (c, lr, A) = fn () => BackTrack.backtrackC (mlFocus (ctx, lr, A, Const c))
		fun matchCtx ([], _) = []
		  | matchCtx ((_, _, NONE)::G, k) = matchCtx (G, k+1)
		  | matchCtx ((x, (A, hds), SOME mode)::G, k) =
		  		let val ctx' = if mode=INT then ctx else #2 $ removeHyp (([], ctx), k)
					val A' = TClos (A, Subst.shift k)
				in List.mapPartial
						(fn (_, HdAtom _) => NONE
						  | (lr, HdMonad) => SOME (fn () =>
							BackTrack.backtrackC (mlFocus (ctx', lr, A', Var (mode, k)))))
						hds
					@ matchCtx (G, k+1)
				end
	in case if fcLim <> SOME 0 then
				PermuteList.findSome (fn f => f ())
					(PermuteList.fromList
						(matchCtx (ctx2list $ ctx, 1) @ map matchSig (getCandMonad ())))
			else NONE of
			  NONE => rightFocus ((l, ctx), genMon (ctx, NONE, S), S,
			  			fn (M, ctxo) => sc (Mon' M, ctxo))
			| SOME (N, sty, ctxm) =>
				let fun syncType2pat sty = case SyncType.prj sty of
						  LExists (p, _, S2) => PDepTensor' (p, syncType2pat S2)
						| TOne => POne'
						| TDown A => PDown' () | TAffi A => PAffi' () | TBang A => PBang' NONE
					val p = syncType2pat sty
					val p' = Util.patternT2O p
				in forwardChain (Option.map (fn x => x - 1) fcLim,
					pBind (p, sty) $ linIntersect (l, ctxm),
					STClos (S, Subst.shift $ nbinds p),
					fn (E, ctxo) => sc (Let' (p', N, E), patUnbind (p', ctxo)))
				end
	end

(* rightFocus : (lcontext * context) * monadObj * syncType * (monadObj * context -> unit) -> unit *)
and rightFocus (ctx, m, sty, sc) =
	( if !traceSolve then
		print ("RightFocus ("^PrettyPrint.printType (TMonad' sty)^")\n")
	  else ()
	; rightFocus' (ctx, m, sty, sc) )
and rightFocus' ((l, ctx), m, sty, sc) = case (MonadObj.prj m, SyncType.prj sty) of
	  (DepPair (m1, m2), LExists (p, S1, S2)) =>
		let val {fst, snd} = multSplit S2
		in rightFocus (fst (l, ctx), m1, S1, fn (M1, ctxm) =>
			rightFocus (snd (l, ctxm), m2,
				STClos (S2, Subst.subM $ normalizeMonadObj M1), (* M1=m1 on free vars in S2 *)
				fn (M2, ctxo) => sc (DepPair' (M1, M2), ctxo)))
		end
	| (One, TOne) => if l <> [] then () else sc (One', ctx)
	| (MonUndef, TDown A) => solve ((l, ctx), A, fn (N, ctxo) => sc (Down' N, ctxo))
	| (MonUndef, TAffi A) => if l <> [] then () else
			solve (([], ctxAffPart ctx), A, fn (N, ctxo) => sc (Affi' N, ctxJoinAffLin (ctxo, ctx)))
	| (MonUndef, TBang A) => if l <> [] then () else
			solve (([], ctxIntPart ctx), A, fn (N, _) => sc (Bang' N, ctx))
	| (Bang N, TBang A) => if l <> [] then () else sc (Bang' N, ctx)
	| _ => raise Fail "Internal error: rightFocus: partial monadObj mismatch"

(* leftFocus : lr list * (lcontext * context) * asyncType * asyncType * (spine * context -> unit) -> unit *)
(* Left Focusing : Gamma;Delta;A >> P  ~~  leftFocus (LR-Oracle, Gamma;Delta, P, A, SuccCont)
 * Construct the spine corresponding to the chosen hypothesis. *)
and leftFocus (lr, ctx, P, ty, sc) =
	( if !traceSolve then
		print ("LeftFocus ("^PrettyPrint.printType ty^")\n")
	  else ()
	; leftFocus' (lr, ctx, P, ty, sc) )
and leftFocus' (lr, (l, ctx), P, ty, sc) = case Util.typePrjAbbrev ty of
	  TLPi (p, A, B) =>
		let val m = genMon (ctx, SOME p, A)
			val {fst, snd} = multSplit A
		in leftFocus (lr, fst (l, ctx), P, TClos (B, Subst.subM $ normalizeMonadObj m),
			fn (S, ctxm) => rightFocus (snd (l, ctxm), m, A,
			fn (M, ctxo) => sc (LApp' (M, S), ctxo)))
		end
	| AddProd (A, B) => (case lr of
			  [] => raise Fail "LR-oracle is out of answers! Internal error!\n"
			| L::lrs => leftFocus (lrs, (l, ctx), P, A, fn (S, ctxo) => sc (ProjLeft' S, ctxo))
			| R::lrs => leftFocus (lrs, (l, ctx), P, B, fn (S, ctxo) => sc (ProjRight' S, ctxo)))
	| TMonad S => raise Fail "Internal error: leftFocus applied to monadic hypothesis!\n"
	| P' as TAtomic _ =>
				if l=[] andalso Unify.unifiable (AsyncType.inj P', P)
				then sc (Nil', ctx)
				else ()
	| TAbbrev _ => raise Fail "Internal error leftFocus: TAbbrev\n"

(* monLeftFocus : lr list * (lcontext * context) * asyncType * (spine * syncType * context -> unit) -> unit *)
and monLeftFocus (lr, ctx, ty, sc) =
	( if !traceSolve then
		print ("monLeftFocus ("^PrettyPrint.printType ty^")\n")
	  else ()
	; monLeftFocus' (lr, ctx, ty, sc) )
and monLeftFocus' (lr, (l, ctx), ty, sc) = case Util.typePrjAbbrev ty of
	  TLPi (p, A, B) => let val m = genMon (ctx, SOME p, A)
			in rightFocus (([], ctx), m, A, fn (M, ctxm) =>
				monLeftFocus (lr, linIntersect (l, ctxm),
					TClos (B, Subst.subM $ normalizeMonadObj m),
					fn (S, sty, ctxo) => sc (LApp' (M, S), sty, ctxo)))
			end
	| AddProd (A, B) => (case lr of
			  [] => raise Fail "LR-oracle is out of answers! Internal error!\n"
			| L::lrs => monLeftFocus (lrs, (l, ctx), A,
				fn (S, sty, ctxo) => sc (ProjLeft' S, sty, ctxo))
			| R::lrs => monLeftFocus (lrs, (l, ctx), B,
				fn (S, sty, ctxo) => sc (ProjRight' S, sty, ctxo)))
	| TMonad sty => sc (Nil', sty, ctx)
	| TAtomic _ => raise Fail "Internal error: monLeftFocus applied to wrong hypothesis!\n"
	| TAbbrev _ => raise Fail "Internal error monLeftFocus: TAbbrev\n"


(* solveEC : asyncType * (obj -> unit) -> unit *)
fun solveEC (ty, sc) = solve (([], emptyCtx), ty, sc o #1)

end
