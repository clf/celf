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

type context = (asyncType * (lr list * headType) list) context

val fcLimit = ref NONE : int option ref

(* solve : context * asyncType * (obj * context -> unit) -> unit *)
(* Right Inversion : Gamma;Delta => A *)
(*fun solve (ctx, ty, sc) = (print ("Solve ("^PrettyPrint.printType ty^")\n"); solve' (ctx, ty, sc))*)
fun solve (ctx, ty, sc : (obj * context -> unit)) = raise Fail "stub2 solve" (*
fun solve (ctx, ty, sc) = case Util.typePrjAbbrev ty of
	  Lolli (A, B) => solve (ctxPushLIN ("", (A, heads A), ctx), TClos (B, Subst.shift 1),
				fn (N, (ctxo, t)) => case ctxPopLINopt (t, ctxo) of
					  NONE => ()
					| SOME ctxo' => sc (LinLam' ("", N), (ctxo', t)))
	| TPi (x, A, B) =>
			let val x' = getOpt (x, "")
				val hds = if isSome x then [] else heads A
				val B' = if isSome x then B else TClos (B, Subst.shift 1)
			in solve (ctxPushINT (x', (A, hds), ctx), B',
				fn (N, ctxo) => sc (Lam' (x', N), map1 ctxPopINT ctxo))
			end
	| AddProd (A, B) => solve (ctx, A,
				fn (N1, (ctxo1, t1)) => solve (ctx, B,
				fn (N2, (ctxo2, t2)) => case ctxAddJoinOpt (t1, t2) (ctxo1, ctxo2) of
					  NONE => ()
					| SOME ctxo => sc (AddPair' (N1, N2), (ctxo, t1 andalso t2))))
	| TMonad S => forwardChain (!fcLimit, ctx, S, fn (E, ctxo) => sc (Monad' E, ctxo))
	| P as TAtomic _ => matchAtom (ctx, P, sc)
	| _ => raise Fail "Internal error solve: TAbbrev\n"

(* matchAtom : context * asyncType asyncTypeF * (obj * context -> unit) -> unit *)
(* Choice point: choose hypothesis and switch from Right Inversion to Left Focusing *)
(*and matchAtom (ctx, P, sc) = (print ("MatchAtom ("^PrettyPrint.printType (AsyncType.inj P)^")\n"); matchAtom' (ctx, P, sc))*)
and matchAtom (ctx, P, sc) =
	let val aP = (case P of TAtomic (a, _) => a
					| _ => raise Fail "Internal error: wrong argument to matchAtom!\n")
		val P' = AsyncType.inj P
		fun lFocus (ctx', lr, A, h) = fn () => leftFocus (lr, ctx', P', A, fn (S, ctxo) =>
										sc (Atomic' (h, S), ctxo))
		fun matchSig (c, lr, A) = BackTrack.backtrack (lFocus (ctx, lr, A, Const c))
		fun matchCtx ([], _) = ()
		  | matchCtx ((_, _, NONE)::G, k) = matchCtx (G, k+1)
		  | matchCtx ((x, (A, hds), SOME mode)::G, k) =
		  		let val ctx' = if mode=INT then ctx else #1 (ctxLookupNum (ctx, k))
					val A' = TClos (A, Subst.shift k)
					val h = Var (mode, k)
					val () = app (fn (lr, _) => BackTrack.backtrack (lFocus (ctx', lr, A', h)))
							(List.filter (fn (_, HdAtom a) => a=aP | _ => false) hds)
				in matchCtx (G, k+1) end
	in
	  matchCtx (ctx2list ctx, 1)
	; app matchSig (getCandAtomic aP)
	end

(* forwardChain : int * context * syncType * (expObj * context -> unit) -> unit *)
(*and forwardChain (fcLim, ctx, S, sc) = (print ("ForwardChain ("^PrettyPrint.printType (TMonad' S)^")\n"); forwardChain' (fcLim, ctx, S, sc))*)
and forwardChain (fcLim, ctx, S, sc) =
	let fun mlFocus (ctx', lr, A, h) = fn commitExn =>
					monLeftFocus (lr, ctx', A, fn (S, ctxo) =>
						raise commitExn ((h, S), ctxo))
		fun matchSig (c, lr, A) = fn () => BackTrack.backtrackC (mlFocus (ctx, lr, A, Const c))
		fun matchCtx ([], _) = []
		  | matchCtx ((_, _, NONE)::G, k) = matchCtx (G, k+1)
		  | matchCtx ((x, (A, hds), SOME mode)::G, k) =
				let val ctx' = if mode=INT then ctx else #1 (ctxLookupNum (ctx, k))
					val A' = TClos (A, Subst.shift k)
				in List.mapPartial
						(fn (_, HdAtom _) => NONE
						  | (lr, HdMonad) => SOME (fn () =>
							BackTrack.backtrackC (mlFocus (ctx', lr, A', Var (mode, k)))))
						hds
					@ matchCtx (G, k+1)
				end
	in
		case if fcLim <> SOME 0 then
				PermuteList.findSome (fn f => f ())
					(PermuteList.fromList (matchCtx (ctx2list ctx, 1) @ map matchSig (getCandMonad ())))
			else NONE of
			  NONE => rightFocus (ctx, S, fn (M, ctxo) => sc (Mon' M, ctxo))
			| SOME (N, ((ctxm, sty), t1)) =>
				let fun syncType2pat sty = case SyncType.prj sty of
						  TTensor (S1, S2) => PTensor' (syncType2pat S1, syncType2pat S2)
						| TOne => POne'
						| Exists (NONE, A, S) =>
								PDepPair' ("", (*A,*) syncType2pat (STClos (S, Subst.shift 1)))
						| Exists (SOME x, A, S) => PDepPair' (x, (*A,*) syncType2pat S)
						| Async A => PVar' ""
					val p = syncType2pat sty
				in forwardChain (Option.map (fn x => x - 1) fcLim,
					patBind (fn A => (A, heads A)) sty ctxm,
					STClos (S, Subst.shift $ nbinds p),
					fn (E, (ctxo', t2)) =>
						case patUnbindOpt (p, ctxo', t2) of
							  NONE => ()
							| SOME ctxo => sc (Let' (p, N, E), (ctxo, t1 orelse t2)))
				end
	end

(* rightFocus : context * syncType * (monadObj * context -> unit) -> unit *)
(* Right Focusing : Gamma;Delta >> S
 * This is the end of forward chaining; construct the monadic object directly. *)
(*and rightFocus (ctx, sty, sc) = (print ("RightFocus ("^PrettyPrint.printType (TMonad' sty)^")\n"); rightFocus' (ctx, sty, sc))*)
and rightFocus (ctx, sty, sc) = case SyncType.prj sty of
	  TTensor (S1, S2) => rightFocus (ctx, S1,
				fn (M1, (ctxm, t1)) => rightFocus (ctxm, S2,
				fn (M2, (ctxo, t2)) => sc (Tensor' (M1, M2), (ctxo, t1 orelse t2))))
	| TOne => sc (One', (ctx, false))
	| Exists (NONE, A, S) => solve (ctxDelLin ctx, A,
				fn (N, _) => rightFocus (ctx, S,
				fn (M, ctxo) => sc (DepPair' (N, M), ctxo)))
	| Exists (SOME x, A, S) => let val N = newLVarCtx (SOME (ctxDelLin (ctxMap #1 ctx))) A
				in rightFocus (ctx, STClos (S, Subst.subI $ normalizeObj N),
				fn (M, ctxo) => sc (DepPair' (N, M), ctxo)) end
	| Async A => solve (ctx, A, fn (N, ctxo) => sc (Norm' N, ctxo))

(* leftFocus : bool list * context * asyncType * asyncType * (spine * context -> unit) -> unit *)
(* Left Focusing : Gamma;Delta;A >> P  ~~  leftFocus (LR-Oracle, Gamma;Delta, P, A, SuccCont)
 * Construct the spine corresponding to the chosen hypothesis. *)
(*and leftFocus (lr, ctx, P, ty, sc) = (print ("LeftFocus ("^PrettyPrint.printType ty^")\n"); leftFocus' (lr, ctx, P, ty, sc))*)
and leftFocus (lr, ctx, P, ty, sc) = case Util.typePrjAbbrev ty of
	  Lolli (A, B) => leftFocus (lr, ctx, P, B,
				fn (S, (ctxm, t1)) => solve (ctxm, A,
				fn (N, (ctxo, t2)) => sc (LinApp' (N, S), (ctxo, t1 orelse t2))))
	| TPi (NONE, A, B) => leftFocus (lr, ctx, P, B,
				fn (S, ctxo) => solve (ctxDelLin (#1 ctxo), A,
				fn (N, _) => sc (App' (N, S), ctxo)))
	| TPi (SOME x, A, B) => let val N = newLVarCtx (SOME (ctxDelLin (ctxMap #1 ctx))) A
				in leftFocus (lr, ctx, P, TClos (B, Subst.subI $ normalizeObj N),
				fn (S, ctxo) => sc (App' (N, S), ctxo)) end
	| AddProd (A, B) => (case lr of
			  [] => raise Fail "LR-oracle is out of answers! Internal error!\n"
			| L::lrs => leftFocus (lrs, ctx, P, A, fn (S, ctxo) => sc (ProjLeft' S, ctxo))
			| R::lrs => leftFocus (lrs, ctx, P, B, fn (S, ctxo) => sc (ProjRight' S, ctxo)))
	| TMonad S => raise Fail "Internal error: leftFocus applied to monadic hypothesis!\n"
	| P' as TAtomic _ =>
				if Unify.unifiable (AsyncType.inj P', P)
				then sc (Nil', (ctx, false))
				else ()
	| _ => raise Fail "Internal error leftFocus: TAbbrev\n"

(*and monLeftFocus (lr, ctx, ty, sc) = (print ("monLeftFocus ("^PrettyPrint.printType ty^")\n"); monLeftFocus' (lr, ctx, ty, sc))*)
and monLeftFocus (lr, ctx, ty, sc) = case Util.typePrjAbbrev ty of
	  Lolli (A, B) => solve (ctx, A,
				fn (N, (ctxm, t1)) => monLeftFocus (lr, ctxm, B,
				fn (S, (ctxo, t2)) => sc (LinApp' (N, S), (ctxo, t1 orelse t2))))
	| TPi (NONE, A, B) => solve (ctxDelLin ctx, A,
				fn (N, _) => monLeftFocus (lr, ctx, B,
				fn (S, ctxo) => sc (App' (N, S), ctxo)))
	| TPi (SOME x, A, B) => let val N = newLVarCtx (SOME (ctxDelLin (ctxMap #1 ctx))) A
				in monLeftFocus (lr, ctx, TClos (B, Subst.subI $ normalizeObj N),
				fn (S, ctxo) => sc (App' (N, S), ctxo)) end
	| AddProd (A, B) => (case lr of
			  [] => raise Fail "LR-oracle is out of answers! Internal error!\n"
			| L::lrs => monLeftFocus (lrs, ctx, A, fn (S, ctxo) => sc (ProjLeft' S, ctxo))
			| R::lrs => monLeftFocus (lrs, ctx, B, fn (S, ctxo) => sc (ProjRight' S, ctxo)))
	| TMonad sty => sc (Nil', ((ctx, sty), false))
	| TAtomic _ => raise Fail "Internal error: monLeftFocus applied to wrong hypothesis!\n"
	| _ => raise Fail "Internal error monLeftFocus: TAbbrev\n"
*)

(* solveEC : asyncType * (obj -> unit) -> unit *)
fun solveEC (ty, sc) = solve (emptyCtx, ty, sc o #1)

end
