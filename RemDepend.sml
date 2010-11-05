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

signature TLU_RemDepend = TOP_LEVEL_UTIL
structure RemDepend :> REMDEPEND =
struct

open Syntax infix with'ty

open NatSet
val depend = member 1

fun join2 f (a1, occ1) (a2, occ2) = (f (a1, a2), union (occ1, occ2))
fun join3 f (a1, occ1) (a2, occ2) (a3, occ3) = (f (a1, a2, a3), union (occ1, union (occ2, occ3)))
fun joinDep clo f NONE (a1, occ1) (a2, occ2) = (f (NONE, a1, a2), union (occ1, occ2))
  | joinDep clo f (SOME x) (a1, occ1) (a2, occ2) =
		if depend occ2 then (f (SOME x, a1, a2), union (occ1, decr occ2))
		else (f (NONE, a1, clo (a2, Subst.invert (Subst.shift 1))), union (occ1, decr occ2))
fun assertEmpty ns = if isEmpty ns then () else raise Fail "Internal error: rdPat"

fun rdPat p occ = case Pattern.prj p of
	  PDepTensor (p1, p2) =>
		let val (occ2, occ1) = splitn (nbinds p2) occ
		in PDepTensor' (rdPat p1 occ1, rdPat p2 occ2) end
	| POne => (assertEmpty occ; POne')
	| PDown () => (assertEmpty occ; PDown' ())
	| PAffi () => (assertEmpty occ; PAffi' ())
	| PBang NONE => (assertEmpty occ; PBang' NONE)
	| PBang (SOME x) => if depend occ then p else PBang' NONE
fun joinDepP c p (a1, occ1) (a2, occ2) =
	let val (occ2p, occ2') = splitn (nbinds p) occ2
	in (c (rdPat p occ2p, a1, a2), union (occ1, occ2')) end

fun rdKind ki = case Kind.prj ki of
	  Type => (Type', empty)
	| KPi (x, A, K) => joinDep KClos KPi' x (rdType A) (rdKind K)
and rdType ty = case AsyncType.prj ty of
	  TLPi (p, A, B) => joinDepP TLPi' p (rdSyncType A) (rdType B)
	| AddProd (A, B) => join2 AddProd' (rdType A) (rdType B)
	| TMonad S => map1 TMonad' (rdSyncType S)
	| TAtomic (a, S) => map1 (fn S' => TAtomic' (a, S')) (rdTypeSpine S)
	| TAbbrev (a, ty) => (TAbbrev' (a, ty), empty)
and rdTypeSpine sp = case TypeSpine.prj sp of
	  TNil => (TNil', empty)
	| TApp (N, S) => join2 TApp' (rdObj N) (rdTypeSpine S)
and rdSyncType sty = case SyncType.prj sty of
	  LExists (p, S1, S2) => joinDepP LExists' p (rdSyncType S1) (rdSyncType S2)
	| TOne => (TOne', empty)
	| TDown A => map1 TDown' (rdType A)
	| TAffi A => map1 TAffi' (rdType A)
	| TBang A => map1 TBang' (rdType A)
and rdObj ob = case Obj.prj ob of
	  LLam (p, N) => map12 (fn N' => LLam' (p, N')) (decrn $ nbinds p) (rdObj N)
	| AddPair (N1, N2) => join2 AddPair' (rdObj N1) (rdObj N2)
	| Monad E => map1 Monad' (rdExp E)
	| Atomic (H, S) => join2 Atomic' (rdHead H) (rdSpine S)
	| Redex (N, A, S) => join2 (fn (N', S') => Redex' (N', A, S')) (rdObj N) (rdSpine S)
	| Constraint (N, A) => join2 Constraint' (rdObj N) (rdType A)
and rdHead h = case h of
	  Const c => (Const c, empty)
	| Var n => (Var n, singleton $ #2 n)
	| UCVar v => (UCVar v, empty)
	| LogicVar (X as {ctx, s, ty, ...}) =>
			let val ctxL = Context.ctxLength $ valOf $ !ctx
				val subL = Subst.fold (fn (_, n) => n+1) (fn _ => 0) s
				fun occurSubOb Undef = empty
				  | occurSubOb (Ob (_, ob)) = (#2 $ rdObj $ unnormalizeObj ob
						handle Subst.ExnUndef => (*empty*) raise Fail "Internal error: rdHead")
				  | occurSubOb (Idx (_, n)) = singleton n
				val occurSub = Subst.fold (union o (map1 occurSubOb))
							(fn m => occurFromTo (m+1) (ctxL-subL+m)) s
			in (LogicVar (X with'ty (#1 (rdType ty))), occurSub) end
and rdSpine sp = case Spine.prj sp of
	  Nil => (Nil', empty)
	| LApp (M, S) => join2 LApp' (rdMonadObj M) (rdSpine S)
	| ProjLeft S => map1 ProjLeft' (rdSpine S)
	| ProjRight S => map1 ProjRight' (rdSpine S)
and rdExp e = case ExpObj.prj e of
	  LetRedex (p, S, N, E) =>
			join2 (fn (N', E') => LetRedex' (p, S, N', E')) (rdObj N)
				(map2 (decrn $ nbinds p) (rdExp E))
	| Let (p, (H, S), E) =>
			join3 (fn (H', S', E') => Let' (p, (H', S'), E')) (rdHead H) (rdSpine S)
				(map2 (decrn $ nbinds p) (rdExp E))
	| Mon M => map1 Mon' (rdMonadObj M)
and rdMonadObj m = case MonadObj.prj m of
	  DepPair (M1, M2) => join2 DepPair' (rdMonadObj M1) (rdMonadObj M2)
	| One => (One', empty)
	| Down N => map1 Down' (rdObj N)
	| Affi N => map1 Affi' (rdObj N)
	| Bang N => map1 Bang' (rdObj N)
	| MonUndef => raise Fail "Internal error: rdMonadObj: MonUndef"

val remDepKind = #1 o rdKind
val remDepType = #1 o rdType
val remDepObj = #1 o rdObj

end
