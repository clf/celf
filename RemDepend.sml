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

type intset = int list
val empty = []
fun occur n = [n]
fun decrn n is = List.filter (fn x => x>=1) (map (fn x => x-n) is)
fun decr is = decrn 1 is
fun depend is = List.exists (fn x => x=1) is
fun union (is1, is2) = is1 @ is2
fun occurFromTo a b = if a <= b then a::occurFromTo (a+1) b else []

fun join2 f (a1, occ1) (a2, occ2) = (f (a1, a2), union (occ1, occ2))
fun joinDep clo f NONE (a1, occ1) (a2, occ2) = (f (NONE, a1, a2), union (occ1, occ2))
  | joinDep clo f (SOME x) (a1, occ1) (a2, occ2) =
		if depend occ2 then (f (SOME x, a1, a2), union (occ1, decr occ2))
		else (f (NONE, a1, clo (a2, Subst.invert (Subst.shift 1))), union (occ1, decr occ2))

fun rdKind ki = case Kind.prj ki of
	  Type => (Type', empty)
	| KPi (x, A, K) => joinDep KClos KPi' x (rdType A) (rdKind K)
and rdType ty = case AsyncType.prj ty of
	  Lolli (A, B) => join2 Lolli' (rdType A) (rdType B)
	| TPi (x, A, B) => joinDep TClos TPi' x (rdType A) (rdType B)
	| AddProd (A, B) => join2 AddProd' (rdType A) (rdType B)
	| Top => (Top', empty)
	| TMonad S => Util.map1 TMonad' (rdSyncType S)
	| TAtomic (a, S) => Util.map1 (fn S' => TAtomic' (a, S')) (rdTypeSpine S)
	| TAbbrev (a, ty) => (TAbbrev' (a, ty), empty)
and rdTypeSpine sp = case TypeSpine.prj sp of
	  TNil => (TNil', empty)
	| TApp (N, S) => join2 TApp' (rdObj N) (rdTypeSpine S)
and rdSyncType sty = case SyncType.prj sty of
	  TTensor (S1, S2) => join2 TTensor' (rdSyncType S1) (rdSyncType S2)
	| TOne => (TOne', empty)
	| Exists (x, A, S) =>
			joinDep STClos Exists' x (rdType A) (rdSyncType S)
		(*join2 (fn (A', S') => Exists' (x, A', S')) (rdType A) (Util.map2 decr (rdSyncType S))*)
	| Async A => Util.map1 Async' (rdType A)
and rdObj ob = case Obj.prj ob of
	  LinLam (x, N) => Util.map12 (fn N' => LinLam' (x, N')) decr (rdObj N)
	| Lam (x, N) => Util.map12 (fn N' => Lam' (x, N')) decr (rdObj N)
	| AddPair (N1, N2) => join2 AddPair' (rdObj N1) (rdObj N2)
	| Unit => (Unit', empty)
	| Monad E => Util.map1 Monad' (rdExp E)
	| Atomic (H, S) => join2 (fn (H', S') => Atomic' (H', S')) (rdHead H) (rdSpine S)
	| Redex (N, A, S) => join2 (fn (N', S') => Redex' (N', A, S')) (rdObj N) (rdSpine S)
	| Constraint (N, A) => join2 Constraint' (rdObj N) (rdType A)
and rdHead h = case h of
	  Const c => (Const c, empty)
	| Var n => (Var n, occur n)
	| UCVar v => (UCVar v, empty)
	| LogicVar (X as {ctx, s, ty, ...}) =>
			let val ctxL = length $ Context.ctx2list $ valOf $ !ctx
				val subL = Subst.fold (fn (_, n) => n+1) (fn _ => 0) s
				fun occurSubOb Undef = empty
				  | occurSubOb (Ob ob) = (#2 (rdObj ob) handle Subst.ExnUndef => empty)
				  | occurSubOb (Idx n) = occur n
				val occurSub = Subst.fold (union o (Util.map1 occurSubOb))
							(fn m => occurFromTo (m+1) (ctxL-subL+m)) s
			in (LogicVar (X with'ty (#1 (rdType ty))), occurSub) end
and rdSpine sp = case Spine.prj sp of
	  Nil => (Nil', empty)
	| App (N, S) => join2 App' (rdObj N) (rdSpine S)
	| LinApp (N, S) => join2 LinApp' (rdObj N) (rdSpine S)
	| ProjLeft S => Util.map1 ProjLeft' (rdSpine S)
	| ProjRight S => Util.map1 ProjRight' (rdSpine S)
and rdExp e = case ExpObj.prj e of
	  Let (p, N, E) =>
			join2 (fn (p', (N', E')) => Let' (p', N', E')) (rdPattern p)
				(join2 (fn x => x) (rdObj N) (Util.map2 (decrn (nbinds p)) (rdExp E)))
	| Mon M => Util.map1 Mon' (rdMonadObj M)
and rdMonadObj m = case MonadObj.prj m of
	  Tensor (M1, M2) => join2 Tensor' (rdMonadObj M1) (rdMonadObj M2)
	| One => (One', empty)
	| DepPair (N, M) => join2 DepPair' (rdObj N) (rdMonadObj M)
	| Norm N => Util.map1 Norm' (rdObj N)
and rdPattern p = case Pattern.prj p of
	  PTensor (p1, p2) => join2 PTensor' (rdPattern p1) (rdPattern p2)
	| POne => (POne', empty)
	| PDepPair (x, A, p) =>
			join2 (fn (A', p') => PDepPair' (x, A', p')) (rdType A) (Util.map2 decr (rdPattern p))
	| PVar (x, A) => Util.map1 (fn A' => PVar' (x, A')) (rdType A)

val remDepKind = #1 o rdKind
val remDepType = #1 o rdType
val remDepObj = #1 o rdObj

end
