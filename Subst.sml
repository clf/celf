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

signature TLU_SubstFun = TOP_LEVEL_UTIL
functor SubstFun (
	structure Syn : SYNTAX_CORE1
	datatype subst = Dot of Syn.subObj * subst | Shift of int
	sharing type Syn.subst = subst
	) =
struct
	open Syn infix with's
	fun Clos' (Ob N, t) = Ob (Clos (N, t))
	  | Clos' (Idx n, Shift n') = Idx (n+n')
	  | Clos' (Idx 1, Dot (N, _)) = N
	  | Clos' (Idx n, Dot (_, t)) = Clos' (Idx (n-1), t)
	  | Clos' (Undef, _) = Undef

	(* comp : subst * subst -> subst *)
	fun comp (Shift 0, s) = s
	  | comp (s, Shift 0) = s
	  | comp (Shift n, Dot (N, s)) = comp (Shift (n-1), s)
	  | comp (Shift n, Shift m) = Shift (n+m)
	  | comp (Dot (N, s), s') = Dot (Clos' (N, s'), comp (s, s'))

	exception ExnUndef

	fun dot1 s = Dot (Idx 1, comp (s, Shift 1))
	fun dotn 0 s = s
	  | dotn n s = dotn (n-1) (dot1 s)

	(* headSub : head * subst -> (head, obj) sum *)
	fun headSub (Const c, _) = INL (Const c)
	  | headSub (UCVar v, _) = INL (UCVar v)
	  | headSub (LogicVar X, s') = INL (LogicVar (X with's comp (#s X, s')))
	  | headSub (Var n, Shift n') = INL (Var (n+n'))
	  | headSub (Var 1, Dot (Idx n, s)) = INL (Var n)
	  | headSub (Var 1, Dot (Ob N, s)) = INR N
	  | headSub (Var 1, Dot (Undef, s)) = raise ExnUndef
	  | headSub (Var n, Dot (_, s)) = headSub (Var (n-1), s)

	fun subKind (Type, _) = Type
	  | subKind (KPi (NONE, A, K), s) = KPi (NONE, TClos (A, s), KClos(K, s))
	  | subKind (KPi (SOME x, A, K), s) = KPi (SOME x, TClos (A, s), KClos(K, dot1 s))
	fun subType (Lolli (A, B), s) = Lolli (TClos (A, s), TClos (B, s))
	  | subType (TPi (NONE, A, B), s) = TPi (NONE, TClos (A, s), TClos (B, s))
	  | subType (TPi (SOME x, A, B), s) = TPi (SOME x, TClos (A, s), TClos (B, dot1 s))
	  | subType (AddProd (A, B), s) = AddProd (TClos (A, s), TClos (B, s))
	  | subType (Top, _) = Top
	  | subType (TMonad S, s) = TMonad (STClos (S, s))
	  | subType (TAtomic (a, S), s) = TAtomic (a, TSClos (S, s))
	  | subType (ty as TAbbrev _, s) = ty
	fun subTypeSpine (TNil, _) = TNil
	  | subTypeSpine (TApp (N, S), s) = TApp (Clos (N, s), TSClos (S, s))
	fun subSyncType (TTensor (S1, S2), s) = TTensor (STClos (S1, s), STClos (S2, s))
	  | subSyncType (TOne, _) = TOne
	  | subSyncType (Exists (NONE, A, S), s) = Exists (NONE, TClos (A, s), STClos (S, s))
	  | subSyncType (Exists (SOME x, A, S), s) = Exists (SOME x, TClos (A, s), STClos (S, dot1 s))
	  | subSyncType (Async A, s) = Async (TClos (A, s))
	
	fun subObj _ (LinLam (x, N), s) = LinLam (x, Clos (N, dot1 s))
	  | subObj _ (Lam (x, N), s) = Lam (x, Clos (N, dot1 s))
	  | subObj _ (AddPair (N1, N2), s) = AddPair (Clos (N1, s), Clos (N2, s))
	  | subObj _ (Unit, _) = Unit
	  | subObj _ (Monad E, s) = Monad (EClos (E, s))
	  | subObj redex (Atomic (H, S), s) = (case headSub (H, s) of
			  INL H' => Atomic (H', SClos (S, s))
			| INR N => redex (N, SClos (S, s)))
	  | subObj _ (Redex (N, A, S), s) = Redex (Clos (N, s), A, SClos (S, s))
	  | subObj _ (Constraint (N, A), s) = Constraint (Clos (N, s), TClos (A, s))
	fun subSpine (Nil, _) = Nil
	  | subSpine (App (N, S), s) = App (Clos (N, s), SClos (S, s))
	  | subSpine (LinApp (N, S), s) = LinApp (Clos (N, s), SClos (S, s))
	  | subSpine (ProjLeft S, s) = ProjLeft (SClos (S, s))
	  | subSpine (ProjRight S, s) = ProjRight (SClos (S, s))
	fun subExpObj (Let (p, N, E), s) = Let (PClos (p, s), Clos (N, s), EClos (E, dotn (nbinds p) s))
	  | subExpObj (Mon M, s) = Mon (MClos (M, s))
	fun subMonadObj (Tensor (M1, M2), s) = Tensor (MClos (M1, s), MClos (M2, s))
	  | subMonadObj (One, s) = One
	  | subMonadObj (DepPair (N, M), s) = DepPair (Clos (N, s), MClos (M, s))
	  | subMonadObj (Norm N, s) = Norm (Clos (N, s))
	fun subPattern (PTensor (p1, p2), s) = PTensor (PClos (p1, s), PClos (p2, s))
	  | subPattern (POne, s) = POne
	  | subPattern (PDepPair (x, A, p), s) = PDepPair (x, TClos (A, s), PClos (p, dot1 s))
	  | subPattern (PVar (x, A), s) = PVar (x, TClos (A, s))
	
	fun leftOf (INL l) = l
	  | leftOf (INR _) = raise Option.Option
	(**************************)

	val id = Shift 0

	fun shiftHead (H, n) = leftOf $ headSub (H, Shift n)

	(* Invariant:
	   Let G1, G2 contexts,
	   n1 = |G1|, n2 = |G2|
	   and G1' = k-prefix of G1
	   G1, G2 |- switchSub' k : G2, G1'
	   G1, G2 |- switchSub (n1,n2) : G2, G1
	*)
	fun switchSub (n1, n2) =
		let fun switchSub' 0 = dotn n2 (Shift n1)
			  | switchSub' k = Dot (Idx (n2+n1+1-k), switchSub' (k-1))
		in switchSub' n1 end

	fun intersection conv s1s2 =
		let fun eq (Idx n, Idx m) = n=m
			  | eq (Idx n, Ob N) = (conv (INL n, N) handle ExnUndef => false)
			  | eq (Ob N, Idx n) = (conv (INL n, N) handle ExnUndef => false)
			  | eq (Ob N1, Ob N2) = (conv (INR N1, N2) handle ExnUndef => false)
			  | eq (Undef, _) = false (*raise Fail "Internal error intersection"*)
			  | eq (_, Undef) = false (*raise Fail "Internal error intersection"*)
			fun intersect (Dot (n1, s1), Dot (n2, s2)) =
					if eq (n1, n2) then dot1 (intersect (s1, s2))
					else comp (intersect (s1, s2), Shift 1)
			  | intersect (s1 as Dot _, Shift n) = intersect (s1, Dot (Idx (n+1), Shift (n+1)))
			  | intersect (Shift n, s2 as Dot _) = intersect (Dot (Idx (n+1), Shift (n+1)), s2)
			  | intersect (Shift n1, Shift n2) =
					if n1=n2 then id else raise Fail "Internal error: intersection\n"
		in intersect s1s2 end

	fun invert s =
		let fun lookup (n, Shift _, p) = NONE
			  | lookup (_, Dot (Ob _, _), _) =
					raise Fail "Internal error: invert called on non-pattern sub\n"
			  | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
			  | lookup (n, Dot (Idx k, s'), p) =
					if k = p then SOME n else lookup (n+1, s', p)
			fun invert'' (0, si) = si
			  | invert'' (p, si) =
					(case lookup (1, s, p) of
						  SOME k => invert'' (p-1, Dot (Idx k, si))
						| NONE => invert'' (p-1, Dot (Undef, si)))
			fun invert' (n, Shift p) = invert'' (p, Shift n)
			  | invert' (n, Dot (_, s')) = invert' (n+1, s')
		in invert' (0, s) end

	fun isId s =
		let fun isId' n (Shift m) = (n = m)
			  | isId' n (Dot (Idx m, s)) = (n+1 = m) andalso isId' (n+1) s
			  | isId' _ _ = false
		in isId' 0 s end

	fun fold f e (Dot (ob, s)) = f (ob, fold f e s)
	  | fold f e (Shift n) = e n
(*	fun fold f e (Dot (Undef, s)) = f (dummy, fold f e s)
	  | fold f e (Dot (Ob ob, s)) = f (ob, fold f e s)
	  | fold f e (Dot (Idx n, s)) = f (dummyvar n, fold f e s)
	  | fold f e (Shift n) = e n*)

	fun map f (Dot (Ob ob, s)) = Dot (Ob $ f ob handle ExnUndef => Undef, map f s)
	  | map f (Dot (Undef, s)) = Dot (Undef, map f s)
	  | map f (Dot (Idx n, s)) = Dot (Idx n, map f s)
	  | map f (Shift n) = Shift n

	fun hdDef (Dot (Undef, _)) = false
	  | hdDef (Dot (Ob _, _)) = raise Fail "Internal error hdDef: not patSub\n"
	  | hdDef (Dot (Idx _, _)) = true
	  | hdDef (Shift _) = true

	fun substToStr f s = if isId s then "" else
			let fun toStr (Dot (Undef, s)) = "*."^(toStr s)
				  | toStr (Dot (Ob ob, s)) = (f ob handle ExnUndef => "*")^"."^(toStr s)
				  | toStr (Dot (Idx n, s)) = (Int.toString n)^"."^(toStr s)
				  | toStr (Shift n) = "^"^(Int.toString n)
			in "["^(toStr s)^"]" end

	fun patSub etaContract s' =
		let exception ExnPatSub
			fun add (n, l) = if List.exists (fn i => i=n) l then raise ExnPatSub else n::l
			fun ps (m, _, s as Shift n) = if m <= n then s else raise ExnPatSub
			  | ps (m, l, Dot (Undef, s)) = Dot (Undef, ps (m, l, s))
			  | ps (m, l, Dot (Idx n, s)) = Dot (Idx n, ps (Int.max (m, n), add (n, l), s))
			  | ps (m, l, Dot (Ob N, s)) =
					ps (m, l, Dot (Idx (etaContract ExnPatSub N) handle ExnUndef => Undef, s))
		in SOME (ps (0, [], s')) handle ExnPatSub => NONE end

	fun shift n = Shift n
end
