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
	open Context
	open Syn infix with's

	fun assertLin b = if b then () else raise Fail "Linearity substitution mismatch"
	fun isUndef Undef = true
	  | isUndef _ = false

	fun dom2lin (Ob (INT, N)) = Ob (LIN, N)
	  | dom2lin (Ob (LIN, _)) = raise Fail "Linearity substitution mismatch"
	  | dom2lin (Idx (ID, n)) = Idx (LIN2INT, n)
	  | dom2lin (Idx (LIN2INT, _)) = raise Fail "Linearity substitution mismatch"
	  | dom2lin Undef = Undef

	fun Clos' (Ob (m, N), t) = Ob (m, Clos (N, t))
	  | Clos' (Idx (M, n), Shift n') = Idx (M, n+n')
	  | Clos' (Idx (ID, 1), Dot (N, _)) = N
	  | Clos' (Idx (LIN2INT, 1), Dot (N, _)) = dom2lin N
	  | Clos' (Idx (M, n), Dot (_, t)) = Clos' (Idx (M, n-1), t)
	  | Clos' (Undef, _) = Undef

	(* comp : subst * subst -> subst *)
	fun comp (Shift 0, s) = s
	  | comp (s, Shift 0) = s
	  | comp (Shift n, Dot (N, s)) = comp (Shift (n-1), s)
	  | comp (Shift n, Shift m) = Shift (n+m)
	  | comp (Dot (N, s), s') = Dot (Clos' (N, s'), comp (s, s'))

	exception ExnUndef

	fun dot1 s = Dot (Idx (ID, 1), comp (s, Shift 1))
	fun dotn 0 s = s
	  | dotn n s = dotn (n-1) (dot1 s)

	(* headSub : head * subst -> (head, obj) sum *)
	fun headSub (Const c, _) = INL (Const c)
	  | headSub (UCVar v, _) = INL (UCVar v)
	  | headSub (LogicVar X, s') = INL (LogicVar (X with's comp (#s X, s')))
	  | headSub (Var (M, n), Shift n') = INL (Var (M, n+n'))
	  | headSub (Var (M, 1), Dot (Idx (ID, n), s)) = INL (Var (M, n))
	  | headSub (Var (LIN, 1), Dot (Idx (LIN2INT, n), s)) = INL (Var (INT, n))
	  | headSub (Var (INT, 1), Dot (Idx (LIN2INT, n), s)) = raise Fail "Linearity mismatch"
	  | headSub (Var (M, 1), Dot (Ob (M', N), s)) = (assertLin (M=M') ; INR N)
	  | headSub (Var (_, 1), Dot (Undef, s)) = raise ExnUndef
	  | headSub (Var (M, n), Dot (_, s)) = headSub (Var (M, n-1), s)

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
			  | switchSub' k = Dot (Idx (ID, n2+n1+1-k), switchSub' (k-1))
		in switchSub' n1 end

	(* Input:
	   G1 |- s1 : G2  and  G1 |- s2 : G2
	   Output:
	   G2 |- w : G3   w weakening substitution
	   Constructs a subcontext G3 of G2 consisting of the parts of G2
	   on which s1 and s2 agrees.
	*)
	fun intersection conv s1s2 =
		let fun modeMult ID m = m
			  | modeMult LIN2INT LIN = INT
			  | modeMult LIN2INT INT = raise Fail "Linearity mismatch in intersection"
			fun eq (Idx (M1, n), Idx (M2, m)) = (assertLin (M1=M2) ; n=m)
			  | eq (Idx (m, n), Ob (M, N)) =
					(conv (INL (modeMult m M, n), N) handle ExnUndef => false)
			  | eq (N1 as Ob _, N2 as Idx _) = eq (N2, N1)
			  | eq (Ob (M1, N1), Ob (M2, N2)) =
					( assertLin (M1=M2) ; conv (INR N1, N2) handle ExnUndef => false )
			  | eq (Undef, _) = false (*raise Fail "Internal error intersection"*)
			  | eq (_, Undef) = false (*raise Fail "Internal error intersection"*)
			fun intersect (Dot (n1, s1), Dot (n2, s2)) =
					if eq (n1, n2) then dot1 (intersect (s1, s2))
					else comp (intersect (s1, s2), Shift 1)
			  | intersect (s1 as Dot _, Shift n) =
			  		intersect (s1, Dot (Idx (ID, n+1), Shift (n+1)))
			  | intersect (Shift n, s2 as Dot _) =
			  		intersect (Dot (Idx (ID, n+1), Shift (n+1)), s2)
			  | intersect (Shift n1, Shift n2) =
					if n1=n2 then id else raise Fail "Internal error: intersection\n"
		in intersect s1s2 end

	fun invert s =
		let fun lookup (_, Shift _, p) = NONE
			  | lookup (_, Dot (Ob _, _), _) =
					raise Fail "Internal error: invert called on non-pattern sub\n"
			  | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
			  | lookup (_, Dot (Idx (LIN2INT, _), _), _) =
					raise Fail "Internal error: invert called on non-pattern sub\n"
			  | lookup (n, Dot (Idx (ID, k), s'), p) =
					if k = p then SOME n else lookup (n+1, s', p)
			fun invert'' (0, si) = si
			  | invert'' (p, si) =
					(case lookup (1, s, p) of
						  SOME k => invert'' (p-1, Dot (Idx (ID, k), si))
						| NONE => invert'' (p-1, Dot (Undef, si)))
			fun invert' (n, Shift p) = invert'' (p, Shift n)
			  | invert' (n, Dot (_, s')) = invert' (n+1, s')
		in invert' (0, s) end

	fun isId s =
		let fun isId' n (Shift m) = (n = m)
			  | isId' n (Dot (Idx (ID, m), s)) = (n+1 = m) andalso isId' (n+1) s
			  | isId' _ _ = false
		in isId' 0 s end

	fun fold f e (Dot (ob, s)) = f (ob, fold f e s)
	  | fold f e (Shift n) = e n
(*	fun fold f e (Dot (Undef, s)) = f (dummy, fold f e s)
	  | fold f e (Dot (Ob ob, s)) = f (ob, fold f e s)
	  | fold f e (Dot (Idx n, s)) = f (dummyvar n, fold f e s)
	  | fold f e (Shift n) = e n*)

	fun map f (Dot (Ob (M, ob), s)) = Dot (Ob (M, f ob) handle ExnUndef => Undef, map f s)
	  | map f (Dot (Undef, s)) = Dot (Undef, map f s)
	  | map f (Dot (Idx n, s)) = Dot (Idx n, map f s)
	  | map f (Shift n) = Shift n

	fun hdDef (Dot (Undef, _)) = false
	  | hdDef (Dot (Ob _, _)) = raise Fail "Internal error hdDef: not patSub\n"
	  | hdDef (Dot (Idx _, _)) = true
	  | hdDef (Shift _) = true

	fun substToStr f s = if isId s then "" else
			let fun m2s LIN = "L"
				  | m2s INT = "!"
				fun cm2s ID = ""
				  | cm2s LIN2INT = "!/L"
				fun toStr (Dot (Undef, s)) = "*."^(toStr s)
				  | toStr (Dot (Ob (M, ob), s)) =
						(f ob handle ExnUndef => "*")^"/"^(m2s M)^"."^(toStr s)
				  | toStr (Dot (Idx (M, n), s)) = (Int.toString n)^(cm2s M)^"."^(toStr s)
				  | toStr (Shift n) = "^"^(Int.toString n)
			in "["^(toStr s)^"]" end

	(* patSub Eta.etaContract s G1
	 *    where G |- s : G1 can give three different results:
	 * NONE
	 *    s is not a pattern sub
	 * SOME ([], s')
	 *    s is equal to s' which is a pattern sub
	 * SOME (p, s')
	 *    s is equal to s' which is a pattern sub, but
	 *    G  |- s : G1
	 *    G' |- s' : G1
	 *    G equals G' on the indices not in p
	 *    n in p => G_n is INT and G'_n is LIN
	 *)
	fun modeInvDiv LIN INT = LIN2INT
	  | modeInvDiv INT LIN = raise Fail "Linearity mismatch patSub"
	  | modeInvDiv _ _ = ID
	fun patSub etaContract s' domCtx =
		let exception ExnPatSub
			val p = ref []
			val domCtx' = List.map #2 $ ctx2list domCtx
			fun add (n : int, l) = if List.exists (fn i => i=n) l then raise ExnPatSub else n::l
			fun ps (m, _, s as Shift n, _) = if m <= n then s else raise ExnPatSub
			  | ps (m, l, Dot (Undef, s), _::G) = Dot (Undef, ps (m, l, s, G))
			  | ps (m, l, Dot (Idx (ID, n), s), _::G) =
					Dot (Idx (ID, n), ps (Int.max (m, n), add (n, l), s, G))
			  | ps (m, l, Dot (Idx (LIN2INT, n), s), G as _::_) =
					( p := n :: !p
					; ps (m, l, Dot (Idx (ID, n), s), G) )
			  | ps (m, l, Dot (Ob (M, N), s), A::G) =
					let val N' = Idx (map1 (modeInvDiv M) $ etaContract ExnPatSub N A)
								handle ExnUndef => if M=INT then Undef else raise Fail "stub:lintop"
					in ps (m, l, Dot (N', s), A::G) end
			  | ps (_, _, Dot _, []) = raise Fail "Internal error: mismatch between ctx and sub"
		in SOME $ (fn s => (!p, s)) $ ps (0, [], s', domCtx') handle ExnPatSub => NONE end

	fun shift n = Shift n
end
