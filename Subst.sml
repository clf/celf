functor SubstFun (
	structure Syn : SYNTAX_CORE1
	datatype subst = Dot of Syn.subObj * Syn.subst | Shift of int
	sharing type Syn.subst = subst
	) =
struct
	open Either
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

	(* headSub : head * subst -> (head, obj) either *)
	fun headSub (Const c, _) = LEFT (Const c)
	  | headSub (UCVar v, _) = LEFT (UCVar v)
	  | headSub (LogicVar X, s') = LEFT (LogicVar (X with's comp (#s X, s')))
	  | headSub (Var n, Shift n') = LEFT (Var (n+n'))
	  | headSub (Var 1, Dot (Idx n, s)) = LEFT (Var n)
	  | headSub (Var 1, Dot (Ob N, s)) = RIGHT N
	  | headSub (Var 1, Dot (Undef, s)) = raise ExnUndef
	  | headSub (Var n, Dot (_, s)) = headSub (Var (n-1), s)

	fun subKind (Type, _) = Type
	  | subKind (KPi (x, A, K), s) = KPi (x, TClos (A, s), KClos(K, dot1 s))
	fun subType (Lolli (A, B), s) = Lolli (TClos (A, s), TClos (B, s))
	  | subType (TPi (x, A, B), s) = TPi (x, TClos (A, s), TClos (B, dot1 s))
	  | subType (AddProd (A, B), s) = AddProd (TClos (A, s), TClos (B, s))
	  | subType (Top, _) = Top
	  | subType (TMonad S, s) = TMonad (STClos (S, s))
	  | subType (TAtomic (a, S), s) = TAtomic (a, TSClos (S, s))
	  | subType (ty as TAbbrev _, s) = ty
	fun subTypeSpine (TNil, _) = TNil
	  | subTypeSpine (TApp (N, S), s) = TApp (Clos (N, s), TSClos (S, s))
	fun subSyncType (TTensor (S1, S2), s) = TTensor (STClos (S1, s), STClos (S2, s))
	  | subSyncType (TOne, _) = TOne
	  | subSyncType (Exists (x, A, S), s) = Exists (x, TClos (A, s), STClos (S, dot1 s))
	  | subSyncType (Async A, s) = Async (TClos (A, s))
	
	fun subObj (LinLam (x, N), s) = LinLam (x, Clos (N, dot1 s))
	  | subObj (Lam (x, N), s) = Lam (x, Clos (N, dot1 s))
	  | subObj (AddPair (N1, N2), s) = AddPair (Clos (N1, s), Clos (N2, s))
	  | subObj (Unit, _) = Unit
	  | subObj (Monad E, s) = Monad (EClos (E, s))
	  | subObj (Atomic (H, A, S), s) = (case headSub (H, s) of
			  LEFT H' => Atomic (H', A, SClos (S, s))
			| RIGHT N => Redex (N, A, SClos (S, s)))
	  | subObj (Redex (N, A, S), s) = Redex (Clos (N, s), A, SClos (S, s))
	  | subObj (Constraint (N, A), s) = Constraint (Clos (N, s), TClos (A, s))
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
	
(*	val dummytype = TLogicVar (ref NONE)
	fun dummyvar n = FixObj (Atomic (Var n, dummytype, FixSpine Nil))
	val dummy = Clos (dummyvar 1, Dot (Undef, Shift 0))*)
	(**************************)

	val id = Shift 0

	fun shiftHead (H, n) = leftOf (headSub (H, Shift n))

	fun intersection (Dot (Idx n, s1), Dot (Idx m, s2)) =
			if n=m then dot1 (intersection (s1, s2)) else comp (intersection (s1, s2), Shift 1)
	  | intersection (s1 as Dot _, Shift n) = intersection (s1, Dot (Idx (n+1), Shift (n+1)))
	  | intersection (Shift n, s2 as Dot _) = intersection (Dot (Idx (n+1), Shift (n+1)), s2)
	  | intersection (Shift n1, Shift n2) =
			if n1=n2 then id else raise Fail "Internal error: intersection\n"
	  | intersection _ = raise Fail "Internal error: intersection called on non-pattern sub\n"

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

	fun hdDef (Dot (Undef, _)) = false
	  | hdDef (Dot (Ob _, _)) = raise Fail "Internal error hdDef: not patSub\n"
	  | hdDef (Dot (Idx _, _)) = true
	  | hdDef (Shift _) = true

	fun substToStr f s = if isId s then "" else
			let fun toStr (Dot (Undef, s)) = "*."^(toStr s)
				  | toStr (Dot (Ob ob, s)) = (f ob)^"."^(toStr s)
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
