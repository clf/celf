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
	type t
	datatype subst' = Dot of t * subst' | Shift of int
	structure Syn : SYNTAX_CORE1
		where type 'a substi = subst'
	sharing type t = Syn.subObj
	) =
struct
	open Context
	open Syn infix with's

	fun assertLin b = if b then () else raise Fail "Internal error: Linearity substitution mismatch"
	fun isUndef Undef = true
	  | isUndef _ = false

	fun domMult ID N = N
	  | domMult INT4LIN (Ob (INT, N)) = Ob (LIN, N)
	  | domMult AFF4LIN (Ob (AFF, N)) = Ob (LIN, N)
	  | domMult INT4AFF (Ob (INT, N)) = Ob (AFF, N)
	  | domMult _ (Ob (_, _)) = raise Fail "Internal error: Linearity substitution mismatch"
	  | domMult M (Idx (ID, n)) = Idx (M, n)
	  | domMult AFF4LIN (Idx (INT4AFF, n)) = Idx (INT4LIN, n)
	  | domMult _ (Idx (_, _)) = raise Fail "Internal error: Linearity substitution mismatch"
	  | domMult _ Undef = Undef

	fun Clos' (Ob (m, N), t) = Ob (m, NfClos (N, t))
	  | Clos' (Idx (M, n), Shift n') = Idx (M, n+n')
	  | Clos' (Idx (M, 1), Dot (N, _)) = domMult M N
	  | Clos' (Idx (M, n), Dot (_, t)) = Clos' (Idx (M, n-1), t)
	  | Clos' (Undef, _) = Undef

	(* comp : subst * subst -> subst *)
	fun comp (Shift 0, s) = s
	  | comp (s, Shift 0) = s
	  | comp (Shift n, Dot (N, s)) = comp (Shift (n-1), s)
	  | comp (Shift n, Shift m) = Shift (n+m)
	  | comp (Dot (N, s), s') = Dot (Clos' (N, s'), comp (s, s'))

	(* Undefs in substitutions are represented explicitly, but outside
	 * substitutions they are represented as a raised ExnUndef.  This
	 * ensures automatic propagation up to the nearest handler. *)
	exception ExnUndef

	fun dot1 s = Dot (Idx (ID, 1), comp (s, Shift 1))
	fun dotn 0 s = s   (* FIXME: easy optimization of dotn is possible *)
	  | dotn n s = dotn (n-1) (dot1 s)

	(* headSub : head * subst -> (head, obj) sum *)
	fun headSub (Const c, _) = INL (Const c)
	  | headSub (UCVar v, _) = INL (UCVar v)
	  | headSub (LogicVar X, s') = INL (LogicVar (X with's comp (#s X, s')))
	  | headSub (Var (M, n), Shift n') = INL (Var (M, n+n'))
	  | headSub (Var (M, 1), Dot (Idx (ID, n), s)) = INL (Var (M, n))
	  | headSub (Var (LIN, 1), Dot (Idx (INT4LIN, n), s)) = INL (Var (INT, n))
	  | headSub (Var (LIN, 1), Dot (Idx (AFF4LIN, n), s)) = INL (Var (AFF, n))
	  | headSub (Var (AFF, 1), Dot (Idx (INT4AFF, n), s)) = INL (Var (INT, n))
	  | headSub (Var (_, 1), Dot (Idx (_, n), s)) = raise Fail "Internal error: Linearity mismatch"
	  | headSub (Var (M, 1), Dot (Ob (M', N), s)) = (assertLin (M=M') ; INR N)
	  | headSub (Var (_, 1), Dot (Undef, s)) = raise ExnUndef
	  | headSub (Var (M, n), Dot (_, s)) = headSub (Var (M, n-1), s)

	(* subXX : XX * subst -> XX
	 * Perform one level of evaluation of the closure to expose a
	 * non-closure constructor.  Any arising redices are further evaluated. *)
	fun subKind (Type, _) = Type
	  | subKind (KPi (NONE, A, K), s) = KPi (NONE, TClos (A, s), KClos(K, s))
	  | subKind (KPi (SOME x, A, K), s) = KPi (SOME x, TClos (A, s), KClos(K, dot1 s))
	fun subType (TLPi (p, S, A), s) = TLPi (p, STClos (S, s), TClos (A, dotn (nbinds p) s))
	  | subType (AddProd (A, B), s) = AddProd (TClos (A, s), TClos (B, s))
	  | subType (TMonad S, s) = TMonad (STClos (S, s))
	  | subType (TAtomic (a, S), s) = TAtomic (a, TSClos (S, s))
	  | subType (ty as TAbbrev _, s) = ty
	fun subTypeSpine (TNil, _) = TNil
	  | subTypeSpine (TApp (N, S), s) = TApp (Clos (N, s), TSClos (S, s))
	fun subSyncType (LExists (p, S1, S2), s) = LExists (p, STClos (S1, s), STClos (S2, dotn (nbinds p) s))
	  | subSyncType (TOne, _) = TOne
	  | subSyncType (TDown A, s) = TDown (TClos (A, s))
	  | subSyncType (TAffi A, s) = TAffi (TClos (A, s))
	  | subSyncType (TBang A, s) = TBang (TClos (A, s))
	
	fun subObj _ (LLam (p, N), s) = LLam (p, Clos (N, dotn (nbinds p) s))
	  | subObj _ (AddPair (N1, N2), s) = AddPair (Clos (N1, s), Clos (N2, s))
	  | subObj _ (Monad E, s) = Monad (EClos (E, s))
	  | subObj redex (Atomic (H, S), s) = (case headSub (H, s) of
			  INL H' => Atomic (H', SClos (S, s))
			| INR N => redex (N, SClos (S, s)))
	  | subObj _ (Redex (N, A, S), s) = Redex (Clos (N, s), A, SClos (S, s))
	  | subObj _ (Constraint (N, A), s) = Constraint (Clos (N, s), TClos (A, s))
	fun subSpine (Nil, _) = Nil
	  | subSpine (LApp (M, S), s) = LApp (MClos (M, s), SClos (S, s))
	  | subSpine (ProjLeft S, s) = ProjLeft (SClos (S, s))
	  | subSpine (ProjRight S, s) = ProjRight (SClos (S, s))
	fun subExpObj _ (LetRedex (p, S, N, E), s) =
			LetRedex (p, S, Clos (N, s), EClos (E, dotn (nbinds p) s))
	  | subExpObj letredex (Let (p, (H, S), E), s) = (case headSub (H, s) of
			  INL H' => Let (p, (H', SClos (S, s)), EClos (E, dotn (nbinds p) s))
			| INR N => letredex (p, (N, SClos (S, s)), EClos (E, dotn (nbinds p) s)))
	  | subExpObj _ (Mon M, s) = Mon (MClos (M, s))
	fun subMonadObj (DepPair (M1, M2), s) = DepPair (MClos (M1, s), MClos (M2, s))
	  | subMonadObj (One, s) = One
	  | subMonadObj (Down N, s) = Down (Clos (N, s))
	  | subMonadObj (Affi N, s) = Affi (Clos (N, s))
	  | subMonadObj (Bang N, s) = Bang (Clos (N, s))
	  | subMonadObj (MonUndef, _) = MonUndef
	
	fun leftOf (INL l) = l
	  | leftOf (INR _) = raise Option.Option
	(**************************)

	(* lciSub: linear-changing identity substitution (sorted by index) *)
	type lciSub = (subMode * int) list

	fun coerce2s s = s  (* subtyping coercion *)
	fun coerce2p_ s = s (* subtyping coercion *)

	val id = Shift 0

	fun shiftHead (H, n) = leftOf $ headSub (H, Shift n)

	(* switchSub : int * int -> patSubst *)
	(* Invariant:
	   Let G1, G2 contexts,
	   n1 = |G1|, n2 = |G2|
	   and G1' = k-prefix of G1
	   G1, G2 |- switchSub' k : G2, G1'
	   G1, G2 |- switchSub (n1,n2) : G2, G1
	   or:
	   let {p2} = N2 in let {p1} = N1[^|p2|] in E ==
	   let {p1} = N1 in let {p2} = N2[^|p1|] in E[switchSub(|p1|,|p2|)]
	*)
	fun switchSub (n1, n2) =
		let fun switchSub' 0 = dotn n2 (Shift n1)
			  | switchSub' k = Dot (Idx (ID, n2+n1+1-k), switchSub' (k-1))
		in switchSub' n1 end

	(* invert : pat_Subst -> pat_Subst *)
	fun invert s =
		let fun lookup (_, Shift _, p) = NONE
			  | lookup (_, Dot (Ob _, _), _) =
					raise Fail "Internal error: invert called on non-pattern sub"
			  | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
			  | lookup (n, Dot (Idx (ID, k), s'), p) =
					if k = p then SOME n else lookup (n+1, s', p)
			  | lookup (_, Dot (Idx (_, _), _), _) =
					raise Fail "Internal error: invert called on non-pattern sub"
			fun invert'' (0, si) = si
			  | invert'' (p, si) =
					(case lookup (1, s, p) of
						  SOME k => invert'' (p-1, Dot (Idx (ID, k), si))
						| NONE => invert'' (p-1, Dot (Undef, si)))
			fun invert' (n, Shift p) = invert'' (p, Shift n)
			  | invert' (n, Dot (_, s')) = invert' (n+1, s')
		in invert' (0, s) end

	(* isId : subst -> bool *)
	fun isId s =
		let fun isId' n (Shift m) = (n = m)
			  | isId' n (Dot (Idx (ID, m), s)) = (n+1 = m) andalso isId' (n+1) s
			  | isId' _ _ = false
		in isId' 0 s end

	(* isWeaken : subst -> patSubst option *)
	fun isWeaken s =
		let fun isWeaken' n (Shift m) = (n <= m)
			  | isWeaken' n (Dot (Idx (ID, m), s)) = (n+1 <= m) andalso isWeaken' m s
			  | isWeaken' _ _ = false
		in if isWeaken' 0 s then SOME s else NONE end

	(* fold : (subObj * 'a -> 'a) -> (int -> 'a) -> subst -> 'a *)
	fun fold f e (Dot (ob, s)) = f (ob, fold f e s)
	  | fold f e (Shift n) = e n

	(* map : (nfObj -> nfObj) -> subst -> subst *)
	fun map f (Dot (Ob (M, ob), s)) = Dot (Ob (M, f ob) handle ExnUndef => Undef, map f s)
	  | map f (Dot (Undef, s)) = Dot (Undef, map f s)
	  | map f (Dot (Idx n, s)) = Dot (Idx n, map f s)
	  | map f (Shift n) = Shift n

	(* hdDef : pat_Subst -> bool *)
	fun hdDef (Dot (Undef, _)) = false
	  | hdDef (Dot (Ob _, _)) = raise Fail "Internal error: hdDef: not patSub"
	  | hdDef (Dot (Idx _, _)) = true
	  | hdDef (Shift _) = true

	(* substToStr : (nfObj -> string) -> subst -> string *)
	fun substToStr f s = if isId s then "" else
			let fun m2s LIN = "L"
				  | m2s AFF = "@"
				  | m2s INT = "!"
				fun cm2s ID = ""
				  | cm2s INT4LIN = "!/L"
				  | cm2s INT4AFF = "!/@"
				  | cm2s AFF4LIN = "@/L"
				fun toStr (Dot (Undef, s)) = "_."^(toStr s)
				  | toStr (Dot (Ob (M, ob), s)) =
						(f ob handle ExnUndef => "_")^"/"^(m2s M)^"."^(toStr s)
				  | toStr (Dot (Idx (M, n), s)) = (Int.toString n)^(cm2s M)^"."^(toStr s)
				  | toStr (Shift n) = "^"^(Int.toString n)
			in "["^(toStr s)^"]" end

	(* intersect : pat_Subst -> patSubst *)
	(* intersect s = w
	 * given pattern (with undefs) G |- s : G
	 * w o s o w^-1 is a permutation *)
	fun intersect s =
		let val w = fold (fn (Undef, w) => comp (w, Shift 1) | (_, w) => dot1 w)
					(fn _ => id) s
		in if isId w then id else comp (intersect (comp (w, comp (s, invert w))), w) end

	(* intersection : ((Context.mode * int, nfObj) sum * nfObj -> bool)
			-> subst * subst -> patSubst *)
	(* Input:
	   G1 |- s1 : G2  and  G1 |- s2 : G2
	   Output:
	   G2 |- w : G3   w weakening substitution
	   Constructs a subcontext G3 of G2 consisting of the parts of G2
	   on which s1 and s2 agrees.
	*)
	fun intersection conv s1s2 =
		let fun modeMult ID m = m
			  | modeMult INT4LIN LIN = INT
			  | modeMult INT4AFF AFF = INT
			  | modeMult AFF4LIN LIN = AFF
			  | modeMult _ _ = raise Fail "Internal error: Linearity mismatch in intersection"
			fun eq (Idx (M1, n), Idx (M2, m)) = (assertLin (M1=M2 orelse n<>m) ; n=m)
			  | eq (Idx (m, n), Ob (M, N)) =
					(conv (INL (modeMult m M, n), N) handle ExnUndef => false)
			  | eq (N1 as Ob _, N2 as Idx _) = eq (N2, N1)
			  | eq (Ob (M1, N1), Ob (M2, N2)) =
					( assertLin (M1=M2) ; conv (INR N1, N2) handle ExnUndef => false )
			  | eq (Undef, _) = false
			  | eq (_, Undef) = false
			fun intersect (Dot (n1, s1), Dot (n2, s2)) =
					if eq (n1, n2) then dot1 (intersect (s1, s2))
					else comp (intersect (s1, s2), Shift 1)
			  | intersect (s1 as Dot _, Shift n) =
			  		intersect (s1, Dot (Idx (ID, n+1), Shift (n+1)))
			  | intersect (Shift n, s2 as Dot _) =
			  		intersect (Dot (Idx (ID, n+1), Shift (n+1)), s2)
			  | intersect (Shift n1, Shift n2) =
					if n1=n2 then id else raise Fail "Internal error: intersection"
		in intersect s1s2 end

	(* qsort2 : ('a * int) list -> ('a * int) list    e.g.: lciSub(unsorted) -> lciSub *)
	fun qsort2 l =
		let fun qsort' [] a = a
			  | qsort' (x::xs) a =
					let val (l, g) = List.partition (fn (_, y) => y < #2 x) xs
					in qsort' l (x :: qsort' g a) end
			fun sorted ((_, x1)::x2::xs) = x1 <= #2 x2 andalso sorted (x2::xs)
			  | sorted _ = true
		in if sorted l then l else qsort' l [] end

	(* modeDiv : Context.mode * Context.mode -> subMode *)
	(* modeDiv combines two flags to the combined representation
	 * modeDiv f1 f2
	 *  f1 : flag on variable
	 *  f2 : flag on substitution extension *)
	fun modeDiv INT INT = ID (* modeDiv is also used in Syntax.sml *)
	  | modeDiv INT AFF = INT4AFF
	  | modeDiv INT LIN = INT4LIN
	  | modeDiv AFF INT = raise Fail "Internal error: Linearity mismatch patSub"
	  | modeDiv AFF AFF = ID
	  | modeDiv AFF LIN = AFF4LIN
	  | modeDiv LIN INT = raise Fail "Internal error: Linearity mismatch patSub"
	  | modeDiv LIN AFF = raise Fail "Internal error: Linearity mismatch patSub"
	  | modeDiv LIN LIN = ID
	fun modeInvDiv m1 m2 = modeDiv m2 m1

	(* patSub : (nfObj -> nfObj * bool) -> (exn -> nfObj -> Context.mode * int) ->
			subst -> (lciSub * pat_Subst) option *)
	(*
	 * patSub Unify.checkExistObj Eta.etaContract s (G1)
	 *    where G |- s : G1 can give three different results:
	 * NONE
	 *    s is not a pattern sub
	 * SOME ([], s')
	 *    s is equal to s' which is a pattern sub
	 * SOME (p, s')
	 *    s is equal (modulo flags) to s' which is a pattern sub, but
	 *    G  |- s : G1
	 *    G' |- s' : G1
	 *    s = s' o lcis2sub p
	 *    G equals G' on the indices not in p
	 *    (INT4LIN, n) in p => G_n is INT and G'_n is LIN
	 *    (INT4AFF, n) in p => G_n is INT and G'_n is AFF
	 *    (AFF4LIN, n) in p => G_n is AFF and G'_n is LIN
	 *)
	fun patSub checkExists etaContract s' =
		let exception ExnPatSub
			fun etaContr N = case checkExists N of
				  (_, false) => raise ExnPatSub
				| (N', true) => etaContract ExnPatSub N'
			val p = ref []
			fun add (n : int, l) = if List.exists (fn i => i=n) l then raise ExnPatSub else n::l
			fun ps (m, _, s as Shift n) = if m <= n then s else raise ExnPatSub
			  | ps (m, l, Dot (Undef, s)) = Dot (Undef, ps (m, l, s))
			  | ps (m, l, Dot (Idx (ID, n), s)) =
					Dot (Idx (ID, n), ps (Int.max (m, n), add (n, l), s))
			  | ps (m, l, Dot (Idx (M, n), s)) =
					( p := (M, n) :: !p
					; ps (m, l, Dot (Idx (ID, n), s)) )
			  | ps (m, l, Dot (Ob (M, N), s)) =
					let val N' = Idx (map1 (modeInvDiv M) $ etaContr N)
								handle ExnUndef => Undef
					in ps (m, l, Dot (N', s)) end
		in SOME $ (fn s => (qsort2 (!p), s)) $ ps (0, [], s') handle ExnPatSub => NONE end

	(* lcisComp : lciSub * pat_Subst -> lciSub *)
	(* Composition for lciSubs; undefs are removed.  Satisfies the following:
	 * (lcis2sub p) o s  ==  s o (lcis2sub (lcisComp (p, s)))  and
	 * s o (lcis2sub p)  ==  (lcis2sub (lcisComp (p, invert s))) o s
	 *)
	fun lcisComp (p, s) =
		let fun f (M, n, Shift m) =
				if n>=1 then SOME (M, n+m) else raise Fail "Internal error: lcisComp: not patsub"
			  | f (M, 1, Dot (Idx (ID, m), _)) = SOME (M, m)
			  | f (M, 1, Dot (Undef, _)) = NONE
			  | f (M, n, Dot (_, s)) = f (M, n-1, s)
		in qsort2 $ List.mapPartial (fn (M, n) => f (M, n, s)) p end

	(* lcis2x : conversion of lciSubs to substitutions parameterized by the action
	 * on the linear changing extensions.  The resulting substitution is the
	 * identity on all variables except the given. *)
	fun lcis2x f (n, p1 as (x, k)::p) =
			if n=k then Dot (f (x, k), lcis2x f (n+1, p))
			else if n<k then Dot (Idx (ID, n), lcis2x f (n+1, p1))
			else raise Fail "Internal error: lcis2x: not sorted"
	  | lcis2x f (n, []) = Shift (n-1)

	(* lcis2sub : lciSub -> subst *)
	(* representation conversion from list form to substitution *)
	fun lcis2sub p = lcis2x Idx (1, p)

	(* pruningsub : ('a * int) list -> pat_Subst   e.g.: lciSub -> pat_Subst *)
	(* build a pruning substitution that prunes all the given indices *)
	fun pruningsub p = lcis2x (fn _ => Undef) (1, p)

	(* lcisDiff : lciSub * lciSub -> lciSub *)
	(* lcisDiff (p, p') = p-p' such that
	 * lcis2sub(p) = lcis2sub(p') o lcis2sub(p-p') *)
	fun lcisDiff (p, []) = p
	  | lcisDiff ([], _::_) = raise Fail "Internal error: lcisDiff 1"
	  | lcisDiff ((m, n : int)::p, (m', n')::p') =
			if n = n' then case (m, m') of
				  (INT4LIN, INT4LIN) => lcisDiff (p, p')
				| (INT4AFF, INT4AFF) => lcisDiff (p, p')
				| (AFF4LIN, AFF4LIN) => lcisDiff (p, p')
				| (INT4LIN, AFF4LIN) => (INT4AFF, n) :: lcisDiff (p, p')
				| _ => raise Fail "Internal error: lcisDiff 2"
			else (m, n) :: lcisDiff (p, (m', n')::p')

	(* subPrj : subst -> (subObj * subst, int) sum *)
	fun subPrj (Dot (N, s)) = INL (N, s)
	  | subPrj (Shift n) = INR n

	fun shift n = Shift n
end
