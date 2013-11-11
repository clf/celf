signature TLU_InternalSubst = TOP_LEVEL_UTIL
structure InternalSubst :> INTERNAL_SUBST =
struct

open InternalSyntax

(* etaContract : exn -> nfObj -> modality * int *)
(* assumes that ob does not contain _
 * etaContract e ob = (m, n)
 * ob == Var (m, n)
 * or raise e if ob is not an eta-expanded var *)
fun etaContract e ob =
    let
      datatype etaSpine = LAp of objPattern | Pl | Pr
      fun nbindsSp sp = foldl (fn (LAp p, n) => n + numBinds p
                              | (_, n) => n) 0 sp
      fun eq ((x : modality * int), y) = if x=y then x else raise e
      fun etaEqC (ob, x) = ignore (eq (etaC' (ob, []), x))
      and etaC' (ob, sp) =
          case ob of
	      LLam (p, N) => etaC' (N, (LAp p)::sp)
	    | AddPair (N1, N2) =>
	      eq (etaC' (N1, Pl::sp), etaC' (N2, Pr::sp))
	    | Monad E => raise Fail "Internal error: etaContract Monad"
	      (* (case Util.NfExpObjAuxDefs.prj2 E of *)
	      (*      NfLet (p, N, NfMon M) => *)
	      (*      (etaP (numBinds p, p, M); etaC (NfAtomic' N, sp)) *)
	      (*    | _ => raise e) *)
	    | Atomic (Var (M, n), S) =>
	      let
                val nb = nbindsSp sp
		val k = n - nb
		val () = if k>0 then () else raise e
		val () = etaSp (nb, S, rev sp)
	      in
                (M, k)
              end
	    | _ => raise e
      and etaP (n, p, m) =
          case (p, m) of
	      (PDepTensor (p1, p2), DepPair (M1, M2)) =>
	      (etaP (n, p1, M1); etaP (n - numBinds p1, p2, M2))
	    | (POne, One) => ()
	    | (PDown _, Down N) => etaEqC (N, (LIN, n))
	    | (PAffi _, Affi N) => etaEqC (N, (AFF, n))
	    | (PBang _, Bang N) => etaEqC (N, (INT, n))
	    | _ => raise e
      and etaSp (m, Sp, sp) =
          case (Sp, sp) of
	      (Nil, []) => ()
	    | (LApp (M, S), (LAp p)::sp) =>
	      (etaSp (m - numBinds p, S, sp); etaP (m, p, M))
	    | (ProjLeft S, Pl::sp) => etaSp (m, S, sp)
	    | (ProjRight S, Pr::sp) => etaSp (m, S, sp)
	    | _ => raise e
    in
      etaC' (ob, [])
    end

(* Substitutions *)

fun fold f e (Dot (ob, s)) = f (ob, fold f e s)
  | fold f e (Shift n) = e n

(* map : (nfObj -> nfObj) -> subst -> subst *)
fun map f (Dot (Ob (M, ob), s)) = Dot (Ob (M, f ob) handle ExnUndef => Undef, map f s)
  | map f (Dot (Undef, s)) = Dot (Undef, map f s)
  | map f (Dot (Idx n, s)) = Dot (Idx n, map f s)
  | map f (Shift n) = Shift n


fun mkSubstMonad (DepPair (M1, M2), s) = mkSubstMonad (M2, mkSubstMonad (M1, s))
  | mkSubstMonad (One, s) = s
  | mkSubstMonad (Down N, s) = Dot (Ob (LIN, N), s)
  | mkSubstMonad (Affi N, s) = Dot (Ob (AFF, N), s)
  | mkSubstMonad (Bang N, s) = Dot (Ob (INT, N), s)
  | mkSubstMonad (MonUndef, s) = Dot (Undef, s)


fun leftOf (INL l) = l
  | leftOf (INR _) = raise Option.Option

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

(* Undefs in substitutions are represented explicitly, but outside
 * substitutions they are represented as a raised ExnUndef.  This
 * ensures automatic propagation up to the nearest handler. *)
exception ExnUndef

fun dot1 s = Dot (Idx (ID, 1), comp (s, Shift 1))
and dotn 0 s = s   (* FIXME: easy optimization of dotn is possible *)
  | dotn n s = dotn (n-1) (dot1 s)

(* substHead : head * spine * subst -> (head, obj) sum *)
and substHead (Const c, s) = Atomic (Const c, Nil)
  | substHead (UCVar v, s) = Atomic (UCVar v, Nil)
  | substHead (LogicVar X, s') =
    Atomic (LogicVar (updS X (comp (#s X, s'))), Nil)
  | substHead (Var (M, n), Shift n') = Atomic (Var (M, n+n'), Nil)
  | substHead (Var (M, 1), Dot (Idx (ID, n), s)) = Atomic (Var (M, n), Nil)
  | substHead (Var (LIN, 1), Dot (Idx (INT4LIN, n), s)) = Atomic (Var (INT, n), Nil)
  | substHead (Var (LIN, 1), Dot (Idx (AFF4LIN, n), s)) = Atomic (Var (AFF, n), Nil)
  | substHead (Var (AFF, 1), Dot (Idx (INT4AFF, n), s)) = Atomic (Var (INT, n), Nil)
  | substHead (Var (_, 1), Dot (Idx (_, n), s)) =
    raise Fail "Internal error: Linearity mismatch"
  | substHead (Var (M, 1), Dot (Ob (M', N), s)) = N
  | substHead (Var (_, 1), Dot (Undef, s)) = raise ExnUndef
  | substHead (Var (M, n), Dot (N, s)) = substHead (Var (M, n-1), s)

(* val reduceObj : object * spine -> object *)
and reduceObj (obj, Nil) = obj
  | reduceObj (LLam (_, obj), LApp (mon, sp)) =
    reduceObj (substObj (obj, mkSubstMonad (mon, idSubst)), sp)
  | reduceObj (AddPair (obj, _), ProjLeft sp) = reduceObj (obj, sp)
  | reduceObj (AddPair (_, obj), ProjRight sp) = reduceObj (obj, sp)
  | reduceObj (Atomic (h, sp1), sp2) = Atomic (h, spineApp (sp1, sp2))
  | reduceObj _ = raise Fail "Internal error: ill-typed reduceObj"



and normalizeObj (LLam (p, ob)) = LLam (p, normalizeObj ob)
  | normalizeObj (AddPair (ob1, ob2)) = AddPair (normalizeObj ob1, normalizeObj ob2)
  | normalizeObj (Monad m) = Monad (normalizeExpObj m)
  | normalizeObj (Atomic (h, sp)) =
    ( case h of
          LogicVar {X, s, ...} =>
          ( case !!X of
                SOME ob' => reduceObj (normalizeObj (substObj (ob', s)), normalizeSpine sp)
              | NONE => Atomic (h, normalizeSpine sp)
          )
        | _ => Atomic (h, normalizeSpine sp)
    )
  | normalizeObj (Clo (ob, s)) = normalizeObj (substObj (ob, s))

and normalizeSpine Nil = Nil
  | normalizeSpine (LApp (m, sp)) = LApp (normalizeMonadObj m, normalizeSpine sp)
  | normalizeSpine (ProjLeft sp) = ProjLeft (normalizeSpine sp)
  | normalizeSpine (ProjRight sp) = ProjRight (normalizeSpine sp)
  | normalizeSpine (SClo (S, s)) = normalizeSpine (substSpine (S, s))

and normalizeExpObj (Let (eps, m)) = Let (eps, m) (* TODO *)

and normalizeMonadObj (DepPair (m1, m2)) = DepPair (normalizeMonadObj m1, normalizeMonadObj m2)
  | normalizeMonadObj One = One
  | normalizeMonadObj (Down ob) = Down (normalizeObj ob)
  | normalizeMonadObj (Affi ob) = Affi (normalizeObj ob)
  | normalizeMonadObj (Bang ob) = Bang (normalizeObj ob)
  | normalizeMonadObj MonUndef = MonUndef

(* val spineApp : spine * spine -> spine *)
and spineApp (Nil, sp) = sp
  | spineApp (LApp (mon, sp1), sp2) = LApp (mon, spineApp (sp1, sp2))
  | spineApp (ProjLeft sp1, sp2) = ProjLeft (spineApp (sp1, sp2))
  | spineApp (ProjRight sp1, sp2) = ProjRight (spineApp (sp1, sp2))
  | spineApp (SClo (S, s), sp) = spineApp (substSpine (S, s), sp)


and whnfObj (ob as LLam _) = ob
  | whnfObj (ob as AddPair _) = ob
  | whnfObj (ob as Monad _) = ob
  | whnfObj (ob as Atomic (h, sp)) = whnfAtomic (h, sp)
  | whnfObj (Clo (ob, s)) = substObj (ob, s)

and whnfAtomic (h as LogicVar {X, s, ...}, sp) =
    ( case !!X of
          SOME ob => whnfObj (reduceObj (substObj (ob, s), sp))
        | NONE => Atomic (h, sp)
    )
  | whnfAtomic (h, sp) = Atomic (h, sp)


(* subXX : XX * subst -> XX
 * Perform one level of evaluation of the closure to expose a
 * non-closure constructor.  Any arising redices are further evaluated. *)
and substKind (Type, _) = Type
  | substKind (KPi (NONE, A, K), s) = KPi (NONE, substType (A, s), substKind (K, s))
  | substKind (KPi (SOME x, A, K), s) = KPi (SOME x, substType (A, s), substKind (K, dot1 s))

and substType (TLPi (p, S, A), s) = TLPi (p, substSyncType (S, s), substType (A, dotn (numBinds p) s))
  | substType (AddProd (A, B), s) = AddProd (substType (A, s), substType (B, s))
  | substType (TMonad S, s) = TMonad (substSyncType (S, s))
  | substType (TAtomic (a, S), s) = TAtomic (a, substTypeSpine (S, s))

and substTypeSpine (TNil, _) = TNil
  | substTypeSpine (TApp (N, S), s) = TApp (substObj (N, s), substTypeSpine (S, s))

and substSyncType (LExists (p, S1, S2), s) = LExists (p, substSyncType (S1, s), substSyncType (S2, dotn (numBinds p) s))
  | substSyncType (TOne, _) = TOne
  | substSyncType (TDown A, s) = TDown (substType (A, s))
  | substSyncType (TAffi A, s) = TAffi (substType (A, s))
  | substSyncType (TBang A, s) = TBang (substType (A, s))

and substObj (LLam (p, N), s) =
    LLam (p, Clo (N, dotn (numBinds p) s))
  | substObj (AddPair (N1, N2), s) =
    (AddPair (Clo (N1, s), Clo (N2, s)))
  | substObj (Monad E, s) = Monad (substExpObj (E, s))
  | substObj (Atomic (H, S), s) =
    reduceObj (substHead (H, s), substSpine (S, s))
  | substObj (Clo (ob, s'), s) = substObj (ob, (comp (s', s)))

and substSpine (Nil, _) = Nil
  | substSpine (LApp (M, S), s) = LApp (subMonadObj (M, s), substSpine (S, s))
  | substSpine (ProjLeft S, s) = ProjLeft (substSpine (S, s))
  | substSpine (ProjRight S, s) = ProjRight (substSpine (S, s))
  | substSpine (SClo (S, s'), s) = substSpine (S, comp (s', s))

(* TODO: implement this function *)
and substExpObj (Let (eps, mon), s) = raise Fail "Internal error: substExpObj not implemented"

and subMonadObj (DepPair (M1, M2), s) = DepPair (subMonadObj (M1, s), subMonadObj (M2, s))
  | subMonadObj (One, s) = One
  | subMonadObj (Down N, s) = Down (substObj (N, s))
  | subMonadObj (Affi N, s) = Affi (substObj (N, s))
  | subMonadObj (Bang N, s) = Bang (substObj (N, s))
  | subMonadObj (MonUndef, s) = MonUndef

(**************************)


and Clos' (Ob (m, N), t) = Ob (m, substObj (N, t))
  | Clos' (Idx (M, n), Shift n') = Idx (M, n+n')
  | Clos' (Idx (M, 1), Dot (N, _)) = domMult M N
  | Clos' (Idx (M, n), Dot (_, t)) = Clos' (Idx (M, n-1), t)
  | Clos' (Undef, _) = Undef

(* comp : subst * subst -> subst *)
and comp (Shift 0, s) = s
  | comp (s, Shift 0) = s
  | comp (Shift n, Dot (N, s)) = comp (Shift (n-1), s)
  | comp (Shift n, Shift m) = Shift (n+m)
  | comp (Dot (N, s), s') = Dot (Clos' (N, s'), comp (s, s'))



(* lciSub: linear-changing identity substitution (sorted by index) *)
type lciSub = (subModality * int) list

fun coerce2s s = s  (* subtyping coercion *)
fun coerce2p_ s = s (* subtyping coercion *)

(* fun shiftHead (H, n) = leftOf $ substHead (H, Shift n) *)

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
		     (fn _ => idSubst) s
    in if isId w then idSubst else comp (intersect (comp (w, comp (s, invert w))), w) end

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
	    if n1=n2 then idSubst else raise Fail "Internal error: intersection"
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

(* modeDiv : Context.mode * Context.mode -> subModality *)
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
fun patternSubst checkExists etaContract s' =
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
	    let
              val N' = Idx (map1 (modeInvDiv M) $ etaContr (normalizeObj N))
		       handle ExnUndef => Undef
              (* val () = print "patternSubst Ob " *)
              (* val () = print (Int.toString (#2 (map1 (modeInvDiv M) $ etaContr (normalizeObj N))) *)
              (*                 handle ExnUndef => "Undef") *)
              (* val () = print "\n" *)
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


fun normalizeType (TLPi (p, sty, ty)) = TLPi (p, normalizeSyncType sty, normalizeType ty)
  | normalizeType (AddProd (ty1, ty2)) = AddProd (normalizeType ty1, normalizeType ty2)
  | normalizeType (TMonad sty) = TMonad (normalizeSyncType sty)
  | normalizeType (TAtomic (x, sp)) = TAtomic (x, normalizeTypeSpine sp)

and normalizeSyncType (LExists (p, sty1, sty2)) = LExists (p, normalizeSyncType sty1, normalizeSyncType sty2)
  | normalizeSyncType TOne = TOne
  | normalizeSyncType (TDown ty) = TDown (normalizeType ty)
  | normalizeSyncType (TAffi ty) = TAffi (normalizeType ty)
  | normalizeSyncType (TBang ty) = TBang (normalizeType ty)

and normalizeTypeSpine TNil = TNil
  | normalizeTypeSpine (TApp (ob, sp)) = TApp (normalizeObj ob, normalizeTypeSpine sp)


end
