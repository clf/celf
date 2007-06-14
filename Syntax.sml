structure Syntax :> SYNTAX =
struct

datatype kind = FixKind of kind kindF | KClos of kind * subst
and asyncType = FixAsyncType of asyncType asyncTypeF | TClos of asyncType * subst
	| TLogicVar of asyncType option ref
and typeSpine = FixTypeSpine of typeSpine typeSpineF | TSClos of typeSpine * subst
and syncType = FixSyncType of syncType syncTypeF | STClos of syncType * subst

and obj = FixObj of obj objF | Clos of obj * subst | EtaTag of obj * int
and spine = FixSpine of spine spineF | SClos of spine * subst
and expObj = FixExpObj of expObj expObjF | EClos of expObj * subst
and monadObj = FixMonadObj of monadObj monadObjF | MClos of monadObj * subst
and pattern = FixPattern of pattern patternF * int | PClos of pattern * subst

and subst = Dot of subObj * subst | Shift of int
and subObj = Ob of obj | Idx of int | Undef

and constr = Solved | Eqn of obj * obj
and head = Const of string * obj list
	| Var of int
	| UCVar of string
	| LogicVar of obj option ref * asyncType * subst
			* asyncType Context.context option ref * constr ref list ref * int


and 'ki kindF = Type
	| KPi of string * asyncType * 'ki
and 'aTy asyncTypeF = Lolli of 'aTy * 'aTy
	| TPi of string * 'aTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| Top
	| TMonad of syncType
	| TAtomic of string * obj list * typeSpine
	| TAbbrev of string * 'aTy
	| TUnknown
and 'tyS typeSpineF = TNil
	| TApp of obj * 'tyS
and 'sTy syncTypeF = TTensor of 'sTy * 'sTy
	| TOne
	| Exists of string * asyncType * 'sTy
	| Async of asyncType
and 'o objF = LinLam of string * 'o
	| Lam of string * 'o
	| AddPair of 'o * 'o
	| Unit
	| Monad of expObj
	| Atomic of head * (*apx*)asyncType * spine
	| Redex of 'o * (*apx*)asyncType * spine
	| Constraint of 'o * asyncType
and 'sp spineF = Nil
	| App of obj * 'sp
	| LinApp of obj * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
and 'e expObjF = Let of pattern * obj * 'e
	| Mon of monadObj
and 'm monadObjF = Tensor of 'm * 'm
	| One
	| DepPair of obj * 'm
	| Norm of obj
and 'p patternF = PTensor of 'p * 'p
	| POne
	| PDepPair of string * asyncType * 'p
	| PVar of string * asyncType

type implicits = (string * asyncType) list
datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * implicits * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj

type apxKind = kind
type apxAsyncType = asyncType
type apxSyncType = syncType

type typeLogicVar = asyncType option ref

datatype 'ki apxKindF = ApxType
	| ApxKPi of apxAsyncType * 'ki
datatype 'aTy apxAsyncTypeF = ApxLolli of 'aTy * 'aTy
	| ApxTPi of 'aTy * 'aTy
	| ApxAddProd of 'aTy * 'aTy
	| ApxTop
	| ApxTMonad of apxSyncType
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype 'sTy apxSyncTypeF = ApxTTensor of 'sTy * 'sTy
	| ApxTOne
	| ApxExists of apxAsyncType * 'sTy
	| ApxAsync of apxAsyncType


fun nbinds (FixPattern (_, n)) = n
  | nbinds (PClos (p, _)) = nbinds p

structure Subst =
struct
	open Either
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
	fun headSub (Const (c, impl), s) = LEFT (Const (c, map (fn x => Clos (x, s)) impl))
	  | headSub (UCVar v, _) = LEFT (UCVar v)
	  | headSub (LogicVar (X, A, s, ctx, cs, l), s') =
					LEFT (LogicVar (X, A, comp (s, s'), ctx, cs, l))
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
	  | subType (TAtomic (a, impl, S), s) =
				TAtomic (a, map (fn N => Clos (N, s)) impl, TSClos (S, s))
	  | subType (ty as TAbbrev _, s) = ty
	  | subType (TUnknown, _) = raise Fail "Internal error: injected TUnknown\n"
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
	
	val dummytype = FixAsyncType TUnknown
	fun dummyvar n = FixObj (Atomic (Var n, dummytype, FixSpine Nil))
	val dummy = Clos (dummyvar 1, Dot (Undef, Shift 0))
	(**************************)

	val id = Shift 0

	fun dot (EtaTag (_, n), s) = Dot (Idx n, s)
	  | dot (Clos (Clos (N, s'), s''), s) = dot (Clos (N, comp (s', s'')), s)
	  | dot (Clos (EtaTag (_, n), s'), s) = Dot (Clos' (Idx n, s'), s)
	  | dot (ob, s) = Dot (Ob ob, s)

	fun sub ob = dot (ob, id)

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

	fun fold f e (Dot (Undef, s)) = f (dummy, fold f e s)
	  | fold f e (Dot (Ob ob, s)) = f (ob, fold f e s)
	  | fold f e (Dot (Idx n, s)) = f (dummyvar n, fold f e s)
	  | fold f e (Shift n) = e n
	
	fun hdDef (Dot (Undef, _)) = false
	  | hdDef (Dot (Ob _, _)) = raise Fail "Internal error firstDefined: not patSub\n"
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

fun etaShortcut ob = case Subst.sub ob of Dot (Idx n, _) => SOME n | _ => NONE


(* structure Kind : TYP where type 'a F = 'a kindF and type t = kind *)
structure Kind =
struct
	type t = kind
	type 'a F = 'a kindF
	fun inj k = FixKind k
	fun prj (FixKind k) = k
	  | prj (KClos (KClos (k, s'), s)) = prj (KClos (k, Subst.comp (s', s)))
	  | prj (KClos (FixKind k, s)) = Subst.subKind (k, s)
	fun Fmap f Type = Type
	  | Fmap f (KPi (x, A, K)) = KPi (x, A, f K)
end
(* structure AsyncType : TYP where type 'a F = 'a asyncTypeF and type t = asyncType *)
structure AsyncType =
struct
	type t = asyncType
	type 'a F = 'a asyncTypeF
	fun inj TUnknown = raise Fail "Cannot inject unknown type"
	  | inj a = FixAsyncType a
	fun prj (FixAsyncType a) = a
	  | prj (TClos (TClos (a, s'), s)) = prj (TClos (a, Subst.comp (s', s)))
	  | prj (TClos (FixAsyncType a, s)) = Subst.subType (a, s)
	  | prj (TClos (TLogicVar (ref NONE), _)) = raise Fail "Ambiguous typing\n"
	  | prj (TClos (TLogicVar (ref (SOME a)), s)) = prj (TClos (a, s))
(*	  | prj (TClos (TAbbrev (_, a), s)) = prj (TClos (a, s))*)
	  | prj (TLogicVar (ref NONE)) = TUnknown
	  | prj (TLogicVar (ref (SOME a))) = prj a
(*	  | prj (TAbbrev (_, a)) = prj a*)
	fun Fmap f (Lolli (A, B)) = Lolli (f A, f B)
	  | Fmap f (TPi (x, A, B)) = TPi (x, f A, f B)
	  | Fmap f (AddProd (A, B)) = AddProd (f A, f B)
	  | Fmap f Top = Top
	  | Fmap f (TMonad S) = TMonad S
	  | Fmap f (TAtomic aImplTS) = TAtomic aImplTS
	  | Fmap f (TAbbrev (a, A)) = TAbbrev (a, f A)
	  | Fmap f TUnknown = TUnknown
end
(* structure TypeSpine : TYP where type 'a F = 'a typeSpineF and type t = typeSpine *)
structure TypeSpine =
struct
	type t = typeSpine
	type 'a F = 'a typeSpineF
	fun inj a = FixTypeSpine a
	fun prj (FixTypeSpine a) = a
	  | prj (TSClos (TSClos (S, s'), s)) = prj (TSClos (S, Subst.comp (s', s)))
	  | prj (TSClos (FixTypeSpine S, s)) = Subst.subTypeSpine (S, s)
	fun Fmap f TNil = TNil
	  | Fmap f (TApp (N, S)) = TApp (N, f S)
end
(* structure SyncType : TYP where type 'a F = 'a syncTypeF and type t = syncType *)
structure SyncType =
struct
	type t = syncType
	type 'a F = 'a syncTypeF
	fun inj a = FixSyncType a
	fun prj (FixSyncType a) = a
	  | prj (STClos (STClos (S, s'), s)) = prj (STClos (S, Subst.comp (s', s)))
	  | prj (STClos (FixSyncType S, s)) = Subst.subSyncType (S, s)
	fun Fmap f (TTensor (S1, S2)) = TTensor (f S1, f S2)
	  | Fmap f TOne = TOne
	  | Fmap f (Exists (x, A, S)) = Exists (x, A, f S)
	  | Fmap f (Async A) = Async A
end

(* structure Obj : TYP where type 'a F = 'a objF and type t = obj *)
structure Obj =
struct
	fun tryLVar (Atomic (LogicVar (ref (SOME N), _, s, _, _, _), A, S)) = Redex (Clos (N, s), A, S)
	  | tryLVar a = a
	type t = obj
	type 'a F = 'a objF
	(*fun inj (Redex (N, _, FixSpine Nil)) = N
	  | inj a = FixObj a*) (* optimization? *)
	fun inj a = FixObj a
	fun prj (FixObj a) = tryLVar a
	  | prj (Clos (Clos (N, s'), s)) = prj (Clos (N, Subst.comp (s', s)))
	  | prj (Clos (FixObj N, s)) = Subst.subObj (tryLVar N, s)
	  | prj (Clos (EtaTag (N, _), s)) = prj (Clos (N, s))
	  | prj (EtaTag (N, _)) = prj N
	fun Fmap f (LinLam (x, N)) = (LinLam (x, f N))
	  | Fmap f (Lam (x, N)) = (Lam (x, f N))
	  | Fmap f (AddPair (N1, N2)) = (AddPair (f N1, f N2))
	  | Fmap f Unit = Unit
	  | Fmap f (Monad E) = Monad E
	  | Fmap f (Atomic at) = Atomic at
	  | Fmap f (Redex (N, A, S)) = Redex (f N, A, S)
	  | Fmap f (Constraint (N, A)) = Constraint (f N, A)
end
(* structure Spine : TYP where type 'a F = 'a spineF and type t = spine *)
structure Spine =
struct
	type t = spine
	type 'a F = 'a spineF
	fun inj a = FixSpine a
	fun prj (FixSpine a) = a
	  | prj (SClos (SClos (S, s'), s)) = prj (SClos (S, Subst.comp (s', s)))
	  | prj (SClos (FixSpine S, s)) = Subst.subSpine (S, s)
	fun Fmap f Nil = Nil
	  | Fmap f (App (N, S)) = App (N, f S)
	  | Fmap f (LinApp (N, S)) = LinApp (N, f S)
	  | Fmap f (ProjLeft S) = ProjLeft (f S)
	  | Fmap f (ProjRight S) = ProjRight (f S)
end
(* structure ExpObj : TYP where type 'a F = 'a expObjF and type t = expObj *)
structure ExpObj =
struct
	type t = expObj
	type 'a F = 'a expObjF
	fun inj a = FixExpObj a
	fun prj (FixExpObj a) = a
	  | prj (EClos (EClos (E, s'), s)) = prj (EClos (E, Subst.comp (s', s)))
	  | prj (EClos (FixExpObj E, s)) = Subst.subExpObj (E, s)
	fun Fmap f (Let (p, N, E)) = Let (p, N, f E)
	  | Fmap f (Mon M) = Mon M
end
(* structure MonadObj : TYP where type 'a F = 'a monadObjF and type t = monadObj *)
structure MonadObj =
struct
	type t = monadObj
	type 'a F = 'a monadObjF
	fun inj a = FixMonadObj a
	fun prj (FixMonadObj a) = a
	  | prj (MClos (MClos (M, s'), s)) = prj (MClos (M, Subst.comp (s', s)))
	  | prj (MClos (FixMonadObj M, s)) = Subst.subMonadObj (M, s)
	fun Fmap f (Tensor (M1, M2)) = Tensor (f M1, f M2)
	  | Fmap f One = One
	  | Fmap f (DepPair (N, M)) = DepPair (N, f M)
	  | Fmap f (Norm N) = Norm N
end
(* structure Pattern : TYP where type 'a F = 'a patternF and type t = pattern *)
structure Pattern =
struct
	type t = pattern
	type 'a F = 'a patternF
	fun pbinds (PTensor (p1, p2)) = nbinds p1 + nbinds p2
	  | pbinds POne = 0
	  | pbinds (PDepPair (_, _, p)) = 1 + nbinds p
	  | pbinds (PVar _) = 1
	fun inj a = FixPattern (a, pbinds a)
	fun prj (FixPattern (a, _)) = a
	  | prj (PClos (PClos (p, s'), s)) = prj (PClos (p, Subst.comp (s', s)))
	  | prj (PClos (FixPattern (p, _), s)) = Subst.subPattern (p, s)
	fun Fmap f (PTensor (p1, p2)) = PTensor (f p1, f p2)
	  | Fmap f POne = POne
	  | Fmap f (PDepPair (x, A, p)) = PDepPair (x, A, f p)
	  | Fmap f (PVar (x, A)) = PVar (x, A)
end

val Type' = Kind.inj Type
val KPi' = Kind.inj o KPi
val Lolli' = AsyncType.inj o Lolli
val TPi' = AsyncType.inj o TPi
val AddProd' = AsyncType.inj o AddProd
val Top' = AsyncType.inj Top
val TMonad' = AsyncType.inj o TMonad
val TAtomic' = AsyncType.inj o TAtomic
val TAbbrev' = AsyncType.inj o TAbbrev
val TNil' = TypeSpine.inj TNil
val TApp' = TypeSpine.inj o TApp
val TTensor' = SyncType.inj o TTensor
val TOne' = SyncType.inj TOne
val Exists' = SyncType.inj o Exists
val Async' = SyncType.inj o Async
val LinLam' = Obj.inj o LinLam
val Lam' = Obj.inj o Lam
val AddPair' = Obj.inj o AddPair
val Unit' = Obj.inj Unit
val Monad' = Obj.inj o Monad
val Atomic' = Obj.inj o Atomic
val Redex' = Obj.inj o Redex
val Constraint' = Obj.inj o Constraint
val Nil' = Spine.inj Nil
val App' = Spine.inj o App
val LinApp' = Spine.inj o LinApp
val ProjLeft' = Spine.inj o ProjLeft
val ProjRight' = Spine.inj o ProjRight
val Let' = ExpObj.inj o Let
val Mon' = ExpObj.inj o Mon
val Tensor' = MonadObj.inj o Tensor
val One' = MonadObj.inj One
val DepPair' = MonadObj.inj o DepPair
val Norm' = MonadObj.inj o Norm
val PTensor' = Pattern.inj o PTensor
val POne' = Pattern.inj POne
val PDepPair' = Pattern.inj o PDepPair
val PVar' = Pattern.inj o PVar

structure KindAuxDefs = AuxDefs (structure T = Kind)
structure AsyncTypeAuxDefs = AuxDefs (structure T = AsyncType)
structure TypeSpineAuxDefs = AuxDefs (structure T = TypeSpine)
structure SyncTypeAuxDefs = AuxDefs (structure T = SyncType)

structure ObjAuxDefs = AuxDefs (structure T = Obj)
structure SpineAuxDefs = AuxDefs (structure T = Spine)
structure ExpObjAuxDefs = AuxDefs (structure T = ExpObj)
structure MonadObjAuxDefs = AuxDefs (structure T = MonadObj)
structure PatternAuxDefs = AuxDefs (structure T = Pattern)

(*
fun getTypeAbbrev (FixAsyncType a) = NONE
  | getTypeAbbrev (TClos (a, _)) = getTypeAbbrev a
  | getTypeAbbrev (TLogicVar (ref NONE)) = NONE
  | getTypeAbbrev (TLogicVar (ref (SOME a))) = getTypeAbbrev a
  | getTypeAbbrev (TAbbrev (a, _)) = SOME a*)

val lVarCnt = ref 0
fun nextLVarCnt () = (lVarCnt := (!lVarCnt) + 1 ; !lVarCnt)

fun newTVar () = TLogicVar (ref NONE)
fun newApxTVar () = TLogicVar (ref NONE)
fun newLVarCtx ctx ty = Atomic' (LogicVar (ref NONE, ty, Subst.id, ref ctx, ref [], nextLVarCnt ()), ty, Nil')
val newLVar = newLVarCtx NONE


structure Signatur =
struct
	open SymbTable

	val sigTable = ref (empty()) : decl Table ref

	fun getType c =
		case peek (!sigTable, c) of
			NONE => raise Fail ("Undeclared identifier: "^c^"\n")
		  | SOME (ConstDecl (_, imps, Ty ty)) => (imps, ty)
		  | SOME (ConstDecl (_, _, Ki _)) => raise Fail ("Type "^c^" is used as a object\n")
		  | SOME _ => raise Fail "Internal error: getType called on abbrev\n"

	fun getKind a =
		case peek (!sigTable, a) of
			NONE => raise Fail ("Undeclared identifier: "^a^"\n")
		  | SOME (ConstDecl (_, _, Ty _)) => raise Fail ("Object "^a^" is used as a type\n")
		  | SOME (ConstDecl (_, imps, Ki ki)) => (imps, ki)
		  | SOME _ => raise Fail "Internal error: getKind called on abbrev\n"

	(* newImplicits implicits -> obj list *)
	fun newImplicits imps = map (fn (_, A) => newLVar A) imps

	(* newTSpine : kind -> typeSpine *)
	fun newTSpine ki = case Kind.prj ki of
		  Type => TNil'
		| KPi (_, A, K) => TApp' (newLVar A, newTSpine K)

	fun idFromDecl (ConstDecl (s, _, _)) = s
	  | idFromDecl (TypeAbbrev (s, _)) = s
	  | idFromDecl (ObjAbbrev (s, _, _)) = s

	(******************)
	
	(* sigAddDecl : decl -> unit *)
	fun sigAddDecl dec = sigTable := insert (!sigTable, idFromDecl dec, dec)

	(* sigLookupKind : string -> kind *)
	fun sigLookupKind a =
		let val (imps, ki) = getKind a
			(*fun im2ki [] = ki
			  | im2ki ((x, A)::im) = KPi' (x, A, im2ki im)*)
		in foldr (fn ((x, A), im) => KPi' (x, A, im)) ki imps end

	(* sigLookupType : string -> asyncType *)
	fun sigLookupType a =
		let val (imps, ty) = getType a
		in foldr (fn ((x, A), im) => TPi' (x, A, im)) ty imps end

	(* sigLookupApxKind : string -> apxKind *)
	fun sigLookupApxKind a = #2 (getKind a)

	(* sigLookupApxType : string -> apxAsyncType *)
	fun sigLookupApxType c = #2 (getType c)

	(* sigNewImplicitsType : string -> obj list *)
	fun sigNewImplicitsType a = newImplicits (#1 (getKind a))

	(* sigNewImplicitsObj : string -> obj list *)
	fun sigNewImplicitsObj a = newImplicits (#1 (getType a))

	(* sigNewTAtomic : string -> asyncType *)
	fun sigNewTAtomic a =
		let val (imps, ki) = getKind a
		in TAtomic' (a, newImplicits imps, newTSpine ki) end

	(* sigGetTypeAbbrev : string -> asyncType option *)
	fun sigGetTypeAbbrev a =
		case peek (!sigTable, a) of
			NONE => raise Fail ("Undeclared identifier: "^a^"\n")
		  | SOME (TypeAbbrev (_, ty)) => SOME ty
		  | SOME (ObjAbbrev _) => raise Fail ("Object "^a^" is used as a type\n")
		  | SOME (ConstDecl _) => NONE

	(* sigGetObjAbbrev : string -> (obj * asyncType) option *)
	fun sigGetObjAbbrev c =
		case peek (!sigTable, c) of
			NONE => raise Fail ("Undeclared identifier: "^c^"\n")
		  | SOME (ObjAbbrev (_, ty, ob)) => SOME (ob, ty)
		  | SOME (TypeAbbrev _) => raise Fail ("Type "^c^" is used as an object\n")
		  | SOME (ConstDecl _) => NONE
end

(* structure ApxKind : TYP where type 'a F = 'a apxKindF and type t = apxKind *)
structure ApxKind =
struct
	type t = apxKind
	type 'a F = 'a apxKindF
	fun inj ApxType = Kind.inj Type
	  | inj (ApxKPi (A, K)) = Kind.inj (KPi ("", A, K))
	fun prj (KClos (K, _)) = prj K
	  | prj k = case Kind.prj k of
		  Type => ApxType
		| KPi (_, A, K) => ApxKPi (A, K)
	fun Fmap f ApxType = ApxType
	  | Fmap f (ApxKPi (A, K)) = ApxKPi (A, f K)
end
(* structure ApxAsyncType : TYP where type 'a F = 'a apxAsyncTypeF and type t = apxAsyncType *)
structure ApxAsyncType =
struct
	type t = apxAsyncType
	type 'a F = 'a apxAsyncTypeF
	fun inj (ApxLolli (A, B)) = AsyncType.inj (Lolli (A, B))
	  | inj (ApxTPi (A, B)) = AsyncType.inj (TPi ("", A, B))
	  | inj (ApxAddProd (A, B)) = AsyncType.inj (AddProd (A, B))
	  | inj ApxTop = AsyncType.inj Top
	  | inj (ApxTMonad S) = AsyncType.inj (TMonad S)
	  | inj (ApxTAtomic a) = Signatur.sigNewTAtomic a
	  | inj (ApxTAbbrev aA) = AsyncType.inj (TAbbrev aA)
	  | inj (ApxTLogicVar X) = TLogicVar X
	fun prj (TLogicVar (ref (SOME A))) = prj A
	  | prj (TLogicVar (X as ref NONE)) = ApxTLogicVar X
	  | prj (TClos (A, _)) = prj A
	  | prj a = case AsyncType.prj a of
		  Lolli (A, B) => ApxLolli (A, B)
		| TPi (_, A, B) => ApxTPi (A, B)
		| AddProd (A, B) => ApxAddProd (A, B)
		| Top => ApxTop
		| TMonad S => ApxTMonad S
		| TAtomic (a, _, _) => ApxTAtomic a
		| TAbbrev (a, A) => ApxTAbbrev (a, A)
		| TUnknown => raise Fail "Internal error: Cannot happen\n"
	fun Fmap f (ApxLolli (A, B)) = ApxLolli (f A, f B)
	  | Fmap f (ApxTPi (A, B)) = ApxTPi (f A, f B)
	  | Fmap f (ApxAddProd (A, B)) = ApxAddProd (f A, f B)
	  | Fmap f ApxTop = ApxTop
	  | Fmap f (ApxTMonad S) = ApxTMonad S
	  | Fmap f (ApxTAtomic a) = ApxTAtomic a
	  | Fmap f (ApxTAbbrev aA) = ApxTAbbrev aA
	  | Fmap f (ApxTLogicVar X) = ApxTLogicVar X
end
(* structure ApxSyncType : TYP where type 'a F = 'a apxSyncTypeF and type t = apxSyncType *)
structure ApxSyncType =
struct
	type t = apxSyncType
	type 'a F = 'a apxSyncTypeF
	fun inj (ApxTTensor (S1, S2)) = SyncType.inj (TTensor (S1, S2))
	  | inj ApxTOne = SyncType.inj TOne
	  | inj (ApxExists (A, S)) = SyncType.inj (Exists ("", A, S))
	  | inj (ApxAsync A) = SyncType.inj (Async A)
	fun prj (STClos (S, _)) = prj S
	  | prj s = case SyncType.prj s of
		  TTensor (S1, S2) => ApxTTensor (S1, S2)
		| TOne => ApxTOne
		| Exists (_, A, S) => ApxExists (A, S)
		| Async A => ApxAsync A
	fun Fmap f (ApxTTensor (S1, S2)) = ApxTTensor (f S1, f S2)
	  | Fmap f ApxTOne = ApxTOne
	  | Fmap f (ApxExists (A, S)) = ApxExists (A, f S)
	  | Fmap f (ApxAsync A) = ApxAsync A
end

val ApxType' = ApxKind.inj ApxType
val ApxKPi' = ApxKind.inj o ApxKPi
val ApxLolli' = ApxAsyncType.inj o ApxLolli
val ApxTPi' = ApxAsyncType.inj o ApxTPi
val ApxAddProd' = ApxAsyncType.inj o ApxAddProd
val ApxTop' = ApxAsyncType.inj ApxTop
val ApxTMonad' = ApxAsyncType.inj o ApxTMonad
val ApxTAtomic' = ApxAsyncType.inj o ApxTAtomic
val ApxTAbbrev' = ApxAsyncType.inj o ApxTAbbrev
val ApxTLogicVar' = ApxAsyncType.inj o ApxTLogicVar
val ApxTTensor' = ApxSyncType.inj o ApxTTensor
val ApxTOne' = ApxSyncType.inj ApxTOne
val ApxExists' = ApxSyncType.inj o ApxExists
val ApxAsync' = ApxSyncType.inj o ApxAsync

structure ApxKindAuxDefs = AuxDefs (structure T = ApxKind)
structure ApxAsyncTypeAuxDefs = AuxDefs (structure T = ApxAsyncType)
structure ApxSyncTypeAuxDefs = AuxDefs (structure T = ApxSyncType)

fun apxCopyType ty = ApxAsyncTypeAuxDefs.fold
	(fn ApxTMonad S => ApxTMonad' (apxCopySyncType S) | A => ApxAsyncType.inj A) ty
and apxCopySyncType sty = ApxSyncTypeAuxDefs.fold
	(fn ApxExists (A, S) => ApxExists' (apxCopyType A, S)
	  | ApxAsync A => ApxAsync' (apxCopyType A)
	  | S => ApxSyncType.inj S) sty

(* typeLogicVar * apxAsyncType -> unit *)
fun updLVar (ref (SOME _), _) = raise Fail "typeLogicVar already updated\n"
  | updLVar (X as ref NONE, A) = X := SOME (apxCopyType A)

fun kindToApx x = x
fun asyncTypeToApx x = x
fun syncTypeToApx x = x

val asyncTypeFromApx = apxCopyType
val syncTypeFromApx = apxCopySyncType
fun kindFromApx ki = case ApxKind.prj ki of
	ApxType => Type' | ApxKPi (A, K) => KPi' ("", asyncTypeFromApx A, kindFromApx K)


end

structure Util =
struct

open Syntax

fun map1 f (a, b) = (f a, b)
fun map2 f (a, b) = (a, f b)
fun map12 f g (a, b) = (f a, g b)

fun linApp (ob1, ob2) = Redex' (ob1, newApxTVar (), LinApp' (ob2, Nil'))
fun app (ob1, ob2) = Redex' (ob1, newApxTVar (), App' (ob2, Nil'))
fun projLeft ob = Redex' (ob, newApxTVar (), ProjLeft' Nil')
fun projRight ob = Redex' (ob, newApxTVar (), ProjRight' Nil')
fun blank () = newLVar (newTVar ())
fun headToObj h = Atomic' (h, newApxTVar (), Nil')

fun linLamConstr (x, A, N) = Constraint' (LinLam' (x, N), Lolli' (A, newTVar ()))
fun lamConstr (x, A, N) = Constraint' (Lam' (x, N), TPi' (x, A, newTVar ()))

(* typePrjAbbrev : asyncType -> asyncType asyncTypeF *)
fun typePrjAbbrev ty = case AsyncType.prj ty of
	  TAbbrev (a, ty) => typePrjAbbrev ty
	| A => A

(* apxTypePrjAbbrev : apxAsyncType -> apxAsyncType apxAsyncTypeF *)
fun apxTypePrjAbbrev ty = case ApxAsyncType.prj ty of
	  ApxTAbbrev (a, ty) => apxTypePrjAbbrev (asyncTypeToApx ty)
	| A => A

(* isNil : spine -> bool *)
fun isNil S = case Spine.prj S of Nil => true | _ => false

(* appendSpine : spine * spine -> spine *)
fun appendSpine (S1', S2) = case Spine.prj S1' of
	  Nil => S2
	| LinApp (N, S1) => LinApp' (N, appendSpine (S1, S2))
	| App (N, S1) => App' (N, appendSpine (S1, S2))
	| ProjLeft S1 => ProjLeft' (appendSpine (S1, S2))
	| ProjRight S1 => ProjRight' (appendSpine (S1, S2))

(* objAppKind : (unit objF -> unit) -> kind -> unit *)
(* objAppType : (unit objF -> unit) -> asyncType -> unit *)
(* objAppObj  : (unit objF -> unit) -> obj -> unit *)
fun objAppKind f ki = KindAuxDefs.fold
	(fn Type => () | KPi (_, A, ()) => objAppType f A) ki
and objAppType f ty = AsyncTypeAuxDefs.fold
	(fn TMonad S => objAppSyncType f S
	  | TAtomic (_, os, S) => (List.app (objAppObj f) os; objAppTSpine f S)
	  | _ => ()) ty
and objAppTSpine f sp = TypeSpineAuxDefs.fold
	(fn TNil => () | TApp (ob, ()) => objAppObj f ob) sp
and objAppSyncType f ty = SyncTypeAuxDefs.fold
	(fn Exists (_, A, ()) => objAppType f A | Async A => objAppType f A | _ => ()) ty
and objAppObj f obj = ObjAuxDefs.fold
	(fn ob =>
		((case ob of
			  Monad E => objAppExp f E
			| Atomic (H, A, S) => (objAppHead f H; objAppSpine f S)
			| Redex ((), A, S) => objAppSpine f S
			| Constraint ((), A) => objAppType f A
			| _ => ())
		; f ob)) obj
and objAppHead f h = case h of
	  Const (_, os) => List.app (objAppObj f) os
	| Var _ => ()
	| UCVar _ => ()
	| LogicVar (_, A, s, rctx, _, _) => objAppType f (TClos (A, s))
and objAppSpine f sp = SpineAuxDefs.fold
	(fn App (ob, ()) => objAppObj f ob | LinApp (ob, ()) => objAppObj f ob | _ => ()) sp
and objAppExp f e = ExpObjAuxDefs.fold
	(fn Let (p, ob, ()) => (objAppPattern f p; objAppObj f ob) | Mon M => objAppMonad f M) e
and objAppMonad f m = MonadObjAuxDefs.fold
	(fn DepPair (ob, ()) => objAppObj f ob | Norm ob => objAppObj f ob | _ => ()) m
and objAppPattern f p = PatternAuxDefs.fold
	(fn PDepPair (_, A, ()) => objAppType f A | PVar (_, A) => objAppType f A | _ => ()) p

(* objExpMapKind : (obj -> obj objF) -> (exp -> exp expF) -> kind -> kind *)
(* objExpMapType : (obj -> obj objF) -> (exp -> exp expF) -> asyncType -> asyncType *)
(* objExpMapObj : (obj -> obj objF) -> (exp -> exp expF) -> obj -> obj *)
fun objExpMapKind g f ki = KindAuxDefs.unfold
	((fn Type => Type | KPi (x, A, k) => KPi (x, objExpMapType g f A, k)) o Kind.prj) ki
and objExpMapType g f ty = AsyncTypeAuxDefs.unfold
	((fn TMonad S => TMonad (objExpMapSyncType g f S)
	  | TAtomic (a, os, S) => TAtomic (a, map (objExpMapObj g f) os, objExpMapTSpine g f S)
	  | A => A) o AsyncType.prj) ty
and objExpMapTSpine g f sp = TypeSpineAuxDefs.unfold
	((fn TNil => TNil | TApp (ob, S) => TApp (objExpMapObj g f ob, S)) o TypeSpine.prj) sp
and objExpMapSyncType g f ty = SyncTypeAuxDefs.unfold
	((fn Exists (x, A, S) => Exists (x, objExpMapType g f A, S)
	   | Async A => Async (objExpMapType g f A)
	   | S => S) o SyncType.prj) ty
and objExpMapObj g f obj = ObjAuxDefs.unfold
	((fn Monad E => Monad (objExpMapExp g f E)
	   | Atomic (H, A, S) => Atomic (objExpMapHead g f H, A, objExpMapSpine g f S)
	   | Redex (N, A, S) => Redex (N, A, objExpMapSpine g f S)
	   | Constraint (N, A) => Constraint (N, objExpMapType g f A)
	   | N => N) o f) obj
and objExpMapHead g f h = case h of
	  Const (c, os) => Const (c, map (objExpMapObj g f) os)
	| LogicVar (r, A, s, rctx, cs, l) => LogicVar (r, A, s, rctx, cs, l)
	| _ => h
and objExpMapSpine g f sp = SpineAuxDefs.unfold
	((fn App (ob, S) => App (objExpMapObj g f ob, S)
	   | LinApp (ob, S) => LinApp (objExpMapObj g f ob, S)
	   | S => S) o Spine.prj) sp
and objExpMapExp g f e = ExpObjAuxDefs.unfold
	((fn Let (p, ob, E) => Let (objExpMapPattern g f p, objExpMapObj g f ob, E)
	   | Mon M => Mon (objExpMapMonad g f M)) o g) e
and objExpMapMonad g f m = MonadObjAuxDefs.unfold
	((fn DepPair (ob, M) => DepPair (objExpMapObj g f ob, M)
	   | Norm ob => Norm (objExpMapObj g f ob)
	   | M => M) o MonadObj.prj) m
and objExpMapPattern g f p = PatternAuxDefs.unfold
	((fn PDepPair (x, A, P) => PDepPair (x, objExpMapType g f A, P)
	   | PVar (x, A) => PVar (x, objExpMapType g f A)
	   | P => P) o Pattern.prj) p

(* objMapKind : (obj -> obj objF) -> kind -> kind *)
(* objMapType : (obj -> obj objF) -> asyncType -> asyncType *)
(* objMapObj : (obj -> obj objF) -> obj -> obj *)
val objMapKind = objExpMapKind ExpObj.prj
val objMapType = objExpMapType ExpObj.prj
val objMapObj = objExpMapObj ExpObj.prj

end
