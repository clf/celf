structure Syntax :> SYNTAX =
struct

structure Syn2 =
struct
structure Syn1 =
struct

open VRef

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
and head = Const of string
	| Var of int
	| UCVar of string
	| LogicVar of {
		X     : obj option vref,
		ty    : asyncType,
		s     : subst,
		ctx   : asyncType Context.context option ref,
		cnstr : constr vref list vref,
		tag   : int }


and ('aTy, 'ki) kindFF = Type
	| KPi of string * 'aTy * 'ki
and ('tyS, 'sTy, 'aTy) asyncTypeFF = Lolli of 'aTy * 'aTy
	| TPi of string * 'aTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| Top
	| TMonad of 'sTy
	| TAtomic of string * 'tyS
	| TAbbrev of string * 'aTy
and ('o, 'tyS) typeSpineFF = TNil
	| TApp of 'o * 'tyS
and ('aTy, 'sTy) syncTypeFF = TTensor of 'sTy * 'sTy
	| TOne
	| Exists of string * 'aTy * 'sTy
	| Async of 'aTy
and ('aTy, 'sp, 'e, 'o) objFF = LinLam of string * 'o
	| Lam of string * 'o
	| AddPair of 'o * 'o
	| Unit
	| Monad of 'e
	| Atomic of head * apxAsyncType * 'sp
	| Redex of 'o * apxAsyncType * 'sp
	| Constraint of 'o * 'aTy
and ('sp, 'e, 'o) nfObjFF = NfLinLam of string * 'o
	| NfLam of string * 'o
	| NfAddPair of 'o * 'o
	| NfUnit
	| NfMonad of 'e
	| NfAtomic of head * apxAsyncType * 'sp
and ('o, 'sp) spineFF = Nil
	| App of 'o * 'sp
	| LinApp of 'o * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
and ('o, 'm, 'p, 'e) expObjFF = Let of 'p * 'o * 'e
	| Mon of 'm
and ('o, 'm) monadObjFF = Tensor of 'm * 'm
	| One
	| DepPair of 'o * 'm
	| Norm of 'o
and ('aTy, 'p) patternFF = PTensor of 'p * 'p
	| POne
	| PDepPair of string * 'aTy * 'p
	| PVar of string * 'aTy

withtype 'ki kindF = (asyncType, 'ki) kindFF
and 'aTy asyncTypeF = (typeSpine, syncType, 'aTy) asyncTypeFF
and 'tyS typeSpineF = (obj, 'tyS) typeSpineFF
and 'sTy syncTypeF = (asyncType, 'sTy) syncTypeFF
and 'o objF = (asyncType, spine, expObj, 'o) objFF
and 'sp spineF = (obj, 'sp) spineFF
and 'e expObjF = (obj, monadObj, pattern, 'e) expObjFF
and 'm monadObjF = (obj, 'm) monadObjFF
and 'p patternF = (asyncType, 'p) patternFF

and apxKind = kind
and apxAsyncType = asyncType
and apxSyncType = syncType

type implicits = (string * asyncType) list
datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * implicits * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj
	| Query of int * int * int * asyncType

type nfKind = kind
type nfAsyncType = asyncType
type nfTypeSpine = typeSpine
type nfSyncType = syncType
type nfObj = obj
type nfSpine = spine
type nfExpObj = expObj
type nfMonadObj = monadObj
type nfPattern = pattern
type nfHead = head

type 'ki nfKindF = (nfAsyncType, 'ki) kindFF
type 'aTy nfAsyncTypeF = (nfTypeSpine, nfSyncType, 'aTy) asyncTypeFF
type 'tyS nfTypeSpineF = (nfObj, 'tyS) typeSpineFF
type 'sTy nfSyncTypeF = (nfAsyncType, 'sTy) syncTypeFF
type 'o nfObjF = (nfSpine, nfExpObj, 'o) nfObjFF
type 'sp nfSpineF = (nfObj, 'sp) spineFF
type 'e nfExpObjF = (nfHead * apxAsyncType * nfSpine, nfMonadObj, nfPattern, 'e) expObjFF
type 'm nfMonadObjF = (nfObj, 'm) monadObjFF
type 'p nfPatternF = (nfAsyncType, 'p) patternFF

type typeLogicVar = asyncType option ref

datatype ('aTy, 'ki) apxKindFF = ApxType
	| ApxKPi of 'aTy * 'ki
datatype ('sTy, 'aTy) apxAsyncTypeFF = ApxLolli of 'aTy * 'aTy
	| ApxTPi of 'aTy * 'aTy
	| ApxAddProd of 'aTy * 'aTy
	| ApxTop
	| ApxTMonad of 'sTy
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype ('aTy, 'sTy) apxSyncTypeFF = ApxTTensor of 'sTy * 'sTy
	| ApxTOne
	| ApxExists of 'aTy * 'sTy
	| ApxAsync of 'aTy
type 'ki apxKindF = (apxAsyncType, 'ki) apxKindFF
type 'aTy apxAsyncTypeF = (apxSyncType, 'aTy) apxAsyncTypeFF
type 'sTy apxSyncTypeF = (apxAsyncType, 'sTy) apxSyncTypeFF


fun nbinds (FixPattern (_, n)) = n
  | nbinds (PClos (p, _)) = nbinds p

infix with'ty with's
fun {X, ty=_, s, ctx, cnstr, tag} with'ty ty' = {X=X, ty=ty', s=s, ctx=ctx, cnstr=cnstr, tag=tag}
fun {X, ty, s=_, ctx, cnstr, tag} with's s' = {X=X, ty=ty, s=s', ctx=ctx, cnstr=cnstr, tag=tag}

end (* structure Syn1 *)
open Syn1

structure Subst =
struct
	structure Subst' = SubstFun (structure Syn = Syn1 datatype subst = datatype subst)
	open Subst'
	open Syn1
	fun dot (EtaTag (_, n), s) = Dot (Idx n, s)
	  | dot (Clos (Clos (N, s'), s''), s) = dot (Clos (N, comp (s', s'')), s)
	  | dot (Clos (EtaTag (_, n), s'), s) = Dot (Clos' (Idx n, s'), s)
	  | dot (ob, s) = Dot (Ob ob, s)

	fun sub ob = dot (ob, id)
end

fun etaShortcut ob = case Subst.sub ob of Dot (Idx n, _) => SOME n | _ => NONE



(* structure Kind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = kind and type a = asyncType *)
structure Kind =
struct
	type t = kind type a = asyncType
	type ('a, 't) F = ('a, 't) kindFF
	fun inj k = FixKind k
	fun prj (FixKind k) = k
	  | prj (KClos (KClos (k, s'), s)) = prj (KClos (k, Subst.comp (s', s)))
	  | prj (KClos (FixKind k, s)) = Subst.subKind (k, s)
	fun Fmap (g, f) Type = Type
	  | Fmap (g, f) (KPi (x, A, K)) = KPi (x, g A, f K)
end
(* structure AsyncType : TYP4 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = asyncType and type a = typeSpine and type b = syncType *)
structure AsyncType =
struct
	type t = asyncType type a = typeSpine type b = syncType
	type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
	fun inj a = FixAsyncType a
	fun prj (FixAsyncType a) = a
	  | prj (TClos (TClos (a, s'), s)) = prj (TClos (a, Subst.comp (s', s)))
	  | prj (TClos (FixAsyncType a, s)) = Subst.subType (a, s)
	  | prj (TClos (TLogicVar (ref NONE), _)) = raise Fail "Ambiguous typing\n"
	  | prj (TClos (TLogicVar (ref (SOME a)), s)) = prj (TClos (a, s))
	  | prj (TLogicVar (ref NONE)) = raise Fail "Ambiguous typing\n"
	  | prj (TLogicVar (ref (SOME a))) = prj a
	fun Fmap (g, f) (Lolli (A, B)) = Lolli (f A, f B)
	  | Fmap (g, f) (TPi (x, A, B)) = TPi (x, f A, f B)
	  | Fmap (g, f) (AddProd (A, B)) = AddProd (f A, f B)
	  | Fmap (g, f) Top = Top
	  | Fmap ((g1, g2), f) (TMonad S) = TMonad (g2 S)
	  | Fmap ((g1, g2), f) (TAtomic (a, ts)) = TAtomic (a, g1 ts)
	  | Fmap (g, f) (TAbbrev (a, A)) = TAbbrev (a, f A)
end
(* structure TypeSpine : TYP2 where type ('a, 't) F = ('a, 't) typeSpineFF
		and type t = typeSpine and type a = obj *)
structure TypeSpine =
struct
	type t = typeSpine type a = obj
	type ('a, 't) F = ('a, 't) typeSpineFF
	fun inj a = FixTypeSpine a
	fun prj (FixTypeSpine a) = a
	  | prj (TSClos (TSClos (S, s'), s)) = prj (TSClos (S, Subst.comp (s', s)))
	  | prj (TSClos (FixTypeSpine S, s)) = Subst.subTypeSpine (S, s)
	fun Fmap (g, f) TNil = TNil
	  | Fmap (g, f) (TApp (N, S)) = TApp (g N, f S)
end
(* structure SyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = syncType and type a = asyncType *)
structure SyncType =
struct
	type t = syncType type a = asyncType
	type ('a, 't) F = ('a, 't) syncTypeFF
	fun inj a = FixSyncType a
	fun prj (FixSyncType a) = a
	  | prj (STClos (STClos (S, s'), s)) = prj (STClos (S, Subst.comp (s', s)))
	  | prj (STClos (FixSyncType S, s)) = Subst.subSyncType (S, s)
	fun Fmap (g, f) (TTensor (S1, S2)) = TTensor (f S1, f S2)
	  | Fmap (g, f) TOne = TOne
	  | Fmap (g, f) (Exists (x, A, S)) = Exists (x, g A, f S)
	  | Fmap (g, f) (Async A) = Async (g A)
end

(* structure Obj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
		and type t = obj and type a = asyncType and type b = spine and type c = expObj *)
structure Obj =
struct
	fun tryLVar (a as Atomic (LogicVar {X, s, ...}, A, S)) =
			(case !!X of NONE => a | SOME N => Redex (Clos (N, s), A, S))
	  | tryLVar a = a
	type t = obj type a = asyncType type b = spine type c = expObj
	type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
	(*fun inj (Redex (N, _, FixSpine Nil)) = N
	  | inj a = FixObj a*) (* optimization? *)
	fun inj a = FixObj a
	fun prj (FixObj a) = tryLVar a
	  | prj (Clos (Clos (N, s'), s)) = prj (Clos (N, Subst.comp (s', s)))
	  | prj (Clos (FixObj N, s)) = Subst.subObj (tryLVar N, s)
	  | prj (Clos (EtaTag (N, _), s)) = prj (Clos (N, s))
	  | prj (EtaTag (N, _)) = prj N
	fun Fmap (g, f) (LinLam (x, N)) = (LinLam (x, f N))
	  | Fmap (g, f) (Lam (x, N)) = (Lam (x, f N))
	  | Fmap (g, f) (AddPair (N1, N2)) = (AddPair (f N1, f N2))
	  | Fmap (g, f) Unit = Unit
	  | Fmap ((g1, g2, g3), f) (Monad E) = Monad (g3 E)
	  | Fmap ((g1, g2, g3), f) (Atomic (h, A, S)) = Atomic (h, A, g2 S)
	  | Fmap ((g1, g2, g3), f) (Redex (N, A, S)) = Redex (f N, A, g2 S)
	  | Fmap ((g1, g2, g3), f) (Constraint (N, A)) = Constraint (f N, g1 A)
end
(* structure Spine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = spine and type a = obj *)
structure Spine =
struct
	type t = spine type a = obj
	type ('a, 't) F = ('a, 't) spineFF
	fun inj a = FixSpine a
	fun prj (FixSpine a) = a
	  | prj (SClos (SClos (S, s'), s)) = prj (SClos (S, Subst.comp (s', s)))
	  | prj (SClos (FixSpine S, s)) = Subst.subSpine (S, s)
	fun Fmap (g, f) Nil = Nil
	  | Fmap (g, f) (App (N, S)) = App (g N, f S)
	  | Fmap (g, f) (LinApp (N, S)) = LinApp (g N, f S)
	  | Fmap (g, f) (ProjLeft S) = ProjLeft (f S)
	  | Fmap (g, f) (ProjRight S) = ProjRight (f S)
end
(* structure ExpObj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
		and type t = expObj and type a = obj and type b = monadObj and type c = pattern *)
structure ExpObj =
struct
	type t = expObj type a = obj type b = monadObj type c = pattern
	type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
	fun inj a = FixExpObj a
	fun prj (FixExpObj a) = a
	  | prj (EClos (EClos (E, s'), s)) = prj (EClos (E, Subst.comp (s', s)))
	  | prj (EClos (FixExpObj E, s)) = Subst.subExpObj (E, s)
	fun Fmap ((g1, g2, g3), f) (Let (p, N, E)) = Let (g3 p, g1 N, f E)
	  | Fmap ((g1, g2, g3), f) (Mon M) = Mon (g2 M)
end
(* structure MonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = monadObj and type a = obj *)
structure MonadObj =
struct
	type t = monadObj type a = obj
	type ('a, 't) F = ('a, 't) monadObjFF
	fun inj a = FixMonadObj a
	fun prj (FixMonadObj a) = a
	  | prj (MClos (MClos (M, s'), s)) = prj (MClos (M, Subst.comp (s', s)))
	  | prj (MClos (FixMonadObj M, s)) = Subst.subMonadObj (M, s)
	fun Fmap (g, f) (Tensor (M1, M2)) = Tensor (f M1, f M2)
	  | Fmap (g, f) One = One
	  | Fmap (g, f) (DepPair (N, M)) = DepPair (g N, f M)
	  | Fmap (g, f) (Norm N) = Norm (g N)
end
(* structure Pattern : TYP2 where type ('a, 't) F = ('a, 't) patternFF
		and type t = pattern and type a = asyncType *)
structure Pattern =
struct
	type t = pattern type a = asyncType
	type ('a, 't) F = ('a, 't) patternFF
	fun pbinds (PTensor (p1, p2)) = nbinds p1 + nbinds p2
	  | pbinds POne = 0
	  | pbinds (PDepPair (_, _, p)) = 1 + nbinds p
	  | pbinds (PVar _) = 1
	fun inj a = FixPattern (a, pbinds a)
	fun prj (FixPattern (a, _)) = a
	  | prj (PClos (PClos (p, s'), s)) = prj (PClos (p, Subst.comp (s', s)))
	  | prj (PClos (FixPattern (p, _), s)) = Subst.subPattern (p, s)
	fun Fmap (g, f) (PTensor (p1, p2)) = PTensor (f p1, f p2)
	  | Fmap (g, f) POne = POne
	  | Fmap (g, f) (PDepPair (x, A, p)) = PDepPair (x, g A, f p)
	  | Fmap (g, f) (PVar (x, A)) = PVar (x, g A)
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

end (* structure Syn2 *)
open Syn2


structure Whnf = WhnfFun (Syn2)
val appendSpine = Whnf.appendSpine

(* structure NfKind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = nfKind and type a = nfAsyncType *)
(* structure NfAsyncType : TYP4 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = nfAsyncType and type a = nfTypeSpine and type b = nfSyncType *)
(* structure NfTypeSpine : TYP2 where type ('a, 't) F = ('a, 't) typeSpineFF
		and type t = nfTypeSpine and type a = nfObj *)
(* structure NfSyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = nfSyncType and type a = nfAsyncType *)
structure NfKind = Kind
structure NfAsyncType = AsyncType
structure NfTypeSpine = TypeSpine
structure NfSyncType = SyncType

(* structure NfObj : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) nfObjFF
		and type t = nfObj and type a = nfSpine and type b = nfExpObj *)
structure NfObj =
struct
	type t = nfObj type a = nfSpine type b = nfExpObj
	type ('a, 'b, 't) F = ('a, 'b, 't) nfObjFF
	fun inj (NfLinLam xN) = FixObj (LinLam xN)
	  | inj (NfLam xN) = FixObj (Lam xN)
	  | inj (NfAddPair N1N2) = FixObj (AddPair N1N2)
	  | inj NfUnit = FixObj Unit
	  | inj (NfMonad E) = FixObj (Monad E)
	  | inj (NfAtomic at) = FixObj (Atomic at)
	val prj = Whnf.whnfObj
	fun Fmap (g, f) (NfLinLam (x, N)) = NfLinLam (x, f N)
	  | Fmap (g, f) (NfLam (x, N)) = NfLam (x, f N)
	  | Fmap (g, f) (NfAddPair (N1, N2)) = NfAddPair (f N1, f N2)
	  | Fmap (g, f) NfUnit = NfUnit
	  | Fmap ((g1, g2), f) (NfMonad E) = NfMonad (g2 E)
	  | Fmap ((g1, g2), f) (NfAtomic (h, A, S)) = NfAtomic (h, A, g1 S)
end
(* structure NfExpObj : TYP4 where type ('a, 'b, 'c, 't) F = (nfHead * apxAsyncType * 'a, 'b, 'c, 't) expObjFF
		and type t = nfExpObj and type a = nfSpine and type b = nfMonadObj and type c = nfPattern *)
structure NfExpObj =
struct
	type t = nfExpObj type a = nfSpine type b = nfMonadObj type c = nfPattern
	type ('a, 'b, 'c, 't) F = (nfHead * apxAsyncType * 'a, 'b, 'c, 't) expObjFF
	fun inj (Let (p, hAS, E)) = FixExpObj (Let (p, FixObj (Atomic hAS), E))
	  | inj (Mon M) = FixExpObj (Mon M)
	val prj = Whnf.whnfExp
	fun Fmap ((g1, g2, g3), f) (Let (p, (h, A, S), E)) = Let (g3 p, (h, A, g1 S), f E)
	  | Fmap ((g1, g2, g3), f) (Mon M) = Mon (g2 M)
end
(* structure NfSpine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = nfSpine and type a = nfObj *)
(* structure NfMonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = nfMonadObj and type a = nfObj *)
(* structure NfPattern : TYP2 where type ('a, 't) F = ('a, 't) patternFF
		and type t = nfPattern and type a = nfAsyncType *)
structure NfSpine = Spine
structure NfMonadObj = MonadObj
structure NfPattern = Pattern


val lVarCnt = ref 0
fun nextLVarCnt () = (lVarCnt := (!lVarCnt) + 1 ; !lVarCnt)

fun newTVar () = TLogicVar (ref NONE)
fun newApxTVar () = TLogicVar (ref NONE)
fun newLVarCtx ctx ty = Atomic' (LogicVar {X=vref NONE, ty=ty, s=Subst.id, ctx=ref ctx,
											cnstr=vref [], tag=nextLVarCnt ()}, ty, Nil')
val newLVar = newLVarCtx NONE


structure Signatur =
struct
	open SymbTable

	val sigTable = ref (empty()) : decl Table ref
	val sigDelta = ref [] : decl list ref

	fun getKiTy c =
		case peek (!sigTable, c) of
			NONE => raise Fail ("Undeclared identifier: "^c^"\n")
		  | SOME (ConstDecl (_, imps, kity)) => (imps, kity)
		  | SOME _ => raise Fail "Internal error: getKiTy called on abbrev\n"

	fun getType c = case getKiTy c of
		  (imps, Ty ty) => (imps, ty)
		| (_, Ki _) => raise Fail ("Type "^c^" is used as a object\n")

	fun getKind a = case getKiTy a of
		  (_, Ty _) => raise Fail ("Object "^a^" is used as a type\n")
		| (imps, Ki ki) => (imps, ki)

	(* newImplicits implicits -> obj list *)
	fun newImplicits imps = map (fn (_, A) => newLVar A) imps

	(* newTSpine : kind -> typeSpine *)
	fun newTSpine ki = case Kind.prj ki of
		  Type => TNil'
		| KPi (_, A, K) => TApp' (newLVar A, newTSpine K)

	fun idFromDecl (ConstDecl (s, _, _)) = s
	  | idFromDecl (TypeAbbrev (s, _)) = s
	  | idFromDecl (ObjAbbrev (s, _, _)) = s
	  | idFromDecl (Query _) = raise Fail "Internal error: Adding query to sig table\n"

	(******************)

	(* getSigDelta : unit -> decl list *)
	fun getSigDelta () = rev (!sigDelta) before sigDelta := []

	(* sigAddDecl : decl -> unit *)
	fun sigAddDecl dec =
		( sigTable := insert (!sigTable, idFromDecl dec, dec)
		; sigDelta := dec :: !sigDelta )

	(* getImplLength : string -> int *)
	val getImplLength = length o #1 o getKiTy

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
		in TAtomic' (a, foldr TApp' (newTSpine ki) (newImplicits imps)) end

	(* sigGetTypeAbbrev : string -> asyncType option *)
	fun sigGetTypeAbbrev a =
		case peek (!sigTable, a) of
			NONE => raise Fail ("Undeclared identifier: "^a^"\n")
		  | SOME (TypeAbbrev (_, ty)) => SOME ty
		  | SOME (ObjAbbrev _) => raise Fail ("Object "^a^" is used as a type\n")
		  | SOME (ConstDecl _) => NONE
		  | SOME (Query _) => raise Fail "Internal error: sigGetTypeAbbrev"

	(* sigGetObjAbbrev : string -> (obj * asyncType) option *)
	fun sigGetObjAbbrev c =
		case peek (!sigTable, c) of
			NONE => raise Fail ("Undeclared identifier: "^c^"\n")
		  | SOME (ObjAbbrev (_, ty, ob)) => SOME (ob, ty)
		  | SOME (TypeAbbrev _) => raise Fail ("Type "^c^" is used as an object\n")
		  | SOME (ConstDecl _) => NONE
		  | SOME (Query _) => raise Fail "Internal error: sigGetObjAbbrev"
end

(* structure ApxKind : TYP2 where type ('a, 't) F = ('a, 't) apxKindFF
		and type t = apxKind and type a = apxAsyncType *)
structure ApxKind =
struct
	type t = apxKind type a = apxAsyncType
	type ('a, 't) F = ('a, 't) apxKindFF
	fun inj ApxType = Kind.inj Type
	  | inj (ApxKPi (A, K)) = Kind.inj (KPi ("", A, K))
	fun prj (KClos (K, _)) = prj K
	  | prj k = case Kind.prj k of
		  Type => ApxType
		| KPi (_, A, K) => ApxKPi (A, K)
	fun Fmap (g, f) ApxType = ApxType
	  | Fmap (g, f) (ApxKPi (A, K)) = ApxKPi (g A, f K)
end
(* structure ApxAsyncType : TYP2 where type ('a, 't) F = ('a, 't) apxAsyncTypeFF
		and type t = apxAsyncType and type a = apxSyncType *)
structure ApxAsyncType =
struct
	type t = apxAsyncType type a = syncType
	type ('a, 't) F = ('a, 't) apxAsyncTypeFF
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
		| TAtomic (a, _) => ApxTAtomic a
		| TAbbrev (a, A) => ApxTAbbrev (a, A)
	fun Fmap (g, f) (ApxLolli (A, B)) = ApxLolli (f A, f B)
	  | Fmap (g, f) (ApxTPi (A, B)) = ApxTPi (f A, f B)
	  | Fmap (g, f) (ApxAddProd (A, B)) = ApxAddProd (f A, f B)
	  | Fmap (g, f) ApxTop = ApxTop
	  | Fmap (g, f) (ApxTMonad S) = ApxTMonad (g S)
	  | Fmap (g, f) (ApxTAtomic a) = ApxTAtomic a
	  | Fmap (g, f) (ApxTAbbrev aA) = ApxTAbbrev aA
	  | Fmap (g, f) (ApxTLogicVar X) = ApxTLogicVar X
end
(* structure ApxSyncType : TYP2 where type ('a, 't) F = ('a, 't) apxSyncTypeFF
		and type t = apxSyncType and type a = apxAsyncType *)
structure ApxSyncType =
struct
	type t = apxSyncType type a = apxAsyncType
	type ('a, 't) F = ('a, 't) apxSyncTypeFF
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
	fun Fmap (g, f) (ApxTTensor (S1, S2)) = ApxTTensor (f S1, f S2)
	  | Fmap (g, f) ApxTOne = ApxTOne
	  | Fmap (g, f) (ApxExists (A, S)) = ApxExists (g A, f S)
	  | Fmap (g, f) (ApxAsync A) = ApxAsync (g A)
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

structure ApxKindRec = Rec2 (structure T = ApxKind)
structure ApxAsyncTypeRec = Rec2 (structure T = ApxAsyncType)
structure ApxSyncTypeRec = Rec2 (structure T = ApxSyncType)

type ('ki, 'aTy, 'sTy) apxFoldFuns = {
	fki  : ('aTy, 'ki) apxKindFF -> 'ki,
	faTy : ('sTy, 'aTy) apxAsyncTypeFF -> 'aTy,
	fsTy : ('aTy, 'sTy) apxSyncTypeFF -> 'sTy }

fun foldApxKind (fs : ('ki, 'aTy, 'sTy) apxFoldFuns) x =
			ApxKindRec.fold (foldApxType fs) (#fki fs) x
and foldApxType fs x = ApxAsyncTypeRec.fold (foldApxSyncType fs) (#faTy fs) x
and foldApxSyncType fs x = ApxSyncTypeRec.fold (foldApxType fs) (#fsTy fs) x

val apxCopyFfs = {fki = ApxKind.inj, faTy = ApxAsyncType.inj, fsTy = ApxSyncType.inj}

(* updLVar : typeLogicVar * apxAsyncType -> unit *)
fun updLVar (ref (SOME _), _) = raise Fail "typeLogicVar already updated\n"
  | updLVar (X as ref NONE, A) = X := SOME (foldApxType apxCopyFfs A)

(* isUnknown : asyncType -> bool *)
fun isUnknown (TClos (A, _)) = isUnknown A
  | isUnknown (FixAsyncType _) = false
  | isUnknown (TLogicVar (ref (SOME A))) = isUnknown A
  | isUnknown (TLogicVar (ref NONE)) = true

fun kindToApx x = x
fun asyncTypeToApx x = x
fun syncTypeToApx x = x

val asyncTypeFromApx = foldApxType apxCopyFfs
val syncTypeFromApx = foldApxSyncType apxCopyFfs
val kindFromApx = foldApxKind apxCopyFfs

fun normalizeKind x = x
fun normalizeType x = x
fun normalizeObj x = x
fun normalizeExpObj x = x

fun unnormalizeKind x = x
fun unnormalizeType x = x
fun unnormalizeObj x = x
fun unnormalizeExpObj x = x

end
