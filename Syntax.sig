signature SYNTAX =
sig

type kind
type asyncType
type typeSpine
type syncType

type apxKind
type apxAsyncType
type apxSyncType

type obj
type spine
type expObj
type monadObj
type pattern

type subst

eqtype typeLogicVar

datatype constr = Solved | Eqn of obj * obj
datatype head = Const of string * obj list
	| Var of int
	| UCVar of string
	| LogicVar of obj option ref * asyncType * subst
			* asyncType Context.context option ref * constr ref list ref * int


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

val ApxType' : apxKind
val ApxKPi' : apxAsyncType * apxKind -> apxKind
val ApxLolli' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxTPi' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxAddProd' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxTop' : apxAsyncType
val ApxTMonad' : apxSyncType -> apxAsyncType
val ApxTAtomic' : string -> apxAsyncType
val ApxTAbbrev' : string * asyncType -> apxAsyncType
val ApxTLogicVar' : apxAsyncType option ref -> apxAsyncType
val ApxTTensor' : apxSyncType * apxSyncType -> apxSyncType
val ApxTOne' : apxSyncType
val ApxExists' : apxAsyncType * apxSyncType -> apxSyncType
val ApxAsync' : apxAsyncType -> apxSyncType


datatype 'ki kindF = Type
	| KPi of string * asyncType * 'ki
datatype 'aTy asyncTypeF = Lolli of 'aTy * 'aTy
	| TPi of string * 'aTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| Top
	| TMonad of syncType
	| TAtomic of string * obj list * typeSpine
	| TAbbrev of string * 'aTy
	| TUnknown
datatype 'tyS typeSpineF = TNil
	| TApp of obj * 'tyS
datatype 'sTy syncTypeF = TTensor of 'sTy * 'sTy
	| TOne
	| Exists of string * asyncType * 'sTy
	| Async of asyncType
datatype 'o objF = LinLam of string * 'o
	| Lam of string * 'o
	| AddPair of 'o * 'o
	| Unit
	| Monad of expObj
	| Atomic of head * apxAsyncType * spine
	| Redex of 'o * apxAsyncType * spine
	| Constraint of 'o * asyncType
datatype 'sp spineF = Nil
	| App of obj * 'sp
	| LinApp of obj * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
datatype 'e expObjF = Let of pattern * obj * 'e
	| Mon of monadObj
datatype 'm monadObjF = Tensor of 'm * 'm
	| One
	| DepPair of obj * 'm
	| Norm of obj
datatype 'p patternF = PTensor of 'p * 'p
	| POne
	| PDepPair of string * asyncType * 'p
	| PVar of string * asyncType

val Type' : kind
val KPi' : string * asyncType * kind -> kind
val Lolli' : asyncType * asyncType -> asyncType
val TPi' : string * asyncType * asyncType -> asyncType
val AddProd' : asyncType * asyncType -> asyncType
val Top' : asyncType
val TMonad' : syncType -> asyncType
val TAtomic' : string * obj list * typeSpine -> asyncType
val TAbbrev' : string * asyncType -> asyncType
val TNil' : typeSpine
val TApp' : obj * typeSpine -> typeSpine
val TTensor' : syncType * syncType -> syncType
val TOne' : syncType
val Exists' : string * asyncType * syncType -> syncType
val Async' : asyncType -> syncType
val LinLam' : string * obj -> obj
val Lam' : string * obj -> obj
val AddPair' : obj * obj -> obj
val Unit' : obj
val Monad' : expObj -> obj
val Atomic' : head * apxAsyncType * spine -> obj
val Redex' : obj * apxAsyncType * spine -> obj
val Constraint' : obj * asyncType -> obj
val Nil' : spine
val App' : obj * spine -> spine
val LinApp' : obj * spine -> spine
val ProjLeft' : spine -> spine
val ProjRight' : spine -> spine
val Let' : pattern * obj * expObj -> expObj
val Mon' : monadObj -> expObj
val Tensor' : monadObj * monadObj -> monadObj
val One' : monadObj
val DepPair' : obj * monadObj -> monadObj
val Norm' : obj -> monadObj
val PTensor' : pattern * pattern -> pattern
val POne' : pattern
val PDepPair' : string * asyncType * pattern -> pattern
val PVar' : string * asyncType -> pattern

val KClos : kind * subst -> kind
val TClos : asyncType * subst -> asyncType
val TSClos : typeSpine * subst -> typeSpine
val STClos : syncType * subst -> syncType
val Clos : obj * subst -> obj
val SClos : spine * subst -> spine
val EClos : expObj * subst -> expObj
val MClos : monadObj * subst -> monadObj
val PClos : pattern * subst -> pattern

val EtaTag : obj * int -> obj


type implicits = (string * asyncType) list
datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * implicits * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj


structure Kind : TYP where type 'a F = 'a kindF and type t = kind
structure AsyncType : TYP where type 'a F = 'a asyncTypeF and type t = asyncType
structure TypeSpine : TYP where type 'a F = 'a typeSpineF and type t = typeSpine
structure SyncType : TYP where type 'a F = 'a syncTypeF and type t = syncType

structure ApxKind : TYP where type 'a F = 'a apxKindF and type t = apxKind
structure ApxAsyncType : TYP where type 'a F = 'a apxAsyncTypeF and type t = apxAsyncType
structure ApxSyncType : TYP where type 'a F = 'a apxSyncTypeF and type t = apxSyncType

structure Obj : TYP where type 'a F = 'a objF and type t = obj
structure Spine : TYP where type 'a F = 'a spineF and type t = spine
structure ExpObj : TYP where type 'a F = 'a expObjF and type t = expObj
structure MonadObj : TYP where type 'a F = 'a monadObjF and type t = monadObj
structure Pattern : TYP where type 'a F = 'a patternF and type t = pattern

structure KindAuxDefs : AUX_DEFS where type 'a T.F = 'a kindF and type T.t = kind
structure AsyncTypeAuxDefs : AUX_DEFS where type 'a T.F = 'a asyncTypeF and type T.t = asyncType
structure TypeSpineAuxDefs : AUX_DEFS where type 'a T.F = 'a typeSpineF and type T.t = typeSpine
structure SyncTypeAuxDefs : AUX_DEFS where type 'a T.F = 'a syncTypeF and type T.t = syncType

structure ApxKindAuxDefs : AUX_DEFS where type 'a T.F = 'a apxKindF and type T.t = apxKind
structure ApxAsyncTypeAuxDefs : AUX_DEFS where type 'a T.F = 'a apxAsyncTypeF and type T.t = apxAsyncType
structure ApxSyncTypeAuxDefs : AUX_DEFS where type 'a T.F = 'a apxSyncTypeF and type T.t = apxSyncType

structure ObjAuxDefs : AUX_DEFS where type 'a T.F = 'a objF and type T.t = obj
structure SpineAuxDefs : AUX_DEFS where type 'a T.F = 'a spineF and type T.t = spine
structure ExpObjAuxDefs : AUX_DEFS where type 'a T.F = 'a expObjF and type T.t = expObj
structure MonadObjAuxDefs : AUX_DEFS where type 'a T.F = 'a monadObjF and type T.t = monadObj
structure PatternAuxDefs : AUX_DEFS where type 'a T.F = 'a patternF and type T.t = pattern


structure Subst : sig
	exception ExnUndef
	val id : subst
	val shift : int -> subst
	val sub : obj -> subst
	val dot : obj * subst -> subst
	val dot1 : subst -> subst
	val dotn : int -> subst -> subst
	val comp : subst * subst -> subst
	val shiftHead : head * int -> head
	val intersection : (*def pat*)subst * (*def pat*)subst -> subst
	val invert : (*pat*)subst -> subst
	val patSub : (exn -> obj -> int) -> subst -> (*pat*)subst option
	val isId : subst -> bool
	val substToStr : (obj -> string) -> subst -> string
	val fold : (obj * 'a -> 'a) -> (int -> 'a) -> subst -> 'a
	val hdDef : subst -> bool
end

val newTVar : unit -> asyncType
val newApxTVar : unit -> apxAsyncType
val newLVar : asyncType -> obj
val newLVarCtx : asyncType Context.context option -> asyncType -> obj

val updLVar : typeLogicVar * apxAsyncType -> unit

val kindToApx : kind -> apxKind
val asyncTypeToApx : asyncType -> apxAsyncType
val syncTypeToApx : syncType -> apxSyncType

val kindFromApx : apxKind -> kind
val asyncTypeFromApx : apxAsyncType -> asyncType
val syncTypeFromApx : apxSyncType -> syncType

val etaShortcut : obj -> int option

val nbinds : pattern -> int

structure Signatur : sig
	val sigAddDecl : decl -> unit
	val sigLookupKind : string -> kind
	val sigLookupType : string -> asyncType
	val sigLookupApxKind : string -> apxKind
	val sigLookupApxType : string -> apxAsyncType
	val sigNewImplicitsType : string -> obj list
	val sigNewImplicitsObj : string -> obj list
	val sigNewTAtomic : string -> asyncType
	val sigGetTypeAbbrev : string -> asyncType option
	val sigGetObjAbbrev : string -> (obj * asyncType) option
end

end
