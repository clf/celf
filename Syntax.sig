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

signature TLU = TOP_LEVEL_UTIL
signature SYNTAX_CORE1 =
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
datatype subObj = Ob of obj | Idx of int | Undef

datatype constr = Solved | Eqn of obj * obj
datatype head = Const of string
	| Var of int
	| UCVar of string
	| LogicVar of {
		X     : obj option VRef.vref,
		ty    : asyncType,
		s     : subst,
		ctx   : asyncType Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref,
		tag   : word }

datatype ('aTy, 'ki) kindFF = Type
	| KPi of string option * 'aTy * 'ki
datatype ('tyS, 'sTy, 'aTy) asyncTypeFF = Lolli of 'aTy * 'aTy
	| TPi of string option * 'aTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| Top
	| TMonad of 'sTy
	| TAtomic of string * 'tyS
	| TAbbrev of string * 'aTy
datatype ('o, 'tyS) typeSpineFF = TNil
	| TApp of 'o * 'tyS
datatype ('aTy, 'sTy) syncTypeFF = TTensor of 'sTy * 'sTy
	| TOne
	| Exists of string option * 'aTy * 'sTy
	| Async of 'aTy
datatype ('aTy, 'sp, 'e, 'o) objFF = LinLam of string * 'o
	| Lam of string * 'o
	| AddPair of 'o * 'o
	| Unit
	| Monad of 'e
	| Atomic of head * 'sp
	| Redex of 'o * apxAsyncType * 'sp
	| Constraint of 'o * 'aTy
datatype ('sp, 'e, 'o) nfObjFF = NfLinLam of string * 'o
	| NfLam of string * 'o
	| NfAddPair of 'o * 'o
	| NfUnit
	| NfMonad of 'e
	| NfAtomic of head * 'sp
datatype ('o, 'sp) spineFF = Nil
	| App of 'o * 'sp
	| LinApp of 'o * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
datatype ('o, 'm, 'p, 'e) expObjFF = Let of 'p * 'o * 'e
	| Mon of 'm
datatype ('o, 'm) monadObjFF = Tensor of 'm * 'm
	| One
	| DepPair of 'o * 'm
	| Norm of 'o
datatype ('aTy, 'p) patternFF = PTensor of 'p * 'p
	| POne
	| PDepPair of string * 'aTy * 'p
	| PVar of string * 'aTy

type 'ki kindF = (asyncType, 'ki) kindFF 
type 'aTy asyncTypeF = (typeSpine, syncType, 'aTy) asyncTypeFF 
type 'tyS typeSpineF = (obj, 'tyS) typeSpineFF 
type 'sTy syncTypeF = (asyncType, 'sTy) syncTypeFF 
type 'o objF = (asyncType, spine, expObj, 'o) objFF 
type 'sp spineF = (obj, 'sp) spineFF 
type 'e expObjF = (obj, monadObj, pattern, 'e) expObjFF 
type 'm monadObjF = (obj, 'm) monadObjFF 
type 'p patternF = (asyncType, 'p) patternFF 

val with'ty :
	{X : obj option VRef.vref, ty : asyncType, s : subst,
		ctx : asyncType Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
	* asyncType -> {X : obj option VRef.vref, ty : asyncType, s : subst,
		ctx : asyncType Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
val with's :
	{X : obj option VRef.vref, ty : asyncType, s : subst,
		ctx : asyncType Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
	* subst -> {X : obj option VRef.vref, ty : asyncType, s : subst,
		ctx : asyncType Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }

(*type implicits = (string * asyncType) list*)
datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * int * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj
	| Query of int * int * int * asyncType

val KClos : kind * subst -> kind
val TClos : asyncType * subst -> asyncType
val TSClos : typeSpine * subst -> typeSpine
val STClos : syncType * subst -> syncType
val Clos : obj * subst -> obj
val SClos : spine * subst -> spine
val EClos : expObj * subst -> expObj
val MClos : monadObj * subst -> monadObj
val PClos : pattern * subst -> pattern

val redex : obj * spine -> obj

val nbinds : pattern -> int

end

signature SYNTAX_CORE2 =
sig
include SYNTAX_CORE1

structure Kind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = kind and type a = asyncType
structure AsyncType : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = asyncType and type a = typeSpine and type b = syncType
structure TypeSpine : TYP2 where type ('a, 't) F = ('a, 't) typeSpineFF
		and type t = typeSpine and type a = obj
structure SyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = syncType and type a = asyncType

structure Obj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) objFF
		and type t = obj and type a = asyncType and type b = spine and type c = expObj
structure Spine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = spine and type a = obj
structure ExpObj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
		and type t = expObj and type a = obj and type b = monadObj and type c = pattern
structure MonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = monadObj and type a = obj
structure Pattern : TYP2 where type ('a, 't) F = ('a, 't) patternFF
		and type t = pattern and type a = asyncType

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
	val switchSub : int * int -> subst
	val intersection : ((int, obj) sum * obj -> bool) -> subst * subst -> subst
	val invert : (*pat*)subst -> subst
	val patSub : (exn -> obj -> int) -> subst -> (*pat*)subst option
	val isId : subst -> bool
	val substToStr : (obj -> string) -> subst -> string
	val fold : (subObj * 'a -> 'a) -> (int -> 'a) -> subst -> 'a
	val map : (obj -> obj) -> subst -> subst
	val hdDef : subst -> bool
end

val Type' : kind
val KPi' : string option * asyncType * kind -> kind
val Lolli' : asyncType * asyncType -> asyncType
val TPi' : string option * asyncType * asyncType -> asyncType
val AddProd' : asyncType * asyncType -> asyncType
val Top' : asyncType
val TMonad' : syncType -> asyncType
val TAtomic' : string * typeSpine -> asyncType
val TAbbrev' : string * asyncType -> asyncType
val TNil' : typeSpine
val TApp' : obj * typeSpine -> typeSpine
val TTensor' : syncType * syncType -> syncType
val TOne' : syncType
val Exists' : string option * asyncType * syncType -> syncType
val Async' : asyncType -> syncType
val LinLam' : string * obj -> obj
val Lam' : string * obj -> obj
val AddPair' : obj * obj -> obj
val Unit' : obj
val Monad' : expObj -> obj
val Atomic' : head * spine -> obj
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

val appendSpine : spine * spine -> spine

end

signature SYNTAX =
sig

include SYNTAX_CORE2

type nfKind
type nfAsyncType
type nfTypeSpine
type nfSyncType
type nfObj
type nfSpine
type nfExpObj
type nfMonadObj
type nfPattern

type nfHead = head

type typeLogicVar

(*
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
*)
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

val ApxType' : apxKind
val ApxKPi' : apxAsyncType * apxKind -> apxKind
val ApxLolli' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxTPi' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxAddProd' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxTop' : apxAsyncType
val ApxTMonad' : apxSyncType -> apxAsyncType
val ApxTAtomic' : string -> apxAsyncType
val ApxTAbbrev' : string * asyncType -> apxAsyncType
val ApxTLogicVar' : typeLogicVar -> apxAsyncType
val ApxTTensor' : apxSyncType * apxSyncType -> apxSyncType
val ApxTOne' : apxSyncType
val ApxExists' : apxAsyncType * apxSyncType -> apxSyncType
val ApxAsync' : apxAsyncType -> apxSyncType


type 'ki nfKindF = (nfAsyncType, 'ki) kindFF
type 'aTy nfAsyncTypeF = (nfTypeSpine, nfSyncType, 'aTy) asyncTypeFF
type 'tyS nfTypeSpineF = (nfObj, 'tyS) typeSpineFF
type 'sTy nfSyncTypeF = (nfAsyncType, 'sTy) syncTypeFF
type 'o nfObjF = (nfSpine, nfExpObj, 'o) nfObjFF
type 'sp nfSpineF = (nfObj, 'sp) spineFF
type 'e nfExpObjF = (nfHead * apxAsyncType * nfSpine, nfMonadObj, nfPattern, 'e) expObjFF
type 'm nfMonadObjF = (nfObj, 'm) monadObjFF
type 'p nfPatternF = (nfAsyncType, 'p) patternFF

val NfKClos : nfKind * subst -> nfKind
val NfTClos : nfAsyncType * subst -> nfAsyncType
val NfTSClos : nfTypeSpine * subst -> nfTypeSpine
val NfSTClos : nfSyncType * subst -> nfSyncType
val NfClos : nfObj * subst -> nfObj
val NfSClos : nfSpine * subst -> nfSpine
val NfEClos : nfExpObj * subst -> nfExpObj
val NfMClos : nfMonadObj * subst -> nfMonadObj
val NfPClos : nfPattern * subst -> nfPattern

val nfnbinds : nfPattern -> int


val EtaTag : obj * int -> obj



structure ApxKind : TYP2 where type ('a, 't) F = ('a, 't) apxKindFF
		and type t = apxKind and type a = apxAsyncType
structure ApxAsyncType : TYP2 where type ('a, 't) F = ('a, 't) apxAsyncTypeFF
		and type t = apxAsyncType and type a = apxSyncType
structure ApxSyncType : TYP2 where type ('a, 't) F = ('a, 't) apxSyncTypeFF
		and type t = apxSyncType and type a = apxAsyncType

type ('ki, 'aTy, 'sTy) apxFoldFuns = {
	fki  : ('aTy, 'ki) apxKindFF -> 'ki,
	faTy : ('sTy, 'aTy) apxAsyncTypeFF -> 'aTy,
	fsTy : ('aTy, 'sTy) apxSyncTypeFF -> 'sTy }

val foldApxKind : ('ki, 'aTy, 'sTy) apxFoldFuns -> apxKind -> 'ki
val foldApxType : ('ki, 'aTy, 'sTy) apxFoldFuns -> apxAsyncType -> 'aTy
val foldApxSyncType : ('ki, 'aTy, 'sTy) apxFoldFuns -> apxSyncType -> 'sTy

(*
structure NfKind : TYP where type 'a F = 'a nfKindF and type t = nfKind
structure NfAsyncType : TYP where type 'a F = 'a nfAsyncTypeF and type t = nfAsyncType
structure NfTypeSpine : TYP where type 'a F = 'a nfTypeSpineF and type t = nfTypeSpine
structure NfSyncType : TYP where type 'a F = 'a nfSyncTypeF and type t = nfSyncType

structure NfObj : TYP where type 'a F = 'a nfObjF and type t = nfObj
structure NfSpine : TYP where type 'a F = 'a nfSpineF and type t = nfSpine
structure NfExpObj : TYP where type 'a F = 'a nfExpObjF and type t = nfExpObj
structure NfMonadObj : TYP where type 'a F = 'a nfMonadObjF and type t = nfMonadObj
structure NfPattern : TYP where type 'a F = 'a nfPatternF and type t = nfPattern
*)

structure NfKind : TYP2 where type ('a, 't) F = ('a, 't) kindFF
		and type t = nfKind and type a = nfAsyncType
structure NfAsyncType : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) asyncTypeFF
		and type t = nfAsyncType and type a = nfTypeSpine and type b = nfSyncType
structure NfTypeSpine : TYP2 where type ('a, 't) F = ('a, 't) typeSpineFF
		and type t = nfTypeSpine and type a = nfObj
structure NfSyncType : TYP2 where type ('a, 't) F = ('a, 't) syncTypeFF
		and type t = nfSyncType and type a = nfAsyncType

structure NfObj : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) nfObjFF
		and type t = nfObj and type a = nfSpine and type b = nfExpObj
structure NfSpine : TYP2 where type ('a, 't) F = ('a, 't) spineFF
		and type t = nfSpine and type a = nfObj
structure NfExpObj : TYP4 where type ('a, 'b, 'c, 't) F = (nfHead * 'a, 'b, 'c, 't) expObjFF
		and type t = nfExpObj and type a = nfSpine and type b = nfMonadObj and type c = nfPattern
structure NfMonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = nfMonadObj and type a = nfObj
structure NfPattern : TYP2 where type ('a, 't) F = ('a, 't) patternFF
		and type t = nfPattern and type a = nfAsyncType

(*
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
*)

(*
structure NfKindAuxDefs : AUX_DEFS where type 'a T.F = 'a nfKindF and type T.t = nfKind
structure NfAsyncTypeAuxDefs : AUX_DEFS where type 'a T.F = 'a nfAsyncTypeF and type T.t = nfAsyncType
structure NfTypeSpineAuxDefs : AUX_DEFS where type 'a T.F = 'a nfTypeSpineF and type T.t = nfTypeSpine
structure NfSyncTypeAuxDefs : AUX_DEFS where type 'a T.F = 'a nfSyncTypeF and type T.t = nfSyncType

structure NfObjAuxDefs : AUX_DEFS where type 'a T.F = 'a nfObjF and type T.t = nfObj
structure NfSpineAuxDefs : AUX_DEFS where type 'a T.F = 'a nfSpineF and type T.t = nfSpine
structure NfExpObjAuxDefs : AUX_DEFS where type 'a T.F = 'a nfExpObjF and type T.t = nfExpObj
structure NfMonadObjAuxDefs : AUX_DEFS where type 'a T.F = 'a nfMonadObjF and type T.t = nfMonadObj
structure NfPatternAuxDefs : AUX_DEFS where type 'a T.F = 'a nfPatternF and type T.t = nfPattern
*)


val newTVar : unit -> asyncType
val newApxTVar : unit -> apxAsyncType
val newLVar : asyncType -> obj
val newLVarCtx : asyncType Context.context option -> asyncType -> obj

val eqLVar : typeLogicVar * typeLogicVar -> bool
val updLVar : typeLogicVar * apxAsyncType -> unit
val isUnknown : asyncType -> bool

val kindToApx : kind -> apxKind
val asyncTypeToApx : asyncType -> apxAsyncType
val syncTypeToApx : syncType -> apxSyncType

(*val kindFromApx : apxKind -> kind*)
(*val asyncTypeFromApx : apxAsyncType -> asyncType
val syncTypeFromApx : apxSyncType -> syncType*)
val injectApxType : apxAsyncType -> asyncType
val injectApxSyncType : apxSyncType -> syncType
val unsafeCast : apxAsyncType -> asyncType

val normalizeKind : kind -> nfKind
val normalizeType : asyncType -> nfAsyncType
val normalizeObj : obj -> nfObj
val normalizeExpObj : expObj -> nfExpObj

val unnormalizeKind : nfKind -> kind
val unnormalizeType : nfAsyncType -> asyncType
val unnormalizeObj : nfObj -> obj
val unnormalizeExpObj : nfExpObj -> expObj
val unnormalizePattern : nfPattern -> pattern

val etaShortcut : obj -> int option

structure Whnf : sig
	val whnfObj : obj -> (spine, expObj, obj) nfObjFF
	val whnfExp : expObj -> (head * spine, monadObj, pattern, expObj) expObjFF
end

structure Signatur : sig
	val getSigDelta : unit -> decl list
	val sigAddDecl : decl -> unit
	val getImplLength : string -> int
	val sigLookupKind : string -> kind
	val sigLookupType : string -> asyncType
(*	val sigLookupApxKind : string -> apxKind
	val sigLookupApxType : string -> apxAsyncType
	val sigNewImplicitsType : string -> obj list
	val sigNewImplicitsObj : string -> obj list
	val sigNewTAtomic : string -> asyncType*)
	val sigGetTypeAbbrev : string -> asyncType option
	val sigGetObjAbbrev : string -> (obj * asyncType) option
end

end
