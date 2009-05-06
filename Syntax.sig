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

signature TLU_SYNTAX = TOP_LEVEL_UTIL
signature SYNTAX_CORE1 =
sig

datatype subMode = ID | INT4LIN | INT4AFF | AFF4LIN

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
type ('x, 'ix) pattern
type opattern = (string, string) pattern
type tpattern = (unit, string option) pattern

type nfKind
type nfAsyncType
type nfTypeSpine
type nfSyncType
type nfObj
type nfSpine
type nfExpObj
type nfMonadObj

type subst
datatype subObj = Ob of Context.mode * nfObj | Idx of subMode * int | Undef

datatype constr = Solved | Eqn of nfObj * nfObj | Exist of nfObj
datatype 'aTy headF
	= Const of string
	| Var of Context.mode * int
	| UCVar of string
	| LogicVar of {
		X     : nfObj option VRef.vref,
		ty    : 'aTy,
		s     : subst,
		ctx   : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref,
		tag   : word }
type head = asyncType headF
type nfHead = nfAsyncType headF

datatype ('aTy, 'ki) kindFF
	= Type
	| KPi of string option * 'aTy * 'ki
datatype ('tyS, 'sTy, 'aTy) asyncTypeFF
	(*= Lolli of 'aTy * 'aTy
	| TPi of string option * 'aTy * 'aTy*)
	= TLPi of tpattern * 'sTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| TMonad of 'sTy
	| TAtomic of string * 'tyS
	| TAbbrev of string * 'aTy
datatype ('o, 'tyS) typeSpineFF
	= TNil
	| TApp of 'o * 'tyS
datatype ('aTy, 'sTy) syncTypeFF
	(*= TTensor of 'sTy * 'sTy
	| TOne
	| Exists of string option * 'aTy * 'sTy
	| Async of 'aTy*)
	= LExists of tpattern * 'sTy * 'sTy
	| TOne
	| TDown of 'aTy
	| TAffi of 'aTy
	| TBang of 'aTy
datatype ('aTy, 'sp, 'e, 'o) objFF
	(*= LinLam of string * 'o
	| Lam of string * 'o*)
	= LLam of opattern * 'o
	| AddPair of 'o * 'o
	| Monad of 'e
	| Atomic of head * 'sp
	| Redex of 'o * apxAsyncType * 'sp
	| Constraint of 'o * 'aTy
datatype ('sp, 'e, 'o) nfObjFF
	(*= NfLinLam of string * 'o
	| NfLam of string * 'o*)
	= NfLLam of opattern * 'o
	| NfAddPair of 'o * 'o
	| NfMonad of 'e
	| NfAtomic of nfHead * 'sp
datatype ('m, 'sp) spineFF
	= Nil
	(*| App of 'o * 'sp
	| LinApp of 'o * 'sp*)
	| LApp of 'm * 'sp
	| ProjLeft of 'sp
	| ProjRight of 'sp
datatype ('o, 'sp, 'm, 'e) expObjFF
	= LetRedex of opattern * apxSyncType * 'o * 'e
	| Let of opattern * (head * 'sp) * 'e
	| Mon of 'm
datatype ('sp, 'm, 'e) nfExpObjFF
	= NfLet of opattern * (nfHead * 'sp) * 'e
	| NfMon of 'm
datatype ('o, 'm) monadObjFF
	= DepPair of 'm * 'm
	| One
	| Down of 'o
	| Affi of 'o
	| Bang of 'o
	| MonUndef
	(*= Tensor of 'm * 'm
	| One
	| DepPair of 'o * 'm
	| Norm of 'o*)
(*datatype 'p patternF
	= PTensor of 'p * 'p
	| POne
	| PDepPair of string * 'p
	| PVar of string*)
datatype ('x, 'ix, 'p) patternF
	= PDepTensor of 'p * 'p
	| POne
	| PDown of 'x
	| PAffi of 'x
	| PBang of 'ix

type 'ki kindF = (asyncType, 'ki) kindFF 
type 'aTy asyncTypeF = (typeSpine, syncType, 'aTy) asyncTypeFF 
type 'tyS typeSpineF = (obj, 'tyS) typeSpineFF 
type 'sTy syncTypeF = (asyncType, 'sTy) syncTypeFF 
type 'o objF = (asyncType, spine, expObj, 'o) objFF 
type 'sp spineF = (monadObj, 'sp) spineFF 
type 'e expObjF = (obj, spine, monadObj, 'e) expObjFF 
type 'm monadObjF = (obj, 'm) monadObjFF 

val with'ty :
	{X : nfObj option VRef.vref, ty : 'aTy, s : subst,
		ctx : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
	* 'aTy -> {X : nfObj option VRef.vref, ty : 'aTy, s : subst,
		ctx : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
val with's :
	{X : nfObj option VRef.vref, ty : 'aTy, s : subst,
		ctx : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
	* subst -> {X : nfObj option VRef.vref, ty : 'aTy, s : subst,
		ctx : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }

(*type implicits = (string * asyncType) list*)
datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * int * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj
	| Query of int option * int option * int option * int * asyncType

val KClos : kind * subst -> kind
val TClos : asyncType * subst -> asyncType
val TSClos : typeSpine * subst -> typeSpine
val STClos : syncType * subst -> syncType
val Clos : obj * subst -> obj
val SClos : spine * subst -> spine
val EClos : expObj * subst -> expObj
val MClos : monadObj * subst -> monadObj

val NfKClos : nfKind * subst -> nfKind
val NfTClos : nfAsyncType * subst -> nfAsyncType
val NfTSClos : nfTypeSpine * subst -> nfTypeSpine
val NfSTClos : nfSyncType * subst -> nfSyncType
val NfClos : nfObj * subst -> nfObj
val NfSClos : nfSpine * subst -> nfSpine
val NfEClos : nfExpObj * subst -> nfExpObj
val NfMClos : nfMonadObj * subst -> nfMonadObj

val redex : obj * spine -> obj

val nbinds : ('x, 'ix) pattern -> int

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
		and type t = spine and type a = monadObj
structure ExpObj : TYP4 where type ('a, 'b, 'c, 't) F = ('a, 'b, 'c, 't) expObjFF
		and type t = expObj and type a = obj and type b = spine and type c = monadObj
structure MonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = monadObj and type a = obj

structure Pattern : sig
	type ('x, 'ix) t = ('x, 'ix) pattern
	type ('x, 'ix, 't) F = ('x, 'ix, 't) patternF
	val inj : ('x, 'ix, ('x, 'ix) t) F -> ('x, 'ix) t
	val prj : ('x, 'ix) t -> ('x, 'ix, ('x, 'ix) t) F
	val Fmap : ('t1 -> 't2) -> ('x, 'ix, 't1) F -> ('x, 'ix, 't2) F
end
structure OPatternRec : REC where type 't T.F = (string, string, 't) patternF
		and type T.t = opattern
structure TPatternRec : REC where type 't T.F = (unit, string option, 't) patternF
		and type T.t = tpattern

structure Subst : sig
	exception ExnUndef
	val id : subst
	val shift : int -> subst
	val subI : nfObj -> subst
	(*val subL : nfObj -> subst*)
	val subM : nfMonadObj -> subst
	(*val dot : Context.mode * nfObj * subst -> subst*)
	val dotMonad : nfMonadObj * subst -> subst
	val Dot : subObj * subst -> subst
	val dot1 : subst -> subst
	val dotn : int -> subst -> subst
	val comp : subst * subst -> subst
	val shiftHead : 'aTy headF * int -> 'aTy headF
	val switchSub : int * int -> subst
	val intersect : subst -> subst
	val intersection : ((Context.mode * int, nfObj) sum * nfObj -> bool) -> subst * subst -> subst
	val invert : (*pat*)subst -> subst
	val patSub : (nfObj -> nfObj * bool) -> (exn -> nfObj -> apxAsyncType -> Context.mode * int) ->
			subst -> apxAsyncType Context.context -> ((subMode * int) list * (*pat*)subst) option
	val lcsComp : (subMode * int) list * subst -> (subMode * int) list
	val lcs2sub : (subMode * int) list -> subst
	val pruningsub : ('a * int) list -> subst
	val lcsDiff : (subMode * int) list * (subMode * int) list -> (subMode * int) list
	val qsort2 : ('a * int) list -> ('a * int) list
	val isId : subst -> bool
	val isWeaken : subst -> bool
	val substToStr : (nfObj -> string) -> subst -> string
	val fold : (subObj * 'a -> 'a) -> (int -> 'a) -> subst -> 'a
	val map : (nfObj -> nfObj) -> subst -> subst
	val hdDef : subst -> bool
end

val Type' : kind
val KPi' : string option * asyncType * kind -> kind
val TLPi' : tpattern * syncType * asyncType -> asyncType
val AddProd' : asyncType * asyncType -> asyncType
val TMonad' : syncType -> asyncType
val TAtomic' : string * typeSpine -> asyncType
val TAbbrev' : string * asyncType -> asyncType
val TNil' : typeSpine
val TApp' : obj * typeSpine -> typeSpine
val LExists' : tpattern * syncType * syncType -> syncType
val TOne' : syncType
val TDown' : asyncType -> syncType
val TAffi' : asyncType -> syncType
val TBang' : asyncType -> syncType
val LLam' : opattern * obj -> obj
val AddPair' : obj * obj -> obj
val Monad' : expObj -> obj
val Atomic' : head * spine -> obj
val Redex' : obj * apxAsyncType * spine -> obj
val Constraint' : obj * asyncType -> obj
val Nil' : spine
val LApp' : monadObj * spine -> spine
val ProjLeft' : spine -> spine
val ProjRight' : spine -> spine
val LetRedex' : opattern * apxSyncType * obj * expObj -> expObj
val Let' : opattern * (head * spine) * expObj -> expObj
val Mon' : monadObj -> expObj
val DepPair' : monadObj * monadObj -> monadObj
val One' : monadObj
val Down' : obj -> monadObj
val Affi' : obj -> monadObj
val Bang' : obj -> monadObj
val MonUndef' : monadObj
val PDepTensor' : ('x, 'ix) pattern * ('x, 'ix) pattern -> ('x, 'ix) pattern
val POne' : ('x, 'ix) pattern
val PDown' : 'x -> ('x, 'ix) pattern
val PAffi' : 'x -> ('x, 'ix) pattern
val PBang' : 'ix -> ('x, 'ix) pattern

val appendSpine : spine * spine -> spine

end

signature SYNTAX =
sig

include SYNTAX_CORE2

type typeLogicVar

(*
datatype 'ki apxKindF = ApxType
	| ApxKPi of apxAsyncType * 'ki
datatype 'aTy apxAsyncTypeF = ApxLolli of 'aTy * 'aTy
	| ApxTPi of 'aTy * 'aTy
	| ApxAddProd of 'aTy * 'aTy
	| ApxTMonad of apxSyncType
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype 'sTy apxSyncTypeF = ApxTTensor of 'sTy * 'sTy
	| ApxTOne
	| ApxExists of apxAsyncType * 'sTy
	| ApxAsync of apxAsyncType
*)
datatype ('aTy, 'ki) apxKindFF
	= ApxType
	| ApxKPi of 'aTy * 'ki
datatype ('sTy, 'aTy) apxAsyncTypeFF
	= ApxLolli of 'sTy * 'aTy
	(*| ApxTPi of 'aTy * 'aTy*)
	| ApxAddProd of 'aTy * 'aTy
	| ApxTMonad of 'sTy
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype ('aTy, 'sTy) apxSyncTypeFF
	= ApxTTensor of 'sTy * 'sTy
	| ApxTOne
	(*| ApxExists of 'aTy * 'sTy*)
	| ApxTDown of 'aTy
	| ApxTAffi of 'aTy
	| ApxTBang of 'aTy
type 'ki apxKindF = (apxAsyncType, 'ki) apxKindFF
type 'aTy apxAsyncTypeF = (apxSyncType, 'aTy) apxAsyncTypeFF
type 'sTy apxSyncTypeF = (apxAsyncType, 'sTy) apxSyncTypeFF

val ApxType' : apxKind
val ApxKPi' : apxAsyncType * apxKind -> apxKind
val ApxLolli' : apxSyncType * apxAsyncType -> apxAsyncType
val ApxAddProd' : apxAsyncType * apxAsyncType -> apxAsyncType
val ApxTMonad' : apxSyncType -> apxAsyncType
val ApxTAtomic' : string -> apxAsyncType
val ApxTAbbrev' : string * asyncType -> apxAsyncType
val ApxTLogicVar' : typeLogicVar -> apxAsyncType
val ApxTTensor' : apxSyncType * apxSyncType -> apxSyncType
val ApxTOne' : apxSyncType
val ApxTDown' : apxAsyncType -> apxSyncType
val ApxTAffi' : apxAsyncType -> apxSyncType
val ApxTBang' : apxAsyncType -> apxSyncType


type 'ki nfKindF = (nfAsyncType, 'ki) kindFF
type 'aTy nfAsyncTypeF = (nfTypeSpine, nfSyncType, 'aTy) asyncTypeFF
type 'tyS nfTypeSpineF = (nfObj, 'tyS) typeSpineFF
type 'sTy nfSyncTypeF = (nfAsyncType, 'sTy) syncTypeFF
type 'o nfObjF = (nfSpine, nfExpObj, 'o) nfObjFF
type 'sp nfSpineF = (nfMonadObj, 'sp) spineFF
type 'e nfExpObjF = (nfSpine, nfMonadObj, 'e) nfExpObjFF
type 'm nfMonadObjF = (nfObj, 'm) monadObjFF

structure NfInj : sig
	val Type' : nfKind
	val KPi' : string option * nfAsyncType * nfKind -> nfKind
	val TLPi' : tpattern * nfSyncType * nfAsyncType -> nfAsyncType
	val AddProd' : nfAsyncType * nfAsyncType -> nfAsyncType
	val TMonad' : nfSyncType -> nfAsyncType
	val TAtomic' : string * nfTypeSpine -> nfAsyncType
	val TAbbrev' : string * nfAsyncType -> nfAsyncType
	val TNil' : nfTypeSpine
	val TApp' : nfObj * nfTypeSpine -> nfTypeSpine
	val LExists' : tpattern * nfSyncType * nfSyncType -> nfSyncType
	val TOne' : nfSyncType
	val TDown' : nfAsyncType -> nfSyncType
	val TAffi' : nfAsyncType -> nfSyncType
	val TBang' : nfAsyncType -> nfSyncType
	val Nil' : nfSpine
	val LApp' : nfMonadObj * nfSpine -> nfSpine
	val ProjLeft' : nfSpine -> nfSpine
	val ProjRight' : nfSpine -> nfSpine
	val DepPair' : nfMonadObj * nfMonadObj -> nfMonadObj
	val One' : nfMonadObj
	val Down' : nfObj -> nfMonadObj
	val Affi' : nfObj -> nfMonadObj
	val Bang' : nfObj -> nfMonadObj
	val MonUndef' : nfMonadObj
end

val NfLLam' : opattern * nfObj -> nfObj
val NfAddPair' : nfObj * nfObj -> nfObj
val NfMonad' : nfExpObj -> nfObj
val NfAtomic' : nfHead * nfSpine -> nfObj
val NfLet' : opattern * (nfHead * nfSpine) * nfExpObj -> nfExpObj
val NfMon' : nfMonadObj -> nfExpObj

val nfredex : nfObj * nfSpine -> nfObj
val nfletredex : opattern * nfObj * nfExpObj -> nfExpObj


val EtaTag : obj * (Context.mode * int) -> obj


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
		and type t = nfSpine and type a = nfMonadObj
structure NfExpObj : TYP3 where type ('a, 'b, 't) F = ('a, 'b, 't) nfExpObjFF
		and type t = nfExpObj and type a = nfSpine and type b = nfMonadObj
structure NfMonadObj : TYP2 where type ('a, 't) F = ('a, 't) monadObjFF
		and type t = nfMonadObj and type a = nfObj

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
*)


val newTVar : unit -> asyncType
val newApxTVar : unit -> apxAsyncType
val newLVar : asyncType -> obj
val newNfLVar : nfAsyncType -> nfObj
val newLVarCtx : asyncType Context.context option -> asyncType -> obj
val newNfLVarCtx : nfAsyncType Context.context option -> nfAsyncType -> nfObj

val eqLVar : typeLogicVar * typeLogicVar -> bool
val updLVar : typeLogicVar * apxAsyncType -> unit
val isUnknown : asyncType -> bool

val kindToApx : kind -> apxKind
val asyncTypeToApx : asyncType -> apxAsyncType
val syncTypeToApx : syncType -> apxSyncType

val nfKindToApx : nfKind -> apxKind
val nfAsyncTypeToApx : nfAsyncType -> apxAsyncType
val nfSyncTypeToApx : nfSyncType -> apxSyncType

(*val kindFromApx : apxKind -> kind*)
(*val asyncTypeFromApx : apxAsyncType -> asyncType
val syncTypeFromApx : apxSyncType -> syncType*)
val injectApxType : apxAsyncType -> asyncType
val injectApxSyncType : apxSyncType -> syncType
val unsafeCast : apxAsyncType -> asyncType
val unsafeCastS : apxSyncType -> syncType

val normalizeKind : kind -> nfKind
val normalizeType : asyncType -> nfAsyncType
val normalizeObj : obj -> nfObj
val normalizeExpObj : expObj -> nfExpObj
val normalizeMonadObj : monadObj -> nfMonadObj

val unnormalizeKind : nfKind -> kind
val unnormalizeType : nfAsyncType -> asyncType
val unnormalizeSyncType : nfSyncType -> syncType
val unnormalizeObj : nfObj -> obj
val unnormalizeExpObj : nfExpObj -> expObj

val etaShortcut : nfObj -> (Context.mode * int) option

(*
structure Whnf : sig
	val whnfObj : obj -> (spine, expObj, obj) nfObjFF
	val whnfExp : expObj -> (spine, monadObj, expObj) nfExpObjFF
end
*)

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
