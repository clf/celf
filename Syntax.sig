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

(* subMode is the combination of the two flags occurring on variables
 * in substitutions:
 * ID is either II, AA, or LL (we never need to distinguish these cases)
 * INT4LIN is IL, i.e. substituting an intuitionistic var for a linear one
 * INT4AFF is IA, i.e. substituting an intuitionistic var for an affine one
 * AFF4LIN is AL, i.e. substituting an affine var for a linear one
 *)
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

(* subtyping relation: patSubst < pat_Subst < subst *)
type pat
type pat_
type gen
type 'a substi
type patSubst = pat substi (* pattern substitutions *)
type pat_Subst = pat_ substi (* pattern substitutions with potential Undefs *)
type subst = gen substi (* general substitutions *)
datatype subObj = Ob of Context.mode * nfObj | Idx of subMode * int | Undef

datatype constr
	= Solved
	| Eqn of nfObj * nfObj * (unit -> string)
	| Exist of nfObj * (unit -> string)
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
	= TLPi of tpattern * 'sTy * 'aTy
	| AddProd of 'aTy * 'aTy
	| TMonad of 'sTy
	| TAtomic of string * 'tyS
	| TAbbrev of string * 'aTy
datatype ('o, 'tyS) typeSpineFF
	= TNil
	| TApp of 'o * 'tyS
datatype ('aTy, 'sTy) syncTypeFF
	= LExists of tpattern * 'sTy * 'sTy
	| TOne
	| TDown of 'aTy
	| TAffi of 'aTy
	| TBang of 'aTy
datatype ('aTy, 'sp, 'e, 'o) objFF
	= LLam of opattern * 'o
	| AddPair of 'o * 'o
	| Monad of 'e
	| Atomic of head * 'sp
	| Redex of 'o * apxAsyncType * 'sp
	| Constraint of 'o * 'aTy
datatype ('sp, 'e, 'o) nfObjFF
	= NfLLam of opattern * 'o
	| NfAddPair of 'o * 'o
	| NfMonad of 'e
	| NfAtomic of nfHead * 'sp
datatype ('m, 'sp) spineFF
	= Nil
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
	{X : nfObj option VRef.vref, ty : 'aTy, s : 'b substi,
		ctx : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }
	* 'a substi -> {X : nfObj option VRef.vref, ty : 'aTy, s : 'a substi,
		ctx : 'aTy Context.context option ref,
		cnstr : constr VRef.vref list VRef.vref, tag : word }

datatype typeOrKind = Ty of asyncType | Ki of kind
datatype decl = ConstDecl of string * int * typeOrKind
	| TypeAbbrev of string * asyncType
	| ObjAbbrev of string * asyncType * obj
	| Query of int option * int option * int option * int * asyncType

datatype declError = TypeErr | KindErr | AmbigType | UndeclId | GeneralErr
exception ExnDeclError of declError * string

val KClos : kind * 'a substi -> kind
val TClos : asyncType * 'a substi -> asyncType
val TSClos : typeSpine * 'a substi -> typeSpine
val STClos : syncType * 'a substi -> syncType
val Clos : obj * 'a substi -> obj
val SClos : spine * 'a substi -> spine
val EClos : expObj * 'a substi -> expObj
val MClos : monadObj * 'a substi -> monadObj

val NfKClos : nfKind * 'a substi -> nfKind
val NfTClos : nfAsyncType * 'a substi -> nfAsyncType
val NfTSClos : nfTypeSpine * 'a substi -> nfTypeSpine
val NfSTClos : nfSyncType * 'a substi -> nfSyncType
val NfClos : nfObj * 'a substi -> nfObj
val NfSClos : nfSpine * 'a substi -> nfSpine
val NfEClos : nfExpObj * 'a substi -> nfExpObj
val NfMClos : nfMonadObj * 'a substi -> nfMonadObj

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
	(* lciSub: linear-changing identity substitution (sorted by index) *)
	type lciSub = (subMode * int) list
	val id : 'a substi
	val coerce2s : 'a substi -> subst     (* subtyping coercion *)
	val coerce2p_ : patSubst -> pat_Subst (* subtyping coercion *)
	val shift : int -> 'a substi
	val subI : nfObj -> subst
	val subM : nfMonadObj -> subst
	val dotMonad : nfMonadObj * 'a substi -> subst
	val Dot : subObj * 'a substi -> subst
	val dot1 : 'a substi -> 'a substi
	val dotn : int -> 'a substi -> 'a substi
	val comp : 'a substi * 'a substi -> 'a substi
	val shiftHead : 'aTy headF * int -> 'aTy headF
	val switchSub : int * int -> patSubst
	val intersect : pat_Subst -> patSubst
	val intersection : ((Context.mode * int, nfObj) sum * nfObj -> bool) -> subst * subst -> patSubst
	val invert : pat_Subst -> pat_Subst
	val patSub : (nfObj -> nfObj * bool) -> (exn -> nfObj -> Context.mode * int) ->
			subst -> (lciSub * pat_Subst) option
	val lcisComp : lciSub * pat_Subst -> lciSub
	val lcis2sub : lciSub -> (*lcPat*)subst
	val pruningsub : ('a * int) list -> pat_Subst (* e.g.: lciSub -> pat_Subst *)
	val lcisDiff : lciSub * lciSub -> lciSub
	val qsort2 : ('a * int) list -> ('a * int) list (* e.g.: lciSub(unsorted) -> lciSub *)
	val isId : 'a substi -> bool
	val isWeaken : 'a substi -> patSubst option
	val substToStr : (nfObj -> string) -> subst -> string
	val fold : (subObj * 'a -> 'a) -> (int -> 'a) -> subst -> 'a
	val map : (nfObj -> nfObj) -> subst -> subst
	val hdDef : pat_Subst -> bool
	val subPrj : subst -> (subObj * subst, int) sum
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

datatype ('aTy, 'ki) apxKindFF
	= ApxType
	| ApxKPi of 'aTy * 'ki
datatype ('sTy, 'aTy) apxAsyncTypeFF
	= ApxLolli of 'sTy * 'aTy
	| ApxAddProd of 'aTy * 'aTy
	| ApxTMonad of 'sTy
	| ApxTAtomic of string
	| ApxTAbbrev of string * asyncType
	| ApxTLogicVar of typeLogicVar
datatype ('aTy, 'sTy) apxSyncTypeFF
	= ApxTTensor of 'sTy * 'sTy
	| ApxTOne
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

val injectApxType : apxAsyncType -> asyncType
val injectApxSyncType : apxSyncType -> syncType
val unsafeCast : apxAsyncType -> asyncType
val unsafeCastS : apxSyncType -> syncType

val normalizeKind : kind -> nfKind
val normalizeType : asyncType -> nfAsyncType
val normalizeObj : obj -> nfObj
val normalizeExpObj : expObj -> nfExpObj
val normalizeMonadObj : monadObj -> nfMonadObj
val normalizeHead : head -> nfHead

val unnormalizeKind : nfKind -> kind
val unnormalizeType : nfAsyncType -> asyncType
val unnormalizeSyncType : nfSyncType -> syncType
val unnormalizeObj : nfObj -> obj
val unnormalizeExpObj : nfExpObj -> expObj

val etaShortcut : nfObj -> (Context.mode * int) option

structure Signatur : sig
	val getSigDelta : unit -> decl list
	val sigAddDecl : decl -> unit
	val getImplLength : string -> int
	val sigLookupKind : string -> kind
	val sigLookupType : string -> asyncType
	val sigGetTypeAbbrev : string -> asyncType option
	val sigGetObjAbbrev : string -> (obj * asyncType) option
end

end
