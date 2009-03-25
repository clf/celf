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

signature TLU_Util = TOP_LEVEL_UTIL
structure Util :> UTIL =
struct

open Syntax infix with'ty

structure ObjAuxDefs = AuxDefs (structure T = Typ1From4 (structure T = Obj))
structure NfExpObjAuxDefs = AuxDefs (structure T = Typ1From3 (structure T = NfExpObj))

structure KindRec = Rec2 (structure T = Kind)
structure AsyncTypeRec = Rec3 (structure T = AsyncType)
structure TypeSpineRec = Rec2 (structure T = TypeSpine)
structure SyncTypeRec = Rec2 (structure T = SyncType)
structure ObjRec = Rec4 (structure T = Obj)
structure SpineRec = Rec2 (structure T = Spine)
structure ExpObjRec = Rec4 (structure T = ExpObj)
structure MonadObjRec = Rec2 (structure T = MonadObj)

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) foldFuns = {
	fki  : ('aTy, 'ki) kindFF -> 'ki,
	faTy : ('tyS, 'sTy, 'aTy) asyncTypeFF -> 'aTy,
	ftyS : ('o, 'tyS) typeSpineFF -> 'tyS,
	fsTy : ('aTy, 'sTy) syncTypeFF -> 'sTy,
	fo   : ('aTy, 'sp, 'e, 'o) objFF -> 'o,
	fsp  : ('m, 'sp) spineFF -> 'sp,
	fe   : ('o, 'sp, 'm, 'e) expObjFF -> 'e,
	fm   : ('o, 'm) monadObjFF -> 'm }

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) unfoldFuns = {
	fki  : 'ki -> ('aTy, 'ki) kindFF,
	faTy : 'aTy -> ('tyS, 'sTy, 'aTy) asyncTypeFF,
	ftyS : 'tyS -> ('o, 'tyS) typeSpineFF,
	fsTy : 'sTy -> ('aTy, 'sTy) syncTypeFF,
	fo   : 'o -> ('aTy, 'sp, 'e, 'o) objFF,
	fsp  : 'sp -> ('m, 'sp) spineFF,
	fe   : 'e -> ('o, 'sp, 'm, 'e) expObjFF,
	fm   : 'm -> ('o, 'm) monadObjFF }

fun foldKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) foldFuns) x =
		KindRec.fold (foldType fs) (#fki fs) x
and foldType fs x = AsyncTypeRec.fold (foldTypeSpine fs, foldSyncType fs) (#faTy fs) x
and foldTypeSpine fs x = TypeSpineRec.fold (foldObj fs) (#ftyS fs) x
and foldSyncType fs x = SyncTypeRec.fold (foldType fs) (#fsTy fs) x
and foldObj fs x = ObjRec.fold (foldType fs, foldSpine fs, foldExpObj fs) (#fo fs) x
and foldSpine fs x = SpineRec.fold (foldMonadObj fs) (#fsp fs) x
and foldExpObj fs x = ExpObjRec.fold (foldObj fs, foldSpine fs, foldMonadObj fs) (#fe fs) x
and foldMonadObj fs x = MonadObjRec.fold (foldObj fs) (#fm fs) x

fun unfoldKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) unfoldFuns) x =
		KindRec.unfold (unfoldType fs) (#fki fs) x
and unfoldType fs x = AsyncTypeRec.unfold (unfoldTypeSpine fs, unfoldSyncType fs) (#faTy fs) x
and unfoldTypeSpine fs x = TypeSpineRec.unfold (unfoldObj fs) (#ftyS fs) x
and unfoldSyncType fs x = SyncTypeRec.unfold (unfoldType fs) (#fsTy fs) x
and unfoldObj fs x = ObjRec.unfold (unfoldType fs, unfoldSpine fs, unfoldExpObj fs) (#fo fs) x
and unfoldSpine fs x = SpineRec.unfold (unfoldMonadObj fs) (#fsp fs) x
and unfoldExpObj fs x = ExpObjRec.unfold (unfoldObj fs, unfoldSpine fs, unfoldMonadObj fs) (#fe fs) x
and unfoldMonadObj fs x = MonadObjRec.unfold (unfoldObj fs) (#fm fs) x

structure NfKindRec = Rec2 (structure T = NfKind)
structure NfAsyncTypeRec = Rec3 (structure T = NfAsyncType)
structure NfTypeSpineRec = Rec2 (structure T = NfTypeSpine)
structure NfSyncTypeRec = Rec2 (structure T = NfSyncType)

structure NfObjRec = Rec3 (structure T = NfObj)
structure NfSpineRec = Rec2 (structure T = NfSpine)
structure NfExpObjRec = Rec3 (structure T = NfExpObj)
structure NfMonadObjRec = Rec2 (structure T = NfMonadObj)

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) nfFoldFuns = {
	fki  : ('aTy, 'ki) kindFF -> 'ki,
	faTy : ('tyS, 'sTy, 'aTy) asyncTypeFF -> 'aTy,
	ftyS : ('o, 'tyS) typeSpineFF -> 'tyS,
	fsTy : ('aTy, 'sTy) syncTypeFF -> 'sTy,
	fo   : ('sp, 'e, 'o) nfObjFF -> 'o,
	fsp  : ('m, 'sp) spineFF -> 'sp,
	fe   : ('sp, 'm, 'e) nfExpObjFF -> 'e,
	fm   : ('o, 'm) monadObjFF -> 'm }

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) nfUnfoldFuns = {
	fki  : 'ki -> ('aTy, 'ki) kindFF,
	faTy : 'aTy -> ('tyS, 'sTy, 'aTy) asyncTypeFF,
	ftyS : 'tyS -> ('o, 'tyS) typeSpineFF,
	fsTy : 'sTy -> ('aTy, 'sTy) syncTypeFF,
	fo   : 'o -> ('sp, 'e, 'o) nfObjFF,
	fsp  : 'sp -> ('m, 'sp) spineFF,
	fe   : 'e -> ('sp, 'm, 'e) nfExpObjFF,
	fm   : 'm -> ('o, 'm) monadObjFF }

fun foldNfKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) nfFoldFuns) x =
		NfKindRec.fold (foldNfType fs) (#fki fs) x
and foldNfType fs x = NfAsyncTypeRec.fold (foldNfTypeSpine fs, foldNfSyncType fs) (#faTy fs) x
and foldNfTypeSpine fs x = NfTypeSpineRec.fold (foldNfObj fs) (#ftyS fs) x
and foldNfSyncType fs x = NfSyncTypeRec.fold (foldNfType fs) (#fsTy fs) x
and foldNfObj fs x = NfObjRec.fold (foldNfSpine fs, foldNfExpObj fs) (#fo fs) x
and foldNfSpine fs x = NfSpineRec.fold (foldNfMonadObj fs) (#fsp fs) x
and foldNfExpObj fs x = NfExpObjRec.fold (foldNfSpine fs, foldNfMonadObj fs) (#fe fs) x
and foldNfMonadObj fs x = NfMonadObjRec.fold (foldNfObj fs) (#fm fs) x

fun unfoldNfKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm) nfUnfoldFuns) x =
		NfKindRec.unfold (unfoldNfType fs) (#fki fs) x
and unfoldNfType fs x = NfAsyncTypeRec.unfold (unfoldNfTypeSpine fs, unfoldNfSyncType fs) (#faTy fs) x
and unfoldNfTypeSpine fs x = NfTypeSpineRec.unfold (unfoldNfObj fs) (#ftyS fs) x
and unfoldNfSyncType fs x = NfSyncTypeRec.unfold (unfoldNfType fs) (#fsTy fs) x
and unfoldNfObj fs x = NfObjRec.unfold (unfoldNfSpine fs, unfoldNfExpObj fs) (#fo fs) x
and unfoldNfSpine fs x = NfSpineRec.unfold (unfoldNfMonadObj fs) (#fsp fs) x
and unfoldNfExpObj fs x = NfExpObjRec.unfold (unfoldNfSpine fs, unfoldNfMonadObj fs) (#fe fs) x
and unfoldNfMonadObj fs x = NfMonadObjRec.unfold (unfoldNfObj fs) (#fm fs) x

(*
type ('o, 'sp, 'e, 'm) nfFoldObjFuns = {
	fo   : ('sp, 'e, 'o) nfObjFF -> 'o,
	fsp  : ('m, 'sp) spineFF -> 'sp,
	fe   : ('sp, 'm, 'e) nfExpObjFF -> 'e,
	fm   : ('o, 'm) monadObjFF -> 'm }

type ('o, 'sp, 'e, 'm) nfUnfoldObjFuns = {
	fo   : 'o -> ('sp, 'e, 'o) nfObjFF,
	fsp  : 'sp -> ('m, 'sp) spineFF,
	fe   : 'e -> ('sp, 'm, 'e) nfExpObjFF,
	fm   : 'm -> ('o, 'm) monadObjFF }

fun refoldNfObj ((u, f) : ('o, 'sp, 'e, 'm) nfUnfoldObjFuns * ('o, 'sp, 'e, 'm) nfFoldObjFuns) x =
		NfObjRec.refold (refoldNfSpine (u, f), refoldNfExpObj (u, f)) (#fo u) (#fo f) x
and refoldNfSpine (u, f) x = NfSpineRec.refold (refoldNfMonadObj (u, f)) (#fsp u) (#fsp f) x
and refoldNfExpObj (u, f) x =
		NfExpObjRec.refold (refoldNfSpine (u, f), refoldNfMonadObj (u, f)) (#fe u) (#fe f) x
and refoldNfMonadObj (u, f) x = NfMonadObjRec.refold (refoldNfObj (u, f)) (#fm u) (#fm f) x
*)

(* typePrjAbbrev : asyncType -> asyncType asyncTypeF *)
fun typePrjAbbrev ty = case AsyncType.prj ty of
	  TAbbrev (a, ty) => typePrjAbbrev ty
	| A => A

(* nfTypePrjAbbrev : nfAsyncType -> nfAsyncType nfAsyncTypeF *)
fun nfTypePrjAbbrev ty = case NfAsyncType.prj ty of
	  TAbbrev (a, ty) => nfTypePrjAbbrev ty
	| A => A

(* apxTypePrjAbbrev : apxAsyncType -> apxAsyncType apxAsyncTypeF *)
fun apxTypePrjAbbrev ty = case ApxAsyncType.prj ty of
	  ApxTAbbrev (a, ty) => apxTypePrjAbbrev (asyncTypeToApx ty)
	| A => A

(* isNil : spine -> bool *)
fun isNil S = case Spine.prj S of Nil => true | _ => false

(* objAppKind : ((unit, unit, unit, unit) objFF -> unit) -> kind -> unit *)
(* objAppType : ((unit, unit, unit, unit) objFF -> unit) -> asyncType -> unit *)
(* objAppObj  : ((unit, unit, unit, unit) objFF -> unit) -> obj -> unit *)
fun ffsApp f =
	let val u = ignore
		fun fe (Let (_, h, _)) = f (Atomic h)
		  | fe _ = ()
	in {fki=u, faTy=u, ftyS=u, fsTy=u, fo=f, fsp=u, fe=fe, fm=u} end
fun objAppKind f = foldKind (ffsApp f)
fun objAppType f = foldType (ffsApp f)
fun objAppObj f = foldObj (ffsApp f)

(* objMapKind : (obj -> obj objF) -> kind -> kind *)
(* objMapType : (obj -> obj objF) -> asyncType -> asyncType *)
(* objMapSyncType : (obj -> obj objF) -> syncType -> syncType *)
(* objMapObj : (obj -> obj objF) -> obj -> obj *)
fun uffsMap f =
	let fun fe e = case ExpObj.prj e of
			  Let (p, hS, E) => (case f $ Atomic' hS of
					  Atomic hS' => Let (p, hS', E)
					| N => raise Fail "Internal error: objMap")
			| E => E
	in {fki=Kind.prj, faTy=AsyncType.prj, ftyS=TypeSpine.prj, fsTy=SyncType.prj,
		fo=f, fsp=Spine.prj, fe=fe, fm=MonadObj.prj} end
fun objMapKind f = unfoldKind (uffsMap f)
fun objMapType f = unfoldType (uffsMap f)
fun objMapSyncType f = unfoldSyncType (uffsMap f)
fun objMapObj f = unfoldObj (uffsMap f)

val ffsCopy = {fki=NfKind.inj, faTy=NfAsyncType.inj, ftyS=NfTypeSpine.inj, fsTy=NfSyncType.inj,
		fo=NfObj.inj, fsp=NfSpine.inj, fe=NfExpObj.inj, fm=NfMonadObj.inj}
val forceNormalizeKind = unnormalizeKind o (foldNfKind ffsCopy) o normalizeKind
val forceNormalizeType = unnormalizeType o (foldNfType ffsCopy) o normalizeType
val forceNormalizeObj = unnormalizeObj o (foldNfObj ffsCopy) o normalizeObj

structure NfExpObjAuxDefs = AuxDefs (structure T = Typ1From3 (structure T = NfExpObj))
val whnfLetSpine = unnormalizeExpObj o (NfExpObjAuxDefs.fold NfExpObj.inj) o normalizeExpObj

fun lvarTypeMap f (Atomic (LogicVar X, S)) =
		Atomic (LogicVar (X with'ty (f $ #ty X)), S)
  | lvarTypeMap _ N = N
fun removeApxKind a = objMapKind (lvarTypeMap removeApxType o Obj.prj) a
and removeApxType a = objMapType (lvarTypeMap removeApxType o Obj.prj) a
fun removeApxSyncType a = objMapSyncType (lvarTypeMap removeApxType o Obj.prj) a
fun removeApxObj a = objMapObj (lvarTypeMap removeApxType o Obj.prj) a
val asyncTypeFromApx = removeApxType o injectApxType
val syncTypeFromApx = removeApxSyncType o injectApxSyncType

(* pat2apxSyncType : pattern -> apxSyncType *)
fun pat2apxSyncType p = case Pattern.prj p of
	  PDepTensor (p1, p2) => ApxTTensor' (pat2apxSyncType p1, pat2apxSyncType p2)
	| POne => ApxTOne'
	| PDown _ => ApxTDown' $ newApxTVar ()
	| PAffi _ => ApxTAffi' $ newApxTVar ()
	| PBang _ => ApxTBang' $ newApxTVar ()

fun pConv _ _ (PDepTensor pp) = PDepTensor' pp
  | pConv _ _ POne = POne'
  | pConv f _ (PDown x) = PDown' (f x)
  | pConv f _ (PAffi x) = PAffi' (f x)
  | pConv _ f (PBang x) = PBang' (f x)
fun patternO2T p = OPatternRec.fold (pConv (fn _ => ()) SOME) p
fun patternT2O p = TPatternRec.fold (pConv (fn () => "") (fn x => getOpt (x, ""))) p

fun patternAddDep (p1, p2) = case (Pattern.prj p1, Pattern.prj p2) of
	  (PDepTensor (p11, p12), PDepTensor (p21, p22)) =>
		PDepTensor' (patternAddDep (p11, p21), patternAddDep (p12, p22))
	| (POne, POne) => POne'
	| (PDown (), PDown ()) => PDown' ()
	| (PAffi (), PAffi ()) => PAffi' ()
	| (PBang NONE, PBang NONE) => PBang' NONE
	| (PBang (SOME x), PBang NONE) => PBang' (SOME x)
	| (PBang NONE, PBang (SOME x)) => PBang' (SOME x)
	| (PBang (SOME x), PBang (SOME _)) => PBang' (SOME x)
	| _ => raise Fail "Internal error: patternAddDep pattern mismatch"


end
