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

structure Util :> UTIL =
struct

open Syntax infix with'ty

structure ObjAuxDefs = AuxDefs (structure T = Typ1From4 (structure T = Obj))
(*structure ExpObjAuxDefs = AuxDefs (structure T = Typ1From4 (structure T = ExpObj))*)

structure KindRec = Rec2 (structure T = Kind)
structure AsyncTypeRec = Rec3 (structure T = AsyncType)
structure TypeSpineRec = Rec2 (structure T = TypeSpine)
structure SyncTypeRec = Rec2 (structure T = SyncType)
structure ObjRec = Rec4 (structure T = Obj)
structure SpineRec = Rec2 (structure T = Spine)
structure ExpObjRec = Rec4 (structure T = ExpObj)
structure MonadObjRec = Rec2 (structure T = MonadObj)
structure PatternRec = Rec2 (structure T = Pattern)

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm, 'p) foldFuns = {
	fki  : ('aTy, 'ki) kindFF -> 'ki,
	faTy : ('tyS, 'sTy, 'aTy) asyncTypeFF -> 'aTy,
	ftyS : ('o, 'tyS) typeSpineFF -> 'tyS,
	fsTy : ('aTy, 'sTy) syncTypeFF -> 'sTy,
	fo   : ('aTy, 'sp, 'e, 'o) objFF -> 'o,
	fsp  : ('o, 'sp) spineFF -> 'sp,
	fe   : ('o, 'm, 'p, 'e) expObjFF -> 'e,
	fm   : ('o, 'm) monadObjFF -> 'm,
	fp   : ('aTy, 'p) patternFF -> 'p }

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm, 'p) unfoldFuns = {
	fki  : 'ki -> ('aTy, 'ki) kindFF,
	faTy : 'aTy -> ('tyS, 'sTy, 'aTy) asyncTypeFF,
	ftyS : 'tyS -> ('o, 'tyS) typeSpineFF,
	fsTy : 'sTy -> ('aTy, 'sTy) syncTypeFF,
	fo   : 'o -> ('aTy, 'sp, 'e, 'o) objFF,
	fsp  : 'sp -> ('o, 'sp) spineFF,
	fe   : 'e -> ('o, 'm, 'p, 'e) expObjFF,
	fm   : 'm -> ('o, 'm) monadObjFF,
	fp   : 'p -> ('aTy, 'p) patternFF }

fun foldKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm, 'p) foldFuns) x =
		KindRec.fold (foldType fs) (#fki fs) x
and foldType fs x = AsyncTypeRec.fold (foldTypeSpine fs, foldSyncType fs) (#faTy fs) x
and foldTypeSpine fs x = TypeSpineRec.fold (foldObj fs) (#ftyS fs) x
and foldSyncType fs x = SyncTypeRec.fold (foldType fs) (#fsTy fs) x
and foldObj fs x = ObjRec.fold (foldType fs, foldSpine fs, foldExpObj fs) (#fo fs) x
and foldSpine fs x = SpineRec.fold (foldObj fs) (#fsp fs) x
and foldExpObj fs x = ExpObjRec.fold (foldObj fs, foldMonadObj fs, foldPattern fs) (#fe fs) x
and foldMonadObj fs x = MonadObjRec.fold (foldObj fs) (#fm fs) x
and foldPattern fs x = PatternRec.fold (foldType fs) (#fp fs) x

fun unfoldKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm, 'p) unfoldFuns) x =
		KindRec.unfold (unfoldType fs) (#fki fs) x
and unfoldType fs x = AsyncTypeRec.unfold (unfoldTypeSpine fs, unfoldSyncType fs) (#faTy fs) x
and unfoldTypeSpine fs x = TypeSpineRec.unfold (unfoldObj fs) (#ftyS fs) x
and unfoldSyncType fs x = SyncTypeRec.unfold (unfoldType fs) (#fsTy fs) x
and unfoldObj fs x = ObjRec.unfold (unfoldType fs, unfoldSpine fs, unfoldExpObj fs) (#fo fs) x
and unfoldSpine fs x = SpineRec.unfold (unfoldObj fs) (#fsp fs) x
and unfoldExpObj fs x = ExpObjRec.unfold (unfoldObj fs, unfoldMonadObj fs, unfoldPattern fs) (#fe fs) x
and unfoldMonadObj fs x = MonadObjRec.unfold (unfoldObj fs) (#fm fs) x
and unfoldPattern fs x = PatternRec.unfold (unfoldType fs) (#fp fs) x

structure NfKindRec = Rec2 (structure T = NfKind)
structure NfAsyncTypeRec = Rec3 (structure T = NfAsyncType)
structure NfTypeSpineRec = Rec2 (structure T = NfTypeSpine)
structure NfSyncTypeRec = Rec2 (structure T = NfSyncType)

structure NfObjRec = Rec3 (structure T = NfObj)
structure NfSpineRec = Rec2 (structure T = NfSpine)
structure NfExpObjRec = Rec4 (structure T = NfExpObj)
structure NfMonadObjRec = Rec2 (structure T = NfMonadObj)
structure NfPatternRec = Rec2 (structure T = NfPattern)

type ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm, 'p) nfFoldFuns = {
	fki  : ('aTy, 'ki) kindFF -> 'ki,
	faTy : ('tyS, 'sTy, 'aTy) asyncTypeFF -> 'aTy,
	ftyS : ('o, 'tyS) typeSpineFF -> 'tyS,
	fsTy : ('aTy, 'sTy) syncTypeFF -> 'sTy,
	fo   : ('sp, 'e, 'o) nfObjFF -> 'o,
	fsp  : ('o, 'sp) spineFF -> 'sp,
	fe   : (nfHead * 'sp, 'm, 'p, 'e) expObjFF -> 'e,
	fm   : ('o, 'm) monadObjFF -> 'm,
	fp   : ('aTy, 'p) patternFF -> 'p }

fun foldNfKind (fs : ('ki, 'aTy, 'tyS, 'sTy, 'o, 'sp, 'e, 'm, 'p) nfFoldFuns) x =
		NfKindRec.fold (foldNfType fs) (#fki fs) x
and foldNfType fs x = NfAsyncTypeRec.fold (foldNfTypeSpine fs, foldNfSyncType fs) (#faTy fs) x
and foldNfTypeSpine fs x = NfTypeSpineRec.fold (foldNfObj fs) (#ftyS fs) x
and foldNfSyncType fs x = NfSyncTypeRec.fold (foldNfType fs) (#fsTy fs) x
and foldNfObj fs x = NfObjRec.fold (foldNfSpine fs, foldNfExpObj fs) (#fo fs) x
and foldNfSpine fs x = NfSpineRec.fold (foldNfObj fs) (#fsp fs) x
and foldNfExpObj fs x = NfExpObjRec.fold (foldNfSpine fs, foldNfMonadObj fs, foldNfPattern fs) (#fe fs) x
and foldNfMonadObj fs x = NfMonadObjRec.fold (foldNfObj fs) (#fm fs) x
and foldNfPattern fs x = NfPatternRec.fold (foldNfType fs) (#fp fs) x

fun linApp (ob1, ob2) = Redex' (ob1, newApxTVar (), LinApp' (ob2, Nil'))
fun app (ob1, ob2) = Redex' (ob1, newApxTVar (), App' (ob2, Nil'))
fun projLeft ob = Redex' (ob, newApxTVar (), ProjLeft' Nil')
fun projRight ob = Redex' (ob, newApxTVar (), ProjRight' Nil')
fun blank () = newLVar (newTVar ())
fun headToObj h = Atomic' (h, Nil')

fun linLamConstr (x, A, N) = Constraint' (LinLam' (x, N), Lolli' (A, newTVar ()))
fun lamConstr (x, A, N) = Constraint' (Lam' (x, N), TPi' (SOME x, A, newTVar ()))

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
fun ffsApp f = let val u = ignore in
		{fki=u, faTy=u, ftyS=u, fsTy=u, fo=f, fsp=u, fe=u, fm=u, fp=u} end
fun objAppKind f = foldKind (ffsApp f)
fun objAppType f = foldType (ffsApp f)
fun objAppObj f = foldObj (ffsApp f)

(* objMapKind : (obj -> obj objF) -> kind -> kind *)
(* objMapType : (obj -> obj objF) -> asyncType -> asyncType *)
(* objMapSyncType : (obj -> obj objF) -> syncType -> syncType *)
(* objMapObj : (obj -> obj objF) -> obj -> obj *)
fun uffsMap f = {fki=Kind.prj, faTy=AsyncType.prj, ftyS=TypeSpine.prj, fsTy=SyncType.prj,
		fo=f, fsp=Spine.prj, fe=ExpObj.prj, fm=MonadObj.prj, fp=Pattern.prj}
fun objMapKind f = unfoldKind (uffsMap f)
fun objMapType f = unfoldType (uffsMap f)
fun objMapSyncType f = unfoldSyncType (uffsMap f)
fun objMapObj f = unfoldObj (uffsMap f)

(* objSRigMapKind : (bool -> obj -> obj objF) -> bool -> kind -> kind *)
(* objSRigMapType : (bool -> obj -> obj objF) -> bool -> asyncType -> asyncType *)
(* objSRigMapObj : (bool -> obj -> obj objF) -> bool -> obj -> obj *)
(* boolean flag indicates a strong rigid context *)
fun pair f y = (f, y)
fun sr2 fmap prj (f, x) = fmap (pair f, pair f) (prj x)
fun sr3 fmap prj (f, x) = fmap ((pair f, pair f), pair f) (prj x)
fun sr4 fmap prj (f, x) = fmap ((pair f, pair f, pair f), pair f) (prj x)
fun sr4' fmap prj (f, x) = fmap ((pair f, pair f, pair f), pair f) (prj f x)
fun checkSRig (Atomic (v as Var _, (_, S))) = (Atomic (v, (false, S)))
  | checkSRig (Atomic (v as LogicVar _, (_, S))) = (Atomic (v, (false, S)))
  | checkSRig N = N
fun uffsSRigMap f = {fki=sr2 Kind.Fmap Kind.prj, faTy=sr3 AsyncType.Fmap AsyncType.prj,
		ftyS=sr2 TypeSpine.Fmap TypeSpine.prj, fsTy=sr2 SyncType.Fmap SyncType.prj,
		fo=checkSRig o (sr4' Obj.Fmap f), fsp=sr2 Spine.Fmap Spine.prj,
		fe=sr4 ExpObj.Fmap ExpObj.prj, fm=sr2 MonadObj.Fmap MonadObj.prj,
		fp=sr2 Pattern.Fmap Pattern.prj}
fun objSRigMapKind f srig k = unfoldKind (uffsSRigMap f) (srig, k)
fun objSRigMapType f srig t = unfoldType (uffsSRigMap f) (srig, t)
fun objSRigMapSyncType f srig t = unfoldSyncType (uffsSRigMap f) (srig, t)
fun objSRigMapObj f srig x = unfoldObj (uffsSRigMap f) (srig, x)

val ffsCopy = {fki=NfKind.inj, faTy=NfAsyncType.inj, ftyS=NfTypeSpine.inj, fsTy=NfSyncType.inj,
		fo=NfObj.inj, fsp=NfSpine.inj, fe=NfExpObj.inj, fm=NfMonadObj.inj, fp=NfPattern.inj}
val forceNormalizeKind = unnormalizeKind o (foldNfKind ffsCopy) o normalizeKind
val forceNormalizeType = unnormalizeType o (foldNfType ffsCopy) o normalizeType
val forceNormalizeObj = unnormalizeObj o (foldNfObj ffsCopy) o normalizeObj

structure NfExpObjAuxDefs = AuxDefs (structure T = Typ1From4 (structure T = NfExpObj))
val whnfLetSpine = unnormalizeExpObj o (NfExpObjAuxDefs.fold NfExpObj.inj) o normalizeExpObj

fun lvarTypeMap f (Atomic (LogicVar X, S)) = Atomic (LogicVar (X with'ty (f (#ty X))), S)
  | lvarTypeMap _ N = N
fun removeApxKind a = objMapKind (lvarTypeMap removeApxType o Obj.prj) a
and removeApxType a = objMapType (lvarTypeMap removeApxType o Obj.prj) a
fun removeApxSyncType a = objMapSyncType (lvarTypeMap removeApxType o Obj.prj) a
fun removeApxObj a = objMapObj (lvarTypeMap removeApxType o Obj.prj) a
val asyncTypeFromApx = removeApxType o injectApxType
val syncTypeFromApx = removeApxSyncType o injectApxSyncType

(* pat2apxSyncType : pattern -> apxSyncType *)
fun pat2apxSyncType p = case Pattern.prj p of
	  PTensor (p1, p2) => ApxTTensor' (pat2apxSyncType p1, pat2apxSyncType p2)
	| POne => ApxTOne'
	| PDepPair (x, A, p) => ApxExists' (asyncTypeToApx A, pat2apxSyncType p)
	| PVar (x, A) => ApxAsync' (asyncTypeToApx A)


end
