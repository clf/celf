structure Util :> UTIL =
struct

open Syntax

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

fun map1 f (a, b) = (f a, b)
fun map2 f (a, b) = (a, f b)
fun map12 f g (a, b) = (f a, g b)

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
(* objMapObj : (obj -> obj objF) -> obj -> obj *)
fun uffsMap f = {fki=Kind.prj, faTy=AsyncType.prj, ftyS=TypeSpine.prj, fsTy=SyncType.prj,
		fo=f, fsp=Spine.prj, fe=ExpObj.prj, fm=MonadObj.prj, fp=Pattern.prj}
fun objMapKind f = unfoldKind (uffsMap f)
fun objMapType f = unfoldType (uffsMap f)
fun objMapObj f = unfoldObj (uffsMap f)

val ffsCopy = {fki=NfKind.inj, faTy=NfAsyncType.inj, ftyS=NfTypeSpine.inj, fsTy=NfSyncType.inj,
		fo=NfObj.inj, fsp=NfSpine.inj, fe=NfExpObj.inj, fm=NfMonadObj.inj, fp=NfPattern.inj}
val forceNormalizeKind = unnormalizeKind o (foldNfKind ffsCopy) o normalizeKind
val forceNormalizeType = unnormalizeType o (foldNfType ffsCopy) o normalizeType
val forceNormalizeObj = unnormalizeObj o (foldNfObj ffsCopy) o normalizeObj

structure NfExpObjAuxDefs = AuxDefs (structure T = Typ1From4 (structure T = NfExpObj))
val whnfLetSpine = unnormalizeExpObj o (NfExpObjAuxDefs.fold NfExpObj.inj) o normalizeExpObj

(* objAppKind : (unit objF -> unit) -> kind -> unit *)
(* objAppType : (unit objF -> unit) -> asyncType -> unit *)
(* objAppObj  : (unit objF -> unit) -> obj -> unit *)
(*
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
	| LogicVar {ty, s, ctx, ...} => objAppType f (TClos (ty, s))
and objAppSpine f sp = SpineAuxDefs.fold
	(fn App (ob, ()) => objAppObj f ob | LinApp (ob, ()) => objAppObj f ob | _ => ()) sp
and objAppExp f e = ExpObjAuxDefs.fold
	(fn Let (p, ob, ()) => (objAppPattern f p; objAppObj f ob) | Mon M => objAppMonad f M) e
and objAppMonad f m = MonadObjAuxDefs.fold
	(fn DepPair (ob, ()) => objAppObj f ob | Norm ob => objAppObj f ob | _ => ()) m
and objAppPattern f p = PatternAuxDefs.fold
	(fn PDepPair (_, A, ()) => objAppType f A | PVar (_, A) => objAppType f A | _ => ()) p
*)

(* objExpMapKind : (nfExpObj -> nfExpObj nfExpObjF) -> (nfObj -> nfObj nfObjF) -> nfKind -> nfKind *)
(* objExpMapType : (nfExpObj -> nfExpObj nfExpObjF) -> (nfObj -> nfObj nfObjF) -> nfAsyncType -> nfAsyncType *)
(* objExpMapObj :  (nfExpObj -> nfExpObj nfExpObjF) -> (nfObj -> nfObj nfObjF) -> nfObj -> nfObj *)
(*
fun objExpMapKind g f ki = NfKindAuxDefs.unfold
	((fn Type => Type | KPi (x, A, k) => KPi (x, objExpMapType g f A, k)) o NfKind.prj) ki
and objExpMapType g f ty = NfAsyncTypeAuxDefs.unfold
	((fn TMonad S => TMonad (objExpMapSyncType g f S)
	  | TAtomic (a, os, S) => TAtomic (a, map (objExpMapObj g f) os, objExpMapTSpine g f S)
	  | A => A) o NfAsyncType.prj) ty
and objExpMapTSpine g f sp = NfTypeSpineAuxDefs.unfold
	((fn TNil => TNil | TApp (ob, S) => TApp (objExpMapObj g f ob, S)) o NfTypeSpine.prj) sp
and objExpMapSyncType g f ty = NfSyncTypeAuxDefs.unfold
	((fn Exists (x, A, S) => Exists (x, objExpMapType g f A, S)
	   | Async A => Async (objExpMapType g f A)
	   | S => S) o NfSyncType.prj) ty
and objExpMapObj g f obj = NfObjAuxDefs.unfold
	((fn NfMonad E => NfMonad (objExpMapExp g f E)
	   | NfAtomic (H, A, S) => NfAtomic (objExpMapHead g f H, A, objExpMapSpine g f S)
(*	   | Redex (N, A, S) => Redex (N, A, objExpMapSpine g f S)
	   | Constraint (N, A) => Constraint (N, objExpMapType g f A)*)
	   | N => N) o f) obj
and objExpMapHead g f h = case h of
	  Const (c, os) => Const (c, raise Fail "stub: map (objExpMapObj g f) os")
	| LogicVar X => LogicVar X
	| _ => h
and objExpMapSpine g f sp = NfSpineAuxDefs.unfold
	((fn App (ob, S) => App (objExpMapObj g f ob, S)
	   | LinApp (ob, S) => LinApp (objExpMapObj g f ob, S)
	   | S => S) o NfSpine.prj) sp
and objExpMapExp g f e = NfExpObjAuxDefs.unfold
	((fn Let (p, (H, A, S), E) =>
				Let (objExpMapPattern g f p, (objExpMapHead g f H, A, objExpMapSpine g f S), E)
	   | Mon M => Mon (objExpMapMonad g f M)) o g) e
and objExpMapMonad g f m = NfMonadObjAuxDefs.unfold
	((fn DepPair (ob, M) => DepPair (objExpMapObj g f ob, M)
	   | Norm ob => Norm (objExpMapObj g f ob)
	   | M => M) o NfMonadObj.prj) m
and objExpMapPattern g f p = NfPatternAuxDefs.unfold
	((fn PDepPair (x, A, P) => PDepPair (x, objExpMapType g f A, P)
	   | PVar (x, A) => PVar (x, objExpMapType g f A)
	   | P => P) o NfPattern.prj) p
*)

(* objMapKind : (nfObj -> nfObj nfObjF) -> nfKind -> nfKind *)
(* objMapType : (nfObj -> nfObj nfObjF) -> nfAsyncType -> nfAsyncType *)
(* objMapObj : (nfObj -> nfObj nfObjF) -> nfObj -> nfObj *)
(*
val objMapKind = objExpMapKind NfExpObj.prj
val objMapType = objExpMapType NfExpObj.prj
val objMapObj = objExpMapObj NfExpObj.prj
*)

end
