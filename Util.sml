structure Util :> UTIL =
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
	| LogicVar {ty, s, ctx, ...} => objAppType f (TClos (ty, s))
and objAppSpine f sp = SpineAuxDefs.fold
	(fn App (ob, ()) => objAppObj f ob | LinApp (ob, ()) => objAppObj f ob | _ => ()) sp
and objAppExp f e = ExpObjAuxDefs.fold
	(fn Let (p, ob, ()) => (objAppPattern f p; objAppObj f ob) | Mon M => objAppMonad f M) e
and objAppMonad f m = MonadObjAuxDefs.fold
	(fn DepPair (ob, ()) => objAppObj f ob | Norm ob => objAppObj f ob | _ => ()) m
and objAppPattern f p = PatternAuxDefs.fold
	(fn PDepPair (_, A, ()) => objAppType f A | PVar (_, A) => objAppType f A | _ => ()) p

(* objExpMapKind : (expObj -> expObj expObjF) -> (obj -> obj objF) -> kind -> kind *)
(* objExpMapType : (expObj -> expObj expObjF) -> (obj -> obj objF) -> asyncType -> asyncType *)
(* objExpMapObj :  (expObj -> expObj expObjF) -> (obj -> obj objF) -> obj -> obj *)
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
	| LogicVar X => LogicVar X
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
