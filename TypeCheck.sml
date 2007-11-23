(* Convertibility among CLF terms and types *)
(* Author: Carsten Schuermann *)

structure TypeCheck :> TYPECHECK =
struct

open Syntax
open Context
open PatternBind

val enabled = ref false
fun enable () = enabled := true
fun isEnabled () = !enabled

type context = asyncType Context.context


fun checkKind (ctx, ki) = raise Fail "Unimplemented"

and checkType (ctx, ty) = raise Fail "Unimplemented"

and checkTypeSpine (ctx, tyS, ki) = raise Fail "Unimplemented"

and checkSyncType (ctx, sty) = raise Fail "Unimplemented"

(* Invariant:
   checkObj (G, N, A) => (G', T')
   if G |- N <= A -| G';T'
   otherwise Fail is raised 
*)
and checkObj (ctx, ob, ty) = case (Obj.prj ob, Util.typePrjAbbrev ty) of
        (Lam (x, N), TPi (_, A, B)) => checkObj (ctxPushUN (x, A, ctx), N, B)
      | (LinLam (x, N), Lolli (A, B)) => checkObj (ctxPushLIN (x, A, ctx), N, B)
      | (AddPair (N, M), AddProd (A, B)) => 
	  let 
	    val (ctx1, tf1) = checkObj (ctx, N, A)
	    val (ctx2, tf2) = checkObj (ctx, M, B)
	  in
	    (ctxAddJoin (tf1, tf2) (ctx1, ctx2), tf1 andalso tf2)	   
	  end
      | (Unit, Top) => (ctx, true)
      | (Monad E, TMonad S) => checkExp (ctx, E, S)
      | (Atomic (H, _, S) , TAtomic _) =>
	  let
	    val (ctx2, tf2, ty2) = inferAtomic (ctx, ob) 
	    val _ = Conv.convAsyncType (ty, ty2)
	  in 
	     (ctx2, tf2)
	  end
(*      (Redex, Constraint cannot occur in a normal form -- cs *)
      | _ => raise Fail "Type mismatch in checkObj"


(* Invariant:
   inferAtomic (G, R) => (G', T', A')
   if G |- R => A' -| G';T'
   otherwise Fail is raised 
*)
and inferAtomic (ctx, ob) = case (Obj.prj ob) of 
       (Atomic (H, _, S)) =>
	  let
	    val (ctx1, tf1, ty1) = inferHead (ctx, H)
	    val (ctx2, tf2, ty2) = inferSpine (ctx1, S, ty1) 
	  in 
	     (ctx2, tf1 orelse tf2 , ty2)
	  end
      | _ => raise Fail "Type mismatch in checkObj"

(* Invariant:
   inferHead (G, R) => (G', T', A')
   if G |- R => A' -| G';T' 
   otherwise Fail is raised 
*)
and inferHead (ctx, hd) = case hd of
        Const c => (ctx, false, Signatur.sigLookupType c)
     | Var n => 
	  let 
	    val (ctx1, A) = ctxLookupNum (ctx, n)     (* think about shifting  --cs *)
	  in 
	    (ctx1, false, TClos (A, Subst.shift n)) 
	  end
(*     UCVar, LogicVar      should also be impossible -cs *)
      | _ => raise Fail "Type mismatch in inferhead"
 
	
(* Invariant:
   inferSpine (G, S, A) => (G', T', A')
   if G |- S => A >> A' -| G';T'
   otherwise Fail is raised 
*)
and inferSpine (ctx, sp, ty) = case (Spine.prj sp, AsyncType.prj ty) of
       (Nil, _) => (ctx, false, ty) 
     | (App (N, S), TPi (_, A, B)) =>
	 let
	   val (_, _) = checkObj (ctxDelLin ctx, N, A)
	   val (ctx1, tf1, ty) = inferSpine (ctx, S, TClos (B, Subst.sub N))
	 in
	   (ctx1, tf1, ty)
	 end
     | (LinApp (N, S), Lolli (A, B)) => 
	 let 
	   val (ctx1, tf1) = checkObj (ctx, N, A)
	   val (ctx2, tf2, ty) = inferSpine (ctx1, S, B)
	 in
	   (ctx2, tf1 orelse tf2, ty)
	 end
     | (ProjLeft (S), AddProd (A, _)) => inferSpine (ctx, S, A) 
     | (ProjRight (S), AddProd (_, B)) => inferSpine (ctx, S, B)
     | _ => raise Fail "Type mismatch in inferSpine"

(* Invariant:
   checkExp (G, E, S) => (G', T')
   if G |- E <= S -| G';T'
   otherwise Fail is raised 
*)
and checkExp (ctx, exp, S) = case (ExpObj.prj exp) of 
       (Let (P, R, E))  => 
	 let 
	   val (ctx1, tf1, ty) = inferAtomic (ctx, R)
	   val _ = case (Util.typePrjAbbrev ty) of
	                (TMonad S') => checkPattern (ctx1, P, S')
			  | _ => raise Fail "Type checking: sync type expected"
	   val ctx2 = patBind (fn x=>x) P ctx1
	   val (ctx3, tf3) = checkExp (ctx2, E, STClos (S, Subst.shift (nbinds P)))
	   val ctx4 = patUnbind (P, ctx3, tf3)
	 in
	   (ctx4, tf1 orelse tf3)
	 end
     | (Mon M) => checkMonad (ctx, M, S)

(* Invariant:
   checkMonad (G, M, S) => (G', T')
   if G |- M <= S -| G';T'
   otherwise Fail is raised 
*)
and checkMonad (ctx, mon, S) = case (MonadObj.prj mon, SyncType.prj S) of
       (Tensor (M1, M2), TTensor (S1, S2)) => 
	 let 
	   val (ctx1, tf1) = checkMonad (ctx, M1, S1)
	   val (ctx2, tf2) = checkMonad (ctx1, M2, S2)
	 in
	   (ctx2, tf1 orelse tf2)
	 end
     | (One, TOne) => (ctx, false) 
     | (DepPair (N, M), Exists (_, A, S)) => 
	 (checkObj (ctxDelLin ctx, N, A); checkMonad (ctx, M, STClos (S, Subst.sub N)))
     | (Norm N, Async A) => checkObj (ctx, N, A) 
     | _ => raise Fail "Type mismatch in checkMonad"

(* Invariant:
   checkPattern (G, P, S) => ()
   if G |- P : S 
   otherwise Fail is raised 
*)
and checkPattern (ctx, pat, S) = case (Pattern.prj pat, SyncType.prj S) of
       (PTensor (P1, P2), TTensor (S1, S2)) => 
	 (checkPattern (ctx, P1, S1);
	 checkPattern (ctx, P2, S2))
     | (POne, TOne) => ()
     | (PDepPair (s, A1, P), Exists (_, A2, S)) => 
	 (Conv.convAsyncType (A1, A2); checkPattern (ctxPushUN (s, A2, ctx), P, S))
     | (PVar (_, A1), Async A2) => 
	 Conv.convAsyncType (A1, A2)
     | _ => raise Fail "Type mismatch in checkPattern"


fun checkKindEC ki = checkKind (emptyCtx, ki)
fun checkTypeEC ty = checkType (emptyCtx, ty)
fun checkObjEC (ob, ty) =
	( checkTypeEC ty
	; ignore (checkObj (emptyCtx, ob, ty)) )

end
