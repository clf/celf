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

type context = nfAsyncType Context.context

val subI = Subst.subI o unnormalizeObj

fun checkKind (ctx, ki) = case NfKind.prj ki of
	  Type => ()
	| KPi (x, A, K) => (checkType (ctx, A); checkKind (ctxCondPushINT (x, A, ctx), K))

and checkType (ctx, ty) = case Util.nfTypePrjAbbrev ty of
	  Lolli (A, B) => (checkType (ctx, A); checkType (ctx, B))
	| TPi (x, A, B) => (checkType (ctx, A); checkType (ctxCondPushINT (x, A, ctx), B))
	| AddProd (A, B) => (checkType (ctx, A); checkType (ctx, B))
	| Top => ()
	| TMonad S => checkSyncType (ctx, S)
	| TAtomic (a, S) => checkTypeSpine (ctx, S, normalizeKind (Signatur.sigLookupKind a))
	| _ => raise Fail "Type mismatch in checkType"

and checkTypeSpine (ctx, sp, ki) = case (NfTypeSpine.prj sp, NfKind.prj ki) of
	  (TNil, Type) => ()
	| (TNil, KPi _) => raise Fail "Wrong kind; expected Type\n"
	| (TApp _, Type) => raise Fail "Wrong kind; cannot apply Type\n"
	| (TApp (N, S), KPi (x, A, K)) =>
			let val _ = checkObj (ctx, N, A)
				val K' = if isSome x then NfKClos (K, subI N) else K 
			in checkTypeSpine (ctx, S, K') end

and checkSyncType (ctx, ty) = case NfSyncType.prj ty of
	  TTensor (S1, S2) => (checkSyncType (ctx, S1); checkSyncType (ctx, S2))
	| TOne => ()
	| Exists (x, A, S) => (checkType (ctx, A); checkSyncType (ctxCondPushINT (x, A, ctx), S))
	| Async A => checkType (ctx, A)

(* Invariant:
   checkObj (G, N, A) => (G', T')
   if G |- N <= A -| G';T'
   otherwise Fail is raised 
*)
and checkObj (ctx, ob, ty) = case (NfObj.prj ob, Util.nfTypePrjAbbrev ty) of
        (NfLam (x, N), TPi (x', A, B)) => (*checkObj (ctxPushINT (x, A, ctx), N, B)*)
			let val B' = if isSome x' then B else NfTClos (B, Subst.shift 1)
				val (ctxo, t) = checkObj (ctxPushINT (x, A, ctx), N, B')
			in (ctxPopINT ctxo, t) end
      | (NfLinLam (x, N), Lolli (A, B)) => (*checkObj (ctxPushLIN (x, A, ctx), N, B)*)
			let val (ctxo, t) = checkObj (ctxPushLIN (x, A, ctx), N, NfTClos (B, Subst.shift 1))
			in (ctxPopLIN (t, ctxo), t) end
      | (NfAddPair (N, M), AddProd (A, B)) => 
	  let 
	    val (ctx1, tf1) = checkObj (ctx, N, A)
	    val (ctx2, tf2) = checkObj (ctx, M, B)
	  in
	    (ctxAddJoin (tf1, tf2) (ctx1, ctx2), tf1 andalso tf2)	   
	  end
      | (NfUnit, Top) => (ctx, true)
      | (NfMonad E, TMonad S) => checkExp (ctx, E, S)
      | (NfAtomic hS , TAtomic _) =>
	  let
	    val (ctx2, tf2, ty2) = inferAtomic (ctx, hS) 
	    val _ = Conv.convAsyncType (ty, ty2)
	  in 
	     (ctx2, tf2)
	  end
(*      (Redex, Constraint cannot occur in a normal form -- cs *)
      | (NfAtomic _, _) => raise Fail "Type mismatch in checkObj: Eta"
      | _ => raise Fail "Type mismatch in checkObj"


(* Invariant:
   inferAtomic (G, R) => (G', T', A')
   if G |- R => A' -| G';T'
   otherwise Fail is raised 
*)
and inferAtomic (ctx, (H, S)) =
	  let
	    val (ctx1, tf1, ty1) = inferHead (ctx, H)
	    val (ctx2, tf2, ty2) = inferSpine (ctx1, S, ty1) 
	  in 
	     (ctx2, tf1 orelse tf2 , ty2)
	  end

(* Invariant:
   inferHead (G, R) => (G', T', A')
   if G |- R => A' -| G';T' 
   otherwise Fail is raised 
*)
and inferHead (ctx, hd) = case hd of
        Const c => (ctx, false, normalizeType (Signatur.sigLookupType c))
     | Var (m, n) => 
	  let 
	    val (ctx1, m', A) = ctxLookupNum (ctx, n)     (* think about shifting  --cs *)
	    val () = if m=m' then () else raise Fail "Linearity mismatch"
	  in 
	    (ctx1, false, NfTClos (A, Subst.shift n)) 
	  end
(*     UCVar, LogicVar      should also be impossible -cs *)
      | _ => raise Fail "Type mismatch in inferhead"
 
	
(* Invariant:
   inferSpine (G, S, A) => (G', T', A')
   if G |- S => A >> A' -| G';T'
   otherwise Fail is raised 
*)
and inferSpine (ctx, sp, ty) = case (NfSpine.prj sp, Util.nfTypePrjAbbrev ty) of
       (Nil, _) => (ctx, false, ty) 
     | (App (N, S), TPi (x, A, B)) =>
	 let
	   val (_, _) = checkObj (ctxDelLin ctx, N, A)
	   val B' = if isSome x then NfTClos (B, subI N) else B
	   val (ctx1, tf1, ty) = inferSpine (ctx, S, B')
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
and checkExp (ctx, exp, S) = case (NfExpObj.prj exp) of 
       (Let (P, R, E))  => 
	 let 
	   val (ctx1, tf1, ty) = inferAtomic (ctx, R)
	   val _ = case Util.nfTypePrjAbbrev ty of
	                TMonad S' => checkPattern (ctx1, P, S')
			  | _ => raise Fail "Type checking: sync type expected"
	   val ctx2 = patBind normalizeType (unnormalizePattern P) ctx1
	   val (ctx3, tf3) = checkExp (ctx2, E, NfSTClos (S, Subst.shift (nfnbinds P)))
	   val ctx4 = patUnbind (unnormalizePattern P, ctx3, tf3)
	 in
	   (ctx4, tf1 orelse tf3)
	 end
     | (Mon M) => checkMonad (ctx, M, S)

(* Invariant:
   checkMonad (G, M, S) => (G', T')
   if G |- M <= S -| G';T'
   otherwise Fail is raised 
*)
and checkMonad (ctx, mon, S) = case (NfMonadObj.prj mon, NfSyncType.prj S) of
       (Tensor (M1, M2), TTensor (S1, S2)) => 
	 let 
	   val (ctx1, tf1) = checkMonad (ctx, M1, S1)
	   val (ctx2, tf2) = checkMonad (ctx1, M2, S2)
	 in
	   (ctx2, tf1 orelse tf2)
	 end
     | (One, TOne) => (ctx, false) 
     | (DepPair (N, M), Exists (x, A, S)) => 
			let val _ = checkObj (ctxDelLin ctx, N, A)
				val S' = if isSome x then NfSTClos (S, subI N) else S
			in checkMonad (ctx, M, S') end
     | (Norm N, Async A) => checkObj (ctx, N, A) 
     | _ => raise Fail "Type mismatch in checkMonad"

(* Invariant:
   checkPattern (G, P, S) => ()
   if G |- P : S 
   otherwise Fail is raised 
*)
and checkPattern (ctx, pat, S) = case (NfPattern.prj pat, NfSyncType.prj S) of
       (PTensor (P1, P2), TTensor (S1, S2)) => 
	 (checkPattern (ctx, P1, S1);
	 checkPattern (ctx, P2, S2))
     | (POne, TOne) => ()
     | (PDepPair (s, A1, P), Exists (x, A2, S)) => 
		let val S' = if isSome x then S else NfSTClos (S, Subst.shift 1)
		in checkType (ctx, A1)
		 ; Conv.convAsyncType (A1, A2)
		 ; checkPattern (ctxPushINT (s, A2, ctx), P, S')
		end
     | (PVar (_, A1), Async A2) => 
	 (checkType (ctx, A1); Conv.convAsyncType (A1, A2))
     | _ => raise Fail "Type mismatch in checkPattern"


fun checkKindEC ki = checkKind (emptyCtx, normalizeKind ki)
fun checkTypeEC ty = checkType (emptyCtx, normalizeType ty)
fun checkObjEC (ob, ty) =
	( checkTypeEC ty
	; ignore (checkObj (emptyCtx, normalizeObj ob, normalizeType ty)) )

end
