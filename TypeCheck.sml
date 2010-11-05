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

signature TLU_TypeCheck = TOP_LEVEL_UTIL
structure TypeCheck :> TYPECHECK =
struct

open Syntax
open Context
open PatternBind

val enabled = ref false
fun enable () = enabled := true
fun isEnabled () = !enabled

type context = nfAsyncType Context.context

fun checkKind (ctx, ki) = case NfKind.prj ki of
	  Type => ()
	| KPi (x, A, K) => (checkType (ctx, A); checkKind (ctxCondPushINT (x, A, ctx), K))

and checkType (ctx, ty) = case Util.nfTypePrjAbbrev ty of
	  TLPi (p, S, B) => (checkSyncType (ctx, S); checkType (tpatBindNf (p, S) ctx, B))
	| AddProd (A, B) => (checkType (ctx, A); checkType (ctx, B))
	| TMonad S => checkSyncType (ctx, S)
	| TAtomic (a, S) => checkTypeSpine (ctx, S, normalizeKind (Signatur.sigLookupKind a))
	| _ => raise Fail "Internal error: checkType match"

and checkTypeSpine (ctx, sp, ki) = case (NfTypeSpine.prj sp, NfKind.prj ki) of
	  (TNil, Type) => ()
	| (TNil, KPi _) => raise Fail "Wrong kind; expected Type\n"
	| (TApp _, Type) => raise Fail "Wrong kind; cannot apply Type\n"
	| (TApp (N, S), KPi (x, A, K)) =>
			let val _ = checkObj (ctx, N, A)
				val K' = if isSome x then NfKClos (K, Subst.subI N) else K
			in checkTypeSpine (ctx, S, K') end

and checkSyncType (ctx, ty) = case NfSyncType.prj ty of
	  LExists (p, S1, S2) => (checkSyncType (ctx, S1); checkSyncType (tpatBindNf (p, S1) ctx, S2))
	| TOne => ()
	| TDown A => checkType (ctx, A)
	| TAffi A => checkType (ctx, A)
	| TBang A => checkType (ctx, A)

(* Invariant:
 * checkObj (G, N, A) => G'
 * if G |- N <= A -| G'
 * otherwise Fail is raised
 *)
and checkObj (ctx, ob, ty) = case (NfObj.prj ob, Util.nfTypePrjAbbrev ty) of
	  (NfLLam (p, N), TLPi (p', A, B)) => patUnbind (p, checkObj (opatBindNf (p, A) ctx, N, B))
	| (NfAddPair (N, M), AddProd (A, B)) => ctxAddJoin (checkObj (ctx, N, A), checkObj (ctx, M, B))
	| (NfMonad E, TMonad S) => checkExp (ctx, E, S)
	| (NfAtomic hS, TAtomic _) =>
		let val (ctx2, ty2) = inferAtomic (ctx, hS)
			val () = Conv.convAsyncType (ty, ty2)
		in ctx2 end
(*      (Redex, Constraint cannot occur in a normal form -- cs *)
	| (NfAtomic _, _) => raise Fail "Type mismatch in checkObj: Eta"
	| _ => raise Fail "Type mismatch in checkObj"


(* Invariant:
 * inferAtomic (G, R) => (G', A')
 * if G |- R => A' -| G'
 * otherwise Fail is raised
 *)
and inferAtomic (ctx, (H, S)) =
	let val (ctx1, ty1) = inferHead (ctx, H)
	in inferSpine (ctx1, S, ty1) end

(* Invariant:
 * inferHead (G, R) => (G', A')
 * if G |- R => A' -| G'
 * otherwise Fail is raised
 *)
and inferHead (ctx, hd) = case hd of
	  Const c => (ctx, normalizeType (Signatur.sigLookupType c))
	| Var (m, n) =>
		let val (ctx1, m', A) = ctxLookupNum (ctx, n)
			val () = if m=m' then () else raise Fail "Linearity mismatch"
		in (ctx1, NfTClos (A, Subst.shift n)) end
	| LogicVar {ctx=ref NONE, ...} => raise Fail "Internal error: inferHead: no ctx"
	| LogicVar {ty, s, ctx=ref (SOME G), ...} => (checkSub (ctx, s, ctx2list G), NfTClos (ty, s))
(*     UCVar      should also be impossible -cs *)
	| _ => raise Fail "Type mismatch in inferhead"


(* Invariant:
 * checkSub (G1, s, G2) => G1'
 * if G1 |- s <= G2 -| G1'
 * otherwise Fail is raised
 *)
and checkSub (ctx, s', ctx') = case (Subst.subPrj s', ctx') of
	  (INR n, _::_) => checkSub (ctx, Subst.Dot (Idx (ID, n+1), Subst.shift (n+1)), ctx')
	| (INR n, []) => if ctxLength ctx = n then ctx else raise Fail "ctx/shift mismatch"
	| (INL _, []) => raise Fail "Substitution/context mismatch"
	| (INL (_, s), (_, A, NONE)::G') => checkSub (ctx, s, G')
	| (INL (Ob (LIN, M), s), (_, A, SOME LIN)::G') =>
		checkSub (checkObj (ctx, M, NfTClos (A, s)), s, G')
	| (INL (Ob (AFF, M), s), (_, A, SOME AFF)::G') =>
		let val ctxm = ctxJoinAffLin (checkObj (ctxAffPart ctx, M, NfTClos (A, s)), ctx)
		in checkSub (ctxm, s, G') end
	| (INL (Ob (INT, M), s), (_, A, SOME INT)::G') =>
		let val _ = checkObj (ctxIntPart ctx, M, NfTClos (A, s))
		in checkSub (ctx, s, G') end
	| (INL (Ob (_, M), s), (_, A, SOME _)::G') => raise Fail "Linearity mismatch"
	| (INL (Idx (ID, n), s), (_, A, SOME m)::G') =>
		checkSub (ctx, Subst.Dot (Ob (m, NfAtomic' (Var (m, n), NfInj.Nil')), s), ctx')
	| (INL (Idx (INT4LIN, n), s), (_, A, SOME _)::G') =>
		checkSub (ctx, Subst.Dot (Ob (LIN, NfAtomic' (Var (INT, n), NfInj.Nil')), s), ctx')
	| (INL (Idx (INT4AFF, n), s), (_, A, SOME _)::G') =>
		checkSub (ctx, Subst.Dot (Ob (AFF, NfAtomic' (Var (INT, n), NfInj.Nil')), s), ctx')
	| (INL (Idx (AFF4LIN, n), s), (_, A, SOME _)::G') =>
		checkSub (ctx, Subst.Dot (Ob (LIN, NfAtomic' (Var (AFF, n), NfInj.Nil')), s), ctx')
	| (INL (Undef, s), (_, A, SOME m)::G') => checkSub (ctx, s, G')


(* Invariant:
 * inferSpine (G, S, A) => (G', A')
 * if G |- S => A >> A' -| G'
 * otherwise Fail is raised
 *)
and inferSpine (ctx, sp, ty) = case (NfSpine.prj sp, Util.nfTypePrjAbbrev ty) of
	  (Nil, _) => (ctx, ty)
	| (LApp (M, S), TLPi (p, A, B)) =>
		let val ctx1 = checkMonad (ctx, M, A)
		in inferSpine (ctx1, S, NfTClos (B, Subst.subM M)) end
	| (ProjLeft S, AddProd (A, _)) => inferSpine (ctx, S, A)
	| (ProjRight S, AddProd (_, B)) => inferSpine (ctx, S, B)
	| _ => raise Fail "Type mismatch in inferSpine"

(* Invariant:
 * checkExp (G, E, S) => G'
 * if G |- E <= S -| G'
 * otherwise Fail is raised
 *)
and checkExp (ctx, exp, S) = case NfExpObj.prj exp of
	  NfLet (P, R, E)  =>
		let val (ctx1, ty) = inferAtomic (ctx, R)
			val sty = case Util.nfTypePrjAbbrev ty of
					  TMonad sty => sty
					| _ => raise Fail "Type checking: sync type expected"
			val () = checkPattern (P, sty)
			val ctx2 = opatBindNf (P, sty) ctx1
			val ctx3 = checkExp (ctx2, E, NfSTClos (S, Subst.shift (nbinds P)))
		in patUnbind (P, ctx3) end
	| NfMon M => checkMonad (ctx, M, S)

(* Invariant:
 * checkMonad (G, M, S) => G'
 * if G |- M <= S -| G'
 * otherwise Fail is raised
 *)
and checkMonad (ctx, mon, S) = case (NfMonadObj.prj mon, NfSyncType.prj S) of
	  (DepPair (M1, M2), LExists (p, S1, S2)) =>
		let val ctx1 = checkMonad (ctx, M1, S1)
		in checkMonad (ctx1, M2, NfSTClos (S2, Subst.subM M1)) end
     | (One, TOne) => ctx
     | (Down N, TDown A) => checkObj (ctx, N, A)
     | (Affi N, TAffi A) => ctxJoinAffLin (checkObj (ctxAffPart ctx, N, A), ctx)
     | (Bang N, TBang A) => let val _ = checkObj (ctxIntPart ctx, N, A) in ctx end
	 | (MonUndef, _) => raise Fail "Internal error: checkMonad: MonUndef"
     | _ => raise Fail "Type mismatch in checkMonad"

(* Invariant:
 * checkPattern (P, S) => ()
 * if |- P : S
 * otherwise Fail is raised
 *)
and checkPattern (pat, S) = case (Pattern.prj pat, NfSyncType.prj S) of
	  (PDepTensor (P1, P2), LExists (_, S1, S2)) =>
		(checkPattern (P1, S1); checkPattern (P2, S2))
	| (POne, TOne) => ()
	| (PDown _, TDown A2) => ()
	| (PAffi _, TAffi A2) => ()
	| (PBang _, TBang A2) => ()
	| _ => raise Fail "Type mismatch in checkPattern"


fun checkKindEC ki = checkKind (emptyCtx, normalizeKind ki)
fun checkTypeEC ty = checkType (emptyCtx, normalizeType ty)
fun checkObjEC (ob, ty) =
	( checkTypeEC ty
	; ignore (checkObj (emptyCtx, normalizeObj ob, normalizeType ty)) )

end
