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

signature TLU_ExactTypes = TOP_LEVEL_UTIL
structure ExactTypes :> EXACTTYPES =
struct

open Syntax
open Context
open PatternBind
open Unify

val traceExact = ref false

type context = asyncType Context.context

(* checkKind : context * kind -> unit *)
fun checkKind (ctx, ki) = case Kind.prj ki of
	  Type => ()
	| KPi (x, A, K) => (checkType (ctx, A); checkKind (ctxCondPushINT (x, A, ctx), K))

(* checkType : context * asyncType -> unit *)
and checkType (ctx, ty) =
	( if !traceExact then
		( print "Checking: "
		; app (fn (x, A, _) => print (x^":"^PrettyPrint.printType A^", ")) (ctx2list ctx)
		; print ("|- "^PrettyPrint.printType ty^" : Type\n") )
	  else ()
	; checkType' (ctx, ty) )
and checkType' (ctx, ty) = case AsyncType.prj ty of
	  TLPi (p, S, B) => (checkSyncType (ctx, S); checkType (tpatBind (p, S) ctx, B))
	| AddProd (A, B) => (checkType (ctx, A); checkType (ctx, B))
	| TMonad S => checkSyncType (ctx, S)
	| TAtomic (a, S) =>
		checkTypeSpine (fn () => PrettyPrint.printType ty) (ctx, S, Signatur.sigLookupKind a)
	| TAbbrev aA => ()

(* checkTypeSpine : (unit -> string) -> context * typeSpine * kind -> unit *)
(* checks that the spine is : ki > Type *)
and checkTypeSpine ty (ctx, sp, ki) = case (TypeSpine.prj sp, Kind.prj ki) of
	  (TNil, Type) => ()
	| (TNil, KPi _) =>
		raise ExnDeclError (KindErr, "Type " ^ ty () ^ " is not well-kinded; too few arguments\n")
	| (TApp _, Type) =>
		raise ExnDeclError (KindErr, "Type " ^ ty () ^ " is not well-kinded; too many arguments\n")
	| (TApp (N, S), KPi (x, A, K)) =>
			let val _ = checkObj (ctx, N, A)
				val K' = if isSome x then KClos (K, Subst.subI $ normalizeObj N) else K 
			in checkTypeSpine ty (ctx, S, K') end

(* checkSyncType : context * syncType -> unit *)
and checkSyncType (ctx, ty) = case SyncType.prj ty of
	  LExists (p, S1, S2) => (checkSyncType (ctx, S1); checkSyncType (tpatBind (p, S1) ctx, S2))
	| TOne => ()
	| TDown A => checkType (ctx, A)
	| TAffi A => checkType (ctx, A)
	| TBang A => checkType (ctx, A)

(* checkObj : context * obj * asyncType -> context *)
and checkObj (ctx, ob, ty) =
	( if !traceExact then
		( print "Checking: "
		; app (fn (x, A, _) => print (x^":"^PrettyPrint.printType A^", ")) (ctx2list ctx)
		; print ("|- "^PrettyPrint.printObj ob^" : "^PrettyPrint.printType ty^"\n") )
	  else ()
	; checkObj' (ctx, ob, ty) )
and checkObj' (ctx, ob, ty) = case (Obj.prj ob, Util.typePrjAbbrev ty) of
	  (LLam (p, N), TLPi (_, S, B)) => patUnbind (p, checkObj (opatBind (p, S) ctx, N, B))
	| (AddPair (N1, N2), AddProd (A, B)) =>
			ctxAddJoin (checkObj (ctx, N1, A), checkObj (ctx, N2, B))
	| (Monad E, TMonad S) => checkExp (ctx, E, S)
	| (Atomic (H, S), A) =>
			let val (ctxm, B) = inferHead (ctx, H)
				val (ctxo, A') = inferSpine (ctxm, S, B)
				fun errmsg () = "Object "^(PrettyPrint.printObj ob)
							^" has type:\n"^(PrettyPrint.printType A')
							^"\nbut expected:\n"^(PrettyPrint.printType ty)
				val () = unify (AsyncType.inj A, A', errmsg)
			in ctxo end
	| (Redex (N, B, S), A) =>
			let val B' = Util.asyncTypeFromApx B
				val () = checkType (ctxIntPart ctx, B')
				val ctxm = checkObj (ctx, N, B')
				val (ctxo, A') = inferSpine (ctxm, S, B')
				fun errmsg () = "Object "^(PrettyPrint.printObj ob)
							^" has type:\n"^(PrettyPrint.printType A')
							^"\nbut expected:\n"^(PrettyPrint.printType ty)
				val () = unify (AsyncType.inj A, A', errmsg)
			in ctxo end
	| (Constraint (N, A'), A) =>
			let val () = checkType (ctxIntPart ctx, A')
				fun errmsg () = "Object "^(PrettyPrint.printObj N)
							^" has ascribed type:\n"^(PrettyPrint.printType A')
							^"\nbut expected:\n"^(PrettyPrint.printType ty)
				val () = unify (AsyncType.inj A, A', errmsg)
			in checkObj (ctx, N, A') end
	| _ => raise Fail "Internal error: checkObj match"

(* inferHead : context * head -> context * asyncType *)
and inferHead (ctx, h) = case h of
	  Const c => (ctx, Signatur.sigLookupType c)
	| Var (m, n) =>
			let val (ctxo, m', A) = ctxLookupNum (ctx, n)
				val () = if m=m' then () else raise Fail "Internal error: Linearity mismatch"
			in (ctxo, TClos (A, Subst.shift n)) end
	| UCVar x =>
			(ctx, TClos (ImplicitVars.ucLookup x, Subst.shift $ ctxLength ctx))
	| LogicVar {X, ty, s, ctx=rctx, ...} =>
			let val calcCtx' = Unify.pruneCtx
						(Fail "Internal error: inferHead:pruning lin") (fn A => A)
				fun calcCtx si c = ctxMap unnormalizeType $ calcCtx' si $ ctxMap normalizeType c
				val s = case Subst.isWeaken s of SOME s => Subst.coerce2p_ s
						| NONE => raise Fail "Internal error: inferHead:unexpected substitution"
				val lvarCtx = calcCtx (Subst.invert s) $ ctxIntPart ctx
				val () = case !rctx of
						  NONE => rctx := SOME lvarCtx
						| SOME prevCtx => (*raise Fail "Internal error: double ctx instantiation"*)
							(* This can happen by eta-expansion of additive pairs *)
							if ctxLength prevCtx = ctxLength lvarCtx then () else
								raise Fail "Internal error: lvar 2x ctx mismatch"
				val () = checkType ((*ctxIntPart*) lvarCtx, ty)
				val () = Unify.pruneLVar $ normalizeHead h
			in (ctx, TClos (ty, s)) end

(* inferSpine : context * spine * asyncType -> context * asyncType *)
and inferSpine (ctx, sp, ty) = case (Spine.prj sp, Util.typePrjAbbrev ty) of
	  (Nil, A) => (ctx, ty)
	| (LApp (M, S), TLPi (_, A, B)) =>
			let val ctxm = checkMonadObj (ctx, M, A)
			in inferSpine (ctxm, S, TClos (B, Subst.subM $ normalizeMonadObj M)) end
	| (ProjLeft S, AddProd (A, _)) => inferSpine (ctx, S, A)
	| (ProjRight S, AddProd (_, B)) => inferSpine (ctx, S, B)
	| _ => raise Fail "Internal error match: inferSpine"

(* checkExp : context * expObj * syncType -> context *)
and checkExp (ctx, ex, ty) = case ExpObj.prj ex of
	  LetRedex (p, S, N, E) =>
			let val S' = Util.syncTypeFromApx S
				val () = checkSyncType (ctxIntPart ctx, S')
				val ctxm = checkObj (ctx, N, TMonad' S')
				val ctxm' = opatBind (p, S') ctxm
				val ctxo' = checkExp (ctxm', E, STClos (ty, Subst.shift (nbinds p)))
			in patUnbind (p, ctxo') end
	| Let (p, (H, S), E) =>
			let val (ctxm1, B) = inferHead (ctx, H)
				val (ctxm2, A) = inferSpine (ctxm1, S, B)
				val sty = case Util.typePrjAbbrev A of TMonad sty => sty
						| _ => raise Fail "Internal error: checkExp"
				val ctxm2' = opatBind (p, sty) ctxm2
				val ctxo' = checkExp (ctxm2', E, STClos (ty, Subst.shift (nbinds p)))
			in patUnbind (p, ctxo') end
	| Mon M => checkMonadObj (ctx, M, ty)

(* checkMonadObj : context * monadObj * syncType -> context *)
and checkMonadObj (ctx, mob, ty) = case (MonadObj.prj mob, SyncType.prj ty) of
	  (DepPair (M1, M2), LExists (p, S1, S2)) =>
			let val ctxm = checkMonadObj (ctx, M1, S1)
			in checkMonadObj (ctxm, M2, STClos (S2, Subst.subM $ normalizeMonadObj M1)) end
	| (One, TOne) => ctx
	| (Down N, TDown A) => checkObj (ctx, N, A)
	| (Affi N, TAffi A) => ctxJoinAffLin (checkObj (ctxAffPart ctx, N, A), ctx)
	| (Bang N, TBang A) => (ignore $ checkObj (ctxIntPart ctx, N, A) ; ctx)
	| (MonUndef, _) => raise Fail "Internal error: checkMonadObj: MonUndef"
	| _ => raise Fail "Internal error match: checkMonadObj"


fun checkKindEC ki = checkKind (emptyCtx, ki)
fun checkTypeEC ty = checkType (emptyCtx, ty)
fun checkObjEC (ob, ty) = ignore (checkObj (emptyCtx, ob, ty))

end
