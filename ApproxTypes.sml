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

signature TLU_ApproxTypes = TOP_LEVEL_UTIL
structure ApproxTypes :> APPROXTYPES =
struct

open Syntax
open Context
open PatternBind

val traceApx = ref false

type context = apxAsyncType Context.context

exception ExnApxUnifyType of string

(* ucase : string -> bool *)
fun ucase x = (*x<>"" andalso Char.isUpper (String.sub (x, 0))*)
	let fun ucase' [] = false
		  | ucase' (c::cs) = Char.isUpper c orelse (c = #"_" andalso ucase' cs)
	in ucase' (String.explode x) end

(* occur : typeLogicVar -> apxAsyncType -> unit *)
fun occur X = foldApxType {fki = ignore, fsTy = ignore, faTy =
	(fn ApxTLogicVar X' => if eqLVar (X, X') then raise ExnApxUnifyType "Occurs check" else ()
	  | _ => ()) }

(* apxUnifyType : apxAsyncType * apxAsyncType -> unit *)
fun apxUnifyType (ty1, ty2) = case (Util.apxTypePrjAbbrev ty1, Util.apxTypePrjAbbrev ty2) of
(*	  (ApxTLogicVar (ref (SOME A1)), A2) => apxUnifyType (A1, ApxAsyncType.inj A2)
	| (A1, ApxTLogicVar (ref (SOME A2))) => apxUnifyType (ApxAsyncType.inj A1, A2)*)
	  (ApxLolli (A1, B1), ApxLolli (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxTPi (A1, B1), ApxTPi (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxAddProd (A1, B1), ApxAddProd (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxTop, ApxTop) => ()
	| (ApxTMonad S1, ApxTMonad S2) => apxUnifySyncType (S1, S2)
	| (ApxTAtomic a1, ApxTAtomic a2) =>
			if a1 = a2 then () else raise ExnApxUnifyType (a1^" and "^a2^" differ")
	| (ApxTLogicVar X, A as ApxTLogicVar X') =>
			if eqLVar (X, X') then () else updLVar (X, ApxAsyncType.inj A)
	(*| (ApxTLogicVar X, A) => let val A' = ApxAsyncType.inj A in (occur X A'; updLVar (X, A')) end
	| (A, ApxTLogicVar X) => let val A' = ApxAsyncType.inj A in (occur X A'; updLVar (X, A')) end*)
	| (ApxTLogicVar X, _) => (occur X ty2; updLVar (X, ty2))
	| (_, ApxTLogicVar X) => (occur X ty1; updLVar (X, ty1))
	| (A1, A2) => raise ExnApxUnifyType
			(PrettyPrint.printType (unsafeCast ty1)^"\nand: "
						^PrettyPrint.printType (unsafeCast ty2))
and apxUnifySyncType (ty1, ty2) = case (ApxSyncType.prj ty1, ApxSyncType.prj ty2) of
	  (ApxTTensor (S1, T1), ApxTTensor (S2, T2)) =>
			(apxUnifySyncType (S1, S2); apxUnifySyncType (T1, T2))
	| (ApxTOne, ApxTOne) => ()
	| (ApxExists (A1, S1), ApxExists (A2, S2)) => (apxUnifyType (A1, A2); apxUnifySyncType (S1, S2))
	| (ApxAsync A1, ApxAsync A2) => apxUnifyType (A1, A2)
	| (S1, S2) => raise ExnApxUnifyType
			(PrettyPrint.printType (unsafeCast (ApxTMonad' ty1))^"\nand: "
						^PrettyPrint.printType (unsafeCast (ApxTMonad' ty2)))

fun apxUnify (ty1, ty2, errmsg) = (apxUnifyType (ty1, ty2))
		handle (e as ExnApxUnifyType s) =>
			( print ("ExnApxUnify: "^s^"\n")
			; print $ errmsg ()
			; raise e)
		(*handle (e as ExnApxUnifyType s) => (print ("ExnApxUnify: "^
			(PrettyPrint.printType (unsafeCast ty1))^"\nand: "
						^(PrettyPrint.printType (unsafeCast ty2))^"\n") ; raise e)*)

val apxCount = ref 0

(* apxCheckKind : context * kind -> kind *)
fun apxCheckKind (ctx, ki) = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) =>
			let val A' = apxCheckType (ctx, A)
			in KPi' (x, A', apxCheckKind (ctxCondPushINT (x, asyncTypeToApx A', ctx), K)) end

(* apxCheckType : context * asyncType -> asyncType *)
and apxCheckType (ctx, ty) =
	if !traceApx then
		let fun join [] = ""
			  | join [s] = s
			  | join (s::ss) = s^", "^join ss
			val t = join (map (fn (x, A, _) =>
							(x^":"^PrettyPrint.printType (unsafeCast A))) (ctx2list ctx))
			val t = t^"|- "^PrettyPrint.printPreType ty
			val () = apxCount := !apxCount + 1
			val a = Int.toString (!apxCount)
			val () = print ("ApxChecking["^a^"]: "^t^" : Type\n")
			val ty' = apxCheckType' (ctx, ty)
			val () = print ("ApxDone["^a^"]: "^t^" ==> "^PrettyPrint.printType ty'^"\n")
		in ty' end
	else apxCheckType' (ctx, ty)
and apxCheckType' (ctx, ty) = if isUnknown ty then ty else case AsyncType.prj ty of
	  Lolli (A, B) => Lolli' (apxCheckType (ctx, A), apxCheckType (ctx, B))
	| TPi (x, A, B) =>
			let val A' = apxCheckType (ctx, A)
			in TPi' (x, A', apxCheckType (ctxCondPushINT (x, asyncTypeToApx A', ctx), B)) end
	| AddProd (A, B) => AddProd' (apxCheckType (ctx, A), apxCheckType (ctx, B))
	| Top => Top'
	| TMonad S => TMonad' (apxCheckSyncType (ctx, S))
	| TAtomic (a, S) =>
		(case Signatur.sigGetTypeAbbrev a of
			  SOME ty =>
				let val _ = apxCheckTypeSpine (ctx, S, ApxType') (* S = TNil *)
				in TAbbrev' (a, ty) end
			| NONE =>
				let val K = kindToApx (Signatur.sigLookupKind a)
					val nImpl = Signatur.getImplLength a
					val S' = foldr TApp' S (List.tabulate (nImpl, fn _ => Util.blank ()))
				in TAtomic' (a, apxCheckTypeSpine (ctx, S', K)) end)
	| TAbbrev _ => raise Fail "Internal error: TAbbrev cannot occur yet\n"

(* apxCheckTypeSpine : context * typeSpine * apxKind -> typeSpine *)
(* checks that the spine is : ki > Type *)
and apxCheckTypeSpine (ctx, sp, ki) = case (TypeSpine.prj sp, ApxKind.prj ki) of
	  (TNil, ApxType) => TNil'
	| (TNil, ApxKPi _) => raise Fail "Wrong kind; expected Type\n"
	| (TApp _, ApxType) => raise Fail "Wrong kind; cannot apply Type\n"
	| (TApp (N, S), ApxKPi (A, K)) =>
			let val (_, _, N') = apxCheckObj (ctx, N, A)
			in TApp' (N', apxCheckTypeSpine (ctx, S, K)) end

(* apxCheckSyncType : context * syncType -> syncType *)
and apxCheckSyncType (ctx, ty) = case SyncType.prj ty of
	  TTensor (S1, S2) => TTensor' (apxCheckSyncType (ctx, S1), apxCheckSyncType (ctx, S2))
	| TOne => TOne'
	| Exists (x, A, S) =>
			let val A' = apxCheckType (ctx, A)
			in Exists' (x, A', apxCheckSyncType (ctxCondPushINT (x, asyncTypeToApx A', ctx), S)) end
	| Async A => Async' (apxCheckType (ctx, A))

(* apxCheckObj : context * obj * apxAsyncType -> context * bool * obj *)
and apxCheckObj (ctx, ob, ty) =
	( if !traceApx then
		( print "ApxChecking: "
		; app (fn (x, A, _) => print (x^":"^PrettyPrint.printType (unsafeCast A)^", "))
			(ctx2list ctx)
		; print ("|- "^PrettyPrint.printPreObj ob^" : "^PrettyPrint.printType (unsafeCast ty)^"\n"))
	  else ()
	; apxCheckObj' (ctx, ob, ty) )
and apxCheckObj' (ctx, ob, A) =
	let val (ctxo, t, N, A') = apxInferObj (ctx, ob)
		fun errmsg () = "Object " ^ PrettyPrint.printObj N ^ " has type " ^
				PrettyPrint.printType (unsafeCast A') ^ "\n" ^
				"but expected " ^ PrettyPrint.printType (unsafeCast A) ^ "\n"
	in apxUnify (A, A', errmsg); (ctxo, t, N) end

(* apxInferObj : context * obj -> context * bool * obj * apxAsyncType *)
and apxInferObj (ctx, ob) = case Util.ObjAuxDefs.prj2 ob of
	  Redex (Redex (N, A, S1), _, S2) => apxInferObj (ctx, Redex' (N, A, appendSpine (S1, S2)))
	| Redex (Atomic (H, S1), _, S2) => apxInferObj (ctx, Atomic' (H, appendSpine (S1, S2)))
	| _ => case Obj.prj ob of
	  LinLam (x, N) =>
			let val A = newApxTVar()
				val (ctxo, t, N', B) = apxInferObj (ctxPushLIN (x, A, ctx), N)
			in (ctxPopLIN (t, ctxo), t, LinLam' (x, N'), ApxLolli' (A, B)) end
	| Lam (x, N) =>
			let val A = newApxTVar()
				val (ctxo, t, N', B) = apxInferObj (ctxPushINT (x, A, ctx), N)
			in (ctxPopINT ctxo, t, Lam' (x, N'), ApxTPi' (A, B)) end
	| AddPair (N1, N2) =>
			let val (ctxo1, t1, N1', A1) = apxInferObj (ctx, N1)
				val (ctxo2, t2, N2', A2) = apxInferObj (ctx, N2)
			in (ctxAddJoin (t1, t2) (ctxo1, ctxo2), t1 andalso t2, 
				AddPair' (N1', N2'), ApxAddProd' (A1, A2)) end
	| Unit => (ctx, true, Unit', ApxTop')
	| Monad E => (fn (c, t, e, s) => (c, t, Monad' e, ApxTMonad' s)) (apxInferExp (ctx, E))
	| Atomic (H, S) =>
			let val (ctxm, t1, H', nImpl, A) = apxInferHead (ctx, H)
				val S' = foldr App' S (List.tabulate (nImpl, fn _ => Util.blank ()))
				fun atomRedex (INL h, sp) = Atomic' (h, sp)
				  | atomRedex (INR h, sp) = Redex' (h, A, sp)
				fun h2str sp = PrettyPrint.printObj $ atomRedex (H', sp)
				val (ctxo, t2, S'', B) = apxInferSpine (ctxm, S', A, h2str)
			in (ctxo, t1 orelse t2, atomRedex (H', S''), B) end
	| Redex (N, A, S) =>
			let val (ctxm, t1, N') = apxCheckObj (ctx, N, A)
				fun h2str sp = PrettyPrint.printObj $ Redex' (N', A, sp)
				val (ctxo, t2, S', B) = apxInferSpine (ctxm, S, A, h2str)
			in (ctxo, t1 orelse t2, Redex' (N', A, S'), B) end
	| Constraint (N, A) =>
			let val A' = apxCheckType (ctxDelLin ctx, A)
				val apxA' = asyncTypeToApx A'
				val (ctxo, t, N') = apxCheckObj (ctx, N, apxA')
			in (ctxo, t, Constraint' (N', A'), apxA') end

(* apxInferHead : context * head -> context * bool * (head, obj) sum * int * apxAsyncType *)
and apxInferHead (ctx, h) = case h of
	  Const c => (* set Top flag to true in case of Top type *)
			(case ctxLookupName (ctx, c) of
				  SOME (n, M, A, ctxo) => (ctxo, true, INL (Var (M, n)), 0, A)
				| NONE =>
					if ucase c then
						(ctx, true, INL (UCVar c), 0, ImplicitVars.apxUCLookup c)
					else (case Signatur.sigGetObjAbbrev c of
						  SOME (ob, ty) => (ctx, true, INR ob, 0, asyncTypeToApx ty)
						| NONE => (ctx, true, INL (Const c), Signatur.getImplLength c,
							asyncTypeToApx (Signatur.sigLookupType c))))
	| Var _ => raise Fail "de Bruijn indices shouldn't occur yet\n"
	| UCVar _ => raise Fail "Upper case variables shouldn't occur yet\n"
	| X as LogicVar {ty, ...} => (ctx, true, INL X, 0, asyncTypeToApx ty)

(* apxInferSpine : context * spine * apxAsyncType * (spine -> string)
	-> context * bool * spine * apxAsyncType *)
and apxInferSpine (ctx, sp, ty, h2str) = case Spine.prj sp of
	  Nil => (ctx, false, Nil', ty)
	| App (N, S) =>
			let val (_, _, N', A) = apxInferObj (ctxDelLin ctx, N)
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is applied to " ^ PrettyPrint.printObj N' ^ " of type " ^
						PrettyPrint.printType (unsafeCast A) ^ "\n"
				val () = apxUnify (ty, ApxTPi' (A, B), errmsg)
				val (ctxo, t, S', tyo) = apxInferSpine (ctx, S, B, fn s => h2str $ App' (N', s))
			in (ctxo, t, App' (N', S'), tyo) end
	| LinApp (N, S) =>
			let val (ctxm, t1, N', A) = apxInferObj (ctx, N)
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is linearly applied to " ^ PrettyPrint.printObj N' ^ " of type " ^
						PrettyPrint.printType (unsafeCast A) ^ "\n"
				val () = apxUnify (ty, ApxLolli' (A, B), errmsg)
				val (ctxo, t2, S', tyo) = apxInferSpine (ctxm, S, B, fn s => h2str $ LinApp' (N', s))
			in (ctxo, t1 orelse t2, LinApp' (N', S'), tyo) end
	| ProjLeft S =>
			let val A = newApxTVar ()
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is used as pair\n"
				val () = apxUnify (ty, ApxAddProd' (A, B), errmsg)
				val (ctxo, t, S', tyo) = apxInferSpine (ctx, S, A, fn s => h2str $ ProjLeft' s)
			in (ctxo, t, ProjLeft' S', tyo) end
	| ProjRight S =>
			let val A = newApxTVar ()
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is used as pair\n"
				val () = apxUnify (ty, ApxAddProd' (A, B), errmsg)
				val (ctxo, t, S', tyo) = apxInferSpine (ctx, S, B, fn s => h2str $ ProjRight' s)
			in (ctxo, t, ProjRight' S', tyo) end

(* apxInferExp : context * expObj -> context * bool * expObj * apxSyncType *)
and apxInferExp (ctx, ex) = case ExpObj.prj ex of
	  Let (p, N, E) =>
			let val p' = apxCheckPattern (ctxDelLin ctx, p)
				val (ctxm, t1, N') = apxCheckObj (ctx, N, ApxTMonad' (Util.pat2apxSyncType p'))
				val (ctxo', t2, E', S) = apxInferExp (patBind asyncTypeToApx p' ctxm, E)
			in (patUnbind (p', ctxo', t2), t1 orelse t2, Let' (p', N', E'), S) end
	| Mon M => (fn (ctxo, t, M', S) => (ctxo, t, Mon' M', S)) (apxInferMonadObj (ctx, M))

(* apxCheckPattern : context * pattern -> pattern *)
and apxCheckPattern (ctx, p) = case Pattern.prj p of
	  PTensor (p1, p2) => PTensor' (apxCheckPattern (ctx, p1), apxCheckPattern (ctx, p2))
	| POne => POne'
	| PDepPair (x, A, p) =>
			let val A' = apxCheckType (ctx, A)
			in PDepPair' (x, A', apxCheckPattern (ctxPushINT (x, asyncTypeToApx A', ctx), p)) end
	| PVar (x, A) => PVar' (x, apxCheckType (ctx, A))

(* apxInferMonadObj : context * monadObj -> context * bool * monadObj * apxSyncType *)
and apxInferMonadObj (ctx, mob) = case MonadObj.prj mob of
	  Tensor (M1, M2) =>
			let val (ctxm, t1, M1', S1) = apxInferMonadObj (ctx, M1)
				val (ctxo, t2, M2', S2) = apxInferMonadObj (ctxm, M2)
			in (ctxo, t1 orelse t2, Tensor' (M1', M2'), ApxTTensor' (S1, S2)) end
	| One => (ctx, false, One', ApxTOne')
	| DepPair (N, M) =>
			let val (_, _, N', A) = apxInferObj (ctxDelLin ctx, N)
				val (ctxo, t, M', S) = apxInferMonadObj (ctx, M)
			in (ctxo, t, DepPair' (N', M'), ApxExists' (A, S)) end
	| Norm N => (fn (ctxo, t, N', A) => (ctxo, t, Norm' N', ApxAsync' A)) (apxInferObj (ctx, N))


fun apxCheckKindEC ki = apxCheckKind (emptyCtx, ki)
fun apxCheckTypeEC ty = apxCheckType (emptyCtx, ty)
fun apxCheckObjEC (ob, ty) = #3 (apxCheckObj (emptyCtx, ob, ty))
(*
fun apxCheckObjEC (ob, ty) = case (Obj.prj o #3 o apxInferObj) (emptyCtx, Constraint' (ob, ty)) of
		  Constraint obty => obty
		| _ => raise Fail "Internal error: apxCheckObjEC\n"
*)

end
