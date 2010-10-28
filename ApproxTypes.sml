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

exception ExnApxUnify of string

(* ucase : string -> bool *)
fun ucase x = (*x<>"" andalso Char.isUpper (String.sub (x, 0))*)
	let fun ucase' [] = false
		  | ucase' (c::cs) = Char.isUpper c orelse (c = #"_" andalso ucase' cs)
	in ucase' (String.explode x) end

(* occur : typeLogicVar -> apxAsyncType -> unit *)
fun occur X = foldApxType {fki = ignore, fsTy = ignore, faTy =
	(fn ApxTLogicVar X' => if eqLVar (X, X') then raise ExnApxUnify "Occurs check failure" else ()
	  | _ => ()) }

(* apxUnifyType : apxAsyncType * apxAsyncType -> unit *)
fun apxUnifyType (ty1, ty2) = case (Util.apxTypePrjAbbrev ty1, Util.apxTypePrjAbbrev ty2) of
	  (ApxLolli (A1, B1), ApxLolli (A2, B2)) => (apxUnifySyncType (A1, A2); apxUnifyType (B1, B2))
	| (ApxAddProd (A1, B1), ApxAddProd (A2, B2)) => (apxUnifyType (A1, A2); apxUnifyType (B1, B2))
	| (ApxTMonad S1, ApxTMonad S2) => apxUnifySyncType (S1, S2)
	| (ApxTAtomic a1, ApxTAtomic a2) =>
			if a1 = a2 then () else raise ExnApxUnify (a1^" and "^a2^" differ")
	| (ApxTLogicVar X, A as ApxTLogicVar X') =>
			if eqLVar (X, X') then () else updLVar (X, ApxAsyncType.inj A)
	| (ApxTLogicVar X, _) => (occur X ty2; updLVar (X, ty2))
	| (_, ApxTLogicVar X) => (occur X ty1; updLVar (X, ty1))
	| (A1, A2) => raise ExnApxUnify
			(PrettyPrint.printType (unsafeCast ty1)^"\nand "
						^PrettyPrint.printType (unsafeCast ty2)^" differ")
and apxUnifySyncType (ty1, ty2) = case (ApxSyncType.prj ty1, ApxSyncType.prj ty2) of
	  (ApxTTensor (S1, T1), ApxTTensor (S2, T2)) =>
			(apxUnifySyncType (S1, S2); apxUnifySyncType (T1, T2))
	| (ApxTOne, ApxTOne) => ()
	| (ApxTDown A1, ApxTDown A2) => apxUnifyType (A1, A2)
	| (ApxTAffi A1, ApxTAffi A2) => apxUnifyType (A1, A2)
	| (ApxTBang A1, ApxTBang A2) => apxUnifyType (A1, A2)
	| (S1, S2) => raise ExnApxUnify
			(PrettyPrint.printSyncType (unsafeCastS ty1)^"\nand "
						^PrettyPrint.printSyncType (unsafeCastS ty2)^" differ")

fun apxUnify (ty1, ty2, errmsg) = (apxUnifyType (ty1, ty2))
		handle ExnApxUnify s =>
			raise ExnDeclError (TypeErr,
				"Type-unification failed: " ^ s ^ "\n" ^ errmsg ())

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
	  TLPi (p, S, B) =>
			let val S' = apxCheckSyncType (ctx, S)
				fun errmsg () = "Pattern does not match type in " ^
						PrettyPrint.printType (TLPi' (p, S, B)) ^ "\n"
				val () = apxUnify (ApxTMonad' $ syncTypeToApx S',
						ApxTMonad' $ Util.pat2apxSyncType p, errmsg)
			in TLPi' (p, S', apxCheckType (tpatBindApx (p, syncTypeToApx S') ctx, B)) end
	| AddProd (A, B) => AddProd' (apxCheckType (ctx, A), apxCheckType (ctx, B))
	| TMonad S => TMonad' (apxCheckSyncType (ctx, S))
	| TAtomic (a, S) =>
			let fun pTy () = PrettyPrint.printPreType ty
			in case Signatur.sigGetTypeAbbrev a of
			  SOME ty =>
				let val _ = apxCheckTypeSpine pTy (ctx, S, ApxType') (* S = TNil *)
				in TAbbrev' (a, ty) end
			| NONE =>
				let val K = kindToApx (Signatur.sigLookupKind a)
					val nImpl = Signatur.getImplLength a
					val S' = foldr TApp' S (List.tabulate (nImpl, fn _ => Parse.blank ()))
				in TAtomic' (a, apxCheckTypeSpine pTy (ctx, S', K)) end
			end
	| TAbbrev _ => raise Fail "Internal error: TAbbrev cannot occur yet"

(* apxCheckTypeSpine : (unit -> string) -> context * typeSpine * apxKind -> typeSpine *)
(* checks that the spine is : ki > Type *)
and apxCheckTypeSpine ty (ctx, sp, ki) = case (TypeSpine.prj sp, ApxKind.prj ki) of
	  (TNil, ApxType) => TNil'
	| (TNil, ApxKPi _) =>
		raise ExnDeclError (KindErr, "Type " ^ ty () ^ " is not well-kinded; too few arguments\n")
	| (TApp _, ApxType) =>
		raise ExnDeclError (KindErr, "Type " ^ ty () ^ " is not well-kinded; too many arguments\n")
	| (TApp (N, S), ApxKPi (A, K)) =>
			let val (_, N') = apxCheckObj (ctx, N, A)
			in TApp' (N', apxCheckTypeSpine ty (ctx, S, K)) end

(* apxCheckSyncType : context * syncType -> syncType *)
and apxCheckSyncType (ctx, ty) = case SyncType.prj ty of
	  LExists (p, S1, S2) =>
			let val S1' = apxCheckSyncType (ctx, S1)
				fun errmsg () = "Pattern does not match type in " ^
						PrettyPrint.printSyncType (LExists' (p, S1, S2)) ^ "\n"
				val () = apxUnify (ApxTMonad' $ syncTypeToApx S1',
						ApxTMonad' $ Util.pat2apxSyncType p, errmsg)
			in LExists' (p, S1', apxCheckSyncType (tpatBindApx (p, syncTypeToApx S1') ctx, S2)) end
	| TOne => TOne'
	| TDown A => TDown' (apxCheckType (ctx, A))
	| TAffi A => TAffi' (apxCheckType (ctx, A))
	| TBang A => TBang' (apxCheckType (ctx, A))

(* apxCheckObj : context * obj * apxAsyncType -> context * obj *)
and apxCheckObj (ctx, ob, ty) =
	( if !traceApx then
		( print "ApxChecking: "
		; app (fn (x, A, _) => print (x^":"^PrettyPrint.printType (unsafeCast A)^", "))
			(ctx2list ctx)
		; print ("|- "^PrettyPrint.printPreObj ob^" : "^PrettyPrint.printType (unsafeCast ty)^"\n"))
	  else ()
	; apxCheckObj' (ctx, ob, ty) )
and apxCheckObj' (ctx, ob, A) =
	let val (ctxo, N, A') = apxInferObj (ctx, ob)
		fun errmsg () = "Object " ^ PrettyPrint.printObj N ^ " has type " ^
				PrettyPrint.printType (unsafeCast A') ^ "\n" ^
				"but expected " ^ PrettyPrint.printType (unsafeCast A) ^ "\n"
	in apxUnify (A, A', errmsg); (ctxo, N) end

(* apxInferObj : context * obj -> context * obj * apxAsyncType *)
and apxInferObj (ctx, ob) = case Util.ObjAuxDefs.prj2 ob of
	  Redex (Redex (N, A, S1), _, S2) => apxInferObj (ctx, Redex' (N, A, appendSpine (S1, S2)))
	| Redex (Atomic (H, S1), _, S2) => apxInferObj (ctx, Atomic' (H, appendSpine (S1, S2)))
	| _ => case Obj.prj ob of
	  LLam (p, N) =>
			let val A = Util.pat2apxSyncType p
				val (ctxo, N', B) = apxInferObj (opatBindApx (p, A) ctx, N)
			in (patUnbind (p, ctxo), LLam' (p, N'), ApxLolli' (A, B)) end
	| AddPair (N1, N2) =>
			let val (ctxo1, N1', A1) = apxInferObj (ctx, N1)
				val (ctxo2, N2', A2) = apxInferObj (ctx, N2)
			in (ctxAddJoin (ctxo1, ctxo2), AddPair' (N1', N2'), ApxAddProd' (A1, A2)) end
	| Monad E => (fn (c, e, s) => (c, Monad' e, ApxTMonad' s)) (apxInferExp (ctx, E))
	| Atomic (H, S) =>
			let val (ctxm, H', nImpl, A) = apxInferHead (ctx, H)
				val S' = foldr LApp' S (List.tabulate (nImpl, fn _ => Bang' $ Parse.blank ()))
				fun atomRedex (INL h, sp) = Atomic' (h, sp)
				  | atomRedex (INR h, sp) = Redex' (h, A, sp)
				fun h2str sp = PrettyPrint.printObj $ atomRedex (H', sp)
				val coerce = case H' of INL (Const _) => true | _ => false
				(* Modalities ! and @ are optional if the head is a Const *)
				val (ctxo, S'', B) = apxInferSpine (coerce, ctxm, S', A, h2str)
			in (ctxo, atomRedex (H', S''), B) end
	| Redex (N, A, S) =>
			let val (ctxm, N') = apxCheckObj (ctx, N, A)
				fun h2str sp = PrettyPrint.printObj $ Redex' (N', A, sp)
				val (ctxo, S', B) = apxInferSpine (false, ctxm, S, A, h2str)
			in (ctxo, Redex' (N', A, S'), B) end
	| Constraint (N, A) =>
			let val A' = apxCheckType (ctxIntPart ctx, A)
				val apxA' = asyncTypeToApx A'
				val (ctxo, N') = apxCheckObj (ctx, N, apxA')
			in (ctxo, Constraint' (N', A'), apxA') end

(* apxInferHead : context * head -> context * (head, obj) sum * int * apxAsyncType *)
and apxInferHead (ctx, h) = case h of
	  Const c =>
			(case ctxLookupName (ctx, c) of
				  SOME (n, M, A, ctxo) => (ctxo, INL (Var (M, n)), 0, A)
				| NONE =>
					if ucase c then
						(ctx, INL (UCVar c), 0, ImplicitVars.apxUCLookup c)
					else (case Signatur.sigGetObjAbbrev c of
						  SOME (ob, ty) => (ctx, INR ob, 0, asyncTypeToApx ty)
						| NONE => (ctx, INL (Const c), Signatur.getImplLength c,
							asyncTypeToApx (Signatur.sigLookupType c))))
	| Var _ => raise Fail "Internal error: de Bruijn indices shouldn't occur yet"
	| UCVar _ => raise Fail "Internal error: Upper case variables shouldn't occur yet"
	| X as LogicVar {ty, ...} => (ctx, INL X, 0, asyncTypeToApx ty)

(* apxInferSpine : bool * context * spine * apxAsyncType * (spine -> string)
	-> context * spine * apxAsyncType *)
and apxInferSpine (coerce, ctx, sp, ty, h2str) = case Spine.prj sp of
	  Nil => (ctx, Nil', ty)
	| LApp (M, S) =>
			let val mty = if coerce then case ApxAsyncType.prj ty of ApxLolli (A, _) => SOME A
							| _ => NONE else NONE
				(* if coerce then we change Down into Affi and Bang to match the head type *)
				val (ctxm, M', A) = apxInferMonadObj (ctx, M, mty)
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is applied to " ^ PrettyPrint.printMonadObj M' ^ " of type " ^
						PrettyPrint.printSyncType (unsafeCastS A) ^ "\n"
				val () = apxUnify (ty, ApxLolli' (A, B), errmsg)
				val (ctxo, S', tyo) = apxInferSpine (coerce, ctxm, S, B, fn s => h2str $ LApp' (M', s))
			in (ctxo, LApp' (M', S'), tyo) end
	| ProjLeft S =>
			let val A = newApxTVar ()
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is used as pair\n"
				val () = apxUnify (ty, ApxAddProd' (A, B), errmsg)
				val (ctxo, S', tyo) = apxInferSpine (coerce, ctx, S, A, fn s => h2str $ ProjLeft' s)
			in (ctxo, ProjLeft' S', tyo) end
	| ProjRight S =>
			let val A = newApxTVar ()
				val B = newApxTVar ()
				fun errmsg () = "Object " ^ h2str Nil' ^ " has type " ^
						PrettyPrint.printType (unsafeCast ty) ^ "\n" ^
						"but is used as pair\n"
				val () = apxUnify (ty, ApxAddProd' (A, B), errmsg)
				val (ctxo, S', tyo) = apxInferSpine (coerce, ctx, S, B, fn s => h2str $ ProjRight' s)
			in (ctxo, ProjRight' S', tyo) end

(* apxInferExp : context * expObj -> context * expObj * apxSyncType *)
and apxInferExp (ctx, ex) =
	let fun letRed (p, S, ob, E) = case Obj.prj ob of
			Atomic hS => Let' (p, hS, E) | _ => LetRedex' (p, S, ob, E)
	in case ExpObj.prj ex of
	  LetRedex (p, sty, N, E) =>
			let val (ctxm, N') = apxCheckObj (ctx, N, ApxTMonad' sty)
				val (ctxo', E', S) = apxInferExp (opatBindApx (p, sty) ctxm, E)
			in (patUnbind (p, ctxo'), letRed (p, sty, N', E'), S) end
	| Let (p, hS, E) => apxInferExp (ctx, LetRedex' (p, Util.pat2apxSyncType p, Atomic' hS, E))
	| Mon M => (fn (ctxo, M', S) => (ctxo, Mon' M', S)) (apxInferMonadObj (ctx, M, NONE))
	end

(* apxInferMonadObj : context * monadObj * apxSyncType option -> context * monadObj * apxSyncType *)
(* If ty is given we try to match the inferred type to the given by adding
 * intuitionistic and affine modalities. *)
and apxInferMonadObj (ctx, mob, ty) = case MonadObj.prj mob of
	  DepPair (M1, M2) =>
			let val (ty1, ty2) = case Option.map ApxSyncType.prj ty of
						  SOME (ApxTTensor (ty1, ty2)) => (SOME ty1, SOME ty2)
						| _ => (NONE, NONE)
				val (ctxm, M1', S1) = apxInferMonadObj (ctx, M1, ty1)
				val (ctxo, M2', S2) = apxInferMonadObj (ctxm, M2, ty2)
			in (ctxo, DepPair' (M1', M2'), ApxTTensor' (S1, S2)) end
	| One => (ctx, One', ApxTOne')
	| Down N => (case Option.map ApxSyncType.prj ty of
		  SOME (ApxTAffi _) => apxInferMonadObj (ctx, Affi' N, ty)
		| SOME (ApxTBang _) => apxInferMonadObj (ctx, Bang' N, ty)
		| _ => (fn (ctxo, N', A) => (ctxo, Down' N', ApxTDown' A)) (apxInferObj (ctx, N)))
	| Affi N => (fn (ctxo, N', A) => (ctxJoinAffLin (ctxo, ctx), Affi' N', ApxTAffi' A))
			(apxInferObj (ctxAffPart ctx, N))
	| Bang N => (fn (_, N', A) => (ctx, Bang' N', ApxTBang' A)) (apxInferObj (ctxIntPart ctx, N))
	| MonUndef => raise Fail "Internal error: apxInferMonadObj: MonUndef"


fun apxCheckKindEC ki = apxCheckKind (emptyCtx, ki)
fun apxCheckTypeEC ty = apxCheckType (emptyCtx, ty)
fun apxCheckObjEC (ob, ty) = #2 (apxCheckObj (emptyCtx, ob, ty))

end
