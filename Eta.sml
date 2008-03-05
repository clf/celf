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

structure Eta :> ETA =
struct

open Syntax infix with'ty with's
open Signatur
open Context
open PatternBind

val traceEta = ref false

type context = apxAsyncType context

(* etaContract : exn -> Syntax.obj -> int *)
fun etaContract e ob =
	let datatype etaSpine = Ap | LAp | Pl | Pr
		fun eq (x, y) = if x=y then x else raise e
		fun nbinds sp = length (List.filter (fn Ap => true | LAp => true | _ => false) sp)
		fun etaC (ob, sp) = case etaShortcut ob of NONE => etaC' (ob, sp) | SOME k => k
		and etaC' (ob, sp) = case Whnf.whnfObj ob of
			  NfLam (_, N) => etaC (N, Ap::sp)
			| NfLinLam (_, N) => etaC (N, LAp::sp)
			| NfAddPair (N1, N2) => eq (etaC (N1, Pl::sp), etaC (N2, Pr::sp))
			| NfMonad E =>
				let fun expFmap f = ExpObj.Fmap ((fn x=>x, fn x=>x, fn x=>x), f)
				in case expFmap Whnf.whnfExp (Whnf.whnfExp E) of
					  Let (p, N, Mon M) => (etaP (p, M); etaC (Atomic' N, sp))
					| _ => raise e
				end
			| NfAtomic (Var n, S) =>
				let val k = n - nbinds sp
					val () = if k>0 then () else raise e
					val () = etaSp (1, S, sp)
				in k end
			| NfAtomic _ => raise e
			| NfUnit => raise e (* Not complete? Pair could perhaps absorb one Unit. --asn *)
		and etaP (p, m) = ignore (etaP' (1, p, m))
		and etaP' (n, p, m) = case (Pattern.prj p, MonadObj.prj m) of
			  (PTensor (p1, p2), Tensor (M1, M2)) => etaP' (n + etaP' (n, p1, M1), p2, M2)
			| (POne, One) => 0
			| (PDepPair (_, _, p), DepPair (N, M)) =>
					if n = etaC (N, []) then etaP' (1+n, p, M) else raise e
			| (PVar _, Norm N) => if n = etaC (N, []) then 1 else raise e
			| _ => raise e
		and etaSp (m, Sp, sp) = case (Spine.prj Sp, sp) of
			  (Nil, []) => ()
			| (App (N, S), Ap::sp) =>
				(etaSp (m+1, S, sp); if etaC (N, []) = m then () else raise e)
			| (LinApp (N, S), LAp::sp) =>
				(etaSp (m+1, S, sp); if etaC (N, []) = m then () else raise e)
			| (ProjLeft S, Pl::sp) => etaSp (m, S, sp)
			| (ProjRight S, Pr::sp) => etaSp (m, S, sp)
			| _ => raise e
	in etaC (ob, []) end
	

(* etaExpand : apxAsyncType * head * spine -> obj *)
fun etaExpand (A, H, S) =
	let (*fun Idx A n = EtaTag (etaExpand (A, Var n, A, Nil'), n)*)
		fun Idx A n = etaExpand (A, Var n, Nil') (*Atomic' (Var n, Nil')*)
		(*fun printResult ob = (print ("Eta> "^(PrettyPrint.printObj (Atomic' (H, AH, S)))^" : "^
								(PrettyPrint.printType (asyncTypeFromApx A))^" = "^
								(PrettyPrint.printObj ob)^"\n")
							; ob)*)
		fun etaSyncType (ty, n) = case ApxSyncType.prj ty of
			  ApxTTensor (S1, S2) =>
				let val (p2, M2) = etaSyncType (S2, n)
					val (p1, M1) = etaSyncType (S1, n + nbinds p2)
				in (PTensor' (p1, p2), Tensor' (M1, M2)) end
			| ApxTOne => (POne', One')
			| ApxExists (A, S) =>
				let val (p, M) = etaSyncType (S, n)
				in (PDepPair' ("", injectApxType A, p), DepPair' (Idx A (n + nbinds p), M)) end
			| ApxAsync A => (PVar' ("", injectApxType A), Norm' (Idx A n))
		fun addEtaSpine (n, Sf) =
				Atomic' (Subst.shiftHead (H, n),
						appendSpine (SClos (S, Subst.shift n), Sf (1, Nil')))
		fun eta' (ty, n, Sf) = case Util.apxTypePrjAbbrev ty of
			  ApxLolli (A, B) =>
				LinLam' ("", eta' (B, n+1, fn (n, S) => Sf (n+1, LinApp' (Idx A n, S))))
			| ApxTPi (A, B) => Lam' ("", eta' (B, n+1, fn (n, S) => Sf (n+1, App' (Idx A n, S))))
			| ApxAddProd (A, B) =>
				AddPair' (eta' (A, n, fn (n, S) => Sf (n, ProjLeft' S)), 
				         eta' (B, n, fn (n, S) => Sf (n, ProjRight' S)))
			| ApxTop => Unit'
			| ApxTMonad S =>
				let val (p, M) = etaSyncType (S, 1)
				in Monad' (Let' (p, addEtaSpine (n, Sf), Mon' M)) end
			| ApxTAtomic _ => addEtaSpine (n, Sf)
			| ApxTAbbrev _ => raise Fail "Internal error eta': ApxTAbbrev cannot happen\n"
			| ApxTLogicVar _ => raise Fail "Ambiguous typing\n"
		val etaResult = eta' (A, 0, fn (n, S) => S)
	in case H of
		  Var n => if Util.isNil S then EtaTag (etaResult, n) else etaResult
		| _ => etaResult
	end

val etaCount = ref 0

(* etaExpandKind : context * kind -> kind *)
fun etaExpandKind (ctx, ki) = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) =>
			let val A' = etaExpandType (ctx, A)
			in KPi' (x, A', etaExpandKind (ctxCondPushUN (x, asyncTypeToApx A', ctx), K)) end

(* etaExpandType : context * asyncType -> asyncType *)
and etaExpandType (ctx, ty) =
	if !traceEta then
		let fun join [] = ""
			  | join [s] = s
			  | join (s::ss) = s^", "^join ss
			val t = join (map (fn (x, A, _) =>
							(x^":"^PrettyPrint.printType (unsafeCast A))) (ctx2list ctx))
			val t = t^"|- "^PrettyPrint.printType ty
			val () = etaCount := !etaCount + 1
			val a = Int.toString (!etaCount)
			val () = print ("Eta["^a^"]: "^t^" : Type\n")
			val ty' = etaExpandType' (ctx, ty)
			val () = print ("EtaDone["^a^"]: "^t^" ==> "^PrettyPrint.printType ty'^"\n")
		in ty' end
	else etaExpandType' (ctx, ty)
and etaExpandType' (ctx, ty) = case AsyncType.prj ty of
	  Lolli (A, B) => Lolli' (etaExpandType (ctx, A), etaExpandType (ctx, B))
	| TPi (x, A, B) =>
			let val A' = etaExpandType (ctx, A)
			in TPi' (x, A', etaExpandType (ctxCondPushUN (x, asyncTypeToApx A', ctx), B)) end
	| AddProd (A, B) => AddProd' (etaExpandType (ctx, A), etaExpandType (ctx, B))
	| Top => Top'
	| TMonad S => TMonad' (etaExpandSyncType (ctx, S))
	| TAtomic (a, S) => TAtomic' (a, etaExpandTypeSpine (ctx, S, kindToApx (sigLookupKind a)))
	| TAbbrev aA => TAbbrev' aA

(* etaExpandTypeSpine : context * typeSpine * apxKind -> typeSpine *)
and etaExpandTypeSpine (ctx, sp, ki) = case (TypeSpine.prj sp, ApxKind.prj ki) of
	  (TNil, ApxType) => TNil'
	| (TApp (N, S), ApxKPi (A, K)) =>
			TApp' (etaExpandObj (ctx, N, A), etaExpandTypeSpine (ctx, S, K))
	| _ => raise Fail "Internal error etaExpandTypeSpine: Match\n"

(* etaExpandSyncType : context * syncType -> syncType *)
and etaExpandSyncType (ctx, ty) = case SyncType.prj ty of
	  TTensor (S1, S2) => TTensor' (etaExpandSyncType (ctx, S1), etaExpandSyncType (ctx, S2))
	| TOne => TOne'
	| Exists (x, A, S) =>
			let val A' = etaExpandType (ctx, A)
			in Exists' (x, A', etaExpandSyncType (ctxCondPushUN (x, asyncTypeToApx A', ctx), S)) end
	| Async A => Async' (etaExpandType (ctx, A))

(* etaExpandObj : context * obj * apxAsyncType -> obj *)
and etaExpandObj (ctx, ob, ty) =
	( if !traceEta then
		( print "Eta: "
		; app (fn (x, A, _) => print (x^":"^PrettyPrint.printType (unsafeCast A)^", "))
			(ctx2list ctx)
		; print ("|- "^PrettyPrint.printObj ob^" : "^PrettyPrint.printType (unsafeCast ty)^"\n"))
	  else ()
	; etaExpandObj' (ctx, ob, ty) )
and etaExpandObj' (ctx, ob, ty) = case (Obj.prj ob, Util.apxTypePrjAbbrev ty) of
	  (_, ApxTLogicVar _) => raise Fail "Ambiguous typing\n"
	| (LinLam (x, N), ApxLolli (A, B)) =>
			LinLam' (x, etaExpandObj (ctxPushUN (x, A, ctx), N, B))
	| (Lam (x, N), ApxTPi (A, B)) =>
			Lam' (x, etaExpandObj (ctxPushUN (x, A, ctx), N, B))
	| (AddPair (N1, N2), ApxAddProd (A, B)) =>
			AddPair' (etaExpandObj (ctx, N1, A), etaExpandObj (ctx, N2, B))
	| (Unit, ApxTop) => Unit'
	| (Monad E, ApxTMonad S) => Monad' (etaExpandExp (ctx, E, S))
	| (Atomic (H, S), _) =>
			let val (H', A) = etaExpandHead (ctx, H)
			in etaExpand (ty, H', etaExpandSpine (ctx, S, A)) end
	| (Redex (N, A, S), _) => Redex' (etaExpandObj (ctx, N, A), A, etaExpandSpine (ctx, S, A))
	| (Constraint (N, A), _) => Constraint' (etaExpandObj (ctx, N, ty), etaExpandType (ctx, A))
	| _ => raise Fail "Internal error etaExpandObj: Match\n"

(* etaExpandHead : context * head -> head * apxAsyncType *)
and etaExpandHead (ctx, h) = case h of
	  Const c => (h, asyncTypeToApx (Signatur.sigLookupType c))
	| Var n => (h, #2 (ctxLookupNum (ctx, n)))
	| UCVar x => (h, asyncTypeToApx (ImplicitVars.ucLookup x))
	| LogicVar X =>
			let val () = if Subst.isId (#s X) then () else raise Fail "Internal error eta lvar"
				val A = etaExpandType (ctx, #ty X)
			in (LogicVar (X with'ty A), asyncTypeToApx A) end

(* etaExpandImpl : obj list -> obj list *)
(*
and etaExpandImpl impl =
	let fun f ob = case Obj.prj ob of
			  Atomic (LogicVar X, A', S) =>
					if Util.isNil S then etaExpand (A', LogicVar (X with'ty etaExpandType (#ty X)), A', S)
					else raise Fail "Internal error: etaExpandImpl 1\n"
			| _ => raise Fail "Internal error: etaExpandImpl 2\n"
	in map f impl end
*)

(* etaExpandSpine : context * spine * apxAsyncType -> spine *)
and etaExpandSpine (ctx, sp, ty) = case (Spine.prj sp, Util.apxTypePrjAbbrev ty) of
	  (_, ApxTLogicVar _) => raise Fail "Ambiguous typing\n"
	| (Nil, _) => Nil'
	| (App (N, S), ApxTPi (A, B)) => App' (etaExpandObj (ctx, N, A), etaExpandSpine (ctx, S, B))
	| (LinApp (N, S), ApxLolli (A, B)) =>
			LinApp' (etaExpandObj (ctx, N, A), etaExpandSpine (ctx, S, B))
	| (ProjLeft S, ApxAddProd (A, B)) => ProjLeft' (etaExpandSpine (ctx, S, A))
	| (ProjRight S, ApxAddProd (A, B)) => ProjRight' (etaExpandSpine (ctx, S, B))
	| _ => raise Fail "Internal error etaExpandSpine: Match\n"

(* etaExpandExp : context * expObj * apxSyncType -> expObj *)
and etaExpandExp (ctx, ex, ty) = case ExpObj.prj ex of
	  Let (p, N, E) =>
			let fun eta' (Atomic (H, S)) =
						let val (H', A) = etaExpandHead (ctx, H)
						in Atomic' (H', etaExpandSpine (ctx, S, A)) end
				  | eta' N = etaExpandObj (ctx, Obj.inj N, ApxTMonad' (ApproxTypes.pat2apxSyncType p))
				val p' = etaExpandPattern (ctx, p)
				val N' = eta' (Obj.prj N)
			in Let' (p', N', etaExpandExp (patBind asyncTypeToApx p' ctx, E, ty)) end
	| Mon M => Mon' (etaExpandMonadObj (ctx, M, ty))

(* etaExpandPattern : context * pattern -> pattern *)
and etaExpandPattern (ctx, p) = case Pattern.prj p of
	  PTensor (p1, p2) => PTensor' (etaExpandPattern (ctx, p1), etaExpandPattern (ctx, p2))
	| POne => POne'
	| PDepPair (x, A, p) =>
			let val A' = etaExpandType (ctx, A)
			in PDepPair' (x, A', etaExpandPattern (ctxPushUN (x, asyncTypeToApx A', ctx), p)) end
	| PVar (x, A) => PVar' (x, etaExpandType (ctx, A))

(* etaExpandMonadObj : context * monadObj * apxSyncType -> monadObj *)
and etaExpandMonadObj (ctx, mob, ty) = case (MonadObj.prj mob, ApxSyncType.prj ty) of
	  (Tensor (M1, M2), ApxTTensor (S1, S2)) =>
			Tensor' (etaExpandMonadObj (ctx, M1, S1), etaExpandMonadObj (ctx, M2, S2))
	| (One, ApxTOne) => One'
	| (DepPair (N, M), ApxExists (A, S)) =>
			DepPair' (etaExpandObj (ctx, N, A), etaExpandMonadObj (ctx, M, S))
	| (Norm N, ApxAsync A) => Norm' (etaExpandObj (ctx, N, A))
	| _ => raise Fail "Internal error etaExpandMonadObj: Match"

fun etaExpandKindEC ki = etaExpandKind (emptyCtx, ki)
fun etaExpandTypeEC ty = etaExpandType (emptyCtx, ty)
fun etaExpandObjEC (ob, ty) = etaExpandObj (emptyCtx, ob, ty)

end
