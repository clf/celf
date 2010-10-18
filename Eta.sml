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

signature TLU_Eta = TOP_LEVEL_UTIL
structure Eta :> ETA =
struct

open Syntax infix with'ty with's
open Signatur
open Context
open PatternBind

val traceEta = ref false

type context = apxAsyncType context

(* etaContract : exn -> nfObj -> mode * int *)
(* assumes that ob does not contain _
 * etaContract e ob = (m, n)
 * ob == Var (m, n)
 * or raise e if ob is not an eta-expanded var *)
fun etaContract e ob =
	let datatype etaSpine = LAp of opattern | Pl | Pr
		fun nbindsSp sp = foldl (fn (LAp p, n) => n + nbinds p | (_, n) => n) 0 sp
		fun eq ((x : mode * int), y) = if x=y then x else raise e
		fun etaEqC (ob, x) = ignore $ eq (etaC (ob, []), x)
		and etaC (ob, sp) = case etaShortcut ob of NONE => etaC' (ob, sp) | SOME k => k
		and etaC' (ob, sp) = case NfObj.prj ob of
			  NfLLam (p, N) => etaC (N, (LAp p)::sp)
			| NfAddPair (N1, N2) =>
				eq (etaC (N1, Pl::sp), etaC (N2, Pr::sp))
			| NfMonad E =>
				(case Util.NfExpObjAuxDefs.prj2 E of
					  NfLet (p, N, NfMon M) =>
						(etaP (nbinds p, p, M); etaC (NfAtomic' N, sp))
					| _ => raise e)
			| NfAtomic (Var (M, n), S) =>
				let val nb = nbindsSp sp
					val k = n - nb
					val () = if k>0 then () else raise e
					val () = etaSp (nb, S, rev sp)
				in (M, k) end
			| _ => raise e
		and etaP (n, p, m) = case (Pattern.prj p, NfMonadObj.prj m) of
			  (PDepTensor (p1, p2), DepPair (M1, M2)) =>
				(etaP (n, p1, M1); etaP (n - nbinds p1, p2, M2))
			| (POne, One) => ()
			| (PDown _, Down N) => etaEqC (N, (LIN, n))
			| (PAffi _, Affi N) => etaEqC (N, (AFF, n))
			| (PBang _, Bang N) => etaEqC (N, (INT, n))
			| _ => raise e
		and etaSp (m, Sp, sp) = case (NfSpine.prj Sp, sp) of
			  (Nil, []) => ()
			| (LApp (M, S), (LAp p)::sp) =>
				(etaSp (m - nbinds p, S, sp); etaP (m, p, M))
			| (ProjLeft S, Pl::sp) => etaSp (m, S, sp)
			| (ProjRight S, Pr::sp) => etaSp (m, S, sp)
			| _ => raise e
	in etaC (ob, []) end

(* etaContractLetMon : nfExpObj -> (nfHead * nfSpine) option *)
fun etaContractLetMon e = case Util.NfExpObjAuxDefs.prj2 e of
	  NfLet (p, hS, NfMon M) =>
		let exception ExnNoEta
			val v = (INT, 1) (* dummy variable *)
			fun isV mn = if mn = v then SOME hS else raise Fail "Internal error: etaContractLetMon"
		in isV (etaContract ExnNoEta (NfMonad' $ NfLet' (p, (Var v, NfInj.Nil'), NfMon' M)))
			handle ExnNoEta => NONE
		end
	| _ => NONE

(* etaExpand : (unit -> string) -> apxAsyncType * head * spine -> obj *)
fun etaExpand pp (A, H, S) =
	let fun Idx M A n = etaExpand pp (A, Var (M, n), Nil')
		(*fun printResult ob = (print ("Eta> "^(PrettyPrint.printObj (Atomic' (H, AH, S)))^" : "^
								(PrettyPrint.printType (asyncTypeFromApx A))^" = "^
								(PrettyPrint.printObj ob)^"\n")
							; ob)*)
		fun etaSyncType ty = case ApxSyncType.prj ty of
			  ApxTTensor (S1, S2) =>
				let val (p2, Mf2) = etaSyncType S2
					val (p1, Mf1) = etaSyncType S1
				in (PDepTensor' (p1, p2), fn n => DepPair' (Mf1 (n + nbinds p2), Mf2 n)) end
			| ApxTOne => (POne', fn _ => One')
			| ApxTDown A => (PDown' "", fn n => Down' (Idx LIN A n))
			| ApxTAffi A => (PAffi' "", fn n => Affi' (Idx AFF A n))
			| ApxTBang A => (PBang' "", fn n => Bang' (Idx INT A n))
		fun addEtaSpine (n, Sf) =
				(Subst.shiftHead (H, n),
				appendSpine (SClos (S, Subst.shift n), Sf (1, Nil')))
		fun eta' (ty, n, Sf) = case Util.apxTypePrjAbbrev ty of
			  ApxLolli (S, B) =>
				let val (p, Mf) = etaSyncType S
					val nb = nbinds p
				in LLam' (p, eta' (B, n+nb, fn (n, S) => Sf (n+nb, LApp' (Mf n, S)))) end
			| ApxAddProd (A, B) =>
				AddPair' (eta' (A, n, fn (n, S) => Sf (n, ProjLeft' S)), 
				         eta' (B, n, fn (n, S) => Sf (n, ProjRight' S)))
			| ApxTMonad S =>
				let val (p, Mf) = etaSyncType S
				in Monad' (Let' (p, addEtaSpine (n, Sf), Mon' $ Mf 1)) end
			| ApxTAtomic _ => Atomic' $ addEtaSpine (n, Sf)
			| ApxTAbbrev _ => raise Fail "Internal error: eta': ApxTAbbrev cannot happen"
			| ApxTLogicVar _ => raise ExnDeclError (AmbigType, pp ())
		val etaResult = eta' (A, 0, fn (n, S) => S)
	in case H of
		  Var mn => if Util.isNil S then EtaTag (etaResult, mn) else etaResult
		| _ => etaResult
	end

val etaCount = ref 0

(* etaExpandKind : context * kind -> kind *)
fun etaExpandKind (ctx, ki) = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) =>
			let val A' = etaExpandType (ctx, A)
			in KPi' (x, A', etaExpandKind (ctxCondPushINT (x, asyncTypeToApx A', ctx), K)) end

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
	  TLPi (p, S, B) =>
			let val S' = etaExpandSyncType (ctx, S)
			in TLPi' (p, S', etaExpandType (tpatBindApx (p, syncTypeToApx S) ctx, B)) end
	| AddProd (A, B) => AddProd' (etaExpandType (ctx, A), etaExpandType (ctx, B))
	| TMonad S => TMonad' (etaExpandSyncType (ctx, S))
	| TAtomic (a, S) => TAtomic' (a, etaExpandTypeSpine (ctx, S, kindToApx (sigLookupKind a)))
	| TAbbrev aA => TAbbrev' aA

(* etaExpandTypeSpine : context * typeSpine * apxKind -> typeSpine *)
and etaExpandTypeSpine (ctx, sp, ki) = case (TypeSpine.prj sp, ApxKind.prj ki) of
	  (TNil, ApxType) => TNil'
	| (TApp (N, S), ApxKPi (A, K)) =>
			TApp' (etaExpandObj (ctx, N, A), etaExpandTypeSpine (ctx, S, K))
	| _ => raise Fail "Internal error: etaExpandTypeSpine match"

(* etaExpandSyncType : context * syncType -> syncType *)
and etaExpandSyncType (ctx, ty) = case SyncType.prj ty of
	  LExists (p, S1, S2) =>
			let val S1' = etaExpandSyncType (ctx, S1)
			in LExists' (p, S1', etaExpandSyncType (tpatBindApx (p, syncTypeToApx S1') ctx, S2)) end
	| TOne => TOne'
	| TDown A => TDown' (etaExpandType (ctx, A))
	| TAffi A => TAffi' (etaExpandType (ctx, A))
	| TBang A => TBang' (etaExpandType (ctx, A))

(* etaExpandObj : context * obj * apxAsyncType -> obj *)
and etaExpandObj (ctx, ob, ty) =
	( if !traceEta then
		( print "Eta: "
		; app (fn (x, A, _) => print (x^":"^PrettyPrint.printType (unsafeCast A)^", "))
			(ctx2list ctx)
		; print ("|- "^PrettyPrint.printObj ob^" : "^PrettyPrint.printType (unsafeCast ty)^"\n"))
	  else ()
	; etaExpandObj' (ctx, ob, ty) )
and etaExpandObj' (ctx, ob, ty) =
	let fun pp () = PrettyPrint.printObj ob ^ " : " ^ PrettyPrint.printType (unsafeCast ty) ^ "\n"
	in case (Obj.prj ob, Util.apxTypePrjAbbrev ty) of
	  (_, ApxTLogicVar _) => raise ExnDeclError (AmbigType, pp ())
	| (LLam (p, N), ApxLolli (A, B)) =>
			LLam' (p, etaExpandObj (opatBindApx (p, A) ctx, N, B))
	| (AddPair (N1, N2), ApxAddProd (A, B)) =>
			AddPair' (etaExpandObj (ctx, N1, A), etaExpandObj (ctx, N2, B))
	| (Monad E, ApxTMonad S) => Monad' (etaExpandExp (ctx, E, S))
	| (Atomic (H, S), _) =>
			let val (H', A) = etaExpandHead (ctx, H)
				fun ppH () = PrettyPrint.printObj (Atomic' (H', S)) ^ " : "
						^ PrettyPrint.printType (unsafeCast A) ^ "\n"
			in etaExpand pp (ty, H', #1 $ etaExpandSpine ppH (ctx, S, A)) end
	| (Redex (N, A, S), _) =>
			Redex' (etaExpandObj (ctx, N, A), A, #1 $ etaExpandSpine (fn () => "") (ctx, S, A))
	| (Constraint (N, A), _) => Constraint' (etaExpandObj (ctx, N, ty), etaExpandType (ctx, A))
	| _ => raise Fail "Internal error: etaExpandObj match"
	end

(* etaExpandHead : context * head -> head * apxAsyncType *)
and etaExpandHead (ctx, h) = case h of
	  Const c => (h, asyncTypeToApx (Signatur.sigLookupType c))
	| Var (_, n) => (h, #3 (ctxLookupNum (ctx, n)))
	| UCVar x => (h, asyncTypeToApx (ImplicitVars.ucLookup x))
	| LogicVar X =>
			let val () = if Subst.isId (#s X) then () else raise Fail "Internal error: eta lvar"
				val A = etaExpandType (ctx, #ty X)
			in (LogicVar (X with'ty A), asyncTypeToApx A) end

(* etaExpandSpine : (unit -> string) -> context * spine * apxAsyncType -> spine * apxAsyncType *)
and etaExpandSpine ppH (ctx, sp, ty) = case (Spine.prj sp, Util.apxTypePrjAbbrev ty) of
	  (_, ApxTLogicVar _) => raise ExnDeclError (AmbigType, ppH ())
	| (Nil, A) => (Nil', ApxAsyncType.inj A)
	| (LApp (N, S), ApxLolli (A, B)) =>
			map1 (fn sp => LApp' (etaExpandMonadObj (ctx, N, A), sp))
				(etaExpandSpine ppH (ctx, S, B))
	| (ProjLeft S, ApxAddProd (A, B)) => map1 ProjLeft' (etaExpandSpine ppH (ctx, S, A))
	| (ProjRight S, ApxAddProd (A, B)) => map1 ProjRight' (etaExpandSpine ppH (ctx, S, B))
	| _ => raise Fail "Internal error: etaExpandSpine match"

(* etaExpandExp : context * expObj * apxSyncType -> expObj *)
and etaExpandExp (ctx, ex, ty) = case ExpObj.prj ex of
	  LetRedex (p, S, N, E) =>
			LetRedex' (p, S, etaExpandObj (ctx, N, ApxTMonad' S),
				etaExpandExp (opatBindApx (p, S) ctx, E, ty))
	| Let (p, (H, S), E) =>
			let val (H', A) = etaExpandHead (ctx, H)
				fun ppH () = PrettyPrint.printObj (Atomic' (H', S)) ^ " : "
						^ PrettyPrint.printType (unsafeCast A) ^ "\n"
				val (S', mTy) = etaExpandSpine ppH (ctx, S, A)
			in case Util.apxTypePrjAbbrev mTy of
				  ApxTMonad sTy =>
					Let' (p, (H', S'), etaExpandExp (opatBindApx (p, sTy) ctx, E, ty))
				| _ => raise Fail "Internal error: etaExpandExp type mismatch"
			end
	| Mon M => Mon' (etaExpandMonadObj (ctx, M, ty))

(* etaExpandMonadObj : context * monadObj * apxSyncType -> monadObj *)
and etaExpandMonadObj (ctx, mob, ty) = case (MonadObj.prj mob, ApxSyncType.prj ty) of
	  (DepPair (M1, M2), ApxTTensor (S1, S2)) =>
			DepPair' (etaExpandMonadObj (ctx, M1, S1), etaExpandMonadObj (ctx, M2, S2))
	| (One, ApxTOne) => One'
	| (Down N, ApxTDown A) => Down' (etaExpandObj (ctx, N, A))
	| (Affi N, ApxTAffi A) => Affi' (etaExpandObj (ctx, N, A))
	| (Bang N, ApxTBang A) => Bang' (etaExpandObj (ctx, N, A))
	| _ => raise Fail "Internal error: etaExpandMonadObj match" (* includes MonUndef *)

fun etaExpandKindEC ki = etaExpandKind (emptyCtx, ki)
fun etaExpandTypeEC ty = etaExpandType (emptyCtx, ty)
fun etaExpandObjEC (ob, ty) = etaExpandObj (emptyCtx, ob, ty)

end
