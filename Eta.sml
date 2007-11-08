structure Eta :> ETA =
struct

open Syntax infix with'ty with's
open Signatur

(* etaContract : exn -> Syntax.obj -> int *)
fun etaContract e ob =
	let datatype etaSpine = Ap | LAp | Pl | Pr
		fun eq (x, y) = if x=y then x else raise e
		fun nbinds sp = length (List.filter (fn Ap => true | LAp => true | _ => false) sp)
		fun etaC (ob, sp) = case etaShortcut ob of NONE => etaC' (ob, sp) | SOME k => k
		and etaC' (ob, sp) = case Whnf.whnfObj ob of
			  NfLam (_, N) => etaC (N, Ap::sp)
			| NfLinLam (_, N) => etaC (N, LAp::sp)
			| NfAddPair (N1, N2) => eq (etaC (N1, Pl::sp), etaC (N1, Pr::sp))
			| NfMonad E =>
				let fun expFmap f = ExpObj.Fmap ((fn x=>x, fn x=>x, fn x=>x), f)
				in case expFmap Whnf.whnfExp (Whnf.whnfExp E) of
					  Let (p, N, Mon M) => (etaP (p, M); etaC (Atomic' N, sp))
					| _ => raise e
				end
			| NfAtomic (Var n, _, S) =>
				let val k = n - nbinds sp
					val () = if k>0 then () else raise e
					val () = etaSp (1, S, sp)
				in k end
			| NfAtomic _ => raise e
			| NfUnit => raise e
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
	

(* etaExpand : apxAsyncType * head * apxAsyncType * spine -> obj *)
fun etaExpand (A, H, AH, S) =
	let (*fun Idx A n = EtaTag (etaExpand (A, Var n, A, Nil'), n)*)
		fun Idx A n = etaExpand (A, Var n, A, Nil') (*Atomic' (Var n, Nil')*)
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
				in (PDepPair' ("", asyncTypeFromApx A, p), DepPair' (Idx A (n + nbinds p), M)) end
			| ApxAsync A => (PVar' ("", asyncTypeFromApx A), Norm' (Idx A n))
		fun addEtaSpine (n, Sf) =
				(*Atomic' (Either.leftOf (Subst.headSub (H, Shift n)), 
						Whnf.appendSpine (S, Shift n, (Sf (1, Nil), id)))*)
				Atomic' (Subst.shiftHead (H, n), AH,
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

(* etaExpandKind : kind -> kind *)
fun etaExpandKind ki = Util.KindRec.unfold etaExpandType Kind.prj ki
(*
fun etaExpandKind ki = case Kind.prj ki of
	  Type => Type'
	| KPi (x, A, K) => KPi' (x, etaExpandType A, etaExpandKind K)*)

(* etaExpandType : asyncType -> asyncType *)
and etaExpandType ty = case AsyncType.prj ty of
	  Lolli (A, B) => Lolli' (etaExpandType A, etaExpandType B)
	| TPi (x, A, B) => TPi' (x, etaExpandType A, etaExpandType B)
	| AddProd (A, B) => AddProd' (etaExpandType A, etaExpandType B)
	| Top => Top'
	| TMonad S => TMonad' (etaExpandSyncType S)
	| TAtomic (a, S) => TAtomic' (a, etaExpandTypeSpine (S, kindToApx (sigLookupKind a)))
	| TAbbrev aA => TAbbrev' aA

(* etaExpandTypeSpine : typeSpine * apxKind -> typeSpine *)
and etaExpandTypeSpine (sp, ki) = case (TypeSpine.prj sp, ApxKind.prj ki) of
	  (TNil, ApxType) => TNil'
	| (TApp (N, S), ApxKPi (A, K)) => TApp' (etaExpandObj (N, A), etaExpandTypeSpine (S, K))
	| _ => raise Fail "Internal error etaExpandTypeSpine: Match\n"

(* etaExpandSyncType : syncType -> syncType *)
and etaExpandSyncType ty = Util.SyncTypeRec.unfold etaExpandType SyncType.prj ty
(*
and etaExpandSyncType ty = case SyncType.prj ty of
	  TTensor (S1, S2) => TTensor' (etaExpandSyncType S1, etaExpandSyncType S2)
	| TOne => TOne'
	| Exists (x, A, S) => Exists' (x, etaExpandType A, etaExpandSyncType S)
	| Async A => Async' (etaExpandType A)*)

(* etaExpandObj : obj * apxAsyncType -> obj *)
and etaExpandObj (ob, ty) = case (Obj.prj ob, Util.apxTypePrjAbbrev ty) of
	  (_, ApxTLogicVar _) => raise Fail "Ambiguous typing\n"
	| (LinLam (x, N), ApxLolli (_, B)) =>
			LinLam' (x, etaExpandObj (N, B))
	| (Lam (x, N), ApxTPi (_, B)) =>
			Lam' (x, etaExpandObj (N, B))
	| (AddPair (N1, N2), ApxAddProd (A, B)) =>
			AddPair' (etaExpandObj (N1, A), etaExpandObj (N2, B))
	| (Unit, ApxTop) => Unit'
	| (Monad E, ApxTMonad S) => Monad' (etaExpandExp (E, S))
	| (Atomic (H, A, S), _) => etaExpand (ty, etaExpandHead H, A, etaExpandSpine (S, A))
	| (Redex (N, A, S), _) => Redex' (etaExpandObj (N, A), A, etaExpandSpine (S, A))
	| (Constraint (N, A), _) => Constraint' (etaExpandObj (N, ty), etaExpandType A)
	| _ => raise Fail "Internal error etaExpandObj: Match\n"

(* etaExpandHead : head -> head *)
and etaExpandHead h = case h of
	  LogicVar X => LogicVar (X with'ty etaExpandType (#ty X))
	| _ => h

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

(* etaExpandSpine : spine * apxAsyncType -> spine *)
and etaExpandSpine (sp, ty) = case (Spine.prj sp, Util.apxTypePrjAbbrev ty) of
	  (_, ApxTLogicVar _) => raise Fail "Ambiguous typing\n"
	| (Nil, _) => Nil'
	| (App (N, S), ApxTPi (A, B)) => App' (etaExpandObj (N, A), etaExpandSpine (S, B))
	| (LinApp (N, S), ApxLolli (A, B)) => LinApp' (etaExpandObj (N, A), etaExpandSpine (S, B))
	| (ProjLeft S, ApxAddProd (A, B)) => ProjLeft' (etaExpandSpine (S, A))
	| (ProjRight S, ApxAddProd (A, B)) => ProjRight' (etaExpandSpine (S, B))
	| _ => raise Fail "Internal error etaExpandSpine: Match\n"

(* etaExpandExp : expObj * apxSyncType -> expObj *)
and etaExpandExp (ex, ty) = case ExpObj.prj ex of
	  Let (p, N, E) =>
			let fun eta' (Atomic (H, A, S)) = Atomic' (etaExpandHead H, A, etaExpandSpine (S, A))
				  | eta' N = etaExpandObj (Obj.inj N, ApxTMonad' (ApproxTypes.pat2apxSyncType p))
			in Let' (etaExpandPattern p, eta' (Obj.prj N), etaExpandExp (E, ty)) end
	| Mon M => Mon' (etaExpandMonadObj (M, ty))

(* etaExpandPattern : pattern -> pattern *)
and etaExpandPattern p = Util.PatternRec.unfold etaExpandType Pattern.prj p
(*
and etaExpandPattern p = case Pattern.prj p of
	  PTensor (p1, p2) => PTensor' (etaExpandPattern p1, etaExpandPattern p2)
	| POne => POne'
	| PDepPair (x, A, p) => PDepPair' (x, etaExpandType A, etaExpandPattern p)
	| PVar (x, A) => PVar' (x, etaExpandType A)*)

(* etaExpandMonadObj : monadObj * apxSyncType -> monadObj *)
and etaExpandMonadObj (mob, ty) = case (MonadObj.prj mob, ApxSyncType.prj ty) of
	  (Tensor (M1, M2), ApxTTensor (S1, S2)) =>
			Tensor' (etaExpandMonadObj (M1, S1), etaExpandMonadObj (M2, S2))
	| (One, ApxTOne) => One'
	| (DepPair (N, M), ApxExists (A, S)) =>
			DepPair' (etaExpandObj (N, A), etaExpandMonadObj (M, S))
	| (Norm N, ApxAsync A) => Norm' (etaExpandObj (N, A))
	| _ => raise Fail "Internal error etaExpandMonadObj: Match"


end
