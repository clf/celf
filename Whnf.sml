functor WhnfFun (Syn : SYNTAX_CORE2) : WHNF =
struct

structure Syn = Syn
open Syn

(* appendSpine : spine * spine -> spine *)
fun appendSpine (S1', S2) = case Spine.prj S1' of
	  Nil => S2
	| LinApp (N, S1) => LinApp' (N, appendSpine (S1, S2))
	| App (N, S1) => App' (N, appendSpine (S1, S2))
	| ProjLeft S1 => ProjLeft' (appendSpine (S1, S2))
	| ProjRight S1 => ProjRight' (appendSpine (S1, S2))

fun whnfObj N = whnfObjP (Obj.prj N)

and whnfObjP (Redex (N, _, S)) = whnfRedex (N, S)
  | whnfObjP (Constraint (N, _)) = whnfObj N
  | whnfObjP (LinLam xN) = NfLinLam xN
  | whnfObjP (Lam xN) = NfLam xN
  | whnfObjP (AddPair N1N2) = NfAddPair N1N2
  | whnfObjP Unit = NfUnit
  | whnfObjP (Monad E) = NfMonad E
  | whnfObjP (Atomic hAS) = NfAtomic hAS

and whnfRedex (ob, sp) = case (Obj.prj ob, Spine.prj sp) of
	  (N, Nil) => whnfObjP N
	| (LinLam (_, N1), LinApp (N2, S)) => whnfRedex (Clos (N1, Subst.sub N2), S)
	| (Lam (_, N1), App (N2, S)) => whnfRedex (Clos (N1, Subst.sub N2), S)
	| (AddPair (N, _), ProjLeft S) => whnfRedex (N, S)
	| (AddPair (_, N), ProjRight S) => whnfRedex (N, S)
	| (Atomic (H, A, S1), S2) => NfAtomic (H, A, appendSpine (S1, Spine.inj S2))
	| (Redex (N, A, S1), S2) => whnfRedex (N, appendSpine (S1, Spine.inj S2))
	| (Constraint (N, A), S) => whnfRedex (N, Spine.inj S)
	| _ => raise Fail "Internal error: whnfRedex\n"


fun whnfExp e = whnfExpP (ExpObj.prj e)
and whnfExpP (Mon M) = Mon M
  | whnfExpP (Let (p, N, E)) =
		(case whnfObj N of
			  NfMonad E' =>
				(case ExpObj.prj E' of
					  Mon M => whnfExp (whnfLetRedex (p, M, E))
					| Let (q, N', E'') =>
							whnfExpP (Let (q, N',
								Let' (PClos (p, Subst.shift (nbinds q)), Monad' E'',
								EClos (E, Subst.dotn (nbinds p) (Subst.shift (nbinds q)))))))
			| NfAtomic hAS => Let (p, hAS, E)
			| _ => raise Fail "Internal error: whnfMonObj\n")
and whnfLetRedex (p, M, E) = case (Pattern.prj p, MonadObj.prj M) of
	  (PTensor (p1, p2), Tensor (M1, M2)) =>
			(* p2 should be PClos(p2,nbinds p1) in the redex below, but
			   it doesn't matter since the types are not considered *)
			whnfLetRedex (p1, M1, whnfLetRedex (p2, MClos (M2, Subst.shift (nbinds p1)), E))
	| (POne, One) => E
	| (PDepPair (x, _, p1), DepPair (N, M1)) => EClos (whnfLetRedex (p1, M1, E), Subst.sub N)
	| (PVar (x, _), Norm N) => EClos (E, Subst.sub N)
	| _ => raise Fail "Internal error: whnfLetRedex\n"


(*
val whnfLetSpine = ExpObjAuxDefs.unfold whnfExp

val normalizeKind = Util.objExpMapKind whnfExp whnfObj
val normalizeType = Util.objExpMapType whnfExp whnfObj
val normalizeObj = Util.objExpMapObj whnfExp whnfObj
*)

end
