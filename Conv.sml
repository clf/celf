(* Convertibility among CLF terms and types *)
(* Author: Carsten Schuermann *)
(* Walked: Oct 18, 12:00 *)

structure Conv :> CONV =
struct

(* All objects, types, spines, patterns, expressions and monadic objects are
   assumed to be well-typed and in normal form  *)

(* does currently not weak head reduce.  --cs *)

open Syntax


(* Invariant:  convAsynType (ty1, ty2) => ()
   if  G |- ty1 == ty2 : kind
   otherwise Fail is raised 
*)
fun convAsyncType (ty1, ty2) = case (Util.typePrjAbbrev ty1, Util.typePrjAbbrev ty2) of
       (TPi (_, A1, A2), TPi (_, B1, B2)) =>
         (convAsyncType (A1, B1); convAsyncType (A2, B2))
     | (Lolli (A1, A2), Lolli (B1, B2)) => 
         (convAsyncType (A1, B1); convAsyncType (A2, B2))
     | (AddProd (A1, A2), AddProd (B1, B2)) =>
         (convAsyncType (A1, B1); convAsyncType (A2, B2))
     | (Top, Top) => ()
     | (TAtomic (a1, imp1, TS1), TAtomic (a2, imp2, TS2)) =>
	 if (a1 = a2) then convTypeSpine (foldr TApp' TS1 imp1, foldr TApp' TS2 imp2)
	   else raise Fail "Convertibility: Type Clash"
     | _ => raise Fail "Convertibility"


(* Invariant:  convTypeSpine (TS1, TS2) => ()
   if  G |- TS1 == TS2 : K1 > K2
   otherwise Fail is raised 
*)
and convTypeSpine (ts1, ts2) = case (TypeSpine.prj ts1, TypeSpine.prj ts2) of
       (TNil, TNil) => ()
     | (TApp (M1, TS1), TApp (M2, TS2)) => (convObj (M1, M2); convTypeSpine (TS1, TS2))
     | _ => raise Fail "Convertibility"


(* Invariant:  convObj (N1, N2) => ()
   if  G |- N1 == N2 : A
   otherwise Fail is raised 
*)
and convObj (ob1, ob2) = case (Obj.prj ob1, Obj.prj ob2) of
       (Lam (x, N), Lam (y, M)) => convObj (N, M)
     | (LinLam (x, N), LinLam (y, M)) => convObj (N, M)
     | (AddPair (N1, N2), AddPair (M1, M2)) => (convObj (N1, M1); convObj (N2, M2))
     | (Unit, Unit) => ()
     | (Monad E1, Monad E2) => convExpObj (E1, E2)
     | (Atomic (H1, _, S1), Atomic (H2, _, S2)) => 
	 (convHead (H1, H2); convSpine (S1, S2))
     | _ => raise Fail "Error in convertibilty"


(* Invariant:  convHead (H1, H2) => ()
   if  G |- H1 == H2 : A
   otherwise Fail is raised 
*)
and convHead (hd1, hd2) = case (hd1, hd2) of
      (Const (c1, impl1), Const (c2, impl2)) => 
	if c1 = c2 then convSpine (foldr App' Nil' impl1, foldr App' Nil' impl2)
	  else raise Fail "Convertibilty failed: Head mismatch"
     | (Var n1, Var n2) =>  
	if n1 = n2 then ()
	  else raise Fail "Convertibilty failed: Bound variable clash"
     | _ => raise Fail "Convertibility failed"


(* Invariant:  convSpine (S1, S2) => ()
   if  G |- S1 == S2 : A1 > A2 
   otherwise Fail is raised 
*)
and convSpine (sp1, sp2) = case (Spine.prj sp1, Spine.prj sp2) of
	 (Nil, Nil) => ()
     | (App (N1, S1), App (N2, S2)) => (convObj (N1, N2); convSpine (S1, S2))
     | (LinApp (N1, S1), LinApp (N2, S2)) => (convObj (N1, N2); convSpine (S1, S2))
     | (ProjLeft S1, ProjLeft S2) => convSpine (S1, S2)
     | (ProjRight S1, ProjRight S2) => convSpine (S1, S2)
     | _ => raise Fail "Convertibility failed"
   

(* Invariant:  convMonadObj (M1, M2) => ()
   if  G |- M1 == M2 : S
   otherwise Fail is raised 
*)
and convMonadObj (M1, M2) = case (MonadObj.prj M1, MonadObj.prj M2) of 
       (Tensor (M11, M12), Tensor (M21, M22)) => 
	 (convMonadObj (M11, M21); convMonadObj (M12, M22))
     | (One, One) => ()
     | (DepPair (N1, M1), DepPair (N2, M2)) => 
	 (convObj (N1, N2);  convMonadObj (M1, M2))
     | (Norm N1, Norm N2) => convObj (N1, N2)
     | _ => raise Fail "Convertibility failed"


(* Invariant:  convExpObj (E1, E2)  => ()
   if  G |- let P11 = R11 in ... let P1n = R1n in E1 
            == let P21 = R21 in ... let P2n = R2n in E2 : S
   otherwise Fail is raised 
   where n = |C1| = |C2| 
   and   Ci = ((Pi1, Ri1), ..., (Pin, Rin))
*)
and convExpObj (E1, E2) = case (ExpObj.prj E1, ExpObj.prj E2) of
       (Mon M1, Mon M2) => convMonadObj (M1, M2)
     | (Let (P1, R1, E1'), Let (P2, R2, E2')) => 
	 convExpObj (E1', convExpObj1 (E1, E2)) 
     | _ => raise Fail "Convertibility failed"


(* Invariant:
   If    G |- E1 == let P1=R1 in E1' : S
   and   G |- E2 : S
   then  there exists E, such that
   and   G, P1 |- E = convExpObj1 (E1, E2) : S
   and   E2 == let P1=R1 in E: S
*)
and convExpObj1 (E1, E2) = case (ExpObj.prj E1, ExpObj.prj E2) of
       (Let (P1, R1, _), Let (P2, R2, E2')) =>
	  if ((convObj (R1, R2); true) handle Fail _ => false) then E2'
	  else
	    let val s1 = Subst.shift (nbinds P1)
	    in (Let' (PClos (P2, s1), Clos (R2, s1), 
		      EClos (convExpObj1 (EClos (E1, Subst.shift (nbinds P2)), E2'),
			     switchSub (nbinds P1, nbinds P2))))
	    end
	| _ => raise Fail "Convertibility failed"

(* please move below *)

(* Invariant: 
   Let G1, G2 contexts,
   n1 = | G1 | , n2 = | G2 |
   and G2' = k-prefix of G2
   G1, G2 |- switchSub' (k,n1,n2) : G1, G2'
*)

and switchSub' (0, n1, n2) = Subst.dotn n2 (Subst.shift n1)     
  | switchSub' (k, n1, n2) = Subst.dot (EtaTag (Unit', n2+n1+1-k), switchSub' (k-1, n1, n2))

(* Invariant: 
   Let G1, G2 contexts,
   n1 = | G1 | , n2 = | G2 |
   G1, G2 |- switchSub (n1,n2) : G1, G2
*)
and switchSub (n1, n2) = switchSub' (n1, n1, n2)
end