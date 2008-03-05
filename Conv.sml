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
fun convAsyncType (ty1, ty2) = case (Util.nfTypePrjAbbrev ty1, Util.nfTypePrjAbbrev ty2) of
       (TPi (x1, A1, B1), TPi (x2, A2, B2)) =>
			let val B1' = if isSome x1 then B1 else NfTClos (B1, Subst.shift 1)
				val B2' = if isSome x2 then B2 else NfTClos (B2, Subst.shift 1)
         in (convAsyncType (A1, A2); convAsyncType (B1', B2')) end
     | (Lolli (A1, B1), Lolli (A2, B2)) => 
         (convAsyncType (A1, A2); convAsyncType (B1, B2))
     | (AddProd (A1, B1), AddProd (A2, B2)) =>
         (convAsyncType (A1, A2); convAsyncType (B1, B2))
     | (Top, Top) => ()
     | (TAtomic (a1, TS1), TAtomic (a2, TS2)) =>
	 if (a1 = a2) then convTypeSpine (TS1, TS2)
	   else raise Fail "Convertibility: Type Clash"
	 | (TMonad S1, TMonad S2) => convSyncType (S1, S2)
     | _ => raise Fail "Convertibility: Types differ"


(* Invariant:  convTypeSpine (TS1, TS2) => ()
   if  G |- TS1 == TS2 : K1 > K2
   otherwise Fail is raised 
*)
and convTypeSpine (ts1, ts2) = case (NfTypeSpine.prj ts1, NfTypeSpine.prj ts2) of
       (TNil, TNil) => ()
     | (TApp (M1, TS1), TApp (M2, TS2)) => (convObj (M1, M2); convTypeSpine (TS1, TS2))
     | _ => raise Fail "Convertibility"

and convSyncType (st1, st2) = case (NfSyncType.prj st1, NfSyncType.prj st2) of
	  (TTensor (S1, T1), TTensor (S2, T2)) => (convSyncType (S1, S2); convSyncType (T1, T2))
	| (TOne, TOne) => ()
	| (Exists (x1, A1, S1), Exists (x2, A2, S2)) =>
			let val S1' = if isSome x1 then S1 else NfSTClos (S1, Subst.shift 1)
				val S2' = if isSome x2 then S2 else NfSTClos (S2, Subst.shift 1)
			in (convAsyncType (A1, A2); convSyncType (S1', S2')) end
	| (Async A1, Async A2) => convAsyncType (A1, A2)
	| _ => raise Fail "Convertibility: SyncTypes differ"

(* Invariant:  convObj (N1, N2) => ()
   if  G |- N1 == N2 : A
   otherwise Fail is raised 
*)
and convObj (ob1, ob2) = case (NfObj.prj ob1, NfObj.prj ob2) of
       (NfLam (x, N), NfLam (y, M)) => convObj (N, M)
     | (NfLinLam (x, N), NfLinLam (y, M)) => convObj (N, M)
     | (NfAddPair (N1, N2), NfAddPair (M1, M2)) => (convObj (N1, M1); convObj (N2, M2))
     | (NfUnit, NfUnit) => ()
     | (NfMonad E1, NfMonad E2) => convExpObj (E1, E2)
     | (NfAtomic (H1, S1), NfAtomic (H2, S2)) => 
	 (convHead (H1, H2); convSpine (S1, S2))
     | _ => raise Fail ("Error in convertibilty of "^PrettyPrint.printObj (unnormalizeObj ob1)
	 			^" and "^PrettyPrint.printObj (unnormalizeObj ob2))


(* Invariant:  convHead (H1, H2) => ()
   if  G |- H1 == H2 : A
   otherwise Fail is raised 
*)
and convHead (hd1, hd2) = case (hd1, hd2) of
      (Const c1, Const c2) => 
	if c1 = c2 then ()
	  else raise Fail "Convertibilty failed: Head mismatch"
     | (Var n1, Var n2) =>  
	if n1 = n2 then ()
	  else raise Fail "Convertibilty failed: Bound variable clash"
     | _ => raise Fail "Convertibility failed"


(* Invariant:  convSpine (S1, S2) => ()
   if  G |- S1 == S2 : A1 > A2 
   otherwise Fail is raised 
*)
and convSpine (sp1, sp2) = case (NfSpine.prj sp1, NfSpine.prj sp2) of
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
and convMonadObj (M1, M2) = case (NfMonadObj.prj M1, NfMonadObj.prj M2) of 
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
and convExpObj (E1, E2) = case (NfExpObj.prj E1, NfExpObj.prj E2) of
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
and convExpObj1 (E1, E2) = case (NfExpObj.prj E1, NfExpObj.prj E2) of
       (Let (P1, (H1, S1), _), Let (P2, (H2, S2), E2')) =>
	  if ((convHead (H1, H2); convSpine (S1, S2); true) handle Fail _ => false) then E2'
	  else
	    let val s1 = Subst.shift (nfnbinds P1)
	    in NfExpObj.inj (Let (NfPClos (P2, s1),
			(Subst.shiftHead (H2, nfnbinds P1), NfSClos (S2, s1)),
		      NfEClos (convExpObj1 (NfEClos (E1, Subst.shift (nfnbinds P2)), E2'),
			     Subst.switchSub (nfnbinds P1, nfnbinds P2))))
	    end
	| _ => raise Fail "Convertibility failed"

end
