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

signature TLU_Match = TOP_LEVEL_UTIL
structure Match :> MATCH =
struct

open VRef infix ::=
open InternalSyntax

structure ISubst = InternalSubst

val outputMatch = ref false

exception ExnMatch of string

val numInst = ref 0

(* instantiate : nfObj option vref * nfObj * constr vref list vref * word -> unit *)
fun instantiate (r, rInst, l : int) =
    if isSome (!! r)
    then raise Fail ("Internal error: double instantiation " ^ Int.toString l ^ " to " ^ PrettyPrinting.printObj rInst)
    else
      ( r ::= SOME rInst
      ; numInst := !numInst + 1
      ; if !outputMatch then
          print ("Instantiating ("^Int.toString (!numInst)^") $"^(Int.toString (* Word.toString *) l)^" = "
                 ^(PrettyPrinting.printObj $ rInst)^"\n")
        else () )

(* lowerLVar : nfAsyncType * nfSpine * subst * context -> nfObj * nfObj nfObjF *)
(* Invariant:
 * lowerLVar (ty, sp, s, G) = (rInst, Y)
 * G |- rInst : ty
 * G1' |- s : G
 * G2' |- sp : ty[s] > a
 * G1'+G2' |- Y = rInst[s] sp : a
 *)
fun lowerLVar (ty, sp, s) =
    case (ty, sp) of
      (TLPi (p, A, B), LApp (M, S)) =>
      let
        val p' = patternTypeToObj p
        val (rInst, Y) = lowerLVar (B, S, ISubst.mkSubstMonad (M, s))
      in
        (LLam (p', rInst), Y)
      end
    | (AddProd (A, B), ProjLeft S) =>
      let
        val (rInst, Y) = lowerLVar (A, S, s)
      in
        (AddPair (rInst, newLVar B), Y)
      end
    | (AddProd (A, B), ProjRight S) =>
      let
        val (rInst, Y) = lowerLVar (B, S, s)
      in
        (AddPair (newLVar A, rInst), Y)
      end
    | (TAtomic _, Nil) =>
      let
        val X = newLVar ty
      in
        (X, ISubst.substObj (X, s))
      end
    | (TMonad _, Nil) => raise Fail "Internal error: TODO lowerLVar Monad"
      (* let *)
      (*   val X = newLVar ty *)
      (* in *)
      (*   (X, ISubst.substObj (X, s)) *)
      (* end *)
    | _ => raise Fail "Internal error: lowerLVar"

fun invAtomic (Atomic a) = a
  | invAtomic _ = raise Fail "Internal error: invAtomic"

(* lowerAtomic : nfHead * nfSpine -> nfHead * nfSpine *)
fun lowerAtomic (N as (LogicVar {X, ty, s, tag}, S)) =
    (case S of
       Nil => N
     | _ =>
       let
         val (rInst, Y) = lowerLVar (ty, S, s)
       in
         instantiate (X, rInst, tag); invAtomic Y
       end)
  | lowerAtomic hS = hS

fun lowerObj (Atomic hS) = Atomic (lowerAtomic hS)
  | lowerObj N = N

fun lowerExp (Let (eps, mon)) = raise Fail "Internal error: lowerExp not implemented" (* NfLet (p, lowerAtomic hS, E)*)

fun isLVar (LogicVar _, _) = true
  | isLVar _ = false

fun invLVar (LogicVar Z, _) = Z
  | invLVar _ = raise Fail "Internal error: invLVar"

fun pat2mon p =
    let
      fun pat2mon' p n =
          case p of
            PDepTensor (p1, p2) => DepPair (pat2mon' p1 (n + numBinds p2), pat2mon' p2 n)
          | POne => One
          | PDown _ => Down (Atomic (Var (LIN, n), Nil))
          | PAffi _ => Affi (Atomic (Var (AFF, n), Nil))
          | PBang _ => Bang (Atomic (Var (INT, n), Nil))
    in
      pat2mon' p 1
    end

val matchProblemCounter = ref 0
fun matchProblemCount () =
    ( matchProblemCounter := (!matchProblemCounter) + 1
    ; !matchProblemCounter )


(* matchObj (ob1, ob2)
 * matches pattern object ob1 against ground object ob2
 * Raises ExnMatch if matching fails; returns () if matching succeeds *)
fun matchObj (obPat', obGnd') =
    let
      val obPat = lowerObj (ISubst.whnfObj obPat')
      (* val obGnd = ISubst.normalizeObj obGnd' *)

      val obGnd = ISubst.whnfObj obGnd'

      val () = if !outputMatch then
                 ( print "["
                 ; print (Int.toString (matchProblemCount ()))
                 ; print "] Matching "
                 ; print (PrettyPrinting.printPreObj obPat)
                 ; print " and "
                 ; print (PrettyPrinting.printPreObj obGnd)
                 ; print "\n" )
               else ()

      fun invLam p hS = ISubst.reduceObj (ISubst.substObj (Atomic hS, Shift (numBinds p)),
                                            LApp (pat2mon p, Nil))
      fun invPair p hS = ISubst.reduceObj (Atomic hS, p Nil)
    in
      case (obPat, obGnd) of
        (LLam (_, N1), LLam (_, N2)) => matchObj (N1, N2)
      | (LLam (p, N2), Atomic hS1) => raise ExnMatch "matchObj NfLLam-NfAtomic"
      | (Atomic hS1, LLam (p, N2)) => matchObj (invLam p hS1, N2)
      | (AddPair (L1, N1), AddPair (L2, N2)) =>
        ( matchObj (L1, L2)
        ; matchObj (N1, N2) )
      | (Atomic hS1, AddPair (L2, N2)) =>
        ( matchObj (invPair ProjLeft hS1, L2)
        ; matchObj (invPair ProjRight hS1, N2) )
      | (AddPair (L1, N1), Atomic hS2) => raise ExnMatch "matchObj NfAddPair-NfAtomic"
      | (Monad E1, Monad E2) => print "Warning: matching on traces is not implemented (Monad-Monad)"
      | (Atomic hS, Monad E) => print "Warning: matching on traces is not implemented (Atomic-Monad)"
      | (Monad E, Atomic hS) => print "Warning: matching on traces is not implemented (Monad-Atomic)"
      | (Atomic hS1, Atomic hS2) => matchHeadSp (hS1, hS2)
      | (N1, N2) => raise Fail "Internal error: matchObj"
    end

and matchHeadSp (hS1 as (h1, S1), hS2 as (h2, S2)) =
    case (h1, h2) of
      (Const c1, Const c2) => if c1 <> c2
                              then raise ExnMatch "matchHeadSp Const-Const"
                              else matchSpine (S1, S2)
    | (UCVar x1, UCVar x2) => if x1 <> x2
                              then raise ExnMatch "matchHeadSp UCVar-UCVar"
                              else matchSpine (S1, S2)
    | (Var n1, Var n2) => if n1 <> n2
                          then raise ExnMatch "matchObj Var-Var"
                          else matchSpine (S1, S2)
    | (LogicVar (X as {X=r, s, tag, ty, ...}), _) =>
      let
        val () = if !outputMatch then
                   print ("Matching LVar " ^ Int.toString tag ^ PrettyPrinting.printSubst s ^ " of type " ^ PrettyPrinting.printType ty ^ "  " ^ PrettyPrinting.printObj (Atomic hS1) ^ "\n")
                 else ()
        fun patSub s = ISubst.patternSubst (fn ob => (ob, true)) ISubst.etaContract s
        val sinv =
            case patSub s of
                NONE => raise Fail ("Internal error: not a pattern substitution " ^ PrettyPrinting.printSubst s)
              | SOME (p, s') =>
                let
                  val sinv = ISubst.invert s'
                in
                  if !outputMatch then
                    print ("Inverted substitution "^PrettyPrinting.printSubst s' ^ " == " ^PrettyPrinting.printSubst sinv^"\n")
                  else ()
                ; sinv
                end
      (* The linear-changing substitution is irrelevant
       * since it behaves like the identity
       * s = s' o lcis2sub p = (lcis2sub (lcisComp (p, invert s'))) o s'
       * cf. Subst.patSub and Subst.lcisComp *)
      in
        instantiate (r, ISubst.substObj (Atomic hS2, sinv), tag)
      end
    | (_, LogicVar X) =>
      ( case !!(#X X) of
            SOME _ => raise Fail "Internal error: not ground object" (* matchObj (Atomic hS1, ISubst.whnfObj (Atomic hS2)) *)
          | NONE =>
            raise Fail ("Internal error: ground side contains LVar\nPattern: "
                        ^ PrettyPrinting.printObj (Atomic hS1)
                        ^ "\nObject: "
                        ^ PrettyPrinting.printObj (Atomic hS2) ^ "\n"
                        ^ (case !!(#X X) of
                               SOME ob => PrettyPrinting.printObj ob
                             | NONE => "????") ^ "\n")
      )
    | _ => raise ExnMatch "matchHeadSp"
and matchSpine (sp1, sp2) =
    case (sp1, sp2) of
      (Nil, Nil) => ()
    | (LApp (M1, S1), LApp (M2, S2)) => (matchMon (M1, M2); matchSpine (S1, S2))
    | (ProjLeft S1, ProjLeft S2) => matchSpine (S1, S2)
    | (ProjRight S1, ProjRight S2) => matchSpine (S1, S2)
    | (ProjLeft _, ProjRight _) => raise ExnMatch "matchSpine Left-Right"
    | (ProjRight _, ProjLeft _) => raise ExnMatch "matchSpine Right-Left"
    | _ => raise Fail "Internal error: matchSpine"
and matchMon (m1, m2) =
    case (m1, m2) of
      (DepPair (M11, M12), DepPair (M21, M22)) =>
      (matchMon (M11, M21); matchMon (M12, M22))
    | (One, One) => ()
    | (Down N1, Down N2) => matchObj (N1, N2)
    | (Affi N1, Affi N2) => matchObj (N1, N2)
    | (Bang N1, Bang N2) => matchObj (N1, N2)
    | _ => raise Fail "Internal error: matchMon"

fun match (ob1, ob2) sc =
    (matchObj (ob1, ob2); sc () )
    handle ExnMatch _ => ()

fun matchList (obs1, obs2) sc =
    let
      fun match' (ob1, ob2) = matchObj (ob1, ob2)
    in
      ( List.app match' (ListPair.zip (obs1, obs2)) ; sc () )
      handle ExnMatch _ => ()
    end

end
