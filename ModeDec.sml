(* Based on Twelf *)

structure ModeDec :> MODEDEC =
struct

open Syntax

datatype Arg = Implicit | Explicit | Local

(* Representation invariant:

       The modes of parameters are represented in the following mode list

       M ::= . | M, <mode, Arg>

       G corresponds to a context. We say M is a mode list for U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for all other syntactic categories)

       The main function of this module is to
        (a) assign modes to implicit arguments in a type family
        (b) check the mode specification for consistency

       Example:

         a : type.
         b : a -> a -> type.
         c : b X X -> b X Y -> type.

       Then

         %mode c +M -N.

       will infer X to be input and Y to be output

         %mode +{X:a} -{Y:a} +{M:b X Y} -{N:b X Y} (c M N).

       Generally, it is inconsistent
       for an unspecified ( * ) or output (-) argument to occur
       in the type of an input (+) argument
 *)

type mcontext = (mode * Arg) list

(* modeConsistent (m1, m2) = true
   iff it is consistent for a variable x with mode m1
   to occur as an index object in the type of a variable y:V(x) with mode m2

   m1\m2 + -
    +    Y Y
    -    N Y

   The entries y,n constitute a bug fix, Wed Aug 20 11:50:27 2003 -fp
   The entry n specifies that the type
 *)
fun modeConsistent (Star, _) = raise Fail "Internal error: declared mode *"
      | modeConsistent (_, Star) = raise Fail "Internal error: declared mode *2"
      | modeConsistent (Minus _, Plus) = false   (* m1 should be Plus *)
      | modeConsistent _ = true

(* fun empty : int * mcontext * kind -> (mcontext, kind)

   empty (k, ms, K) = (ms', K')

   Invariant:
   If    K = Pi x_1:A_1. .. Pi x_n:A_n. K1
   and   K has n implicit arguments
   then  ms' = <*, Implicit> ... <*, Implicit>  ms   (n times)
   and   K' = K1
 *)

fun empty (0, ms, K) = (ms, K)
  | empty (n, ms, ki) =
    case NfKind.prj ki of
        Type => raise Fail "Internal error: more implicit args than actual args"
      | KPi (_, _, B) => empty (n-1, (Star, Implicit) :: ms, B)

(* fun pushLocal : int * mcontext -> mcontext *)
fun pushLocal (0, ms) = ms
  | pushLocal (n, ms) = (Star, Local) :: pushLocal (n-1, ms)

(* inferVar (ms, m, k) = ms'

   Invariant:
   If  ms is a mode list,
   and k is declared with mode mk in ms
   and m is the mode for a variable y in whose type k occurs
   then ms' is the same as ms replacing only mk by
   mk' = m o mk

   m o mk  + * -
   --------------
   +       + + +
   -       + - -


    Effect: if the mode mk for k was explicitly declared and inconsistent
            with m o mk, an error is raised
 *)

fun inferVar ((Star, Implicit)::ms, m, 1) = (m, Implicit) :: ms
  | inferVar ((_, Implicit)::ms, Plus, 1) = (Plus, Implicit) :: ms
  | inferVar (ms as (_, Implicit) :: _, _, 1) = ms
  | inferVar (ms as (_, Local) :: _, _, 1) = ms
  | inferVar (ms as (m', Explicit) :: _, m, 1) =
    if modeConsistent (m', m)
    then ms
    else raise ExnDeclError (ModeErr, "Mode declaration not consistent")
  | inferVar (m'::ms, m, n) = m' :: inferVar (ms, m, n-1)
  | inferVar ([], _, _) = raise Fail "Internal error: out of bound index"



(* fun inferSyncType : mcontext * mode * syncType -> mcontext *)
fun inferSyncType (ms, m, sty) =
    case NfSyncType.prj sty of
        LExists (p, S1, S2)
        => let val nb = nbinds p in
               List.drop (inferSyncType (pushLocal (nb, inferPatType (ms, m, p, S1)), m, S2), nb)
           end
      | TOne => ms
      | TDown A => inferType (ms, m, A)
      | TAffi A => inferType (ms, m, A)
      | TBang A => inferType (ms, m, A)

(* fun inferPatType : mcontext * mode * tpattern * syncType -> mcontext *)
and inferPatType (ms, m, p, sty) =
    case (Pattern.prj p, NfSyncType.prj sty) of
        (PDepTensor (p1, p2), LExists (_, S1, S2))
        => let val nb = nbinds p in
               List.drop (inferPatType (pushLocal (nb, inferPatType (ms, m, p1, S1)), m, p2, S2), nb)
           end
      | (POne, TOne) => ms
      | (PDown _, TDown A) => inferType (ms, m, A)
      | (PAffi _, TAffi A) => inferType (ms, m, A)
      | (PBang _, TBang A) => inferType (ms, m, A)
      | (_,_) => raise Fail "Internal error: inferPatType: patterns and type do not match"

(* fun inferTypeSpine : mcontext * mode * typeSpine -> mcontext *)
and inferTypeSpine (ms, m, sp) =
    case NfTypeSpine.prj sp of
        TNil => ms
      | TApp (N, S) => inferTypeSpine (inferObj (ms, m, N), m, S)

and inferHeadSpine (ms, m, H, sp) =
    case H of
        Const _ => inferSpine (ms, m, sp)
      | Var (_, n) => inferSpine (inferVar (ms, m, n), m, sp)
      | UCVar _ => raise Fail "Internal error: inferHeadSpine on UCVar"
      | LogicVar _ => raise Fail "Internal error: inferHeadSpine on LogicVar"

and inferObj (ms, m, ob) =
    case NfObj.prj ob of
        NfLLam (p, N)
        => let val nb = nbinds p in
               List.drop (inferObj (pushLocal (nb, ms), m, N), nb)
           end
      | NfAddPair (N1, N2) => inferObj (inferObj (ms, m, N1), m, N2)
      | NfMonad E => inferExpObj (ms, m, E)
      | NfAtomic (H, S) => inferHeadSpine (ms, m, H, S)

and inferSpine (ms, m, sp) =
    case NfSpine.prj sp of
        Nil => ms
      | LApp (M, S) => inferSpine (inferMonObj (ms, m, M), m, S)
      | ProjLeft S => inferSpine (ms, m, S)
      | ProjRight S => inferSpine (ms, m, S)

and inferMonObj (ms, m, ob) =
    case NfMonadObj.prj ob of
        DepPair (M1, M2) => inferMonObj (inferMonObj (ms, m, M1), m, M2)
      | One => ms
      | Down N => inferObj (ms, m, N)
      | Affi N => inferObj (ms, m, N)
      | Bang N => inferObj (ms, m, N)
      | MonUndef => raise Fail "Internal error: inferMonObj on MonUndef"

and inferExpObj (ms, m, ob) =
    case NfExpObj.prj ob of
        NfLet (p, (H, S), E)
        => let val nb = nbinds p in
               List.drop (inferExpObj (pushLocal (nb, inferHeadSpine (ms, m, H, S)), m, E), nb)
           end
      | NfMon M => inferMonObj (ms, m, M)

(* fun inferType : mcontext * mode * asyncType -> mcontext *)
and inferType (ms, m, ty) =
    case Util.nfTypePrjAbbrev ty of
        TLPi (p, A, B) => List.tl (inferType ((Star, Local) :: inferPatType (ms, m, p, A), m, B))
      | AddProd (A, B) => inferType (inferType (ms, m, A), m, B)
      | TMonad S => inferSyncType (ms, m, S)
      | TAtomic (H, S) => inferTypeSpine (ms, m, S)
      | TAbbrev _ => raise Fail "Internal error: inferType on TAbbrev"


(* fun inferMode : (mcontext * kind) * mcontext -> mcontext *)
fun inferMode ((mctx, ki), ms) =
    case (NfKind.prj ki, ms) of
        (Type, []) => mctx
      | (KPi (x, A, B), (m'::ms'))
        => (case x of
               SOME _ => List.tl (inferMode (((m',Explicit) :: inferType (mctx, m', A), B), ms'))
             | NONE => inferMode ((inferType (mctx, m', A), B), ms'))
      | (Type, _::_) => raise ExnDeclError (ModeErr, "too many modes")
      | (KPi _, []) => raise ExnDeclError (ModeErr, "too few modes")

    (* abstractMode (ms, mS) = mS'

       Invariant:
       If    K = {A1} .. {An} K1  is a type (with n implicit parameter)
       and   ms is a mode list for K,
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for the implicit parameters
    *)
    fun abstractMode ([], mS) = mS
      | abstractMode ((m,_)::ms, mS) = abstractMode (ms, m :: mS)

    (* shortToFull (ki, impl, mS) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       ki is a kind, impl is the number of implicit parameters.
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *)
    fun shortToFull (ki, impl, mS) =
        let val (a, b) = empty (impl, [], ki)
        in
            abstractMode (inferMode (empty (impl, [], ki), mS), mS)
        end

    fun checkFull (ki, mS) = (inferMode (([], ki), mS); ())

end
