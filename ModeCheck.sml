structure ModeCheck :> MODECHECK =
struct

open Syntax
open Context
structure RAList = RandomAccessList

exception ModeCheckError of string


(* Variable status:
   - Ground:    an existential variable that is known to be ground
   - Unknown:   an existential variable that is not known yet if it is ground
   - Universal: a universal variable (can be treated as a constant)
*)

datatype status = Ground
                | Unknown
                | Universal

(* A groundness context is a list indicating the groundness status of bound
   variables and a boolean indicating an obligation to be ground *)
type mcontext = (string * mode * (status * bool)) RAList.ralist

(* status has the following join and meet (partial) operations *)
fun stJoin (Unknown,_) = Unknown
  | stJoin (_,Unknown) = Unknown
  | stJoin (Ground,Ground) = Ground
  | stJoin (Universal,Universal) = Universal
  | stJoin (_,_) = raise Fail "Internal error: status Join"

fun stMeet (Ground,_) = Ground
  | stMeet (_,Ground) = Ground
  | stMeet (Unknown,Unknown) = Unknown
  | stMeet (Universal,Universal) = Universal
  | stMeet (_,_) = raise Fail "Internal error: status Join"

(* a pair (variable status, ground obligation) has the following join and
   meet operations *)
fun varJoin ((st1,g1),(st2,g2)) = (stJoin (st1,st2),g1 andalso g2)
fun varMeet ((st1,g1),(st2,g2)) = (stMeet (st1,st2),g1 orelse g2)

(* the above operations extend to mcontexts of a given length *)
(* TODO: implement more efficient version *)
fun mcJoin x =
  RAList.pairMapEq (fn ((x, m, st1), (_, _, st2)) => (x, m, varJoin (st1, st2))) x
fun mcMeet x =
  RAList.pairMapEq (fn ((x, m, st1), (_, _, st2)) => (x, m, varMeet (st1, st2))) x

(* mctxPush : string * mode -> status -> mcontext -> mcontext *)
fun mctxPush (x, m) st ctx = RAList.cons (x, m, (st, false)) ctx

(* mctxPushNO : mcontext -> mcontext *)
fun mctxPushNO ctx = mctxPush ("", INT) Universal ctx

(* mctxPop : mcontext -> mcontext *)
val mctxPop = RAList.tail

(* getMode : mcontext * int -> mode *)
fun getMode (ctx, k) = let val (_, m, (_, _)) = RAList.lookup ctx (k-1)
                       in
                           m
                       end

(* isUniversal : mcontext * int -> bool *)
fun isUniversal (ctx, k) = let val (_, _, (st, _)) = RAList.lookup ctx (k-1)
                           in
                               case st of
                                   Universal => true
                                 | _ => false
                           end




fun sync2async (TDown A) = A
  | sync2async (TAffi A) = A
  | sync2async (TBang A) = A
  | sync2async _ = raise Fail "Internal error sync2async: pattern not normalized?"


fun pushTPattern st (ctx, p) =
    let fun patNameMode p =
            case Pattern.prj p of
                PDown _ => ("", LIN)
              | PAffi _ => ("", AFF)
              | PBang x => (getOpt (x, ""), INT)
              | _ => raise Fail "Internal error: patName: pattern not normalized"
        fun pushTPatternInt (ctx, n, p) =
            case Pattern.prj p of
                POne => (ctx, n)
              | PDepTensor (p1, p2) => pushTPatternInt (mctxPush (patNameMode p1) st ctx, n+1, p2)
              | _ => raise Fail "Internal error: pushTPattern: pattern not normalized"
    in
        pushTPatternInt (ctx, 0, p)
    end

fun pushOPattern st (ctx, p) =
    let fun patNameMode p =
            case Pattern.prj p of
                PDown x => (x, LIN)
              | PAffi x => (x, AFF)
              | PBang x => (x, INT)
              | _ => raise Fail "Internal error: patName: pattern not normalized"
        fun pushOPatternInt (ctx, n, p) =
            case Pattern.prj p of
                POne => (ctx, n)
              | PDepTensor (p1, p2) => pushOPatternInt (mctxPush (patNameMode p1) st ctx, n+1, p2)
              | _ => raise Fail "Internal error: pushOPattern: pattern not normalized"
    in
        pushOPatternInt (ctx, 0, p)
    end


(* Infer groundness information for objects *)
(* gInfer* : mcontext * object -> mcontext *)
(* These functions satisfy the following property:

      gInfer* (ctx, ob) = ctx'

      lookup (ctx, k-1) = (x, (Unknown, b)) /\ k \in FV(ob)
            ==> lookup (ctx',k-1) = (x, (Ground, b))
 *)
(* The implementation of gInfer* and associated functions below
   is based on the Twelf implementation *)


(* mkGround : mcontext -> int -> mcontext *)
fun mkGround ctx n = let val (x, m, (st, oblig)) = RAList.lookup ctx (n-1)
                     in
                         case st of
                             Unknown => RAList.update ctx (n-1) (x, m, (Ground, oblig))
                           | _ => ctx
                     end

(* unique (k, ks) = B

   Invariant:
   B iff k does not occur in ks
 *)
fun unique (k, nil) = true
  | unique (k, k'::ks) = (k <> k') andalso unique (k, ks)

exception Eta

(* isPattern : mcontext * int * spine -> bool

   isPattern (D, k, mS) = B

   Invariant:
   B iff k > k' for all k' in mS
         and for all k in mS: k is parameter
         and for all k', k'' in mS: k' <> k''
 *)
fun checkPattern (ctx, k, args, sp) =
    let fun checkPatternObj (ctx, k, args, ob, m, sp) =
            let
	        val (_, k') = Eta.etaContract Eta (normalizeObj ob)
            in
	        if (k > k')
                   andalso isUniversal (ctx, k')
	           andalso unique (k', args)
                   andalso getMode (ctx, k') = m
	        then checkPattern (ctx, k, k'::args, sp)
	        else raise Eta
            end
    in
        case Spine.prj sp of
            Nil => ()
          | LApp (M, S) =>
            (case MonadObj.prj M of
                 DepPair _ => raise Eta
               | One => checkPattern (ctx, k, args, S)
               | Down N => checkPatternObj (ctx, k, args, N, LIN, S)
               | Affi N => checkPatternObj (ctx, k, args, N, AFF, S)
               | Bang N => checkPatternObj (ctx, k, args, N, INT, S)
               | MonUndef => raise Fail "Internal error: checkPattern on MonUndef")
          | ProjLeft S => checkPattern (ctx, k, args, S)
          | ProjRight S => checkPattern (ctx, k, args, S)
    end

fun isPattern (ctx, k, S) =
    (checkPattern (ctx, k, nil, S); true)
    handle Eta => false


fun gInferObj (ctx, ob) =
    case Obj.prj ob of
        LLam (p, N) => let val (ctx', k) = pushOPattern Universal (ctx, PatternNormalize.opatNormalize p)
                       in
                           RAList.drop (gInferObj (ctx', N)) k
                       end
      | AddPair (N1, N2) => mcMeet (gInferObj (ctx, N1), gInferObj (ctx, N2))
      | Monad E => ctx (* Monadic objects are ignored for the moment -- js *)
      | Atomic (H, S) => (case H of
                              Const x => gInferSpine (ctx, S)
                            | Var (_, n) => if isUniversal (ctx, n)
                                            then gInferSpine (ctx, S)
                                            else if isPattern (ctx, n, S)
                                                 then mkGround ctx n
                                                 else ctx
                            | UCVar _ => raise Fail "Internal error: gInferObj on UCVar"
                            | LogicVar _ => raise Fail "Internal error: gInferObj on LogicVar")

      | _ => raise Fail "Internal error: gInferObj on Redex or Constraint"


and gInferMonadObj (ctx, ob) =
    case MonadObj.prj ob of
        DepPair (M1, M2) => mcMeet (gInferMonadObj (ctx, M1), gInferMonadObj (ctx, M2))
      | One => ctx
      | Down N => gInferObj (ctx, N)
      | Affi N => gInferObj (ctx, N)
      | Bang N => gInferObj (ctx, N)
      | MonUndef => raise Fail "Internal error: gInferMonadObj on MonUndef"


and gInferSpine (ctx, sp) =
    case Spine.prj sp of
        Nil => ctx
      | LApp (M, S) => mcMeet (gInferMonadObj (ctx, M), gInferSpine (ctx, S))
      | ProjLeft S => gInferSpine (ctx, S)
      | ProjRight S => gInferSpine (ctx, S)



(* Request groundness obligation for objects *)
(* gOblig* : mcontext * object -> mcontext *)
(* These functions satisfy the following property:

      gOblig* (ctx, ob) = ctx'

      lookup (ctx, k-1) = (x, (st, b)) /\ k \in FV(ob)
            ==> lookup (ctx',k-1) = (x, (st, true)), for st = Unknown,Ground

 *)

(* addOblig : mcontext -> int -> mcontext *)
fun addOblig ctx n = let val (x, m, (st, oblig)) = RAList.lookup ctx (n-1)
                     in
                         case st of
                             Universal => ctx
                           | _ => RAList.update ctx (n-1) (x, m, (st, true))
                     end


fun gObligObj (ctx, ob) =
    case Obj.prj ob of
        LLam (p, N) => let val (ctx', k) = pushOPattern Universal (ctx, PatternNormalize.opatNormalize p)
                       in
                           RAList.drop (gObligObj (ctx', N)) k
                       end
      | AddPair (N1, N2) => mcMeet (gObligObj (ctx, N1), gObligObj (ctx, N2))
      | Monad E => gObligExpObj (ctx, E)
      | Atomic (H, S) => (case H of
                              Const x => gObligSpine (ctx, S)
                            | Var (_, n) => gObligSpine (addOblig ctx n, S)
                            | UCVar _ => raise Fail "Internal error: gObligObj on UCVar"
                            | LogicVar _ => raise Fail "Internal error: gObligObj on LogicVar")

      | _ => raise Fail "Internal error: gObligObj on Redex or Constraint"

and gObligExpObj (ctx, ob) =
    case ExpObj.prj ob of
        Let (p, (H, S), E)
        => (case H of
                Const x => let val ctx' = gObligSpine (ctx, S)
                               val (ctx'', k) = pushOPattern Universal (ctx', PatternNormalize.opatNormalize p)
                           in
                               RAList.drop (gObligExpObj (ctx'', E)) k
                           end
              | Var (_,n) => let val ctx' = gObligSpine (addOblig ctx n, S)
                                 val (ctx'', k) = pushOPattern Universal (ctx', PatternNormalize.opatNormalize p)
                             in
                                 RAList.drop (gObligExpObj (ctx'', E)) k
                             end
              | UCVar _ => raise Fail "Internal error: gObligExpObj on UCVar"
              | LogicVar _ => raise Fail "Internal error: gObligExpObj on LogicVar")
      | Mon M => gObligMonadObj (ctx, M)
      | LetRedex _ => raise Fail "Internal error: gObligExpObj on LetRedex"

and gObligMonadObj (ctx, ob) =
    case MonadObj.prj ob of
        DepPair (M1, M2) => mcMeet (gObligMonadObj (ctx, M1), gObligMonadObj (ctx, M2))
      | One => ctx
      | Down N => gObligObj (ctx, N)
      | Affi N => gObligObj (ctx, N)
      | Bang N => gObligObj (ctx, N)
      | MonUndef => raise Fail "Internal error: gObligMonadObj on MonUndef"


and gObligSpine (ctx, ob) =
    case Spine.prj ob of
        Nil => ctx
      | LApp (M, S) => mcMeet (gObligMonadObj (ctx, M), gObligSpine (ctx, S))
      | ProjLeft S => gObligSpine (ctx, S)
      | ProjRight S => gObligSpine (ctx, S)




(* Check groundness information for objects *)
(* gCheck* : mcontext * object -> unit *)
(* gCheck* (ctx, ob) raises ModeCheckError if

      exists k. k \in FV(ob) /\ lookup (ctx, k-1) = (_, (Unknown, _))

   or returns () if no such k exists.
 *)
fun gCheckObj (ctx, ob) =
    case Obj.prj ob of
        LLam (p, N) => gCheckObj (#1 (pushOPattern Universal (ctx, PatternNormalize.opatNormalize p)), N)
      | AddPair (N1, N2) => (gCheckObj (ctx, N1); gCheckObj (ctx, N2))
      | Monad E => gCheckExpObj (ctx, E)
      | Atomic (H, S) => (case H of
                              Const x => gCheckSpine (ctx, S)
                            | Var (_, n) => let val (x, _, (st, _)) = RAList.lookup ctx (n-1)
                                            in
                                                case st of
                                                    Unknown => raise ModeCheckError (x^" not necessarily ground1")
                                                  | _ => gCheckSpine (ctx, S)
                                            end
                            | UCVar _ => raise Fail "Internal error: gCheckObj on UCVar"
                            | LogicVar _ => raise Fail "Internal error: gCheckObj on LogicVar")

      | _ => raise Fail "Internal error: gCheckObj on Redex or Constraint"

and gCheckExpObj (ctx, ob) =
    case ExpObj.prj ob of
        Let (p, (H, S), E)
        => (case H of
                Const x => (gCheckSpine (ctx, S);
                            gCheckExpObj (#1 (pushOPattern Universal (ctx, PatternNormalize.opatNormalize p)), E))
              | Var (_,n) => let val (x, _, (st, _)) = RAList.lookup ctx (n-1)
                             in
                                 case st of
                                     Unknown => raise ModeCheckError (x^" not necessarily ground2")
                                   | _ => gCheckSpine (ctx, S)
                             end
              | UCVar _ => raise Fail "Internal error: gCheckExpObj on UCVar"
              | LogicVar _ => raise Fail "Internal error: gCheckExpObj on LogicVar")
      | Mon M => gCheckMonadObj (ctx, M)
      | LetRedex _ => raise Fail "Internal error: gCheckExpObj on LetRedex"

and gCheckMonadObj (ctx, ob) =
    case MonadObj.prj ob of
        DepPair (M1, M2) => (gCheckMonadObj (ctx, M1); gCheckMonadObj (ctx, M2))
      | One => ()
      | Down N => gCheckObj (ctx, N)
      | Affi N => gCheckObj (ctx, N)
      | Bang N => gCheckObj (ctx, N)
      | MonUndef => raise Fail "Internal error: gCheckMonadObj on MonUndef"


and gCheckSpine (ctx, ob) =
    case Spine.prj ob of
        Nil => ()
      | LApp (M, S) => (gCheckMonadObj (ctx, M); gCheckSpine (ctx, S))
      | ProjLeft S => gCheckSpine (ctx, S)
      | ProjRight S => gCheckSpine (ctx, S)



(* fun bwdHead : mcontext * typeSpine * modeDecl -> mcontext *)
(* bwdHead calls gInfer* for input arguments and gOblig* for output arguments in the spine *)
fun bwdHead (ctx, sp, m) =
    case (TypeSpine.prj sp, m) of
        (TNil, []) => ctx
      | (TApp (N,S), (h::t)) => let val ctx' = case h of
                                                   Plus => gInferObj (ctx, N)
                                                 | Minus => gObligObj (ctx, N)
                                                 | Star => raise Fail "Internal error: * mode in bwdHead"
                                    val ctx'' = bwdHead (ctx, S, t)
                                in
                                    mcMeet (ctx', ctx'')
                                end
      | _ => raise Fail "Internal error: bwdHead spine and mode declaration length do not coincide"

(* goalAtomic : mcontext * typeSpine * modeDecl -> mcontext *)
(* goalAtomic calls gCheck* for input arguments and gInfer* for output arguments in the spine *)
fun goalAtomic (ctx, sp, m) =
    case (TypeSpine.prj sp, m) of
        (TNil, []) => ctx
      | (TApp (N,S), (h::t)) => let val ctx' = case h of
                                                   Plus => (gCheckObj (ctx,N); ctx)
                                                 | Minus => gInferObj (ctx, N)
                                                 | Star => raise Fail "Internal error: * mode in goalAtomic"
                                    val ctx'' = goalAtomic (ctx, S, t)
                                in
                                    mcMeet (ctx', ctx'')
                                end
      | _ => raise Fail "Internal error: goalAtomic spine and mode declaration length do not coincide"


(* bwdType : mcontext * asyncType -> mcontext *)
(* Entry point for checking backward-chaining declarations *)
fun bwdType (ctx, ty) =
    case AsyncType.prj ty of
        TAtomic (a, S) => (case Signatur.getModeDecl a of
                               NONE => raise ModeCheckError ("mode declaration of "^a^" not defined")
                             | SOME m => bwdHead (ctx, S, m))
      | AddProd (A1, A2) => let val ctx1 = bwdType (ctx, A1)
                                val ctx2 = bwdType (ctx, A2)
                            in
                                mcJoin (ctx1, ctx2)
                            end
      | TLPi (p, A, B) => let val (p', A') = PatternNormalize.tpatNormalize (p, A) in
                              bwdPatType (ctx, p', A', B)
                          end
      | TMonad _ =>  raise Fail "Internal error: bwdType on forward goal"
      | TAbbrev _ => raise Fail "Internal error: bwdType on TAbbrev"


(* bwdPatType : mcontext * tpattern * syncType * asyncType -> unit *)
(* Precondition  bwdPatType (ctx, p, sty, ty)
      - p must be normalized
      - p and sty must be related
 *)
and bwdPatType (ctx, p, sty, ty) =
    case (Pattern.prj p, SyncType.prj sty) of
        (POne, TOne) => bwdType (ctx, ty)
      | (PDepTensor (p1, p2), LExists (_, S1, S2))
        => (case (Pattern.prj p1, SyncType.prj S1) of
                (PBang (SOME x), TBang A)
                => let val ctx' = bwdPatType (mctxPush (x, INT) Unknown ctx, p2, S2, ty)
                       val ((x, _, (st, oblig)), ctxRet) = valOf (RAList.prj ctx')
                   in
                       if oblig (* x has a groundness obligation *)
                       then case st of
                                Ground => ctxRet
                              | Unknown => raise ModeCheckError (x^" not necessarily ground3")
                              | Universal => raise Fail "Internal error: bwdPatType: Unknown changed to Univ"
                       else ctxRet
                   end
              | (_, S)  (* _ is PDown, PAffi, or PBang NONE, since patterns are normalized *)
                => let val ctx1 = bwdPatType (mctxPushNO ctx, p2, S2, ty)
                   in goalType (mctxPop ctx1, sync2async S) end
           )
      | _ => raise Fail "Internal error: bwdPatType: pattern not normalized"


(* fun goalType : mcontext * asyncType -> mcontext *)
and goalType (ctx, ty) =
    case AsyncType.prj ty of
        TAtomic (a, S) => (case Signatur.getModeDecl a of
                               NONE => raise Fail ("Mode declaration of "^a^" not defined")
                             | SOME m => goalAtomic (ctx, S, m)
                          )
      | AddProd (A1, A2) => goalType (goalType (ctx, A1), A2)
      | TLPi (p, A, B) => let val (p', A') = PatternNormalize.tpatNormalize (p, A) in
                              goalPatType (ctx, p', A', B)
                          end
      | TMonad S => goalSyncType (ctx, S)
      | TAbbrev _ => raise Fail "Internal error: bwdType on TAbbrev"


(* fun goalSyncType : mcontext * synctType -> mcontext *)
and goalSyncType (ctx, sty) =
    case SyncType.prj sty of
        TOne => ctx
      | LExists (p, S1, S2) => let val (p', _) = PatternNormalize.tpatNormalize (p, S1)
                                   val (ctx', k) = pushTPattern Unknown (ctx, p')
                               in
                                   RAList.drop (goalSyncType (ctx', S2)) k
                               end
      | S (* TDown, TAffi, TBang *)
        => goalType (ctx, sync2async S)


(* goalPatType : mcontext * pattern * syncType * asyncType -> mcontext *)
(* Precondition  goalPatType (ctx, p, sty, ty)
      - p must be normalized
      - p and sty must be related
 *)
and goalPatType (ctx, p, sty, ty) =
    case (Pattern.prj p, SyncType.prj sty) of
        (POne, TOne) => goalType (ctx, ty)
      | (PDepTensor (p1, p2), LExists (_, S1, S2))
        => (case (Pattern.prj p1, SyncType.prj S1) of
                (PBang (SOME x), TBang A) => mctxPop (goalPatType (mctxPush (x, INT) Universal ctx, p2, S2, ty))

              | (_, S) (* _ is PDown, PAffi, or PBang NONE, since patterns are normalized *)
                => (modeCheckDeclInt (ctx, sync2async S);
                    mctxPop (goalPatType (mctxPushNO ctx, p2, S2, ty))))

      | _ => raise Fail "Internal error: goalPatType: pattern not normalized"


(* fwdType : mcontext * asyncType -> unit *)
(* Entry point for forward-chaining declarations *)
and fwdType (ctx, ty) =
    case AsyncType.prj ty of
        TLPi (p, A, B) => let val (p', A') = PatternNormalize.tpatNormalize (p, A) in
                              fwdPatType (ctx, p', A', B)
                          end
      | AddProd (A, B) => (fwdType (ctx, A); fwdType (ctx, B))
      | TMonad S => fwdSyncType (ctx, S)
      | TAtomic _ => raise Fail "Internal error: fwdType on backward goal"
      | TAbbrev _ => raise Fail "Internal error: fwdType on TAbbrev"


(* fwdSyncType : mcontext * syncType -> unit *)
and fwdSyncType (ctx, sty) =
    case SyncType.prj sty of
        TOne => ()
      | LExists (p, S1, S2) => let val (p', _) = PatternNormalize.tpatNormalize (p, S1)
                                   val (ctx', _) = pushTPattern Universal (ctx, p')
                               in
                                   fwdSyncType (ctx', S2)
                               end
      | S (* TDown, TAffi, TBang *)
        => modeCheckDeclInt (ctx, sync2async S)


(* fwdPatType : mcontext * tpattern * syncType * asyncType -> unit *)
(* Precondition  fwdPatType (ctx, p, sty, ty)
      - p must be normalized
      - p and sty must be related
 *)
and fwdPatType (ctx, p, sty, ty) =
    case (Pattern.prj p, SyncType.prj sty) of
        (POne, TOne) => fwdType (ctx, ty)
      | (PDepTensor (p1, p2), LExists (_, S1, S2))
        => (case (Pattern.prj p1, SyncType.prj S1) of
                (PBang (SOME x), TBang A) => fwdPatType (mctxPush (x, INT) Unknown ctx, p2, S2, ty)
              | (_, S) (* _ is PDown, PAffi, or PBang NONE, since patterns are normalized *)
                => fwdPatType (mctxPushNO (goalType (ctx, sync2async S)), p2, S2, ty))
      | _ => raise Fail "Internal error: fwdPatType: pattern not normalized"


(* modeCheckDeclInt : mcontext * asyncType -> unit *)
(* Main entry point for mode-checking declarations.
   Calls bwdType or fwdType if the declarations is backward-chaining or forward-chaining, resp.
   Returns () if the declaration is mode-correct.
   Raises ModeCheckError otherwise.
 *)
and modeCheckDeclInt (ctx, ty) =
    if GoalMode.isBchain ty
    then let val _ = bwdType (ctx, ty) in () end
    else if GoalMode.isFchain ty
    then fwdType (ctx, ty)
    else raise Fail "Internal error: modeCheckDeclInt on MIXED goal"


(* fun isNeeded : asyncType -> bool *)
(* TODO: check this function *)
fun isNeeded ty =
    let fun isNeededType ty =
            case AsyncType.prj ty of
                TLPi (p, A, B) => isNeeded B
              | AddProd (A, B) => isNeeded A orelse isNeeded B
              | TMonad A => isNeededSyncType A
              | TAtomic (x, S) => Signatur.hasModeDecl x
              | TAbbrev _ => raise Fail "Internal error: mode checking on TAbbrev"
        and isNeededSyncType sty =
            case SyncType.prj sty of
                TOne => false
              | LExists (p, S1, S2) => isNeededSyncType S2
              | S => isNeededType (sync2async S)
    in
        isNeededType ty
    end


(* modeCheckDecl : asyncType -> unit *)
fun modeCheckDecl ty = modeCheckDeclInt (RAList.empty, ty)

end
