structure GoalMode :> GOALMODE =
struct

open Syntax
open PatternNormalize

(* okGoal : nfAsyncType -> bool *)
fun okGoal ty =
    case Util.nfTypePrjAbbrev ty of
        TAtomic (_, _) => true
      | TMonad A => okGoalSync (syncNormalize A)
      | AddProd (A, B) => okGoal A andalso okGoal B
      | TLPi (p, A, B) => let val (_, A') = tpatNormalize (p, A)
                          in
                              okChainSync A' andalso okGoal B
                          end
      | TAbbrev _ => raise Fail "Internal error: okGoal TAbbrev"

(* okGoalSync : nfSyncType -> bool *)
and okGoalSync sty =
    case NfSyncType.prj sty of
        TOne => true
      | LExists (p1, S1, S2)
        => (case (Pattern.prj p1, NfSyncType.prj S1) of
                (PBang (SOME _), TBang _) => okGoalSync S2
              | (_, _) => okGoal (sync2async S1) andalso okGoalSync S2)
      | S => raise Fail "Internal error: okGoalSync: pattern not normalized"

(* isBchain : nfAsyncType -> bool *)
and isBchain ty =
    case Util.nfTypePrjAbbrev ty of
        TAtomic (_,_) => true
      | AddProd (A, B) => isBchain A andalso isBchain B
      | TLPi (p, A, B) => let val (_, A') = tpatNormalize (p, A)
                          in
                              isBchain B andalso okGoalSync A'
                          end
      | TMonad _ => false
      | _ => raise Fail "Internal error: isBchain TAbbrev"

(* isFchain : nfAsyncType -> bool *)
and isFchain ty =
    case Util.nfTypePrjAbbrev ty of
        TAtomic (_,_) => false
      | AddProd (A, B) => isFchain A andalso isFchain B
      | TLPi (p, A, B) => let val (_, A') = tpatNormalize (p, A)
                          in
                              isFchain B andalso okGoalSync A'
                          end
      | TMonad A => okGoalSync (syncNormalize A)
      | _ => raise Fail "Internal error: isFchain TAbbrev"

and okChain ty = isBchain ty orelse isFchain ty

(* okChainSync : nfSyncType -> bool *)
and okChainSync sty =
    case NfSyncType.prj sty of
        TOne => true
      | LExists (p1, S1, S2)
        => (case (Pattern.prj p1, NfSyncType.prj S1) of
                (PBang (SOME _), TBang _) => okChainSync S2
              | (_, _) => okChain (sync2async S1) andalso okChainSync S2)
      | _ => raise Fail "Internal error: okChainSync: pattern not normalized"

end
