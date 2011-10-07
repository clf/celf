structure GoalMode :> GOALMODE =
struct

open Syntax

datatype goalMode = FORWARD
                  | BACKWARD
                  | MIXED

fun gmAnd (MIXED,_) = MIXED
  | gmAnd (_,MIXED) = MIXED
  | gmAnd (BACKWARD,FORWARD) = MIXED
  | gmAnd (FORWARD,BACKWARD) = MIXED
  | gmAnd (BACKWARD,BACKWARD) = BACKWARD
  | gmAnd (FORWARD,FORWARD) = FORWARD

fun isgmFB FORWARD = true
  | isgmFB BACKWARD = true
  | isgmFB MIXED = false

(* gmType : asyncType -> goalMode *)
fun gmType ty =
    case AsyncType.prj ty of
        TLPi (p, A, B) => (case gmType B of
                              MIXED => MIXED
                            | m => if gmSyncType A then m else MIXED)
      | AddProd (A, B) => gmAnd (gmType A, gmType B)
      | TMonad A => FORWARD
      | TAtomic (_,_) => BACKWARD
      | _ => raise Fail "Internal error: gmType TAbbrev"

(* gmType : syncType -> goalMode *)
and gmSyncType sty =
    case SyncType.prj sty of
        LExists (_, S1, S2) => gmSyncType S1 andalso gmSyncType S2
      | TOne => true
      | TDown A => isgmFB (gmType A)
      | TAffi A => isgmFB (gmType A)
      | TBang A => isgmFB (gmType A)


(* isBchain : asyncType -> bool *)
fun isBchain ty = case gmType ty of
                      BACKWARD => true
                    | _ => false

(* isFchain : asyncType -> bool *)
fun isFchain ty = case gmType ty of
                      FORWARD => true
                    | _ => false


end
