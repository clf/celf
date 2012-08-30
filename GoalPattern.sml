structure GoalPattern:> GOALPATTERN =
struct

open SymbTable

(* Goal patterns in lack of a better name *)

type goalPattern = (string * string option) option

val goalPatternTable = ref (empty()) : goalPattern Table ref

(* addGoalPattern : string * goalPattern -> unit *)
fun addGoalPattern (c, g) =
    goalPatternTable := insert (!goalPatternTable, c, g)

(* getGoalPattern : string -> goalPattern option *)
fun getGoalPattern id = valOf (peek (!goalPatternTable, id))


datatype goalPatInt = HasGoal of string * string option
                    | NotFound
                    | NotGoal

fun goalPatternType ty =
    case Util.nfTypePrjAbbrev ty of
      Syntax.TLPi (p, A, B) =>
      ( case goalPatternSyncType (p, A) of
          g as (HasGoal _) => g
        | NotFound => goalPatternType B
        | NotGoal => NotGoal
      )
    | Syntax.TAtomic (fam, sp) =>
      if Syntax.Signatur.hasEmptyDecl fam
      then
        ( case Syntax.NfTypeSpine.prj sp of
            Syntax.TNil => NotGoal
          | Syntax.TApp (M, _) =>
            ( case Syntax.NfObj.prj M of
                Syntax.NfAtomic (Syntax.Const constr, _) => HasGoal (fam, SOME constr)
              | _ => HasGoal (fam, NONE)
            )
        )
      else NotFound
    | Syntax.AddProd _ => NotGoal
    | Syntax.TMonad _ => NotGoal
    | Syntax.TAbbrev _ => raise Fail "Internal error: goalPatternType: TAbbrev"

and goalPatternSyncType (p, sty) =
    case (Syntax.Pattern.prj p, Syntax.NfSyncType.prj sty) of
      (Syntax.PDepTensor (p1, p2), Syntax.LExists (p1', S1, S2)) =>
      ( case goalPatternSyncType (Util.patternAddDep (p1, p1'), S1) of
          g as (HasGoal _) => g
        | NotFound => goalPatternSyncType (p2, S2)
        | NotGoal => NotGoal )
    | (Syntax.POne, Syntax.TOne) => NotFound
    | (Syntax.PDown (), Syntax.TDown A) => goalPatternType A
    | (Syntax.PAffi (), Syntax.TAffi A) => goalPatternType A
    | (Syntax.PBang x, Syntax.TBang A) => NotFound
    | _ => raise Fail "Internal error: goalPatternSyncType"


(* goalPattern : Syntax.nfAsyncType -> goalPattern *)
fun goalPattern ty =
    case goalPatternType ty of
      HasGoal g => SOME g
    | _ => NONE



end
