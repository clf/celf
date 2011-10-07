structure PatternNormalize :> PATTERNNORMALIZE =
struct

open Syntax

fun tpatNormalize (p,sty) =
    case (Pattern.prj p, SyncType.prj sty) of
        (POne, TOne) => (POne', TOne')

      | (PDepTensor (p1, p2), LExists (_, S1, S2)) (* _ = p1 *)
        => (case (Pattern.prj p1, SyncType.prj S1) of
                (POne, TOne) => tpatNormalize (p2, S2)

              | (PDepTensor (p1a, p1b), LExists (_, S1a, S1b)) (* _ = p1a *)
                => tpatNormalize (PDepTensor' (p1a, PDepTensor' (p1b, p2)),
                                  LExists' (p1a, S1a, LExists' (p1b, S1b, S2)))

              | (PDown x, TDown A) => (* x = () *)
                let val (p2', S2') = tpatNormalize (p2, S2) in
                    (PDepTensor' (PDown' x, p2'), LExists' (PDown' x, TDown' A, S2'))
                end
              | (PAffi x, TAffi A) => (* x = () *)
                let val (p2', S2') = tpatNormalize (p2, S2) in
                    (PDepTensor' (PAffi' x, p2'), LExists' (PAffi' x, TAffi' A, S2'))
                end
              | (PBang x, TBang A) => (* x : string option *)
                let val (p2', S2') = tpatNormalize (p2, S2) in
                    (PDepTensor' (PBang' x, p2'), LExists' (PBang' x, TBang' A, S2'))
                end
              | _ => raise Fail "Internal error: tpatNormalize: internal patterns do not match")

      | (PDown x, TDown A) => (PDepTensor' (PDown' x, POne'), LExists' (PDown' x, TDown' A, TOne'))
      | (PAffi x, TAffi A) => (PDepTensor' (PAffi' x, POne'), LExists' (PAffi' x, TAffi' A, TOne'))
      | (PBang x, TBang A) => (PDepTensor' (PBang' x, POne'), LExists' (PBang' x, TBang' A, TOne'))

      | _ => raise Fail "Internal error: tpatNormalize: patterns do not match"


fun opatNormalize p =
    case Pattern.prj p of
        POne => POne'
      | PDepTensor (p1,p2) =>
        (case Pattern.prj p1 of
             POne => opatNormalize p2
           | PDepTensor (p1a, p1b) => opatNormalize (PDepTensor' (p1a, (PDepTensor' (p1b, p2))))
           | PDown x => PDepTensor' (PDown' x, opatNormalize p2)
           | PAffi x => PDepTensor' (PAffi' x, opatNormalize p2)
           | PBang x => PDepTensor' (PBang' x, opatNormalize p2))
      | PDown x => PDepTensor' (PDown' x, POne')
      | PAffi x => PDepTensor' (PAffi' x, POne')
      | PBang x => PDepTensor' (PBang' x, POne')

end
