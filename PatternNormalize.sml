structure PatternNormalize :> PATTERNNORMALIZE =
struct

open Syntax

fun sync2async sty =
    case NfSyncType.prj sty of
        TDown A => A
      | TAffi A => A
      | TBang A => A
      |  _ => raise Fail "Internal error sync2async: pattern not normalized?"

fun syncNormalize sty =
    case NfSyncType.prj sty of
        TOne => NfInj.TOne'

      | LExists (p1, S1, S2)
        => (case (Pattern.prj p1, NfSyncType.prj S1) of
                (POne, TOne) => syncNormalize S2

              | (PDepTensor (p1a, p1b), LExists (_, S1a, S1b)) (* _ = p1a *)
                => syncNormalize (NfInj.LExists' (p1a, S1a, NfInj.LExists' (p1b, S1b, S2)))

              | (PDown x, TDown A) => (* x = () *)
                let val S2' = syncNormalize S2 in
                    NfInj.LExists' (PDown' x, NfInj.TDown' A, S2')
                end
              | (PAffi x, TAffi A) => (* x = () *)
                let val S2' = syncNormalize S2 in
                    NfInj.LExists' (PAffi' x, NfInj.TAffi' A, S2')
                end
              | (PBang x, TBang A) => (* x : string option *)
                let val S2' = syncNormalize S2 in
                    NfInj.LExists' (PBang' x, NfInj.TBang' A, S2')
                end
              | _ => raise Fail "Internal error: syncNormalize: internal patterns do not match")

      | TDown A => NfInj.LExists' (PDown' (), NfInj.TDown' A, NfInj.TOne')
      | TAffi A => NfInj.LExists' (PAffi' (), NfInj.TAffi' A, NfInj.TOne')
      | TBang A => NfInj.LExists' (PBang' NONE, NfInj.TBang' A, NfInj.TOne')

fun tpatNormalize (p,sty) =
    case (Pattern.prj p, NfSyncType.prj sty) of
        (POne, TOne) => (POne', NfInj.TOne')

      | (PDepTensor (p1, p2), LExists (_, S1, S2)) (* _ = p1 *)
        => (case (Pattern.prj p1, NfSyncType.prj S1) of
                (POne, TOne) => tpatNormalize (p2, S2)

              | (PDepTensor (p1a, p1b), LExists (_, S1a, S1b)) (* _ = p1a *)
                => tpatNormalize (PDepTensor' (p1a, PDepTensor' (p1b, p2)),
                                  NfInj.LExists' (p1a, S1a, NfInj.LExists' (p1b, S1b, S2)))

              | (PDown x, TDown A) => (* x = () *)
                let val (p2', S2') = tpatNormalize (p2, S2) in
                    (PDepTensor' (PDown' x, p2'), NfInj.LExists' (PDown' x, NfInj.TDown' A, S2'))
                end
              | (PAffi x, TAffi A) => (* x = () *)
                let val (p2', S2') = tpatNormalize (p2, S2) in
                    (PDepTensor' (PAffi' x, p2'), NfInj.LExists' (PAffi' x, NfInj.TAffi' A, S2'))
                end
              | (PBang x, TBang A) => (* x : string option *)
                let val (p2', S2') = tpatNormalize (p2, S2) in
                    (PDepTensor' (PBang' x, p2'), NfInj.LExists' (PBang' x, NfInj.TBang' A, S2'))
                end
              | _ => raise Fail "Internal error: tpatNormalize: internal patterns do not match")

      | (PDown x, TDown A) => (PDepTensor' (PDown' x, POne'), NfInj.LExists' (PDown' x, NfInj.TDown' A, NfInj.TOne'))
      | (PAffi x, TAffi A) => (PDepTensor' (PAffi' x, POne'), NfInj.LExists' (PAffi' x, NfInj.TAffi' A, NfInj.TOne'))
      | (PBang x, TBang A) => (PDepTensor' (PBang' x, POne'), NfInj.LExists' (PBang' x, NfInj.TBang' A, NfInj.TOne'))

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
