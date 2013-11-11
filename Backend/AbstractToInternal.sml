structure AbstractToInternal :> ABSTRACT_TO_INTERNAL =
struct

structure A = Syntax
structure I = InternalSyntax

fun patternTI p =
    case A.Pattern.prj p of
        (A.PDepTensor (p1, p2)) => I.PDepTensor (patternTI p1, patternTI p2)
      | A.POne => I.POne
      | A.PDown x => I.PDown x
      | A.PAffi x => I.PAffi x
      | A.PBang x => I.PBang x

fun modalityTI Context.INT = I.INT
  | modalityTI Context.LIN = I.LIN
  | modalityTI Context.AFF = I.AFF

fun kindTI ki =
    case A.NfKind.prj ki of
        A.Type => I.Type
      | A.KPi (x, aty, ki1) => I.KPi (x, asyncTI aty, kindTI ki1)

and asyncTI aty =
    case A.NfAsyncType.prj aty of
        A.TLPi (tpat, sty, aty1) => I.TLPi ( patternTI tpat
                                           , syncTI sty
                                           , asyncTI aty1 )
      | A.AddProd (aty1, aty2) => I.AddProd ( asyncTI aty1
                                            , asyncTI aty2 )
      | A.TMonad sty => I.TMonad (syncTI sty)
      | A.TAtomic (x, sp) => I.TAtomic (x, typeSpineTI sp)
      | A.TAbbrev _ => raise Fail "Internal error: asyncTI TAbbrev"

and syncTI sty =
    case A.NfSyncType.prj sty of
        A.LExists (tpat, sty1, sty2) => I.LExists ( patternTI tpat
                                                  , syncTI sty1
                                                  , syncTI sty2 )
      | A.TOne => I.TOne
      | A.TDown aty => I.TDown (asyncTI aty)
      | A.TAffi aty => I.TAffi (asyncTI aty)
      | A.TBang aty => I.TBang (asyncTI aty)

and typeSpineTI sp =
    case A.NfTypeSpine.prj sp of
        A.TNil => I.TNil
      | A.TApp (obj, sp1) => I.TApp (objectTI obj, typeSpineTI sp1)

and objectTI obj =
    case A.NfObj.prj obj of
        A.NfLLam (opat, obj1) => I.LLam (patternTI opat, objectTI obj1)
      | A.NfAddPair (obj1, obj2) => I.AddPair (objectTI obj1, objectTI obj2)
      | A.NfMonad e => I.Monad (expTI e)
      | A.NfAtomic (h, sp) => I.Atomic (headTI h, spineTI sp)

and spineTI sp =
    case A.NfSpine.prj sp of
        A.Nil => I.Nil
      | A.LApp (m, sp1) => I.LApp (monadTI m, spineTI sp1)
      | A.ProjLeft sp1 => I.ProjLeft (spineTI sp1)
      | A.ProjRight sp1 => I.ProjRight (spineTI sp1)

and expTI e =
    let
      fun stepTI (pat, (h, sp)) = (patternTI pat, (headTI h, spineTI sp))
      fun getEpsilon e =
          case A.NfExpObj.prj e of
              A.NfLet (pat, (h, sp), e1) =>
              let
                val (eps, r) = getEpsilon e1
              in
                ( (pat, (h, sp)) :: eps, r )
              end
            | A.NfMon m => ([], m)

      val (eps, m) = getEpsilon e
    in
      I.Let (map stepTI eps, monadTI m)
    end

and monadTI m =
    case A.NfMonadObj.prj m of
        A.DepPair (m1, m2) => I.DepPair (monadTI m1, monadTI m2)
      | A.One => I.One
      | A.Down obj => I.Down (objectTI obj)
      | A.Affi obj => I.Affi (objectTI obj)
      | A.Bang obj => I.Bang (objectTI obj)
      | A.MonUndef => raise Fail "Internal error: monadTI MonUndef"

and headTI h =
    case h of
        A.Const s => I.Const s
      | A.Var (m, k) => I.Var (modalityTI m, k)
      | A.UCVar s => I.UCVar s
      | A.LogicVar _ => raise Fail "Internal error: headTI LogicVar"

fun opSemTI A.OpSemUnif = I.OpSemUnif
  | opSemTI A.OpSemMatch = I.OpSemMatch

fun modeModTI A.Normal = I.Normal
  | modeModTI A.Destination = I.Destination

fun modeTI A.Plus = I.Plus
  | modeTI (A.Minus m) = I.Minus (modeModTI m)
  | modeTI A.Star = I.Star


fun declToInternal (A.ConstDecl (id,k,A.Ty ty)) =
    I.ConstDecl (id,k,I.Ty (asyncTI (A.normalizeType ty)))
  | declToInternal (A.ConstDecl (id,k,A.Ki ki)) =
    I.ConstDecl (id,k,I.Ki (kindTI (A.normalizeKind ki)))
  | declToInternal (A.TypeAbbrev (id,ty)) =
    I.TypeAbbrev (id, asyncTI (A.normalizeType ty))
  | declToInternal (A.ObjAbbrev (id,ty,obj)) =
    I.ObjAbbrev (id, asyncTI (A.normalizeType ty), objectTI (A.normalizeObj obj))
  | declToInternal (A.Query (t,n1,n2,n3,n4,ty)) =
    I.Query (opSemTI t, n1, n2, n3, n4, asyncTI (A.normalizeType ty))
  | declToInternal (A.Trace (n,ty)) = I.Trace (n, syncTI (A.normalizeSyncType ty))
  | declToInternal (A.Exec (n,ty)) = I.Exec (n, syncTI (A.normalizeSyncType ty))
  | declToInternal (A.Mode (id,m1,m2)) =
    I.Mode (id, Option.map (map modeTI) m1, map modeTI m2)
  | declToInternal (A.Empty s) = I.Empty s

val typeToInternal = asyncTI o A.normalizeType

end
