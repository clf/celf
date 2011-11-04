structure Skel:> SKEL =
struct

datatype head = 
   Monadic of Syntax.nfSyncType
 | Atomic of string * Syntax.nfTypeSpine

datatype syncSkel =
   DepPair of syncSkel * syncSkel
 | One
 | Down
 | Affi
 | Bang 

datatype asyncSkel = 
   Nil
 | LApp of syncSkel * asyncSkel
 | ProjLeft of asyncSkel
 | ProjRight of asyncSkel

fun patString pat = 
   case Syntax.Pattern.prj pat of
      Syntax.PDepTensor (pat1, pat2) =>
         "[" ^ patString pat1 ^ ", " ^ patString pat2 ^ "]"
    | Syntax.POne => "1"
    | Syntax.PDown () => "_"
    | Syntax.PAffi () => "@_"
    | Syntax.PBang NONE => "!_"
    | Syntax.PBang (SOME x) => "!"^x

type patternCtx = (string option * Syntax.nfAsyncType * Context.modality) list

fun syncPatterns (pat, tyS) =
   case (Syntax.Pattern.prj pat, Syntax.NfSyncType.prj tyS) of
      (Syntax.PDepTensor (pat1, pat2), Syntax.LExists (pat1', tyS1, tyS2)) => 
      let
         val (skel1, patCtx1) = syncPatterns (pat1, tyS1)
         val (skel2, patCtx2) = syncPatterns (pat2, tyS2)
      in
       ( print ("Strange case: overlapping patterns.\n")
       ; print ("Pattern in externally-bound pattern: "^patString pat1^"\n")
       ; print ("Pattern in internally-bound pattern: "^patString pat1'^"\n\n")
       ; (DepPair (skel1, skel2), patCtx1 @ patCtx2))
      end
    | (Syntax.POne, Syntax.TOne) => 
         (One, [])
    | (Syntax.PDown (), Syntax.TDown tyA) => 
         (Down, [ (NONE, tyA, Context.LIN) ])
    | (Syntax.PAffi (), Syntax.TAffi tyA) => 
         (Affi, [ (NONE, tyA, Context.AFF) ])
    | (Syntax.PBang name, Syntax.TBang tyA) => 
         (Bang, [ (name, tyA, Context.INT) ])
    | _ => raise Fail "Type error in syncPatterns"

fun asyncPatterns tyA = 
   case Util.nfTypePrjAbbrev tyA of 
      Syntax.TLPi (pat, tyS1, tyA2) =>
      let
         val (skel1, patCtx1) = syncPatterns (pat, tyS1)
      in
         map (fn (skel2, patCtx2, head) =>
                 (LApp (skel1, skel2), patCtx1 @ patCtx2, head))
            (asyncPatterns tyA2)
      end 
    | Syntax.AddProd (tyA1, tyA2) => 
      let
         val ans1 = asyncPatterns tyA1
         val ans2 = asyncPatterns tyA2
         fun mapans f (skel, patCtx, head) = (f skel, patCtx, head)
      in
         map (mapans ProjLeft) ans1 @ map (mapans ProjRight) ans2
      end  
    | Syntax.TMonad tyS => [ (Nil, [], Monadic tyS) ]
    | Syntax.TAtomic (a, spine) => [ (Nil, [], Atomic (a, spine)) ] 
    | Syntax.TAbbrev _ => raise Fail "Why isn't this case precluded?"

val patterns = asyncPatterns

end
