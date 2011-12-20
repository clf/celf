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

fun syncString skel = 
   case skel of 
      DepPair (skel1, skel2) =>
         "[" ^ syncString skel1 ^ ", " ^ syncString skel2 ^ "]"
    | One => "1"
    | Down => "_"
    | Affi => "@_"
    | Bang => "!_"

fun asyncString skel =
   case skel of 
      Nil => "nil"
    | LApp (skel1, skel2) => syncString skel1 ^ "; " ^ asyncString skel2
    | ProjLeft skel1 => "#1 " ^ asyncString skel1
    | ProjRight skel1 => "#2 " ^ asyncString skel1


(* Useful, de Bruijn-exposing  *)
and termString n = 
   case Syntax.NfObj.prj n of 
      Syntax.NfLLam _ => "(\\...)"
    | Syntax.NfAddPair (n1, n2) => 
         "<" ^ termString n1 ^ ", " ^ termString n2 ^ ">"
    | Syntax.NfMonad _ => "{...}"
    | Syntax.NfAtomic (h, spine) => 
      let val c = 
             case h of 
                Syntax.Const c => c
              | Syntax.Var (Context.LIN, i) => Int.toString i
              | Syntax.Var (Context.AFF, i) => "@" ^ Int.toString i
              | Syntax.Var (Context.INT, i) => "!" ^ Int.toString i
              | _ => raise Fail "Skel.termString"
      in
         case Syntax.NfSpine.prj spine of
            Syntax.Nil => c
          | _ => c ^ " ..."
      end

fun asyncTypeString tyA =
   case Util.nfTypePrjAbbrev tyA of
      Syntax.TLPi _ => "(PI...)"
    | Syntax.AddProd (tyA1, tyA2) => 
         "(" ^ asyncTypeString tyA1 ^ ", " ^ asyncTypeString tyA2 ^ ")"
    | Syntax.TMonad tyS => "{" ^ syncTypeString tyS ^ "}"
    | Syntax.TAtomic (a, spine) => 
      let fun terms str spine = 
             case Syntax.NfTypeSpine.prj spine of 
                Syntax.TNil => str
              | Syntax.TApp (term, spine) => 
                   terms (str ^ " " ^ termString term) spine
      in
         terms a spine
      end
    | _ => raise Fail "Skel.asyncTypeString"

and syncTypeString tyS = 
   case Syntax.NfSyncType.prj tyS of
      Syntax.LExists _ => "(EX...)"
    | Syntax.TOne => "1"
    | Syntax.TDown tyA => asyncTypeString tyA
    | Syntax.TAffi tyA => "@" ^ asyncTypeString tyA
    | Syntax.TBang tyA => "!" ^ asyncTypeString tyA

fun headString (Monadic tyS) = "{" ^ syncTypeString tyS ^ "}"
  | headString (Atomic (a, spine)) =
       asyncTypeString (Syntax.NfInj.TAtomic' (a, spine))

(* mergePats pat pat'
 * 
 * Invariant:
 * Delta ||- pat : S
 * Delta ||- pat' : S
 * 
 * Two patterns for the same synchronous (positive) type with different 
 * dependency information need to be merged to basically identify the union of
 * the "dependently flagged" variables
 * from the first and second patterns. *)
fun mergePats (pat: Syntax.tpattern) (pat': Syntax.tpattern) = 
   case (Syntax.Pattern.prj pat, Syntax.Pattern.prj pat') of
      (Syntax.PDepTensor (pat1, pat2), Syntax.PDepTensor (pat1', pat2')) =>
         Syntax.PDepTensor' (mergePats pat1 pat1', mergePats pat2 pat2')
    | (Syntax.POne, Syntax.POne) => Syntax.POne'
    | (Syntax.PDown (), Syntax.PDown ()) => Syntax.PDown' ()
    | (Syntax.PAffi (), Syntax.PAffi ()) => Syntax.PAffi' ()
    | (Syntax.PBang (SOME x), Syntax.PBang _) => Syntax.PBang' (SOME x)
    | (Syntax.PBang NONE, Syntax.PBang (SOME x)) => Syntax.PBang' (SOME x)
    | (Syntax.PBang NONE, Syntax.PBang NONE) => Syntax.PBang' NONE
    | _ => raise Fail "Skel.mergePats"

type patCtx = (string option * Syntax.nfAsyncType * Context.modality) list

fun syncPatterns (pat, tyS) =
   case (Syntax.Pattern.prj pat, Syntax.NfSyncType.prj tyS) of
      (Syntax.PDepTensor (pat1, pat2), Syntax.LExists (pat1', tyS1, tyS2)) => 
      let
         val (skel1, patCtx1) = syncPatterns (mergePats pat1 pat1', tyS1)
         val (skel2, patCtx2) = syncPatterns (pat2, tyS2)
      in
         (DepPair (skel1, skel2), patCtx1 @ patCtx2)
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

fun patterns tyA = 
let 
   val pats = asyncPatterns tyA 
   val concat = String.concatWith ", "
   fun f (NONE, tyA, Context.LIN) = asyncTypeString tyA ^ " lin"
     | f (NONE, tyA, Context.AFF) = asyncTypeString tyA ^ " aff" 
     | f (NONE, tyA, Context.INT) = asyncTypeString tyA ^ " pers"
     | f (SOME x, tyA, Context.INT) = x ^ ": " ^ asyncTypeString tyA
     | f _ = raise Fail "context formation: Skel.patterns"
in
 ( print "\n=====\n"
 ; app (fn (skel, patCtx, head) => 
         ( print ("Skeleton:        " ^ asyncString skel ^ "\
                 \\nPattern context: " ^ concat (map f patCtx) ^ "\
                 \\nHead type:       " ^ headString head ^ "\n")))
       pats
 ; pats)
end

end
