(* Mode checking *)

structure DestCheck:> DESTCHECK =
struct

(*
fun syncConsequent tyS shift = 
   case tyS of 
      Syntax.LExists _ => "(EX...)"
    | Syntax.TOne => "1"
    | Syntax.TDown tyA => asyncTypeString tyA
    | Syntax.TAffi tyA => "@" ^ asyncTypeString tyA
    | Syntax.TBang tyA => "!" ^ asyncTypeString tyA


fun patternCheck (skel, patCtx, Atomic (a, _)) = 
      (case Signatur.getModeDecl a of
          NONE => ()
        | SOME ms =>
             if List.exists 
                   (fn (Syntax.Minus Syntax.Destination) => true | _ => false)
                   ms
             then raise ModeCheck.ModeCheckError 
                     ("Type family `" ^ a ^ "' has estination output mode -D\
                      \ and therefore cannot appear as the consequent of a\
                      \ backward-chaining rule.")
             else ())
  | patternCheck (skel, patCtx, Monadic tyS) =
    let 
       val patvars = syncConsequent tyS 0
    in
       app (fn i => print ("Must be dest in patCtx: " ^ Int.toString i ^ "\n"))
          patvars
    end
    
*)

fun destCheckDecl tyA = 
let
   val patterns = Skel.patterns tyA
in
   ()
end

end
