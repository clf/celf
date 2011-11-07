signature SKEL = 
sig

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

type patCtx = (string option * Syntax.nfAsyncType * Context.modality) list

(* "Patterns" decomposes an asynchronous type into its skeleton *)
val patterns: Syntax.nfAsyncType -> (asyncSkel * patCtx * head) list

end
