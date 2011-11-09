signature SKEL = 
sig

datatype head = 
   Monadic of Syntax.nfSyncType
 | Atomic of string * Syntax.nfTypeSpine

(* p ::= [p1,p2] | 1 | _ | @_ | !_ *)
datatype syncSkel =
   DepPair of syncSkel * syncSkel
 | One
 | Down
 | Affi
 | Bang 

(* k ::= nil | p;k | #1 k | #2 k *)
datatype asyncSkel = 
   Nil
 | LApp of syncSkel * asyncSkel
 | ProjLeft of asyncSkel
 | ProjRight of asyncSkel

(* PCtx ::= emp | A lin | A aff | A int | x:A *)
type patCtx = (string option * Syntax.nfAsyncType * Context.modality) list

(* "Patterns" decomposes an asynchronous type into its skeleton *)
val patterns: Syntax.nfAsyncType -> (asyncSkel * patCtx * head) list

end
