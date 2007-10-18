signature TYPECHECK =
sig

(* Page 9: of CLF TR CMU-CS-02-101 *)

type context

exception Error 

val checkObj : context * Syntax.obj * Syntax.asyncType -> context * bool
val inferSpine : context * Syntax.spine * Syntax.asyncType -> context * bool * Syntax.asyncType
val inferHead : context * Syntax.head -> context * bool * Syntax.asyncType
end
