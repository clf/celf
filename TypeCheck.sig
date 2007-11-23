signature TYPECHECK =
sig

(* Page 9: of CLF TR CMU-CS-02-101 *)

type context

val enable : unit -> unit
val isEnabled : unit -> bool

val checkKind : context * Syntax.kind -> unit
val checkType : context * Syntax.asyncType -> unit
val checkTypeSpine : context * Syntax.typeSpine * Syntax.kind -> unit
val checkSyncType : context * Syntax.syncType -> unit
val checkObj : context * Syntax.obj * Syntax.asyncType -> context * bool
val inferSpine : context * Syntax.spine * Syntax.asyncType -> context * bool * Syntax.asyncType
val inferHead : context * Syntax.head -> context * bool * Syntax.asyncType

val checkKindEC : Syntax.kind -> unit
val checkTypeEC : Syntax.asyncType -> unit
val checkObjEC : Syntax.obj * Syntax.asyncType -> unit

end
