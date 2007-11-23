signature TYPECHECK =
sig

(* Page 9: of CLF TR CMU-CS-02-101 *)

type context

val enable : unit -> unit
val isEnabled : unit -> bool

val checkKind : context * Syntax.nfKind -> unit
val checkType : context * Syntax.nfAsyncType -> unit
val checkTypeSpine : context * Syntax.nfTypeSpine * Syntax.nfKind -> unit
val checkSyncType : context * Syntax.nfSyncType -> unit
val checkObj : context * Syntax.nfObj * Syntax.nfAsyncType -> context * bool
val inferSpine : context * Syntax.nfSpine * Syntax.nfAsyncType -> context * bool * Syntax.nfAsyncType
val inferHead : context * Syntax.nfHead -> context * bool * Syntax.nfAsyncType

val checkKindEC : Syntax.kind -> unit
val checkTypeEC : Syntax.asyncType -> unit
val checkObjEC : Syntax.obj * Syntax.asyncType -> unit

end
