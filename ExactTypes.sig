signature EXACTTYPES =
sig

type context
val emptyCtx : context

val checkKind : context * Syntax.kind -> unit
val checkType : context * Syntax.asyncType -> unit
val checkTypeSpine : context * Syntax.typeSpine * Syntax.kind -> unit
val checkSyncType : context * Syntax.syncType -> unit
val checkObj : context * Syntax.obj * Syntax.asyncType -> context * bool
val inferHead : context * Syntax.head -> context * Syntax.asyncType
val inferSpine : context * Syntax.spine * Syntax.asyncType -> context * bool * Syntax.asyncType
val checkExp : context * Syntax.expObj * Syntax.syncType -> context * bool
val checkPattern : context * Syntax.pattern -> Syntax.syncType
val checkMonadObj : context * Syntax.monadObj * Syntax.syncType -> context * bool

val checkKindEC : Syntax.kind -> unit
val checkTypeEC : Syntax.asyncType -> unit
val checkObjEC : Syntax.obj * Syntax.asyncType -> unit

end
