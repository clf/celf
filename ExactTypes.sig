signature EXACTTYPES =
sig

type context
val emptyCtx : context

exception ExnUnify of string

val resetConstrs : unit -> unit
val noConstrs : unit -> unit
val addConstraint : Syntax.constr ref * Syntax.constr ref list ref list -> unit
val instantiate : Syntax.obj option ref * Syntax.obj * Syntax.constr ref list ref * int -> unit

val lowerObj : Syntax.obj Syntax.objF -> Syntax.obj Syntax.objF

val objExists : bool -> Syntax.obj option ref -> Syntax.subst -> Syntax.obj -> Syntax.obj option
val typeExists : bool -> Syntax.obj option ref -> Syntax.subst -> Syntax.asyncType -> Syntax.asyncType option

val unify : Syntax.asyncType * Syntax.asyncType * (unit -> string) -> unit

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
