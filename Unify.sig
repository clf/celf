signature UNIFY =
sig

exception ExnUnify of string

val resetConstrs : unit -> unit
val noConstrs : unit -> unit
val addConstraint : Syntax.constr VRef.vref * Syntax.constr VRef.vref list VRef.vref list -> unit
val instantiate : Syntax.obj option VRef.vref * Syntax.obj * Syntax.constr VRef.vref list VRef.vref * int -> unit

val lowerObj : Syntax.obj Syntax.objF -> Syntax.obj Syntax.objF

val objExists : bool -> Syntax.obj option VRef.vref -> Syntax.subst -> Syntax.obj -> Syntax.obj option
val typeExists : bool -> Syntax.obj option VRef.vref -> Syntax.subst -> Syntax.asyncType -> Syntax.asyncType option

val unify : Syntax.asyncType * Syntax.asyncType * (unit -> string) -> unit
val unifiable : Syntax.asyncType * Syntax.asyncType -> bool

end
