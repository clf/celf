signature IMPLICITVARS =
sig

val resetUCTable : unit -> unit
val mapUCTable : (Syntax.asyncType -> Syntax.asyncType) -> unit
val noUCVars : unit -> unit
val apxUCLookup : string -> Syntax.apxAsyncType
val ucLookup : string -> Syntax.asyncType
val sort : unit -> Syntax.implicits

val logicVarsToUCVarsObj : Syntax.obj -> unit
val logicVarsToUCVarsType : Syntax.asyncType -> unit
val logicVarsToUCVarsKind : Syntax.kind -> unit

val convertUCVarsKind : Syntax.implicits -> Syntax.kind -> Syntax.kind
val convertUCVarsType : Syntax.implicits -> Syntax.asyncType -> Syntax.asyncType
val convertUCVarsImps : Syntax.implicits -> Syntax.implicits

end
