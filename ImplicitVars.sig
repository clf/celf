signature IMPLICITVARS =
sig

val resetUCTable : unit -> unit
val mapUCTable : (Syntax.asyncType -> Syntax.asyncType) -> unit
val appUCTable : (Syntax.asyncType -> unit) -> unit
val noUCVars : unit -> unit
val apxUCLookup : string -> Syntax.apxAsyncType
val ucLookup : string -> Syntax.asyncType
val sort : unit -> Syntax.implicits

val logicVarsToUCVarsObj : Syntax.obj -> unit
val logicVarsToUCVarsType : Syntax.asyncType -> unit
val logicVarsToUCVarsKind : Syntax.kind -> unit

val convUCVars2VarsKind : Syntax.implicits -> Syntax.kind -> Syntax.kind
val convUCVars2VarsType : Syntax.implicits -> Syntax.asyncType -> Syntax.asyncType
val convUCVars2VarsImps : Syntax.implicits -> Syntax.implicits

val convUCVars2LogicVarsType : Syntax.asyncType -> Syntax.asyncType * (string * Syntax.obj) list

end
