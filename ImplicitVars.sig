signature IMPLICITVARS =
sig

type implicits = (string * Syntax.asyncType) list

val resetUCTable : unit -> unit
val mapUCTable : (Syntax.asyncType -> Syntax.asyncType) -> unit
val appUCTable : (Syntax.asyncType -> unit) -> unit
val noUCVars : unit -> unit
val apxUCLookup : string -> Syntax.apxAsyncType
val ucLookup : string -> Syntax.asyncType
val sort : unit -> implicits

val logicVarsToUCVarsObj : Syntax.obj -> unit
val logicVarsToUCVarsType : Syntax.asyncType -> unit
val logicVarsToUCVarsKind : Syntax.kind -> unit

val convUCVars2VarsKind : implicits -> Syntax.kind -> Syntax.kind
val convUCVars2VarsType : implicits -> Syntax.asyncType -> Syntax.asyncType
val convUCVars2VarsImps : implicits -> implicits

val convUCVars2LogicVarsType : Syntax.asyncType -> Syntax.asyncType * (string * Syntax.obj) list

end
