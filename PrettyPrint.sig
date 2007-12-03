signature PRETTYPRINT =
sig

val printImpl : bool ref

val printKind : Syntax.kind -> string
val printType : Syntax.asyncType -> string
val printObj : Syntax.obj -> string

val printPreType : Syntax.asyncType -> string
val printPreObj : Syntax.obj -> string

val remDepKind : Syntax.kind -> Syntax.kind
val remDepType : Syntax.asyncType -> Syntax.asyncType
val remDepObj : Syntax.obj -> Syntax.obj

end
