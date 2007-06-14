signature WHNF =
sig

val whnfObj : Syntax.obj -> Syntax.obj Syntax.objF
val whnfExp : Syntax.expObj -> Syntax.expObj Syntax.expObjF

val whnfLetSpine : Syntax.expObj -> Syntax.expObj

val normalizeKind : Syntax.kind -> Syntax.kind
val normalizeType : Syntax.asyncType -> Syntax.asyncType
val normalizeObj : Syntax.obj -> Syntax.obj

end
