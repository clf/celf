signature PATTERNBIND =
sig

val patBind : (Syntax.asyncType -> 'a) -> Syntax.pattern -> 'a Context.context -> 'a Context.context
val patUnbind : Syntax.pattern * 'a Context.context * bool -> 'a Context.context
val patUnbindOpt : Syntax.pattern * 'a Context.context * bool -> 'a Context.context option

end
