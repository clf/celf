signature ABSTRACT_TO_INTERNAL =
sig

val declToInternal : Syntax.decl -> InternalSyntax.decl

val typeToInternal : Syntax.asyncType -> InternalSyntax.asyncType

end
