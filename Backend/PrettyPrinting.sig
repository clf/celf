signature PRETTY_PRINTING =
sig

  val printDecl : InternalSyntax.decl -> string

  val printMode : InternalSyntax.mode -> string

  val printImpl : bool ref

  val printKind : InternalSyntax.kind -> string
  val printType : InternalSyntax.asyncType -> string
  val printTypeInCtx : string list -> InternalSyntax.asyncType -> string
  val printSyncType : InternalSyntax.syncType -> string
  val printObj : InternalSyntax.object -> string
  val printPreObj : InternalSyntax.object -> string
  val printMonadObj : InternalSyntax.monadObj -> string

  val printSubst : InternalSyntax.subst -> string
end
