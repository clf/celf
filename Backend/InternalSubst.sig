signature INTERNAL_SUBST =
sig

  val etaContract : exn -> InternalSyntax.object -> InternalSyntax.modality * int

  val invert : InternalSyntax.subst -> InternalSyntax.subst


  val substType : InternalSyntax.asyncType * InternalSyntax.subst -> InternalSyntax.asyncType
  val substSyncType : InternalSyntax.syncType * InternalSyntax.subst -> InternalSyntax.syncType
  val substObj : InternalSyntax.object * InternalSyntax.subst -> InternalSyntax.object



  val mkSubstMonad : InternalSyntax.monadObj * InternalSyntax.subst -> InternalSyntax.subst
  val patternSubst : (InternalSyntax.object -> InternalSyntax.object * bool)
                     -> (exn -> InternalSyntax.object -> InternalSyntax.modality * int)
                     -> InternalSyntax.subst
                     -> ((InternalSyntax.subModality * int) list
                         * InternalSyntax.subst) option


  val whnfObj : InternalSyntax.object -> InternalSyntax.object
  val reduceObj : InternalSyntax.object * InternalSyntax.spine -> InternalSyntax.object

  val normalizeType : InternalSyntax.asyncType -> InternalSyntax.asyncType
  val normalizeSyncType : InternalSyntax.syncType -> InternalSyntax.syncType
  val normalizeObj : InternalSyntax.object -> InternalSyntax.object

end
