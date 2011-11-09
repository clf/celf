signature PATTERNNORMALIZE =
sig

    val sync2async : Syntax.nfSyncType -> Syntax.nfAsyncType

    val syncNormalize : Syntax.nfSyncType -> Syntax.nfSyncType

    val tpatNormalize : Syntax.tpattern * Syntax.nfSyncType -> Syntax.tpattern * Syntax.nfSyncType

    val opatNormalize : Syntax.opattern -> Syntax.opattern

end
