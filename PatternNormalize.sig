signature PATTERNNORMALIZE =
sig

    val sync2async : Syntax.syncType -> Syntax.asyncType

    val syncNormalize : Syntax.syncType -> Syntax.syncType

    val tpatNormalize : Syntax.tpattern * Syntax.syncType -> Syntax.tpattern * Syntax.syncType

    val opatNormalize : Syntax.opattern -> Syntax.opattern

end
