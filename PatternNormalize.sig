signature PATTERNNORMALIZE =
sig

    val tpatNormalize : Syntax.tpattern * Syntax.syncType -> Syntax.tpattern * Syntax.syncType

    val opatNormalize : Syntax.opattern -> Syntax.opattern

end
