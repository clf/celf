signature MODEDEC =
sig

    val shortToFull : Syntax.nfKind * int * Syntax.modeDecl -> Syntax.modeDecl
    val checkFull : Syntax.nfKind * Syntax.modeDecl -> unit

end
