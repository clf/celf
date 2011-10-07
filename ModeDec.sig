signature MODEDEC =
sig

    val shortToFull : Syntax.kind * int * Syntax.modeDecl -> Syntax.modeDecl
    val checkFull : Syntax.kind * Syntax.modeDecl -> unit

end
