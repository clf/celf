signature GOALMODE =
sig

    val okGoal   : Syntax.nfAsyncType -> bool
    val isBchain : Syntax.nfAsyncType -> bool
    val isFchain : Syntax.nfAsyncType -> bool

end
