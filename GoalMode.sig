signature GOALMODE =
sig

    val okGoal   : Syntax.asyncType -> bool
    val isBchain : Syntax.asyncType -> bool
    val isFchain : Syntax.asyncType -> bool

end
