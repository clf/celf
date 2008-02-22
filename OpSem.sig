signature OPSEM =
sig

type context

val fcLimit : int ref

val solve : context * Syntax.asyncType * (Syntax.obj * (context * bool) -> unit) -> unit

val solveEC : Syntax.asyncType * (Syntax.obj -> unit) -> unit

end
