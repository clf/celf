signature OPSEM =
sig

type context

val solve : context * Syntax.asyncType * (Syntax.obj * (context * bool) -> unit) -> unit

end
