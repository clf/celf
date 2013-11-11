signature BACKEND =
sig

exception QueryFailed of int

val processDecl : Syntax.decl -> unit


end
