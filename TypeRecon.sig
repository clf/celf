signature TYPERECON =
sig

val reconstructDecl : Syntax.decl -> Syntax.decl
val reconstructSignature : Syntax.decl list -> unit

end
