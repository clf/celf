signature SIGNATURE =
sig

  val insertDecl : InternalSyntax.decl -> unit

  val getImplicitNum : string -> int

  val getMonadicCand : unit -> (string * InternalSyntax.lr list * InternalSyntax.asyncType) list

  val getAtomicCand : string -> (string * InternalSyntax.lr list * InternalSyntax.asyncType) list

  val getModeDecl : string -> InternalSyntax.modeDecl option
  val isPosAtom : string -> bool

end
