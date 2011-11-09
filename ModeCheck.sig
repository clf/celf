(* Mode checking *)

signature MODECHECK =
sig

    exception ModeCheckError of string

    val isNeeded : Syntax.nfAsyncType -> bool
    (* Returns true if at least one of the type families in head position
       has a mode declaration.
     *)

    val modeCheckDecl : Syntax.nfAsyncType -> unit
    (* Returns () if the declaration is mode-correct.
       Raises ModeCheckError otherwise.
     *)

end
