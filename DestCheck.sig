(* Mode checking *)

signature DESTCHECK =
sig
    val destCheckDecl : Syntax.nfAsyncType -> unit
    (* Returns () if the declaration is mode-correct.
       Raises ModeCheck.ModeCheckError otherwise. *)
end
