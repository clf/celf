signature CONV =
sig

(* Invariant: We assume that all objects are in canonical form
   this means that we only have to study the let floating
   properties
*)

val convAsyncType : Syntax.asyncType * Syntax.asyncType -> unit  
val convObj : Syntax.obj * Syntax.obj -> unit
val convSpine : Syntax.spine * Syntax.spine -> unit
val convHead : Syntax.head * Syntax.head -> unit

end