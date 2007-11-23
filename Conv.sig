signature CONV =
sig

(* Invariant: We assume that all objects are in canonical form
   this means that we only have to study the let floating
   properties
*)

val convAsyncType : Syntax.nfAsyncType * Syntax.nfAsyncType -> unit  
val convObj : Syntax.nfObj * Syntax.nfObj -> unit
val convSpine : Syntax.nfSpine * Syntax.nfSpine -> unit
val convHead : Syntax.nfHead * Syntax.nfHead -> unit

end
