signature CONTEXT =
sig

datatype mode = UN | LIN | NO
type 'a context

val ctx2list : 'a context -> (string * 'a * mode) list
val ctxCons : (string * 'a * mode) -> 'a context -> 'a context

val emptyCtx : 'a context

val ctxDelLin : 'a context -> 'a context

val ctxLookupNum : 'a context * int -> 'a context * 'a
val ctxLookupName : 'a context * string -> (int * 'a * 'a context) option

val ctxPushUN : string * 'a * 'a context -> 'a context
val ctxPushLIN : string * 'a * 'a context -> 'a context
val ctxPopUN : 'a context -> 'a context
val ctxPopLIN : bool * 'a context -> 'a context

val ctxAddJoin : bool * bool -> 'a context * 'a context -> 'a context

end
