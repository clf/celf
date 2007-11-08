signature SIGNATUR_TABLE =
sig

datatype lr = L | R
datatype headType = HdMonad | HdAtom of string

val heads : Syntax.asyncType -> (lr list * headType) list

val getCandMonad : unit -> (string * lr list * Syntax.asyncType) list
val getCandAtomic : string -> (string * lr list * Syntax.asyncType) list

end
