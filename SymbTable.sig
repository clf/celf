signature SYMBTABLE =
sig

type 'a Table

val empty : unit -> 'a Table
val peek : 'a Table * string -> 'a option
val insert : 'a Table * string * 'a -> 'a Table
val toList : 'a Table -> (string * 'a) list
val numItems : 'a Table -> int
val delete : 'a Table * string -> 'a Table
val mapTable : ('a -> 'b) -> 'a Table -> 'b Table

end
