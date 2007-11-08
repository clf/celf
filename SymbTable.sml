structure SymbTable :> SYMBTABLE =
struct

type 'a Table = (string, 'a) Binarymap.dict

val empty = fn () => Binarymap.mkDict String.compare
val peek = Binarymap.peek
val insert = Binarymap.insert
(*fun equal (t1,t2) = (Binarymap.listItems t1) = (Binarymap.listItems t2)*)
val toList = Binarymap.listItems
val numItems = Binarymap.numItems
fun delete tk = #1 (Binarymap.remove tk)
val mapTable = Binarymap.transform
fun appTable f t = Binarymap.app (f o #2) t

end
