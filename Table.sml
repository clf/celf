(* From Twelf *)

structure StringRedBlackTree =
  RedBlackTree (type key' = string
		val compare = String.compare) 

structure IntRedBlackTree =
  RedBlackTree (type key' = int
		val compare = Int.compare) 

