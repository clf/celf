(* Global sets and data structures *)
(* Robert J. Simmons *)

structure SetS = 
RedBlackSetFn(struct type ord_key = string val compare = String.compare end)

structure MapS = 
RedBlackMapFn(struct type ord_key = string val compare = String.compare end)

structure SetI = 
RedBlackSetFn(struct type ord_key = int val compare = Int.compare end)

structure MapI = 
RedBlackMapFn(struct type ord_key = int val compare = Int.compare end)

structure SetII = 
RedBlackSetFn(struct type ord_key = IntInf.int val compare = IntInf.compare end)

structure MapII = 
RedBlackMapFn(struct type ord_key = IntInf.int val compare = IntInf.compare end)

structure MapP = 
RedBlackMapFn(struct 
   type ord_key = int list 
   fun compare ([], []) = EQUAL
     | compare ([], _) = LESS
     | compare (_, []) = GREATER
     | compare (x :: xs, y :: ys) = 
       if x < y then LESS
       else if x > y then GREATER 
       else compare (xs, ys)
end)
