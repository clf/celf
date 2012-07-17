
signature TLU_RandomAccessList = TOP_LEVEL_UTIL

structure RandomAccessList : RANDOM_ACCESS_LIST =
struct
  type 'a ralist = 'a list

  fun toList x = x
  fun fromList x = x

  exception Empty
  exception Subscript

  val empty = []
  fun cons h t = h :: t
  val head = List.hd
  val tail = List.tl

  fun isempty [] = true
    | isempty (_::_) = false

  fun lookup x n = List.nth (x, n)
  fun update [] _ _ = raise Subscript
    | update (h::t) 0 x = x::t
    | update (h::t) n x = h :: update t (n-1) x

  val length = List.length
  fun create x 0 = []
    | create x n = x :: create x (n-1)
  fun drop x n = List.drop (x, n)

  fun prj [] = NONE
    | prj (h::t) = SOME (h, t)

  val foldl = List.foldl
  val foldr = List.foldr

  val map = List.map
  val exists = List.exists

  fun pairMapEq f (x, y) = map f (ListPair.zip (x, y))

end
