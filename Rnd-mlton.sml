structure Rnd :> RND =
struct

type rndState = Random.rand

fun rndNew s = Random.rand (42, s)
val rndReal = Random.randReal

end
