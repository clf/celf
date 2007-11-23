structure Rnd :> RND =
struct

type rndState = Random.generator

val rndNew = Random.newgenseed o real
val rndReal = Random.random

end
