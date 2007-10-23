signature UTIL =
sig

val map1 : ('a -> 'c) -> 'a * 'b -> 'c * 'b
val map2 : ('b -> 'd) -> 'a * 'b -> 'a * 'd
val map12 : ('a -> 'c) -> ('b -> 'd) -> 'a * 'b -> 'c * 'd

val linApp : Syntax.obj * Syntax.obj -> Syntax.obj
val app : Syntax.obj * Syntax.obj -> Syntax.obj
val projLeft : Syntax.obj -> Syntax.obj
val projRight : Syntax.obj -> Syntax.obj
val blank : unit -> Syntax.obj
val headToObj : Syntax.head -> Syntax.obj

val linLamConstr : string * Syntax.asyncType * Syntax.obj -> Syntax.obj
val lamConstr : string * Syntax.asyncType * Syntax.obj -> Syntax.obj

val typePrjAbbrev : Syntax.asyncType -> Syntax.asyncType Syntax.asyncTypeF

val apxTypePrjAbbrev : Syntax.apxAsyncType -> Syntax.apxAsyncType Syntax.apxAsyncTypeF

val isNil : Syntax.spine -> bool

val appendSpine : Syntax.spine * Syntax.spine -> Syntax.spine

val objAppKind : (unit Syntax.objF -> unit) -> Syntax.kind -> unit
val objAppType : (unit Syntax.objF -> unit) -> Syntax.asyncType -> unit
val objAppObj  : (unit Syntax.objF -> unit) -> Syntax.obj -> unit

val objExpMapKind : (Syntax.expObj -> Syntax.expObj Syntax.expObjF) ->
	(Syntax.obj -> Syntax.obj Syntax.objF) -> Syntax.kind -> Syntax.kind
val objExpMapType : (Syntax.expObj -> Syntax.expObj Syntax.expObjF) ->
	(Syntax.obj -> Syntax.obj Syntax.objF) -> Syntax.asyncType -> Syntax.asyncType
val objExpMapObj : (Syntax.expObj -> Syntax.expObj Syntax.expObjF) ->
	(Syntax.obj -> Syntax.obj Syntax.objF) -> Syntax.obj -> Syntax.obj

val objMapKind : (Syntax.obj -> Syntax.obj Syntax.objF) -> Syntax.kind -> Syntax.kind
val objMapType : (Syntax.obj -> Syntax.obj Syntax.objF) -> Syntax.asyncType -> Syntax.asyncType
val objMapObj : (Syntax.obj -> Syntax.obj Syntax.objF) -> Syntax.obj -> Syntax.obj
(*
val objMapKind = objExpMapKind ExpObj.prj
val objMapType = objExpMapType ExpObj.prj
val objMapObj = objExpMapObj ExpObj.prj
*)

end
