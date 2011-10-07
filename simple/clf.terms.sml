structure ClfTerms:> CLF_TERMS =
struct
   (* Datatype views *)

   datatype fake_ = Fake_ of fake_
   
   and world_view =
      WSgn
    | WHeadS of pos
    | WHeadA of neg
    | WSubordS of pos
    | WSubordA of neg
    | WSubord
    | WPosAtom
   and world = injWorld of world_view
   
   and rel_view =
      Typ of Symbol.symbol
    | Con of Symbol.symbol * neg
    | HeadS of pos * head
    | HeadA of neg * head
    | SubordS of pos * head * head
    | SubordA of neg * head * head
    | Subord of head * head
    | PosAtom of Symbol.symbol
   and rel = injRel of rel_view
   
   and mode_view =
      Per
    | Aff
    | Lin
   and mode = injMode of mode_view
   
   and pos_view =
      Down of mode * neg
    | One
    | Tensor of pos * pos
   and pos = injPos of pos_view
   
   and neg_view =
      Atom of Symbol.symbol
    | Monad of pos
    | Lolli of pos * neg
    | With of neg * neg
   and neg = injNeg of neg_view
   
   and head_view =
      Monadic
    | Atomic of Symbol.symbol
   and head = injHead of head_view
   

   (* Constructor-specific projections, injections, and aborts *)

   fun prjWorld (injWorld x) = x
   fun prjRel (injRel x) = x
   fun prjMode (injMode x) = x
   fun prjPos (injPos x) = x
   fun prjNeg (injNeg x) = x
   fun prjHead (injHead x) = x
   val WSgn' = injWorld WSgn
   val WHeadS' = injWorld o WHeadS
   val WHeadA' = injWorld o WHeadA
   val WSubordS' = injWorld o WSubordS
   val WSubordA' = injWorld o WSubordA
   val WSubord' = injWorld WSubord
   val WPosAtom' = injWorld WPosAtom
   val Typ' = injRel o Typ
   val Con' = injRel o Con
   val HeadS' = injRel o HeadS
   val HeadA' = injRel o HeadA
   val SubordS' = injRel o SubordS
   val SubordA' = injRel o SubordA
   val Subord' = injRel o Subord
   val PosAtom' = injRel o PosAtom
   val Per' = injMode Per
   val Aff' = injMode Aff
   val Lin' = injMode Lin
   val Down' = injPos o Down
   val One' = injPos One
   val Tensor' = injPos o Tensor
   val Atom' = injNeg o Atom
   val Monad' = injNeg o Monad
   val Lolli' = injNeg o Lolli
   val With' = injNeg o With
   val Monadic' = injHead Monadic
   val Atomic' = injHead o Atomic
   

   (* String encoding functions *)

   fun strFake_ (Fake_ x) = strFake_ x
   
   and strWorld x_ = 
      case prjWorld x_ of
         WSgn =>
         "wSgn"
       | WHeadS x_0 =>
         ("(wHeadS"
          ^ " " ^ strPos x_0
          ^ ")")
       | WHeadA x_0 =>
         ("(wHeadA"
          ^ " " ^ strNeg x_0
          ^ ")")
       | WSubordS x_0 =>
         ("(wSubordS"
          ^ " " ^ strPos x_0
          ^ ")")
       | WSubordA x_0 =>
         ("(wSubordA"
          ^ " " ^ strNeg x_0
          ^ ")")
       | WSubord =>
         "wSubord"
       | WPosAtom =>
         "wPosAtom"
   
   and strRel x_ = 
      case prjRel x_ of
         Typ x_0 =>
         ("(typ"
          ^ " " ^ Symbol.name x_0
          ^ ")")
       | Con (x_0, x_1) =>
         ("(con"
          ^ " " ^ Symbol.name x_0
          ^ " " ^ strNeg x_1
          ^ ")")
       | HeadS (x_0, x_1) =>
         ("(headS"
          ^ " " ^ strPos x_0
          ^ " " ^ strHead x_1
          ^ ")")
       | HeadA (x_0, x_1) =>
         ("(headA"
          ^ " " ^ strNeg x_0
          ^ " " ^ strHead x_1
          ^ ")")
       | SubordS (x_0, x_1, x_2) =>
         ("(subordS"
          ^ " " ^ strPos x_0
          ^ " " ^ strHead x_1
          ^ " " ^ strHead x_2
          ^ ")")
       | SubordA (x_0, x_1, x_2) =>
         ("(subordA"
          ^ " " ^ strNeg x_0
          ^ " " ^ strHead x_1
          ^ " " ^ strHead x_2
          ^ ")")
       | Subord (x_0, x_1) =>
         ("(subord"
          ^ " " ^ strHead x_0
          ^ " " ^ strHead x_1
          ^ ")")
       | PosAtom x_0 =>
         ("(posAtom"
          ^ " " ^ Symbol.name x_0
          ^ ")")
   
   and strMode x_ = 
      case prjMode x_ of
         Per =>
         "per"
       | Aff =>
         "aff"
       | Lin =>
         "lin"
   
   and strPos x_ = 
      case prjPos x_ of
         Down (x_0, x_1) =>
         ("(down"
          ^ " " ^ strMode x_0
          ^ " " ^ strNeg x_1
          ^ ")")
       | One =>
         "one"
       | Tensor (x_0, x_1) =>
         ("(tensor"
          ^ " " ^ strPos x_0
          ^ " " ^ strPos x_1
          ^ ")")
   
   and strNeg x_ = 
      case prjNeg x_ of
         Atom x_0 =>
         ("(atom"
          ^ " " ^ Symbol.name x_0
          ^ ")")
       | Monad x_0 =>
         ("(monad"
          ^ " " ^ strPos x_0
          ^ ")")
       | Lolli (x_0, x_1) =>
         ("(lolli"
          ^ " " ^ strPos x_0
          ^ " " ^ strNeg x_1
          ^ ")")
       | With (x_0, x_1) =>
         ("(with"
          ^ " " ^ strNeg x_0
          ^ " " ^ strNeg x_1
          ^ ")")
   
   and strHead x_ = 
      case prjHead x_ of
         Monadic =>
         "monadic"
       | Atomic x_0 =>
         ("(atomic"
          ^ " " ^ Symbol.name x_0
          ^ ")")
   

   (* Equality *)

   fun eqWorld (x: world) (y: world) = x = y
   fun eqRel (x: rel) (y: rel) = x = y
   fun eqMode (x: mode) (y: mode) = x = y
   fun eqPos (x: pos) (y: pos) = x = y
   fun eqNeg (x: neg) (y: neg) = x = y
   fun eqHead (x: head) (y: head) = x = y
   
   
   (* Map helpers: sub *)

   fun subT x_ = DiscMap.subX x_

   fun subNat x_ = DiscMap.subII x_

   fun subString x_ = DiscMap.subS x_

   and subWorld x_ = 
      case prjWorld x_ of
         WPosAtom =>
         DiscMap.sub 0
       | WSubord =>
         DiscMap.sub 1
       | WSubordA x_0 =>
         subNeg x_0 o
         DiscMap.sub 2
       | WSubordS x_0 =>
         subPos x_0 o
         DiscMap.sub 3
       | WHeadA x_0 =>
         subNeg x_0 o
         DiscMap.sub 4
       | WHeadS x_0 =>
         subPos x_0 o
         DiscMap.sub 5
       | WSgn =>
         DiscMap.sub 6
   
   and subRel x_ = 
      case prjRel x_ of
         PosAtom x_0 =>
         subT x_0 o
         DiscMap.sub 0
       | Subord (x_0, x_1) =>
         subHead x_1 o
         subHead x_0 o
         DiscMap.sub 1
       | SubordA (x_0, x_1, x_2) =>
         subHead x_2 o
         subHead x_1 o
         subNeg x_0 o
         DiscMap.sub 2
       | SubordS (x_0, x_1, x_2) =>
         subHead x_2 o
         subHead x_1 o
         subPos x_0 o
         DiscMap.sub 3
       | HeadA (x_0, x_1) =>
         subHead x_1 o
         subNeg x_0 o
         DiscMap.sub 4
       | HeadS (x_0, x_1) =>
         subHead x_1 o
         subPos x_0 o
         DiscMap.sub 5
       | Con (x_0, x_1) =>
         subNeg x_1 o
         subT x_0 o
         DiscMap.sub 6
       | Typ x_0 =>
         subT x_0 o
         DiscMap.sub 7
   
   and subMode x_ = 
      case prjMode x_ of
         Lin =>
         DiscMap.sub 0
       | Aff =>
         DiscMap.sub 1
       | Per =>
         DiscMap.sub 2
   
   and subPos x_ = 
      case prjPos x_ of
         Tensor (x_0, x_1) =>
         subPos x_1 o
         subPos x_0 o
         DiscMap.sub 0
       | One =>
         DiscMap.sub 1
       | Down (x_0, x_1) =>
         subNeg x_1 o
         subMode x_0 o
         DiscMap.sub 2
   
   and subNeg x_ = 
      case prjNeg x_ of
         With (x_0, x_1) =>
         subNeg x_1 o
         subNeg x_0 o
         DiscMap.sub 0
       | Lolli (x_0, x_1) =>
         subNeg x_1 o
         subPos x_0 o
         DiscMap.sub 1
       | Monad x_0 =>
         subPos x_0 o
         DiscMap.sub 2
       | Atom x_0 =>
         subT x_0 o
         DiscMap.sub 3
   
   and subHead x_ = 
      case prjHead x_ of
         Atomic x_0 =>
         subT x_0 o
         DiscMap.sub 0
       | Monadic =>
         DiscMap.sub 1
   
   
   (* Map helpers: unzip *)

   fun unzipT x_ = DiscMap.unzipX x_

   fun unzipNat x_ = DiscMap.unzipII x_

   fun unzipString x_ = DiscMap.unzipS x_

   and unzipWorld x_ = 
      case prjWorld x_ of
         WPosAtom =>
         DiscMap.unzip (0, 7)
       | WSubord =>
         DiscMap.unzip (1, 7)
       | WSubordA x_0 =>
         unzipNeg x_0 o
         DiscMap.unzip (2, 7)
       | WSubordS x_0 =>
         unzipPos x_0 o
         DiscMap.unzip (3, 7)
       | WHeadA x_0 =>
         unzipNeg x_0 o
         DiscMap.unzip (4, 7)
       | WHeadS x_0 =>
         unzipPos x_0 o
         DiscMap.unzip (5, 7)
       | WSgn =>
         DiscMap.unzip (6, 7)
   
   and unzipRel x_ = 
      case prjRel x_ of
         PosAtom x_0 =>
         unzipT x_0 o
         DiscMap.unzip (0, 8)
       | Subord (x_0, x_1) =>
         unzipHead x_1 o
         unzipHead x_0 o
         DiscMap.unzip (1, 8)
       | SubordA (x_0, x_1, x_2) =>
         unzipHead x_2 o
         unzipHead x_1 o
         unzipNeg x_0 o
         DiscMap.unzip (2, 8)
       | SubordS (x_0, x_1, x_2) =>
         unzipHead x_2 o
         unzipHead x_1 o
         unzipPos x_0 o
         DiscMap.unzip (3, 8)
       | HeadA (x_0, x_1) =>
         unzipHead x_1 o
         unzipNeg x_0 o
         DiscMap.unzip (4, 8)
       | HeadS (x_0, x_1) =>
         unzipHead x_1 o
         unzipPos x_0 o
         DiscMap.unzip (5, 8)
       | Con (x_0, x_1) =>
         unzipNeg x_1 o
         unzipT x_0 o
         DiscMap.unzip (6, 8)
       | Typ x_0 =>
         unzipT x_0 o
         DiscMap.unzip (7, 8)
   
   and unzipMode x_ = 
      case prjMode x_ of
         Lin =>
         DiscMap.unzip (0, 3)
       | Aff =>
         DiscMap.unzip (1, 3)
       | Per =>
         DiscMap.unzip (2, 3)
   
   and unzipPos x_ = 
      case prjPos x_ of
         Tensor (x_0, x_1) =>
         unzipPos x_1 o
         unzipPos x_0 o
         DiscMap.unzip (0, 3)
       | One =>
         DiscMap.unzip (1, 3)
       | Down (x_0, x_1) =>
         unzipNeg x_1 o
         unzipMode x_0 o
         DiscMap.unzip (2, 3)
   
   and unzipNeg x_ = 
      case prjNeg x_ of
         With (x_0, x_1) =>
         unzipNeg x_1 o
         unzipNeg x_0 o
         DiscMap.unzip (0, 4)
       | Lolli (x_0, x_1) =>
         unzipNeg x_1 o
         unzipPos x_0 o
         DiscMap.unzip (1, 4)
       | Monad x_0 =>
         unzipPos x_0 o
         DiscMap.unzip (2, 4)
       | Atom x_0 =>
         unzipT x_0 o
         DiscMap.unzip (3, 4)
   
   and unzipHead x_ = 
      case prjHead x_ of
         Atomic x_0 =>
         unzipT x_0 o
         DiscMap.unzip (0, 2)
       | Monadic =>
         DiscMap.unzip (1, 2)
   
   
   (* Maps *)

   structure MapWorld = DiscMapFn
   (struct
      type key = world
      val unzip = unzipWorld
      val sub = subWorld
   end)

   structure MapRel = DiscMapFn
   (struct
      type key = rel
      val unzip = unzipRel
      val sub = subRel
   end)

   structure MapMode = DiscMapFn
   (struct
      type key = mode
      val unzip = unzipMode
      val sub = subMode
   end)

   structure MapPos = DiscMapFn
   (struct
      type key = pos
      val unzip = unzipPos
      val sub = subPos
   end)

   structure MapNeg = DiscMapFn
   (struct
      type key = neg
      val unzip = unzipNeg
      val sub = subNeg
   end)

   structure MapHead = DiscMapFn
   (struct
      type key = head
      val unzip = unzipHead
      val sub = subHead
   end)

end

