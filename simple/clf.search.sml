structure ClfSearch:> CLF_SEARCH =
struct
   open ClfTerms
   open ClfTables

   fun loop fs = if !cnt = (app (fn f => f ()) fs; !cnt) then () else loop fs
   exception Revisit

   fun fake () = ()

   and saturateWSgn worldmap =
      let
         val w = WSgn'
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            ((fn x => x)
            , [])
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

   and saturateWHeadS x_0 worldmap =
      let
         val w = WHeadS' x_0
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            (case prjPos x_0 of
               Tensor (x_0_0, x_0_1) => 
               (saturateWHeadS x_0_0
                o saturateWHeadS x_0_1
               , exec6 (x_0_0, x_0_1) ::
                 exec7 (x_0_1, x_0_0) ::
                 [])
             | One => 
               ((fn x => x)
               , [])
             | Down (x_0_0, x_0_1) => 
               (saturateWHeadA x_0_1
               , exec5 (x_0_1, x_0_0) ::
                 [])
            )
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

   and saturateWHeadA x_0 worldmap =
      let
         val w = WHeadA' x_0
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            (case prjNeg x_0 of
               With (x_0_0, x_0_1) => 
               (saturateWHeadA x_0_0
                o saturateWHeadA x_0_1
               , exec3 (x_0_0, x_0_1) ::
                 exec4 (x_0_1, x_0_0) ::
                 [])
             | Lolli (x_0_0, x_0_1) => 
               (saturateWHeadA x_0_1
               , exec2 (x_0_1, x_0_0) ::
                 [])
             | Monad x_0_0 => 
               ((fn x => x)
               , exec1 x_0_0 ::
                 [])
             | Atom x_0_0 => 
               ((fn x => x)
               , exec0 x_0_0 ::
                 [])
            )
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

   and saturateWSubordS x_0 worldmap =
      let
         val w = WSubordS' x_0
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            (case prjPos x_0 of
               Tensor (x_0_0, x_0_1) => 
               (saturateWSubordS x_0_0
                o saturateWSubordS x_0_1
               , exec10 (x_0_0, x_0_1) ::
                 exec11 (x_0_1, x_0_0) ::
                 [])
             | One => 
               ((fn x => x)
               , [])
             | Down (x_0_0, x_0_1) => 
               (saturateWSubordA x_0_1
               , exec9 (x_0_1, x_0_0) ::
                 [])
            )
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

   and saturateWSubordA x_0 worldmap =
      let
         val w = WSubordA' x_0
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            (case prjNeg x_0 of
               With (x_0_0, x_0_1) => 
               ((fn x => x)
               , [])
             | Lolli (x_0_0, x_0_1) => 
               (saturateWHeadA x_0_1
                o saturateWHeadS x_0_0
                o saturateWSubordA x_0_1
                o saturateWSubordS x_0_0
               , exec8 (x_0_0, x_0_1) ::
                 exec13 (x_0_0, x_0_1) ::
                 exec14 (x_0_0, x_0_1) ::
                 [])
             | Monad x_0_0 => 
               (saturateWSubordS x_0_0
               , exec12 x_0_0 ::
                 [])
             | Atom x_0_0 => 
               ((fn x => x)
               , [])
            )
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

   and saturateWSubord worldmap =
      let
         val w = WSubord'
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            (saturateWSubord
             o saturateWSubord
            , exec15 ::
              [])
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

   and saturateWPosAtom worldmap =
      let
         val w = WPosAtom'
         val () = if isSome (MapWorld.find (worldmap, w))
                  then raise Revisit else ()
         val worldmap = MapWorld.insert (worldmap, w, ())
         val (child_searches, rulefns) = 
            (saturateWSubord
             o saturateWSubord
             o saturateWSgn
             o saturateWPosAtom
            , exec16 ::
              exec17 ::
              [])
         val worldmap' = child_searches worldmap
         val () = loop rulefns
      in
         worldmap'
      end handle Revisit => worldmap

end
