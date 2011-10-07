signature CLF_TERMS = 
sig
   type world
   type rel
   type mode
   type pos
   type neg
   type head
   
   datatype world_view =
      WSgn
    | WHeadS of pos
    | WHeadA of neg
    | WSubordS of pos
    | WSubordA of neg
    | WSubord
    | WPosAtom
   structure MapWorld: DISC_MAP where type key = world
   val strWorld: world -> String.string
   val injWorld: world_view -> world
   val prjWorld: world -> world_view
   val eqWorld: world -> world -> bool
   val WSgn': world
   val WHeadS': pos -> world
   val WHeadA': neg -> world
   val WSubordS': pos -> world
   val WSubordA': neg -> world
   val WSubord': world
   val WPosAtom': world
   
   datatype rel_view =
      Typ of Symbol.symbol
    | Con of Symbol.symbol * neg
    | HeadS of pos * head
    | HeadA of neg * head
    | SubordS of pos * head * head
    | SubordA of neg * head * head
    | Subord of head * head
    | PosAtom of Symbol.symbol
   structure MapRel: DISC_MAP where type key = rel
   val strRel: rel -> String.string
   val injRel: rel_view -> rel
   val prjRel: rel -> rel_view
   val eqRel: rel -> rel -> bool
   val Typ': Symbol.symbol -> rel
   val Con': Symbol.symbol * neg -> rel
   val HeadS': pos * head -> rel
   val HeadA': neg * head -> rel
   val SubordS': pos * head * head -> rel
   val SubordA': neg * head * head -> rel
   val Subord': head * head -> rel
   val PosAtom': Symbol.symbol -> rel
   
   datatype mode_view =
      Per
    | Aff
    | Lin
   structure MapMode: DISC_MAP where type key = mode
   val strMode: mode -> String.string
   val injMode: mode_view -> mode
   val prjMode: mode -> mode_view
   val eqMode: mode -> mode -> bool
   val Per': mode
   val Aff': mode
   val Lin': mode
   
   datatype pos_view =
      Down of mode * neg
    | One
    | Tensor of pos * pos
   structure MapPos: DISC_MAP where type key = pos
   val strPos: pos -> String.string
   val injPos: pos_view -> pos
   val prjPos: pos -> pos_view
   val eqPos: pos -> pos -> bool
   val Down': mode * neg -> pos
   val One': pos
   val Tensor': pos * pos -> pos
   
   datatype neg_view =
      Atom of Symbol.symbol
    | Monad of pos
    | Lolli of pos * neg
    | With of neg * neg
   structure MapNeg: DISC_MAP where type key = neg
   val strNeg: neg -> String.string
   val injNeg: neg_view -> neg
   val prjNeg: neg -> neg_view
   val eqNeg: neg -> neg -> bool
   val Atom': Symbol.symbol -> neg
   val Monad': pos -> neg
   val Lolli': pos * neg -> neg
   val With': neg * neg -> neg
   
   datatype head_view =
      Monadic
    | Atomic of Symbol.symbol
   structure MapHead: DISC_MAP where type key = head
   val strHead: head -> String.string
   val injHead: head_view -> head
   val prjHead: head -> head_view
   val eqHead: head -> head -> bool
   val Monadic': head
   val Atomic': Symbol.symbol -> head
end
