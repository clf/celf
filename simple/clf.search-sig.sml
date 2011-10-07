signature CLF_SEARCH =
sig
   val saturateWSgn: unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
   val saturateWHeadS: ClfTerms.pos -> unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
   val saturateWHeadA: ClfTerms.neg -> unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
   val saturateWSubordS: ClfTerms.pos -> unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
   val saturateWSubordA: ClfTerms.neg -> unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
   val saturateWSubord: unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
   val saturateWPosAtom: unit ClfTerms.MapWorld.map -> unit ClfTerms.MapWorld.map
end
