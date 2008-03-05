(*  Celf
 *  Copyright (C) 2008 Anders Schack-Nielsen and Carsten Schürmann
 *
 *  This file is part of Celf.
 *
 *  Celf is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  Celf is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with Celf.  If not, see <http://www.gnu.org/licenses/>.
 *)

signature CONV =
sig

(* Invariant: We assume that all objects are in canonical form
   this means that we only have to study the let floating
   properties
*)

val convAsyncType : Syntax.nfAsyncType * Syntax.nfAsyncType -> unit  
val convObj : Syntax.nfObj * Syntax.nfObj -> unit
val convSpine : Syntax.nfSpine * Syntax.nfSpine -> unit
val convHead : Syntax.nfHead * Syntax.nfHead -> unit

end
