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

signature SYMBTABLE =
sig

type 'a Table

val empty : unit -> 'a Table
val peek : 'a Table * string -> 'a option
val insert : 'a Table * string * 'a -> 'a Table
val toList : 'a Table -> (string * 'a) list
val numItems : 'a Table -> int
val delete : 'a Table * string -> 'a Table
val mapTable : ('a -> 'b) -> 'a Table -> 'b Table
val appTable : ('a -> unit) -> 'a Table -> unit

end
