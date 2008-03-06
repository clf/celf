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

structure SymbTable :> SYMBTABLE =
struct

structure Binarymap = BinaryMapFn (struct
			type ord_key = string
			val compare = String.compare
			end)

(*type 'a Table = (string, 'a) Binarymap.dict*)
type 'a Table = 'a Binarymap.map

(*val empty = fn () => Binarymap.mkDict String.compare*)
val empty = fn () => Binarymap.empty
(*val peek = Binarymap.peek*)
val peek = Binarymap.find
val insert = Binarymap.insert
(*val toList = Binarymap.listItems*)
val toList = Binarymap.listItemsi
val numItems = Binarymap.numItems
fun delete tk = #1 (Binarymap.remove tk)
(*val mapTable = Binarymap.transform*)
val mapTable = Binarymap.map
(*fun appTable f t = Binarymap.app (f o #2) t*)
val appTable = Binarymap.app

end
