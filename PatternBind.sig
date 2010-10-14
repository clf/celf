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

signature PATTERNBIND =
sig

val tpatBind : Syntax.tpattern * Syntax.syncType -> Syntax.asyncType Context.context
		-> Syntax.asyncType Context.context
val opatBind : Syntax.opattern * Syntax.syncType -> Syntax.asyncType Context.context
		-> Syntax.asyncType Context.context
val tpatBindApx : Syntax.tpattern * Syntax.apxSyncType -> Syntax.apxAsyncType Context.context
		-> Syntax.apxAsyncType Context.context
val opatBindApx : Syntax.opattern * Syntax.apxSyncType -> Syntax.apxAsyncType Context.context
		-> Syntax.apxAsyncType Context.context
val tpatBindNf : Syntax.tpattern * Syntax.nfSyncType -> Syntax.nfAsyncType Context.context
		-> Syntax.nfAsyncType Context.context
val opatBindNf : Syntax.opattern * Syntax.nfSyncType -> Syntax.nfAsyncType Context.context
		-> Syntax.nfAsyncType Context.context
val depPatBind : {dep : Syntax.asyncType -> 'a, nodep : Syntax.asyncType -> 'a}
		-> Syntax.tpattern * Syntax.syncType -> 'a Context.context -> 'a Context.context
val patUnbind : Syntax.opattern * 'a Context.context -> 'a Context.context

end
