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

type pos = int * int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token
val linepos = ref 1
val linecharpos = ref 0
fun getpos charcount = (!linepos,charcount - !linecharpos)
fun eof () = Tokens.EOF((!linepos,0),(!linepos,0))
fun number (s,p) =
	if s = "1" then Tokens.ONE(p,p)
	else Tokens.NUM(
			case Int.fromString s of
				  SOME n => n
				| NONE => raise Fail"Internal error: lexer on int\n",
			p,p)
fun keyword (s,p) =
	(case s of
		"type" => Tokens.TYPE(p,p)
	  | "Pi" => Tokens.PI(p,p)
	  | "PI" => Tokens.LPI(p,p)
	  | "#1" => Tokens.PROJLEFT(p,p)
	  | "#2" => Tokens.PROJRIGHT(p,p)
	  | "Exists" => Tokens.EXISTS(p,p)
	  | "EXISTS" => Tokens.LEXISTS(p,p)
	  | "let" => Tokens.LET(p,p)
	  | "in" => Tokens.IN(p,p)
	  | "#query" => Tokens.QUERY(p,p)
	  | "#mode" => Tokens.MODE(p,p)
	  | _ => Tokens.ID(s,p,p))

%%
%header (functor ClfLexFun(structure Tokens: Clf_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t];
%%
\n => (linepos := (!linepos) + 1; linecharpos := yypos; lex());
{ws}+ => (lex());
"%"[^\n]* => (lex());
"-o" => (Tokens.LOLLI(getpos yypos,getpos yypos));
"o-" => (Tokens.BACKLOLLI(getpos yypos,getpos yypos));
":" => (Tokens.COLON(getpos yypos,getpos yypos));
"." => (Tokens.DOT(getpos yypos,getpos yypos));
"_" => (Tokens.UNDERSCORE(getpos yypos,getpos yypos));
"&" => (Tokens.AMPH(getpos yypos,getpos yypos));
"{" => (Tokens.LCURLY(getpos yypos,getpos yypos));
"}" => (Tokens.RCURLY(getpos yypos,getpos yypos));
"*" => (Tokens.TENSOR(getpos yypos,getpos yypos));
\\ => (Tokens.LAMBDA(getpos yypos,getpos yypos));
"<" => (Tokens.LANGLE(getpos yypos,getpos yypos));
">" => (Tokens.RANGLE(getpos yypos,getpos yypos));
"," => (Tokens.COMMA(getpos yypos,getpos yypos));
"=" => (Tokens.EQUAL(getpos yypos,getpos yypos));
"[" => (Tokens.LBRACKET(getpos yypos,getpos yypos));
"]" => (Tokens.RBRACKET(getpos yypos,getpos yypos));
"(" => (Tokens.LPAREN(getpos yypos,getpos yypos));
")" => (Tokens.RPAREN(getpos yypos,getpos yypos));
"->" => (Tokens.ARROW(getpos yypos,getpos yypos));
"<-" => (Tokens.BACKARROW(getpos yypos,getpos yypos));
"@" => (Tokens.AFF(getpos yypos,getpos yypos));
"!" => (Tokens.BANG(getpos yypos,getpos yypos));
"-@" => (Tokens.AFFLOLLI(getpos yypos,getpos yypos));
"@-" => (Tokens.BACKAFFLOLLI(getpos yypos,getpos yypos));
"+" => (Tokens.PLUS(getpos yypos,getpos yypos));
"-" => (Tokens.MINUS(getpos yypos,getpos yypos));
[0-9]+ => (number (yytext,getpos yypos));
[-a-zA-Z0-9<>=/|_'*#+&~;$?]+ => (keyword (yytext,getpos yypos));
. => (let val (l,c) = getpos(yypos) in
		print ("Lexer Warning: Ignoring illegal symbol ``"^yytext^"'' in line "^
					(Int.toString l)^" pos "^(Int.toString c)^"\n")
		end; lex());

