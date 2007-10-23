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
	  | "pi_1" => Tokens.PROJLEFT(p,p)
	  | "pi_2" => Tokens.PROJRIGHT(p,p)
	  | "top" => Tokens.TOP(p,p)
	  | "T" => Tokens.TOP(p,p)
	  | "one" => Tokens.ONE(p,p)
	  (*| "1" => Tokens.ONE(p,p)*)
	  | "Exists" => Tokens.EXISTS(p,p)
	  | "let" => Tokens.LET(p,p)
	  | "in" => Tokens.IN(p,p)
	  | "#query" => Tokens.QUERY(p,p)
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
"@" => (Tokens.TENSOR(getpos yypos,getpos yypos));
\\"^" => (Tokens.LINLAMBDA(getpos yypos,getpos yypos));
\\ => (Tokens.LAMBDA(getpos yypos,getpos yypos));
"<>" => (Tokens.UNIT(getpos yypos,getpos yypos));
"<" => (Tokens.LANGLE(getpos yypos,getpos yypos));
">" => (Tokens.RANGLE(getpos yypos,getpos yypos));
"," => (Tokens.COMMA(getpos yypos,getpos yypos));
"^" => (Tokens.LINAPP(getpos yypos,getpos yypos));
"=" => (Tokens.EQUAL(getpos yypos,getpos yypos));
"[" => (Tokens.LBRACKET(getpos yypos,getpos yypos));
"]" => (Tokens.RBRACKET(getpos yypos,getpos yypos));
"(" => (Tokens.LPAREN(getpos yypos,getpos yypos));
")" => (Tokens.RPAREN(getpos yypos,getpos yypos));
"->" => (Tokens.ARROW(getpos yypos,getpos yypos));
"<-" => (Tokens.BACKARROW(getpos yypos,getpos yypos));
[0-9]+ => (number (yytext,getpos yypos));
[-a-zA-Z0-9<>=/_'*#+]+ => (keyword (yytext,getpos yypos));
. => (let val (l,c) = getpos(yypos) in
		print ("Lexer Warning: Ignoring illegal symbol ``"^yytext^"'' in line "^
					(Int.toString l)^" pos "^(Int.toString c)^"\n")
		end; lex());

