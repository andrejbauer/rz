(** The lexical structure of theories *)

{
  open Parser

  let reserved =
    [
      "all", FORALL;
      "and", AND;
      "axiom", AXIOM;
      "begin", BEGIN;
      "bool", BOOL;
      "const", CONSTANT;
      "constant", CONSTANT;
      "corollary", COROLLARY;
      "end", END;
      "equiv", EQUIVALENCE;
      "equivalence", EQUIVALENCE;
      "exists", EXISTS;
      "exists1", UNIQUE;
      "some", EXISTS;
      "some1", UNIQUE;
      "false", FALSE;
      "forall", FORALL;
      "iff", IFF;
      "implicit", IMPLICIT;
      "implies", IMPLY;
      "in", IN;
      "lam", LAMBDA;
      "lemma", LEMMA;
      "let", LET;
      "match", MATCH;
      "model", MODEL;
      "not", NOT;
      "on", ON;
      "or", OR;
      "predicate", PREDICATE;
      "Prop", PROP;
      "proposition", PROPOSITION;
      "relation", RELATION;
      "rz", RZ;
      "set", SET;
      "stable", STABLE;
      "Stable", STABLEPROP;
      "structure", MODEL;
      "the", THE;
      "theorem", THEOREM;
      "theory", THEORY;
      "thy", THY ;
      "true", TRUE;
      "with", WITH
    ]

  let commentdepth = ref 0
  exception BadComment

  (* Characters (as length-1 strings) stored in reverse order,
     so we can more efficiently add them to the list as the
     comment is read. *)
  let current_comment : string list ref = ref []

  (* http://pllab.kaist.ac.kr/~shoh/ocaml/ocamllex-ocamlyacc/ocamlyacc-tutorial/ocamlyacc-tutorial.html *)
  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
}


let ident = ['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*

let tident = ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*

let symbolchar =
  ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']

rule token = parse
    '#' [^'\n']* '\n' { incr_linenum lexbuf; incr Message.lineno; token lexbuf }
  | '\n'            { incr_linenum lexbuf; incr Message.lineno; token lexbuf }
  | [' ' '\t' '\r']      { token lexbuf }
  | ['0'-'9']+      { match (int_of_string(Lexing.lexeme lexbuf)) with
			  0 -> ZERO
			| 1 -> ONE
			| 2 -> TWO
			| k -> INTEGER k
		    }
  | '='             { EQUAL }
  | '|'             { BAR }
  | "->"            { ARROW }
  | '`' ident       { let w = Lexing.lexeme lexbuf in
			LABEL (String.sub w 1 (String.length w - 1))
		    }

  | ':'             { COLON }
  | "::"            { PATHSEP }
  | ":>"            { SUBIN }
  | ":<"            { SUBOUT }
  | '.'             { PERIOD }
  | ','             { COMMA }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | '['             { LBRACK }
  | ']'             { RBRACK }
  | '{'             { LBRACE }
  | '}'             { RBRACE }
  | '+'             { PLUS }
  | '*'             { STAR }
  | '%'             { PERCENT }
  | "=>"            { IMPLY }
  | "<=>"           { IFF }
  | "&&"            { AND }
  | "||"            { OR }
  | ident           { let w = Lexing.lexeme lexbuf in
                        begin
                          try
                            List.assoc w reserved 
                          with Not_found -> NAME w
                        end
                    }
  | tident           { let w = Lexing.lexeme lexbuf in
                        begin
                          try
                            List.assoc w reserved 
                          with Not_found -> TNAME w
                        end
                    }
  | "!" symbolchar *
            { PREFIXOP(Lexing.lexeme lexbuf) }
  | ['~' '?'] symbolchar *
            { PREFIXOP(Lexing.lexeme lexbuf) }
  | ['=' '<' '>' '|' '&' '$'] symbolchar *
            { INFIXOP0(Lexing.lexeme lexbuf) }
  | ['@' '^'] symbolchar *
            { INFIXOP1(Lexing.lexeme lexbuf) }
  | ['+' '-'] symbolchar *
            { INFIXOP2(Lexing.lexeme lexbuf) }
  | "**" symbolchar *
            { INFIXOP4(Lexing.lexeme lexbuf) }
  | ['*' '/' '%'] symbolchar *
            { INFIXOP3(Lexing.lexeme lexbuf) }
  | "(*"    { commentdepth := 1;
	      current_comment := [];
              comment lexbuf }
  | "*)"    { print_string "ERROR:  too many close comments\n";
              raise BadComment}
  | eof             { EOF }

and comment = parse
    "*)"    { commentdepth := !commentdepth - 1;
              if (!commentdepth > 0) then comment lexbuf else 
		COMMENT ( String.concat "" (List.rev !current_comment)) }
  | "(*"    { commentdepth := !commentdepth + 1;
              comment lexbuf }
  | "\n"    { incr_linenum lexbuf; comment lexbuf }
  | _       { current_comment := (Lexing.lexeme lexbuf) :: !current_comment;
	      comment lexbuf }

(* trailer *)
{
}
