(** The lexical structure of theories *)

{
  open Parser

  let reserved =
    [
      "Axiom", AXIOM;
      "Definition", DEFINITION;
      "empty", EMPTY;
      "Empty", EMPTY;
      "end", END;
      "End", END;
      "Equiv", EQUIV;
      "exists", EXISTS;
      "exists1", UNIQUE;
      "False", FALSE;
      "forall", FORALL;
      "fun", FUN;
      "Hypothesis", HYPOTHESIS;
      "Implicit", IMPLICIT;
      "in", IN;
      "include", INCLUDE;
      "let", LET;
      "match", MATCH;
      "model", MODEL;
      "Module", MODULE;
      "not", NOT;
      "Parameter", PARAMETER;
      "Prop", PROP;
      "Require", REQUIRE;
      "rz", RZ;
      "Set", SET;
      "Stable", STABLE;
      "the", THE;
      "theory", THEORY;
      "thy", THY ;
      "Thy", THY ;
      "True", TRUE;
      "tt", EMPTYTUPLE;
      "Type", TYPE;
      "unit", UNIT;
      "with", WITH;
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

  (* Remove the first character from a string *)
  let trim w = 
    String.sub w 1 (String.length w - 1)
}


(*
let ident = ['a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*
let tident = ['A'-'Z']['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*
*)

let ident = ['A'-'Z' 'a'-'z' '_']['a'-'z' 'A'-'Z' '0'-'9' '_']* '\''*

let symbolchar =
  ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' '?' '@' '^' '|' '~']
  
let prefixop = ['~' '?' '!']             symbolchar*
let infixop0 = ['=' '<' '>' '|' '&' '$'] symbolchar*
let infixop1 = ['@' '^']                 symbolchar*
let infixop2 = ['+' '-']                 symbolchar*
let infixop4 = "**"                      symbolchar*
let infixop3 = ['*' '/' '%']             symbolchar*

rule token = parse
    '#' [^'\n']* '\n'? { incr_linenum lexbuf; incr Message.lineno; token lexbuf }
  | '\n'            { incr_linenum lexbuf; incr Message.lineno; token lexbuf }
  | [' ' '\t' '\r']      { token lexbuf }
  | '='             { EQUAL }
  | ":="            { COLONEQUAL }
  | '|'             { BAR }
  | "->"            { ARROW }
  | '`' ident       { LABEL (trim (Lexing.lexeme lexbuf)) }
  | '.' ['0'-'9']+  { PROJECT (int_of_string (trim (Lexing.lexeme lexbuf))) }
  | '.' ident       { MPROJECT (trim (Lexing.lexeme lexbuf)) }
  | '.' prefixop    { MPROJECTP (trim (Lexing.lexeme lexbuf)) }
  | '.' infixop0    { MPROJECT0 (trim (Lexing.lexeme lexbuf)) }
  | '.' infixop1    { MPROJECT1 (trim (Lexing.lexeme lexbuf)) }
  | '.' infixop2    { MPROJECT2 (trim (Lexing.lexeme lexbuf)) }
  | '.' infixop3    { MPROJECT3 (trim (Lexing.lexeme lexbuf)) }
  | '.' infixop4    { MPROJECT4 (trim (Lexing.lexeme lexbuf)) }
  | '.' '('         { PERIOD_LPAREN }
  | '.'             { PERIOD }
  | ':'             { COLON }
  | ":>"            { SUBIN }
  | ":<"            { SUBOUT }
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
  | "=>"            { DOUBLEARROW }
  | "<->"           { IFFSYMBOL }
  | "/\\"           { ANDSYMBOL }
  | "\\/"           { ORSYMBOL }
  | ident           { let w = Lexing.lexeme lexbuf in
                        begin
                          try
                            List.assoc w reserved 
                          with Not_found -> NAME w
                        end
                    }
  | prefixop
            { PREFIXOP(Lexing.lexeme lexbuf) }
  | infixop0
            { INFIXOP0(Lexing.lexeme lexbuf) }
  | infixop1
            { INFIXOP1(Lexing.lexeme lexbuf) }
  | infixop2
            { INFIXOP2(Lexing.lexeme lexbuf) }
  | infixop4 (* Comes before infixop3 because ** matches the infixop3 pattern too *)
            { INFIXOP4(Lexing.lexeme lexbuf) }
  | infixop3
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
  | "\n"    { current_comment := (Lexing.lexeme lexbuf) :: !current_comment;
	      incr_linenum lexbuf; comment lexbuf }
  | _       { current_comment := (Lexing.lexeme lexbuf) :: !current_comment;
	      comment lexbuf }

(* trailer *)
{
}
