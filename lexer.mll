

{
  open Parser;;
  exception Lexical_error;;
}

rule token = parse
    [' ' '\t']  { token lexbuf }
  | "lambda"    { LAMBDA }
  | "L"         { LAMBDA }
  | "true"      { TRUE }
  | "false"     { FALSE }
  | "if"        { IF }
  | "then"      { THEN }
  | "else"      { ELSE }
  | "succ"      { SUCC }
  | "pred"      { PRED }
  | "iszero"    { ISZERO }
  | "let"       { LET }
  | "letrec"    { LETREC }
  | "in"        { IN }
  | "fix"       { FIX }
  | "concat"    { CONCAT }
  | "length"    { LENGTH }
  | "compare"   { COMPARE }
  | "Bool"      { BOOL }
  | "Nat"       { NAT }
  | "List"      { LIST }
  | "nil"       { NIL }
  | "cons"      { CONS }
  | "isnil"     { ISNIL }
  | "head"      { HEAD }
  | "tail"      { TAIL }
  | "String"    { STRING }
  | "as"        { AS }
  | "case"      { CASE }
  | "of"        { OF }
  | '('         { LPAREN }
  | ')'         { RPAREN }
  | '.'         { DOT }
  | '='         { EQ }
  | '{'         { LBRACE }
  | '}'         { RBRACE }
  | ':'         { COLON }
  | ','         { COMMA }
  | '['         { LBRACKET }
  | ']'         { RBRACKET }
  | '>'         { GT }
  | '<'         { LT }
  | "->"        { ARROW }
  | "|"         { OR }
  | ['0'-'9']+  { INTV (int_of_string (Lexing.lexeme lexbuf)) }
  | ['a'-'z']['a'-'z' '_' '0'-'9']*
                { IDV (Lexing.lexeme lexbuf) }
  | ['A'-'Z']['a'-'z' '_' '0'-'9']*
                { IDV2 (Lexing.lexeme lexbuf) }  
  | '"'[^ '"' ';' '\n']*'"'
                { let s = Lexing.lexeme lexbuf in
                 STRINGV (String.sub s 1 (String.length s - 2)) }
  | eof         { EOF }
  | _           { raise Lexical_error }

