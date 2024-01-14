(*
Diego Suárez Ramos : diego.suarez.ramos@udc.es
Pablo Fernández Perez : pablo.fperez@udc.es   
*)
open Parsing;;
open Lexing;;

open Lambda;;
open Parser;;
open Lexer;;


let read_command ()=
  let delete_char s = String.map (fun c -> if (c = ';') then ' ' else c) s in
  let rec aux s=
    let s2 = (String.trim (read_line ())) in
    if (String.contains s2 ';') then
      (s^" "^(delete_char s2))
    else
      aux (s^" "^s2)
  in aux "" ;; 


let top_level_loop () =
  print_endline "Evaluator of lambda expressions...";
  let rec loop (defctx, typectx) =
    print_string ">> ";
    flush stdout;
    try
      let tm = s token (from_string (read_command ())) in
      loop (execute (defctx, typectx) tm)
    with
       Lexical_error ->
         print_endline "lexical error";
         loop (defctx, typectx)
     | Parse_error ->
         print_endline "syntax error";
         loop (defctx, typectx)
     | Type_error e ->
         print_endline ("type error: " ^ e);
         loop (defctx, typectx)
     | End_of_file ->
         print_endline "...bye!!!"
  in
    loop (emptyctx, emptyctx)
  ;;

top_level_loop ()
;;

