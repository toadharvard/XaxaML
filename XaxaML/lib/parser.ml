(** Copyright 2024, aartdem, toadharvard *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

(* open Angstrom *)
open Ast
open Angstrom

let const_int i = Const_int i
let const_bool b = Const_bool b
let expr_const c = Expr_const c
let expr_val v = Expr_val v
let expr_app f items = Expr_app (f, items)

let is_whitespace = function
  | ' ' | '\t' | '\n' | '\r' -> true
  | _ -> false
;;

let is_low_letter = function
  | 'a' .. 'z' -> true
  | _ -> false
;;

let is_up_letter = function
  | 'A' .. 'Z' -> true
  | _ -> false
;;

let is_letter c = is_low_letter c || is_up_letter c

let is_digit = function
  | '0' .. '9' -> true
  | _ -> false
;;

let is_keyword str =
  (* TODO: add types *)
  let keyword_list =
    [ "else"
    ; "false"
    ; "fun"
    ; "if"
    ; "in"
    ; "let"
    ; "match"
    ; "or"
    ; "rec"
    ; "then"
    ; "true"
    ; "with"
    ]
  in
  List.mem str keyword_list
;;

let take_whitespaces = take_while is_whitespace

let token =
  take_whitespaces *> take_while1 (fun c -> is_letter c || is_digit c || c = '_')
;;

let keyword s = token >>= fun res -> if res = s then return s else fail "keyword expected"
let left_bracket = take_whitespaces *> char '('
let right_bracket = take_whitespaces *> char ')'
let parenthesis p = left_bracket *> take_whitespaces *> p <* right_bracket

(* https://ocaml.org/manual/5.2/lex.html#sss:lex-ops-symbols *)
let is_core_operator_char c =
  let list = [ '$'; '&'; '*'; '+'; '-'; '/'; '='; '>'; '@'; '^'; '|' ] in
  List.mem c list
;;

let is_operator_char c =
  is_core_operator_char c || List.mem c [ '~'; '!'; '?'; '%'; '<'; ':'; '.' ]
;;

(* TODO *)
let is_infix_operator _ = true

(* TODO *)
let is_prefix_operator _ = true

let parse_operator ~starts_with =
  take_whitespaces *> choice (List.map string starts_with)
  >>= fun head ->
  take_while (fun c -> is_operator_char c || Char.equal c '#') >>| fun tail -> head ^ tail
;;

let unary_plus_or_minus =
  parse_operator ~starts_with:[ "+"; "-" ]
  >>= function
  | "+" -> return true
  | "-" -> return false
  | _ -> fail "not an unary plus or minus"
;;

let int_without_sign =
  token
  >>= fun s ->
  try int_of_string s |> return with
  | Failure _ -> fail "integer expected"
;;

let parse_int =
  fix (fun parser ->
    choice
      [ parenthesis parser
      ; (unary_plus_or_minus
         >>= fun sign -> if sign then parser else parser >>| fun number -> -number)
      ; int_without_sign
      ])
  >>| const_int
  >>| expr_const
;;

(*TODO: remove or change to tests that print*)
let%test "integer_test" =
  let expected = Result.Ok (expr_const @@ const_int 123) in
  let actual = parse_string ~consume:All parse_int " (+ - (+ -( +123) ))" in
  expected = actual
;;

let parse_bool =
  token
  >>= (function
         | "false" -> return @@ const_bool false
         | "true" -> return @@ const_bool true
         | _ -> fail "bool constant expected")
  >>| expr_const
;;

let parse_valname =
  token
  >>= fun s ->
  let c = s.[0] in
  if (not @@ is_keyword s) && s <> "_" && (is_low_letter c || c = '_')
  then return @@ expr_val s
  else fail "name of value expected"
;;

(* TODO: change c to start_with*)
let parse_bin_op atom c =
  fix (fun parser ->
    atom
    >>= (fun left ->
          string c *> parser >>| fun right -> expr_app (expr_val c) [ left; right ])
    <|> atom)
;;

let parse_expr =
  fix (fun parser ->
    let expr = choice [ parenthesis parser; parse_int; parse_bool; parse_valname ] in
    let expr = parse_bin_op expr "*" in
    parse_bin_op expr "+")
;;

(*TODO: remove or change to tests that print*)
let%test "binary_test" =
  let expected =
    Result.ok
      (Expr_app
         ( Expr_val "+"
         , [ Expr_const (Const_int 1)
           ; Expr_app
               (Expr_val "*", [ Expr_const (Const_int 2); Expr_const (Const_int 3) ])
           ] ))
  in
  let actual = parse_string ~consume:All parse_expr "1+2*3" in
  Format.printf "%a\n" Ast.pp_expr (Result.get_ok actual);
  expected = actual
;;

let parse_program = return [ Expr (Expr_const (Const_int 1)) ] (* TODO: remove mocking *)
let run_parser s = parse_string ~consume:All parse_program s
