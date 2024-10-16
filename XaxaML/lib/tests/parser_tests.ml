(** Copyright 2024, aartdem, toadharvard *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

open XaxaML

let parse_and_print str =
  match Parser.run_parser str with
  | Result.Ok program -> Format.printf "%a\n" Ast.pp_program program
  | Result.Error str -> Format.printf "Parsing error: %s\n" str
;;

let%expect_test _ =
  parse_and_print {||};
  [%expect {| [(Expr (Expr_const (Const_int 1)))] |}]
;;
