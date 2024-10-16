(** Copyright 2024, aartdem, toadharvard *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

(** creates AST from the text of the program if program is correct or returns error message *)
val run_parser : string -> (Ast.program, string) result
