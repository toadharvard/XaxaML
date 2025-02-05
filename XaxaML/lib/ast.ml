(** Copyright 2023, aartdem *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type const =
  | Int of int (** 1 *)
  | Bool of bool (** true *)
  | Const_empty_list (** [] *)
  | Const_unit (** () *)
[@@deriving show { with_path = false }]

type un_op =
  | Un_plus (** + *)
  | Un_minus (** - *)
[@@deriving show { with_path = false }]

type bin_op =
  | Add (** + *)
  | Sub (** - *)
  | Mul (** * *)
  | Div (** / *)
  | Eq (** = *)
  | Neq (** <> *)
  | Leq (** <= *)
  | Geq (** >= *)
  | Gre (**  > *)
  | Less (** < *)
  | And (** && *)
  | Or (** || *)
[@@deriving show { with_path = false }]

type val_name = LCIdent of string (** variable_name1 *)
[@@deriving show { with_path = false }]

type pattern =
  | Pat_any (** _ *)
  | Pat_val of val_name (** abc *)
  | Pat_const of const (** 1 *)
  | Pat_tuple of pattern * pattern list (** (1, 2) *)
  | Pat_cons_list of pattern * pattern (** 1::[] or [1;2] *)
[@@deriving show { with_path = false }]

type expr =
  | Expr_const of const (** 1 *)
  | Un_op of un_op * expr (** -1 *)
  | Bin_op of bin_op * expr * expr (** 2 + 2 *)
  | Expr_val of val_name (** val1 *)
  | Expr_ite of expr * expr * expr (** if a then b else c *)
  | Expr_fun of pattern * pattern list * expr (** fun x -> x + 1 *)
  | Expr_app of expr * expr (** f x *)
  | Expr_let of decl * expr (** let a = 1 in b *)
  | Expr_match of expr * (pattern * expr) list (** match x with | 1 -> 0 | _ -> 1 *)
  | Expr_cons_list of expr * expr (** 1::[] or [1;2] *)
  | Expr_tuple of expr * expr list (** (1, a) *)
[@@deriving show { with_path = false }]

and decl = bool * pattern * expr

type toplevel =
  | Let_decl of decl (** let a = 1 *)
  | Expr of expr (** printf "abc" *)
[@@deriving show { with_path = false }]

type program = toplevel list [@@deriving show { with_path = false }]
