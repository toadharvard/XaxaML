(** Copyright 2025, aartdem, toadharvard *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

type typ =
  | TVar of int (** type var *)
  | TPrim of string (** ground type *)
  | TArr of typ * typ (** function type *)
  | TUnit (** unit *)
  | TTuple of typ * typ list (** tuple type *)
  | TList of typ (** list type *)

module TypeVarSet = Stdlib.Set.Make (Int)

type scheme = Scheme of TypeVarSet.t * typ

let type_var x = TVar x
let int_typ = TPrim "int"
let bool_typ = TPrim "bool"
let unit_typ = TUnit
let arrow l r = TArr (l, r)
let ( @-> ) = arrow
