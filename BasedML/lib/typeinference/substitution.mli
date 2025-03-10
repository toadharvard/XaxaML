(** Copyright 2024-2025, Pavel Averin, Alexey Efremov *)

(** SPDX-License-Identifier: LGPL-2.1 *)

type ('st, 'a) t = 'st -> 'st * ('a, string) result

val return : 'a -> 'b -> 'b * ('a, 'c) result
val fail : 'a -> 'b -> 'b * ('c, 'a) result
val ( >>= ) : ('s, 'a) t -> ('a -> ('s, 'b) t) -> ('s, 'b) t
val read : ('st, 'st) t
val write : 'st -> ('st, unit) t
val run : ('st, 'a) t -> 'st -> 'st * ('a, string) result
val ( let* ) : ('a, 'b) t -> ('b -> ('a, 'c) t) -> ('a, 'c) t
val ( *> ) : ('a, 'b) t -> ('a, 'c) t -> ('a, 'c) t
val ( >>| ) : ('a, 'b) t -> ('b -> 'c) -> ('a, 'c) t
val ( <* ) : ('a, 'b) t -> ('a, 'c) t -> ('a, 'b) t
val map_list : ('a -> ('st, 'b) t) -> 'a list -> ('st, 'b list) t

type substitution_list = (string * Ast.type_name) list

val pp_substitution_list : Format.formatter -> substitution_list -> unit
val show_substitution_list : substitution_list -> string
val apply_subst : string * Ast.type_name -> Ast.type_name -> Ast.type_name
val apply_substs : (string * Ast.type_name) list -> Ast.type_name -> Ast.type_name
val unify : Ast.type_name -> Ast.type_name -> (substitution_list, Ast.type_name) t
val insert_subst : string * Ast.type_name -> (substitution_list, Ast.type_name) t
