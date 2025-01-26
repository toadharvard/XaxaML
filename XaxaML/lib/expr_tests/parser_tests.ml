(** Copyright 2025, aartdem, toadharvard *)

(** SPDX-License-Identifier: LGPL-3.0-or-later *)

open XaxaML

(* Tests for parsing expressions *)

let parse_and_print str =
  match Parser.run_parser_expr str with
  | Result.Ok expr -> Format.printf "%a\n" Ast.pp_expr expr
  | Result.Error str -> Format.printf "Parsing error%s\n" str
;;

let%expect_test _ =
  parse_and_print {|let rec fac n = if n <= 1 then 1 else n * fac (n - 1) in fac|};
  [%expect
    {|
    (Expr_let (
       (true, (Pat_val (LCIdent "fac")),
        (Expr_fun ((Pat_val (LCIdent "n")), [],
           (Expr_ite (
              (Bin_op (Leq, (Expr_val (LCIdent "n")), (Expr_const (Int 1)))),
              (Expr_const (Int 1)),
              (Bin_op (Mul, (Expr_val (LCIdent "n")),
                 (Expr_app ((Expr_val (LCIdent "fac")),
                    (Bin_op (Sub, (Expr_val (LCIdent "n")), (Expr_const (Int 1))
                       ))
                    ))
                 ))
              ))
           ))),
       (Expr_val (LCIdent "fac")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let f = fun a b -> fun z -> a + b * z in f |};
  [%expect
    {|
    (Expr_let (
       (false, (Pat_val (LCIdent "f")),
        (Expr_fun ((Pat_val (LCIdent "a")), [(Pat_val (LCIdent "b"))],
           (Expr_fun ((Pat_val (LCIdent "z")), [],
              (Bin_op (Add, (Expr_val (LCIdent "a")),
                 (Bin_op (Mul, (Expr_val (LCIdent "b")), (Expr_val (LCIdent "z"))
                    ))
                 ))
              ))
           ))),
       (Expr_val (LCIdent "f")))) |}]
;;

let%expect_test _ =
  parse_and_print
    {|let f = if true then if true then a else b else if false then x else y in f|};
  [%expect
    {|
    (Expr_let (
       (false, (Pat_val (LCIdent "f")),
        (Expr_ite ((Expr_const (Bool true)),
           (Expr_ite ((Expr_const (Bool true)), (Expr_val (LCIdent "a")),
              (Expr_val (LCIdent "b")))),
           (Expr_ite ((Expr_const (Bool false)), (Expr_val (LCIdent "x")),
              (Expr_val (LCIdent "y"))))
           ))),
       (Expr_val (LCIdent "f")))) |}]
;;

let%expect_test _ =
  parse_and_print
    {|let a = let id x = x in let f = fun x -> if x > 0 then t else id b in f 1 in a|};
  [%expect
    {|
    (Expr_let (
       (false, (Pat_val (LCIdent "a")),
        (Expr_let (
           (false, (Pat_val (LCIdent "id")),
            (Expr_fun ((Pat_val (LCIdent "x")), [], (Expr_val (LCIdent "x"))))),
           (Expr_let (
              (false, (Pat_val (LCIdent "f")),
               (Expr_fun ((Pat_val (LCIdent "x")), [],
                  (Expr_ite (
                     (Bin_op (Gre, (Expr_val (LCIdent "x")), (Expr_const (Int 0))
                        )),
                     (Expr_val (LCIdent "t")),
                     (Expr_app ((Expr_val (LCIdent "id")),
                        (Expr_val (LCIdent "b"))))
                     ))
                  ))),
              (Expr_app ((Expr_val (LCIdent "f")), (Expr_const (Int 1))))))
           ))),
       (Expr_val (LCIdent "a")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let tuple1 = (1,x, 1+2 , (1, 2, 3)) in tuple1|};
  [%expect
    {|
    (Expr_let (
       (false, (Pat_val (LCIdent "tuple1")),
        (Expr_tuple ((Expr_const (Int 1)),
           [(Expr_val (LCIdent "x"));
             (Bin_op (Add, (Expr_const (Int 1)), (Expr_const (Int 2))));
             (Expr_tuple ((Expr_const (Int 1)),
                [(Expr_const (Int 2)); (Expr_const (Int 3))]))
             ]
           ))),
       (Expr_val (LCIdent "tuple1")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let a =5::4::[1; 2; 3] in a|};
  [%expect
    {|
      (Expr_let (
         (false, (Pat_val (LCIdent "a")),
          (Expr_cons_list ((Expr_const (Int 5)),
             (Expr_cons_list ((Expr_const (Int 4)),
                (Expr_cons_list ((Expr_const (Int 1)),
                   (Expr_cons_list ((Expr_const (Int 2)),
                      (Expr_cons_list ((Expr_const (Int 3)),
                         (Expr_const Const_empty_list)))
                      ))
                   ))
                ))
             ))),
         (Expr_val (LCIdent "a")))) |}]
;;

let%expect_test _ =
  parse_and_print
    {|let f x = match x with
      | h::tl -> let x = 1 in x
      | _ -> let id = fun x -> x in
         if (0 < 1) then 2 else id 3
      in f |};
  [%expect
    {|
    (Expr_let (
       (false, (Pat_val (LCIdent "f")),
        (Expr_fun ((Pat_val (LCIdent "x")), [],
           (Expr_match ((Expr_val (LCIdent "x")),
              [((Pat_cons_list ((Pat_val (LCIdent "h")), (Pat_val (LCIdent "tl"))
                   )),
                (Expr_let (
                   (false, (Pat_val (LCIdent "x")), (Expr_const (Int 1))),
                   (Expr_val (LCIdent "x")))));
                (Pat_any,
                 (Expr_let (
                    (false, (Pat_val (LCIdent "id")),
                     (Expr_fun ((Pat_val (LCIdent "x")), [],
                        (Expr_val (LCIdent "x"))))),
                    (Expr_ite (
                       (Bin_op (Less, (Expr_const (Int 0)), (Expr_const (Int 1))
                          )),
                       (Expr_const (Int 2)),
                       (Expr_app ((Expr_val (LCIdent "id")), (Expr_const (Int 3))
                          ))
                       ))
                    )))
                ]
              ))
           ))),
       (Expr_val (LCIdent "f")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let k (1, 2) = 3 in k|};
  [%expect
    {|
    (Expr_let (
       (false, (Pat_val (LCIdent "k")),
        (Expr_fun ((Pat_tuple ((Pat_const (Int 1)), [(Pat_const (Int 2))])),
           [], (Expr_const (Int 3))))),
       (Expr_val (LCIdent "k")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let f [] = 1 in f|};
  [%expect
    {|
  (Expr_let (
     (false, (Pat_val (LCIdent "f")),
      (Expr_fun ((Pat_const Const_empty_list), [], (Expr_const (Int 1))))),
     (Expr_val (LCIdent "f")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let f (h :: tl) = 1 in f|};
  [%expect
    {|
  (Expr_let (
     (false, (Pat_val (LCIdent "f")),
      (Expr_fun (
         (Pat_cons_list ((Pat_val (LCIdent "h")), (Pat_val (LCIdent "tl")))),
         [], (Expr_const (Int 1))))),
     (Expr_val (LCIdent "f")))) |}]
;;

let%expect_test _ =
  parse_and_print {|let x [] = 1 in x|};
  [%expect
    {|
  (Expr_let (
     (false, (Pat_val (LCIdent "x")),
      (Expr_fun ((Pat_const Const_empty_list), [], (Expr_const (Int 1))))),
     (Expr_val (LCIdent "x")))) |}]
;;
