  $ ./run_parser.exe << EOF
  > let a =  10/( 2+(+ +5) )*( 7 + - 1) - ( 1 + 2*  3 )
  [(Let_decl
      (false, (Pat_val (LCIdent "a")),
       (Bin_op (Sub,
          (Bin_op (Mul,
             (Bin_op (Div, (Expr_const (Int 10)),
                (Bin_op (Add, (Expr_const (Int 2)),
                   (Un_op (Un_plus, (Un_op (Un_plus, (Expr_const (Int 5))))))))
                )),
             (Bin_op (Add, (Expr_const (Int 7)),
                (Un_op (Un_minus, (Expr_const (Int 1))))))
             )),
          (Bin_op (Add, (Expr_const (Int 1)),
             (Bin_op (Mul, (Expr_const (Int 2)), (Expr_const (Int 3))))))
          ))))
    ]
  $ ./run_parser.exe << EOF
  Parsing error: no more choices
