(** Copyright 2025, tepa46, Arsene-Baitenov *)

(** SPDX-License-Identifier: LGPL-2.1-or-later *)

open Containers
open Std

let get_var_name_from_sid = function
  | Simple_ast.SId (Ast.Id var_name) -> Some var_name
  | Simple_ast.SSpecial SUnit -> None
;;

let get_var_names_from_sid_lst sid_lst =
  let rec helper acc = function
    | [] -> acc
    | h :: tl ->
      let var_name = get_var_name_from_sid h in
      let new_acc =
        match var_name with
        | None -> acc
        | Some var_name -> VarSSet.add var_name acc
      in
      helper new_acc tl
  in
  helper VarSSet.empty sid_lst
;;

let get_sid_lst_from_var_names_lst var_names_lst =
  let rev_id_lst_to_add =
    List.fold_left
      (fun acc new_var ->
        let new_id = Simple_ast.SId (Ast.Id new_var) in
        new_id :: acc)
      []
      var_names_lst
  in
  List.rev rev_id_lst_to_add
;;

let get_vars_from_expr expr env =
  let rec helper acc env = function
    | Simple_ast.SEConst _ -> acc
    | Simple_ast.SEVar (Id var_name) ->
      (match VarSSet.find_opt var_name env with
       | Some _ -> acc
       | None -> VarSSet.add var_name acc)
    | Simple_ast.SETuple exp_lst ->
      List.fold_left (fun acc exp -> helper acc env exp) acc exp_lst
    | Simple_ast.SEFun (id_lst, expr) ->
      let vars_from_id_lst = get_var_names_from_sid_lst id_lst in
      let new_env =
        VarSSet.fold (fun var_name acc -> VarSSet.add var_name acc) vars_from_id_lst env
      in
      helper acc new_env expr
    | Simple_ast.SELet (Ast.Nonrecursive, (ident, expr1), expr2) ->
      let var_name = get_var_name_from_sid ident in
      let new_acc = helper acc env expr1 in
      let new_env =
        match var_name with
        | None -> env
        | Some var_name -> VarSSet.add var_name env
      in
      helper new_acc new_env expr2
    | Simple_ast.SELet (Ast.Recursive, (ident, expr1), expr2) ->
      let var_name = get_var_name_from_sid ident in
      let new_env =
        match var_name with
        | None -> env
        | Some var_name -> VarSSet.add var_name env
      in
      let new_acc = helper acc new_env expr1 in
      helper new_acc new_env expr2
    | Simple_ast.SEApp (expr1, expr2) -> helper (helper acc env expr1) env expr2
    | Simple_ast.SEIf (expr1, expr2, expr3) ->
      helper (helper (helper acc env expr1) env expr2) env expr3
    | Simple_ast.SECons (expr1, expr2) -> helper (helper acc env expr1) env expr2
  in
  helper VarSSet.empty env expr
;;

let recursively_add_params start_expr var_name env =
  let rec helper start_expr var_name =
    match VarSMap.find_opt var_name env with
    | Some param_lst ->
      List.fold_left
        (fun exp param ->
          Simple_ast.SEApp (exp, helper (Simple_ast.SEVar (Ast.Id param)) param))
        start_expr
        param_lst
    | None -> start_expr
  in
  helper start_expr var_name
;;

let rec convert_fun_expr env global_env = function
  | Simple_ast.SEFun (id_lst, expr) as f ->
    let vars_from_id_lst = get_var_names_from_sid_lst id_lst in
    let updated_env =
      VarSSet.fold (fun new_var acc -> VarSMap.remove new_var acc) vars_from_id_lst env
    in
    let vars_to_add = VarSSet.elements (get_vars_from_expr f global_env) in
    let updated_env =
      List.fold_left
        (fun acc new_var -> VarSMap.remove new_var acc)
        updated_env
        vars_to_add
    in
    let updated_expr = convert_expr updated_env global_env expr in
    let id_lst_to_add = get_sid_lst_from_var_names_lst vars_to_add in
    let all_vars = List.append id_lst_to_add id_lst in
    vars_to_add, Simple_ast.SEFun (all_vars, updated_expr)
  | _ as expr -> [], expr

and convert_expr env global_env = function
  | Simple_ast.SEConst _ as const -> const
  | Simple_ast.SEVar (Ast.Id var_name) as s -> recursively_add_params s var_name env
  | Simple_ast.SETuple exp_lst ->
    let rev_new_exp_lst =
      List.fold_left
        (fun lst exp ->
          let new_exp = convert_expr env global_env exp in
          new_exp :: lst)
        []
        exp_lst
    in
    Simple_ast.SETuple (List.rev rev_new_exp_lst)
  | Simple_ast.SEFun _ as f ->
    let vars_to_add, new_efun = convert_fun_expr env global_env f in
    List.fold_left
      (fun acc var_to_add ->
        Simple_ast.SEApp
          ( acc
          , recursively_add_params (Simple_ast.SEVar (Ast.Id var_to_add)) var_to_add env
          ))
      new_efun
      vars_to_add
  | Simple_ast.SELet (Ast.Nonrecursive, (ident, expr1), expr2) ->
    (match expr1 with
     | Simple_ast.SEFun _ as f ->
       let vars_to_add, new_efun = convert_fun_expr env global_env f in
       let new_value_binding = ident, new_efun in
       let var_name = get_var_name_from_sid ident in
       let updated_env =
         match var_name with
         | None -> env
         | Some var_name -> VarSMap.add var_name vars_to_add env
       in
       let converted_expr2 = convert_expr updated_env global_env expr2 in
       Simple_ast.SELet (Ast.Nonrecursive, new_value_binding, converted_expr2)
     | _ ->
       Simple_ast.SELet
         ( Ast.Nonrecursive
         , (ident, convert_expr env global_env expr1)
         , convert_expr env global_env expr2 ))
  | Simple_ast.SELet (Ast.Recursive, (ident, expr1), expr2) ->
    let ident_var_name = get_var_name_from_sid ident in
    (match expr1 with
     | Simple_ast.SEFun (id_lst, fexpr) as f ->
       let vars_from_id_lst = get_var_names_from_sid_lst id_lst in
       let updated_env =
         VarSSet.fold (fun new_var acc -> VarSMap.remove new_var acc) vars_from_id_lst env
       in
       let vars_to_add = VarSSet.elements (get_vars_from_expr f global_env) in
       let vars_to_add =
         List.filter (fun var_name -> Some var_name <> ident_var_name) vars_to_add
       in
       let updated_env =
         List.fold_left
           (fun acc new_var -> VarSMap.remove new_var acc)
           updated_env
           vars_to_add
       in
       let updated_env =
         match ident_var_name with
         | None -> updated_env
         | Some ident_var_name -> VarSMap.add ident_var_name vars_to_add updated_env
       in
       let id_lst_to_add = get_sid_lst_from_var_names_lst vars_to_add in
       let all_vars = List.append id_lst_to_add id_lst in
       let converted_expr1 =
         Simple_ast.SEFun (all_vars, convert_expr updated_env global_env fexpr)
       in
       let converted_value_binding = ident, converted_expr1 in
       let updated_env =
         match ident_var_name with
         | None -> env
         | Some ident_var_name -> VarSMap.add ident_var_name vars_to_add env
       in
       let converted_expr2 = convert_expr updated_env global_env expr2 in
       Simple_ast.SELet (Ast.Recursive, converted_value_binding, converted_expr2)
     | _ ->
       let updated_env =
         match ident_var_name with
         | None -> env
         | Some ident_var_name -> VarSMap.remove ident_var_name env
       in
       let converted_expr1 = convert_expr updated_env global_env expr1 in
       let converted_expr2 = convert_expr updated_env global_env expr2 in
       Simple_ast.SELet (Ast.Nonrecursive, (ident, converted_expr1), converted_expr2))
  | Simple_ast.SEApp (expr1, expr2) ->
    let new_expr1 = convert_expr env global_env expr1 in
    let new_expr2 = convert_expr env global_env expr2 in
    Simple_ast.SEApp (new_expr1, new_expr2)
  | Simple_ast.SEIf (expr1, expr2, expr3) ->
    let new_expr1 = convert_expr env global_env expr1 in
    let new_expr2 = convert_expr env global_env expr2 in
    let new_expr3 = convert_expr env global_env expr3 in
    Simple_ast.SEIf (new_expr1, new_expr2, new_expr3)
  | Simple_ast.SECons (expr1, expr2) ->
    let new_expr1 = convert_expr env global_env expr1 in
    let new_expr2 = convert_expr env global_env expr2 in
    Simple_ast.SECons (new_expr1, new_expr2)
;;

let get_var_names_from_value_binding_lst value_binding_lst =
  List.fold_left
    (fun acc value_binding ->
      let sid, _ = value_binding in
      let opt_var_name = get_var_name_from_sid sid in
      match opt_var_name with
      | None -> acc
      | Some var_name -> var_name :: acc)
    []
    value_binding_lst
;;

let convert_value_binding_lst global_env value_binding_lst =
  let rev_value_binding_lst =
    List.fold_left
      (fun acc (id, expr) ->
        let new_expr = convert_expr VarSMap.empty global_env expr in
        (id, new_expr) :: acc)
      []
      value_binding_lst
  in
  List.rev rev_value_binding_lst
;;

let convert_rec_value_binding_lst global_env value_binding_lst =
  let rev_value_binding_lst =
    List.fold_left
      (fun acc (id, expr) ->
        match expr with
        | Simple_ast.SEFun (id_lst, fexpr) ->
          let updated_fexpr = convert_expr VarSMap.empty global_env fexpr in
          (id, Simple_ast.SEFun (id_lst, updated_fexpr)) :: acc
        | _ ->
          let new_expr = convert_expr VarSMap.empty global_env expr in
          (id, new_expr) :: acc)
      []
      value_binding_lst
  in
  List.rev rev_value_binding_lst
;;

let convert_structure_item global_env = function
  | Simple_ast.SSILet (Ast.Nonrecursive, value_binding_lst) ->
    let new_value_bindings = convert_value_binding_lst global_env value_binding_lst in
    Simple_ast.SSILet (Ast.Nonrecursive, new_value_bindings)
  | Simple_ast.SSILet (Ast.Recursive, value_binding_lst) ->
    let new_value_bindings = convert_rec_value_binding_lst global_env value_binding_lst in
    Simple_ast.SSILet (Ast.Recursive, new_value_bindings)
  | Simple_ast.SSIExpr expr ->
    let new_expr = convert_expr VarSMap.empty global_env expr in
    Simple_ast.SSIExpr new_expr
;;

let convert_structure global_env (structure : Simple_ast.sstructure) =
  let rev_new_structure, _ =
    List.fold_left
      (fun (new_structure, global_env) structure_item ->
        let new_structure_item = convert_structure_item global_env structure_item in
        let vars_from_structure_item =
          match structure_item with
          | Simple_ast.SSILet (_, value_binding_lst) ->
            get_var_names_from_value_binding_lst value_binding_lst
          | Simple_ast.SSIExpr _ -> []
        in
        let new_global_env =
          List.fold_left
            (fun acc new_var -> VarSSet.add new_var acc)
            global_env
            vars_from_structure_item
        in
        new_structure_item :: new_structure, new_global_env)
      ([], global_env)
      structure
  in
  List.rev rev_new_structure
;;

let run_closure_conversion (structure : Simple_ast.sstructure) =
  convert_structure extended_std_var_set structure
;;
