open Xi_lib
open Ast
(* W Xi_lib.Types są definicje typów i środowiska typowego *)
open Types

module Make() = struct

  (* Logger: używa się go jak Format.printf *)
  let logf fmt = Logger.make_logf __MODULE__ fmt

  module Check () = struct

    (* Zgłaszaczka błędów *)
    module ErrorReporter = Typechecker_errors.MakeOneShotErrorReporter ()

    (* Hashtablica którą zwracamy jak wszystko jest OK.
     * Mapuje znacznik węzła na przypisany typ. Dzięki tej tablicy
     * późniejsze etapy kompilatora będą miały dostęp do policzonych
     * typów wyrażeń 
     * 
     * Jeżeli typowanie się powiedzie to zawartość tablicy wydrukuje się
     * do pliku xilog/004.typechecking.types
     *)
    let rec normal_of_type_expr = function
        | TEXPR_Int _ -> TP_Int
        | TEXPR_Bool _ -> TP_Bool
        | TEXPR_Array {sub; _} -> TP_Array (normal_of_type_expr sub) 
     
    let node2type_map = Hashtbl.create 513

    (* --------------------------------------------------- *)
    (* Funkcja nakładka na inferencję, jej zadanie to uzupełniać hashtablicę node2type_map *)
    let rec infer_expression env e =
      let tp = _infer_expression env e in
      Hashtbl.replace node2type_map (tag_of_expression e) tp;
      logf "%s: inferred type %s"
        (string_of_location
        (location_of_expression e))
        (string_of_normal_type tp);
      tp

    (* --------------------------------------------------- *)
    (* Oddolna strategia *)
    and _infer_expression env = function
      | EXPR_Id {id; loc; tag} -> 
        begin match TypingEnvironment.lookup id env with
        | Some (ENVTP_Var tp) -> tp
        | _ -> ErrorReporter.report_identifier_is_not_variable
              ~loc:loc
              ~id:id
        end


      | EXPR_Int _ ->
        TP_Int

      | EXPR_Char _ ->
        TP_Int

      | EXPR_Bool _ ->
        TP_Bool

      (*{1, 2, 3}[1 + 0]*)
      | EXPR_Index {expr;index;loc; _} ->
        begin match infer_expression env expr with
        | TP_Array tp ->
           check_expression env TP_Int index;
           tp
        | tp -> ErrorReporter.report_expected_array
                 ~loc:loc
                 ~actual: tp
        end

      | EXPR_Call call ->
        begin match check_function_call env call with
        | ret_tp::[] -> ret_tp
        | _ -> ErrorReporter.report_expected_function_returning_one_value 
                ~loc: (location_of_call call)
                ~id: (identifier_of_call call)
        end

      | EXPR_Length {arg;loc;_} ->
        begin match infer_expression env arg with
        | (TP_Array _) -> TP_Int
        | _ ->
          let descr = "operator 'length' expects array" in
         ErrorReporter.report_other_error ~loc ~descr
        end

(* ___________________________ <, >, <=, >= _________________________________*)

      | EXPR_Relation {lhs; rhs; op=RELOP_Ge; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Bool
          | _ -> let descr = "operator >= expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end 

      | EXPR_Relation {lhs; rhs; op=RELOP_Gt; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Bool
          | _ -> let descr = "operator > expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end


      | EXPR_Relation {lhs; rhs; op=RELOP_Lt; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Bool
          | _ -> let descr = "operator < expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end


      | EXPR_Relation {lhs; rhs; op=RELOP_Le; loc; _}  ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Bool
          | _ -> let descr = "operator <= expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end
(* ____________________________==, !, + ___________________________________   *)


      | EXPR_Relation {lhs; rhs; op=RELOP_Eq; loc; _} ->
	    let tp = infer_expression env lhs in check_expression env tp rhs;
        TP_Bool

 
      | EXPR_Relation {lhs; rhs; op=RELOP_Ne; loc; _} ->
        let tp = infer_expression env lhs in check_expression env tp rhs;
        TP_Bool


        (* Reguła dla dodawania, jak w treści zadania *)
      | EXPR_Binop {loc; lhs; rhs; op=BINOP_Add; _} ->
        begin match infer_expression env lhs with
        | (TP_Array _) as tp
        | (TP_Int as tp) ->
          check_expression env tp rhs;
          tp
        | _ ->
          let descr = "operator + expects integer or array" in
         ErrorReporter.report_other_error ~loc ~descr
        end
(*________________________________ &, | ________________________________*)

      | EXPR_Binop {lhs; rhs; op=BINOP_And; loc;_}  ->
        begin match infer_expression env lhs with
          | TP_Bool as tp -> 
            check_expression env tp rhs;
            TP_Bool
          | _ -> let descr = "operator & expects booleans as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end
 
      | EXPR_Binop {lhs; rhs; op=BINOP_Or; loc;_}  ->
        begin match infer_expression env lhs with
          | TP_Bool as tp -> 
            check_expression env tp rhs;
            TP_Bool
          | _ -> let descr = "operator | expects booleans as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end
(*_____________________________ -, *, /, % _______________________________________*)

      | EXPR_Binop {lhs; rhs; op=BINOP_Sub; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Int
          | _ -> let descr = "operator - expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end 
 
      | EXPR_Binop {lhs; rhs; op=BINOP_Rem; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Int
          | _ -> let descr = "operator % expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end  


      | EXPR_Binop {lhs; rhs; op=BINOP_Mult; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Int
          | _ -> let descr = "operator * expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end 
  
      | EXPR_Binop {lhs; rhs; op=BINOP_Div; loc; _} ->
        begin match infer_expression env lhs with
          | TP_Int as tp -> 
            check_expression env tp rhs;
            TP_Int
          | _ -> let descr = "operator / expects integers as arguments" in
                    ErrorReporter.report_other_error ~loc ~descr
        end 
 
(*_________________________-, ! ______________________________________________*)

      | EXPR_Unop {op=UNOP_Neg; sub; loc; _} -> 
        begin match infer_expression env sub with
        (*check_expression env TP_Int sub*)
        | TP_Int as tp -> tp
        | _ -> let descr = "int expression expected" in
                    ErrorReporter.report_other_error 
                        ~loc
                        ~descr
        end

      | EXPR_Unop {op=UNOP_Not; sub; loc; _} ->
        begin match infer_expression env sub with
        | TP_Bool as tp -> tp
        | _ -> let descr = "bool expression expected" in
                    ErrorReporter.report_other_error 
                        ~loc 
                        ~descr
        end
(*_____________________________________________________________________*)


      | EXPR_String _ -> TP_Array TP_Int

      | EXPR_Struct {elements=[]; loc; _} ->
        ErrorReporter.report_cannot_infer ~loc

      | EXPR_Struct {elements=x::xs; _} ->
        let tp = infer_expression env x in List.iter (check_expression env tp) xs;
        TP_Array tp

    and check_function_call env (Call {loc; callee; arguments; _}) = 
      let check_ret_types (expr, tp) = check_expression env tp expr in
        begin match TypingEnvironment.lookup callee env with
          | Some ENVTP_Fn (arg_tp, ret_tp) -> begin try
              List.combine arguments arg_tp |> List.iter check_ret_types;
              ret_tp
              with Invalid_argument _ -> 
                  ErrorReporter.report_bad_number_of_arguments 
                  ~loc 
                  ~expected: (List.length arg_tp) 
                  ~actual: (List.length arguments)
              end
          | _ -> ErrorReporter.report_identifier_is_not_callable 
                  ~loc 
                  ~id: callee
        end

              

    (* --------------------------------------------------- *)
    (* Odgórna strategia: zapish (zapish? xd) w node2type_map oczekiwanie a następnie
     * sprawdź czy nie zachodzi specjalny przypadek. *)
    and check_expression env expected e =
      logf "%s: checking expression against %s"
        (string_of_location (location_of_expression e))
        (string_of_normal_type expected);
      Hashtbl.replace node2type_map (tag_of_expression e) expected;

      (* Sprawdzamy specjalne przypadki *)
      match e, expected with
          (* Mamy sprawdzić `{elements...}` kontra `tp[]`, czyli sprawdzamy 
          * elementy kontra typ elementu tablicy `tp` *)
      | EXPR_Struct {elements; _}, TP_Array tp ->
        List.iter (check_expression env tp) elements

      (* ========== !! Zaimplementuj pozostale przypadki !! =========  *)

      (* Fallback do strategii oddolnej *)
      | _ ->
        let actual = infer_expression env e in
        if actual <> expected then
          ErrorReporter.report_type_mismatch
            ~loc:(location_of_expression e)
            ~actual
            ~expected

    (* --------------------------------------------------- *)
    (* Pomocnicza funkcja do sprawdzania wywołania procedury *)

    let check_procedure_call env call : unit = 
      match check_function_call env call with
      | [] -> ()
      | _ -> ErrorReporter.report_procedure_cannot_return_value
             ~loc: (location_of_call call)
      
      

    (* --------------------------------------------------- *)
    (* Rekonstrukcja typu dla lvalue *)

    let infer_lvalue env = function
      | LVALUE_Id {id;loc;_} -> 
        begin match TypingEnvironment.lookup_unsafe id env with
        | ENVTP_Var tp -> tp
        | _ -> ErrorReporter.report_identifier_is_not_variable
               ~loc 
               ~id
        end
        
      | LVALUE_Index {index; sub; loc} ->
        check_expression env TP_Int index;
        infer_expression env sub


    let check_var_declaration env tp var =   
        let tp' = normal_of_type_expr (type_expression_of_var_declaration var) in
          if tp' = tp then 
              begin match TypingEnvironment.add 
                  (identifier_of_var_declaration var) 
                  (ENVTP_Var tp') env
              with
                | (env', true) -> env'
                | _ -> ErrorReporter.report_shadows_previous_definition
                      ~loc: (location_of_var_declaration var)
                      ~id: (identifier_of_var_declaration var)
              end
          else ErrorReporter.report_type_mismatch 
               ~loc: (location_of_var_declaration var)
               ~expected: tp 
               ~actual: tp'
    
    (* --------------------------------------------------- *)
    (* Sprawdzanie statementów *)

    let rec check_statement env = function
      (* Proste, wyinferuj typ `lhs` i sprawdź `rhs` kontra wynik *)
      | STMT_Assign {lhs; rhs; _} ->
        let lhs_tp = infer_lvalue env lhs in
        check_expression env lhs_tp rhs;
        env, RT_Unit

      | STMT_MultiVarDecl {vars; init; loc; _} ->
        let check_var_decl_opt env = function
          | None, _ -> env
          | Some var_decl, tp -> check_var_declaration env tp var_decl
        and ret_tp_list = check_function_call env init in
        let new_env = begin try 
          List.combine vars ret_tp_list |> List.fold_left check_var_decl_opt env
          with Invalid_argument _ -> 
            ErrorReporter.report_bad_number_of_return_values
                  ~loc
                  ~expected: (List.length vars) 
                  ~actual: (List.length ret_tp_list) 
          end in (new_env, RT_Unit)
          
        

      | STMT_Block body ->
        check_statement_block env body

      | STMT_Call call ->
        check_procedure_call env call;
        env, RT_Unit

      | STMT_If {cond; then_branch; else_branch; _} ->
        check_expression env TP_Bool cond;
        begin match else_branch with
        | Some else_st -> 
          let (_, tp) = check_statement env then_branch in 
             begin match tp with 
             | RT_Unit-> (env, tp)
             | RT_Void -> let (_, tp') = check_statement env else_st in (env, tp')
             end
        | None -> let _ = check_statement env then_branch in 
                  (env, RT_Unit)
        end

      | STMT_Return {values;loc} ->
        let check_ret_types (expr, tp) = check_expression env tp expr in
           begin match TypingEnvironment.get_return env with
            | None -> failwith "TypingEnvironment.get_return internal error"
            | Some ext_tp -> begin try
              List.combine values ext_tp |> List.iter check_ret_types;
              (env, RT_Void) with Invalid_argument _ -> 
                ErrorReporter.report_bad_number_of_return_values
                ~loc
                ~expected: (List.length ext_tp) 
                ~actual: (List.length values)                                 
             end
           end

      | STMT_VarDecl {var; init} ->
        let tp = normal_of_type_expr (type_expression_of_var_declaration var) in
          begin match TypingEnvironment.add (identifier_of_var_declaration var) (ENVTP_Var tp) env
          with
            | (env', true) -> begin match init with
                | Some expr -> 
                    check_expression env' tp expr;
                    (env', RT_Unit)
                | None -> (env', RT_Unit)
                end
            | _ -> ErrorReporter.report_shadows_previous_definition
                  ~loc: (location_of_var_declaration var)
                  ~id: (identifier_of_var_declaration var)
          end

      | STMT_While {cond; body; _} ->
        check_expression env TP_Bool cond;
        let _ = check_statement env body in (env, RT_Unit)

    and check_statement_block env (STMTBlock {body; loc; _}) = 
      begin match body with 
      | [] -> (env, RT_Unit)
      | _ ->
        let aux (env, prev_ret_tp) st = begin match prev_ret_tp with
          | RT_Unit -> check_statement env st
          | RT_Void -> ErrorReporter.report_other_error
                        ~loc: (location_of_statement st)
                        ~descr: "Unreachable statement"
          end
        in List.fold_left aux (env, RT_Unit) body 
      end

    
    let rec normal_of_var_declaration = function
        | VarDecl {tp; _} -> normal_of_type_expr tp

    let rec normal_of_var_declarations = function
        | [] -> []
        | (VarDecl {tp; _})::t -> (normal_of_type_expr tp)::(normal_of_var_declarations t)

    let rec normal_of_type_expressions = function
        | [] -> []
        | h::t -> (normal_of_type_expr h)::(normal_of_type_expressions t)
    (*List.map normal_of_type_expr xs *)

    let add_arg_to_env env var_decl = begin match 
        TypingEnvironment.add (identifier_of_var_declaration var_decl) 
          (ENVTP_Var (normal_of_var_declaration var_decl)) env 
          with 
          | (env, true) -> env
          | _ -> ErrorReporter.report_shadows_previous_definition
                  ~loc: (location_of_var_declaration var_decl)
                  ~id: (identifier_of_var_declaration var_decl)
      end
      
    (* --------------------------------------------------- *)
    (* Top-level funkcje *)

    let check_global_declaration env = function
      | GDECL_Function {formal_parameters; return_types; body; loc; id; _} ->
        let env' = List.fold_left add_arg_to_env (TypingEnvironment.set_return env (normal_of_type_expressions return_types)) formal_parameters in
          begin match body with
            | Some st_block -> 
              begin match check_statement_block env' st_block with
                | _, RT_Void -> ()
                | _ -> ErrorReporter.report_function_must_return_something 
                        ~loc
              end
            | None -> ()
          end

    let scan_global_declaration env = function
      | GDECL_Function {id; formal_parameters; return_types; loc; _} ->
        (* Dodaj idenetyfkator funkcji i jej typ do środowiska *)
        begin match 
            TypingEnvironment.add id (ENVTP_Fn (
            (normal_of_var_declarations formal_parameters), 
            (normal_of_type_expressions return_types)))
            env
        with
            | (env, true) -> env
            | _ -> ErrorReporter.report_shadows_previous_definition
                    ~loc:loc 
                    ~id:id
        end


    let scan_module env (ModuleDefinition {global_declarations; _}) =
      List.fold_left scan_global_declaration env global_declarations

    let check_module env (ModuleDefinition {global_declarations; _}) =
      List.iter (check_global_declaration env) global_declarations

    (* --------------------------------------------------- *)
    (* Przetwórz moduł *)
    let process_module env mdef =
      (* Najpierw przeskanuj globalne definicje aby uzupełnić środowisko *)
      let env = scan_module env mdef in
      (* Zweryfikuj wszystko *)
      check_module env mdef

    let computation mdef = 
      (* Zaczynamy z pustym środowiskiem *)
      let env = TypingEnvironment.empty in
      process_module env mdef;
      node2type_map
  end

  (* --------------------------------------------------- *)
  (* Procedura wejściowa *)
  let check_module mdef =
    (* Stwórz instancję typecheckera i ją odpal *)
    let module M = Check() in
    M.ErrorReporter.wrap M.computation mdef 

end
