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
        check_function_call env call

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
(* _______________________________________________________________   *)


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
 
(*________________________________________________________________________*)

      | EXPR_Unop {op=UNOP_Neg; sub; _} ->
        failwith "not yet implemented"

      | EXPR_Unop {op=UNOP_Not; sub; _} ->
        failwith "not yet implemented"

      | EXPR_String _ ->
        failwith "not yet implemented"

      | EXPR_Struct {elements=[]; loc; _} ->
        ErrorReporter.report_cannot_infer ~loc

      | EXPR_Struct {elements=x::xs; _} ->
        failwith "not yet implemented"

    and check_function_call env call = 
      failwith "not yet implemented"

    (* --------------------------------------------------- *)
    (* Odgórna strategia: zapish w node2type_map oczekiwanie a następnie
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
      failwith "not yet implemented"

    (* --------------------------------------------------- *)
    (* Rekonstrukcja typu dla lvalue *)

    let infer_lvalue env = function
      | LVALUE_Id {id;loc;_} -> 
        failwith "not yet implemented"

      | LVALUE_Index {index; sub; loc} ->
        failwith "not yet implemented"


    (* --------------------------------------------------- *)
    (* Sprawdzanie statementów *)

    let rec check_statement env = function
      (* Proste, wyinferuj typ `lhs` i sprawdź `rhs` kontra wynik *)
      | STMT_Assign {lhs; rhs; _} ->
        let lhs_tp = infer_lvalue env lhs in
        check_expression env lhs_tp rhs;
        env, RT_Unit

      | STMT_MultiVarDecl {vars; init; _} ->
        failwith "not yet implemented"

      | STMT_Block body ->
        check_statement_block env body

      | STMT_Call call ->
        check_procedure_call env call;
        env, RT_Unit

      | STMT_If {cond;then_branch;else_branch; _} ->
        failwith "not yet implemented"

      | STMT_Return {values;loc} ->
        failwith "not yet implemented"

      | STMT_VarDecl {var; init} ->
        failwith "not yet implemented"

      | STMT_While {cond; body; _} ->
        failwith "not yet implemented"

    and check_statement_block env (STMTBlock {body; _}) =
        failwith "not yet implemented"

    (* --------------------------------------------------- *)
    (* Top-level funkcje *)

    let check_global_declaration env = function
      | GDECL_Function {formal_parameters; return_types; body; loc; id; _} ->
        (* Sprawdź wszystko *)
        failwith "not yet implemented"

    let scan_global_declaration env = function
      | GDECL_Function {id; formal_parameters; return_types; loc; _} ->
        (* Dodaj idenetyfkator funkcji i jej typ do środowiska *)
        begin match 
            TypingEnvironment.add id (
            (normal_of_var_declarations formal_parameters) 
            (normal_of_type_expressions return_types)
            ) env 
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
      (* Wpierw przeskanuj globalne definicje aby uzupełnić środowisko *)
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
