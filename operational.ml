(* invoke e.g. with 
./cppmem -testoperational -i ../examples/sorted/mp/t48-mp-rel_acq.c
 *)

open Nat_num
open Opsem
open Opsem_conversion
open Cabs

(* ToString methods *)

let rec int_exp_tostring (e:int_exp) : string = 
  match e with
  | ConstI v      -> Printf.sprintf "%i" v
  | Var v         -> Printf.sprintf "r%i" v
  | Plus (e1, e2) -> Printf.sprintf "%s + %s"
                     (int_exp_tostring e1)
                     (int_exp_tostring e2)
                      
let rec bool_exp_tostring (e:bool_exp) : string = 
  match e with
  | ConstB b         -> Printf.sprintf "%b" b
  | Equals (e1, e2)  -> Printf.sprintf "%s = %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
  | Greater (e1, e2) -> Printf.sprintf "%s > %s"
                        (int_exp_tostring e1)
                        (int_exp_tostring e2)
  | Not e1           -> Printf.sprintf "~%s" (bool_exp_tostring e1)
  | And (e1, e2)     -> Printf.sprintf "%s && %s"
                        (bool_exp_tostring e1)
                        (bool_exp_tostring e2)
                        
let memory_order_tostring (mo:Cmm.memory_order) : string = 
match mo with 
  | Cmm.NA      -> "NA"
  | Cmm.Seq_cst -> "Seq_cst"
  | Cmm.Relaxed -> "Relaxed"
  | Cmm.Release -> "Release"
  | Cmm.Acquire -> "Acquire"
  | Cmm.Consume -> "Consume"
  | Cmm.Acq_rel -> "Acq_rel"
                      
let statement_tostring (s:Opsem.statement) : string = 
  match s with 
  | Load (mo, reg, var)  -> Printf.sprintf "Load %s r%i %s" (memory_order_tostring mo) reg var
  | Store (mo, var, exp) -> Printf.sprintf "Store %s %s %s" (memory_order_tostring mo) var (int_exp_tostring exp)
  | Assert exp           -> Printf.sprintf "Assert %s" (bool_exp_tostring exp)
  | CreateThread node    -> Printf.sprintf "Create thread %i" node
  | JoinThread node      -> Printf.sprintf "Join thread %i" node
  
let rec edges_tostring_aux (start_node:node) (edges:(Opsem.statement * node) list) : string =
  match edges with 
  | [] -> ""
  | (statement, end_node)::t -> Printf.sprintf "%i -> %i %s\n%s" start_node end_node (statement_tostring statement) (edges_tostring_aux start_node t)
  
let rec edges_tostring (edges:(node * ((Opsem.statement * node) Pset.set)) list) : string = 
  match edges with
  | [] -> ""
  | (node, sub_edges)::t -> Printf.sprintf "%s%s" (edges_tostring_aux node (Pset.elements sub_edges)) (edges_tostring t)
  
let program_tostring (program:program) : string = 
  Printf.sprintf "Start node: %i, end node: %i, edges:\n%s" program.start_node program.end_node (edges_tostring (Pmap.bindings program.edges))
                                            
let action_tostring (a:action) : string = 
  match a with
  | Load2 (aid, tid, mo, reg, v, n) -> Printf.sprintf "Load %s %s %i r%i" (memory_order_tostring mo) v n reg
  | Store2 (aid, tid, mo, v, n) -> Printf.sprintf "Store %s %s %i" (memory_order_tostring mo) v n
  | Assert2 (aid, tid, e) -> Printf.sprintf "Assert %s" (bool_exp_tostring e)
  | CreateThread2 (aid, tid, node) -> Printf.sprintf "Create thread %i" node
  | JoinThread2 (aid, tid, node) -> Printf.sprintf "Join thread %i" node
  | CommitRead -> Printf.sprintf "Commit read" 
  | CommitWrite -> Printf.sprintf "Commit write" 
  
let rec registry_to_string_aux (l:(register * num) list) : string  = 
  match l with
  | [] -> ""
  | (r, n)::t -> Printf.sprintf "r%i = %i; %s" r n (registry_to_string_aux t)
  
let registry_to_string (registry:registry) : string = 
  registry_to_string_aux (Pmap.bindings registry)

(* Convert AST to Opsem.programs *)

let log_converting (construct:string) = 
  (* Uncomment the following line when debugging the conversion functions *)
  (* Printf.printf "operational.ml Converting %s\n" construct; *)
  ()  

let log_ignoring (construct:string) = 
  Printf.printf "operational.ml Ignoring %s\n" construct
  
let log (value:string) = 
  Printf.printf "operational.ml %s\n" value
  
let convert_memory_order (mo:Cabs.memory_order) : Cmm.memory_order = 
  match mo with 
  | MO_RELAXED -> Cmm.Relaxed
  | MO_CONSUME -> Cmm.Consume
  | MO_ACQUIRE -> Cmm.Acquire
  | MO_RELEASE -> Cmm.Release
  | MO_ACQ_REL -> Cmm.Acq_rel
  | MO_SEQ_CST -> Cmm.Seq_cst
  
let convert_constant (c:constant) : int_exp option  = 
  match c with 
  | CONST_INT (value:string) -> log_converting "constant CONST_INT"; Some (ConstI (int_of_string value))
  | CONST_FLOAT (_:string) -> log_ignoring "constant CONST_FLOAT"; None
  | CONST_CHAR (_:int64 list) -> log_ignoring "constant CONST_CHAR"; None
  | CONST_WCHAR (_:int64 list) -> log_ignoring "constant CONST_WCHAR"; None
  | CONST_STRING (_:string) -> log_ignoring "constant CONST_STRING"; None
  | CONST_WSTRING (_:int64 list) -> log_ignoring "constant CONST_WSTRING"; None
  
let rec convert_expression (expression:expression) : (program_aux option * int_exp option * bool_exp option) = 
  match expression with 
  | NOTHING                                                        -> log_ignoring "expression NOTHING"; (None, None, None)
  | ATOMIC_LOAD ((exp1:expression), (mo:memory_order), (exp2:expression option))                                  
                                                                   -> log_converting "expression ATOMIC_LOAD"; convert_load exp1 mo exp2
  | ATOMIC_CAS_WEAK ((_:expression), (_:expression), (_:expression), (_:memory_order), (_:memory_order))  
                                                                   -> log_ignoring "expression ATOMIC_CAS_WEAK"; (None, None, None)
  | ATOMIC_CAS_STRONG ((_:expression), (_:expression), (_:expression), (_:memory_order), (_:memory_order))
                                                                   -> log_ignoring "expression ATOMIC_CAS_STRONG"; (None, None, None)
  | UNARY ((operator:unary_operator), (exp:expression))            -> log_converting "expression UNARY"; convert_unary_operator operator exp
  | LABELADDR ((_:string))                                         -> log_ignoring "expression LABELADDR"; (None, None, None)
  | BINARY ((operator:binary_operator), (exp1:expression), (exp2:expression))  
                                                                   -> log_converting "expression BINARY"; convert_binary_operator operator exp1 exp2
  | QUESTION ((_:expression), (_:expression), (_:expression))      -> log_ignoring "expression QUESTION"; (None, None, None)
  | CAST ((_:(specifier * decl_type)), (_:init_expression))        -> log_ignoring "expression CAST"; (None, None, None)
  | CALL ((exp:expression), (arguments:expression list))           -> log_ignoring "expression CALL, but evaluating its arguments";
                                                                      (convert_arguments arguments, None, None)
  | COMMA ((_:expression list))                                    -> log_ignoring "expression COMMA"; (None, None, None)
  | CONSTANT ((c:constant))                                        -> log_converting "expression CONSTANT"; (None, convert_constant c, None)
  | PAREN ((_:expression))                                         -> log_ignoring "expression PAREN"; (None, None, None)
  | VARIABLE ((var:string), (exp:expression option))               -> log_converting "expression VARIABLE"; convert_variable var exp
  | EXPR_SIZEOF ((_:expression))                                   -> log_ignoring "expression EXPR_SIZEOF"; (None, None, None)
  | TYPE_SIZEOF ((_:specifier), (_:decl_type))                     -> log_ignoring "expression TYPE_SIZEOF"; (None, None, None)
  | EXPR_ALIGNOF ((_:expression))                                  -> log_ignoring "expression EXPR_ALIGNOF"; (None, None, None)
  | TYPE_ALIGNOF ((_:specifier), (_:decl_type))                    -> log_ignoring "expression TYPE_ALIGNOF"; (None, None, None)
  | INDEX ((_:expression), (_:expression))                         -> log_ignoring "expression INDEX"; (None, None, None)
  | MEMBEROF ((_:expression), (_:string))                          -> log_ignoring "expression MEMBEROF"; (None, None, None)
  | MEMBEROFPTR ((_:expression), (_:string))                       -> log_ignoring "expression MEMBEROFPTR"; (None, None, None)
  | GNU_BODY ((_:block))                                           -> log_ignoring "expression GNU_BODY"; (None, None, None)
  | EXPR_PATTERN ((_:string))                                      -> log_ignoring "expression EXPR_PATTERN"; (None, None, None)
  
and convert_arguments (l:expression list) : program_aux option = 
  match l with 
  | [] -> None
  | h::t -> let (first, _, _) = convert_expression h in
            let second = convert_arguments t in
            compose_sequential first second
            
and convert_unary_operator (operator:unary_operator) (exp:expression) : (program_aux option * int_exp option * bool_exp option) =
  match operator with
  | MINUS   -> log_ignoring "unary operator MINUS"; (None, None, None)
  | PLUS    -> log_ignoring "unary operator PLUS"; (None, None, None)
  | NOT     -> log_ignoring "unary operator NOT"; (None, None, None)
  | BNOT    -> log_ignoring "unary operator BNOT"; (None, None, None)
  | MEMOF   -> log_ignoring "unary operator MEMOF"; (None, None, None)
  | ADDROF  -> log_ignoring "unary operator ADDROF"; convert_expression exp; (None, None, None)
  | PREINCR -> log_ignoring "unary operator PREINCR"; (None, None, None)
  | PREDECR -> log_ignoring "unary operator PREDECR"; (None, None, None)
  | POSINCR -> log_ignoring "unary operator POSINCR"; (None, None, None)
  | POSDECR -> log_ignoring "unary operator POSDECR"; (None, None, None)
  
and convert_binary_operator (operator:binary_operator) (exp1:expression) (exp2:expression) : (program_aux option * int_exp option * bool_exp option) =
  match operator with
  | ADD         -> log_ignoring "binary operator ADD"; (None, None, None)
  | SUB         -> log_ignoring "binary operator SUB"; (None, None, None)
  | MUL         -> log_ignoring "binary operator MUL"; (None, None, None)
  | DIV         -> log_ignoring "binary operator DIV"; (None, None, None)
  | MOD         -> log_ignoring "binary operator MOD"; (None, None, None)
  | AND         -> log_ignoring "binary operator AND"; (None, None, None)
  | OR          -> log_ignoring "binary operator OR"; (None, None, None)
  | BAND        -> log_ignoring "binary operator BAND"; (None, None, None)
  | BOR         -> log_ignoring "binary operator BOR"; (None, None, None)
  | XOR         -> log_ignoring "binary operator XOR"; (None, None, None)
  | SHL         -> log_ignoring "binary operator SHL"; (None, None, None)
  | SHR         -> log_ignoring "binary operator SHR"; (None, None, None)
  | EQ          -> log_ignoring "binary operator EQ"; (None, None, None)
  | NE          -> log_ignoring "binary operator NE"; (None, None, None)
  | LT          -> log_ignoring "binary operator LT"; (None, None, None)
  | GT          -> log_ignoring "binary operator GT"; (None, None, None)
  | LE          -> log_ignoring "binary operator LE"; (None, None, None)
  | GE          -> log_ignoring "binary operator GE"; (None, None, None)
  | ASSIGN      -> log_converting "binary operator ASSIGN"; (convert_assign exp1 exp2, None, None)
  | ADD_ASSIGN  -> log_ignoring "binary operator ADD_ASSIGN"; (None, None, None)
  | SUB_ASSIGN  -> log_ignoring "binary operator SUB_ASSIGN"; (None, None, None)
  | DIV_ASSIGN  -> log_ignoring "binary operator DIV_ASSIGN"; (None, None, None)
  | MOD_ASSIGN  -> log_ignoring "binary operator MOD_ASSIGN"; (None, None, None)
  | BAND_ASSIGN -> log_ignoring "binary operator BAND_ASSIGN"; (None, None, None)
  | BOR_ASSIGN  -> log_ignoring "binary operator BOR_ASSIGN"; (None, None, None)
  | XOR_ASSIGN  -> log_ignoring "binary operator XOR_ASSIGN"; (None, None, None)
  | SHL_ASSIGN  -> log_ignoring "binary operator SHL_ASSIGN"; (None, None, None)
  | SHR_ASSIGN  -> log_ignoring "binary operator SHR_ASSIGN"; (None, None, None)

(* We convert a variable that is part of an expression to a load. Variables that are part of assignments are converted differently. *)
and convert_variable (var:string) (exp:expression option) : (program_aux option * int_exp option * bool_exp option) = 
  (match exp with
  | None -> ();
  | Some _ -> log_ignoring "expression inside variable");
  let (program, result_exp) = create_load Cmm.NA var in
  (Some program, Some result_exp, None)
  
and convert_load (exp1:expression) (mo:memory_order) (exp2:expression option) : (program_aux option * int_exp option * bool_exp option) = 
  (match exp2 with
  | None -> ();
  | Some _ -> log_ignoring "expression inside atomic load");
  match exp1 with 
  | UNARY (ADDROF, VARIABLE (var, exp3)) -> (match exp3 with
                                             | None -> ();
                                             | Some _ -> log_ignoring "expression inside variable");
                                            let (program, result_exp) = create_load (convert_memory_order mo) var in
                                            (Some program, Some result_exp, None)
  | _ -> log "Cannot convert atomic load when the first expression is not a UNARY (ADDROF, VARIABLE)"; (None, None, None)  

and convert_assign (exp1:expression) (exp2:expression) : program_aux option = 
  match exp1 with 
  | VARIABLE (var, _) -> (let (program_option, exp_option, _) = convert_expression exp2 in
                          match exp_option with 
                          | None -> log "Cannot convert assignment when expression is empty"; None
                          | Some exp -> Some (create_store program_option Cmm.NA var exp))
  | _ -> log "Cannot convert assignment when the first expression is not a variable"; None
            
let convert_store (exp1:expression) (exp2:expression) (mo:memory_order) : program_aux option = 
  match exp1 with 
  | UNARY (ADDROF, VARIABLE (var, exp3)) -> (match exp3 with
                                             | None -> ();
                                             | Some _ -> log_ignoring "expression inside variable");
                                            (let (program_option, exp_option, _) = convert_expression exp2 in 
                                             match exp_option with 
                                             | None -> log "Cannot convert atomic store when expression is empty"; None
                                             | Some exp -> Some (create_store program_option (convert_memory_order mo) var exp))
  | _ -> log "Cannot convert atomic store when the first expression is not a UNARY (ADDROF, VARIABLE)"; None
 
let rec convert_statement (statement:statement) : program_aux option = 
  match statement with 
  | NOP ((_:cabsloc))                                                              -> log_ignoring "statement NOP"; None
  | COMPUTATION ((expression:expression), (_:cabsloc))                             -> log_converting "statement COMPUTATION"; 
                                                                                      let (program, _, _) = convert_expression expression in program
  | BLOCK ((block:block), (_:cabsloc))                                             -> log_converting "statement BLOCK"; convert_block block
  | SEQUENCE ((_:statement), (_:statement), (_:cabsloc))                           -> log_ignoring "statement SEQUENCE"; None
  | IF ((_:expression), (_:statement), (_:statement), (_:cabsloc))                 -> log_ignoring "statement IF"; None
  | WHILE ((_:expression), (_:statement), (_:cabsloc))                             -> log_ignoring "statement WHILE"; None
  | DOWHILE ((_:expression), (_:statement), (_:cabsloc))                           -> log_ignoring "statement DOWHILE"; None
  | FOR ((_:for_clause), (_:expression), (_:expression), (_:statement), (_:cabsloc)) -> log_ignoring "statement FOR"; None
  | BREAK ((_:cabsloc))                                                            -> log_ignoring "statement BREAK"; None
  | LOCK ((_:string), (_:cabsloc))                                                 -> log_ignoring "statement LOCK"; None
  | UNLOCK ((_:string), (_:cabsloc))                                               -> log_ignoring "statement UNLOCK"; None
  | ATOMIC_FENCE ((_:memory_order), (_:cabsloc))                                   -> log_ignoring "statement ATOMIC_FENCE"; None
  | ATOMIC_INT ((_:string), (_:expression), (_:cabsloc))                           -> log_ignoring "statement ATOMIC_INT"; None
  | ATOMIC_STORE ((exp1:expression), (exp2:expression), (mo:memory_order), (_:cabsloc)) -> log_converting "statement ATOMIC_STORE"; convert_store exp1 exp2 mo
  | MYTHREAD ((_:string), (_:string), (_:expression list), (_:cabsloc))            -> log_ignoring "statement MYTHREAD"; None
  | JOIN ((_:string), (_:cabsloc))                                                 -> log_ignoring "statement JOIN"; None
  | PAR ((statements:statement list), (_:cabsloc))                                 -> log_converting "statement PAR"; convert_parallel statements
  | CONTINUE ((_:cabsloc))                                                         -> log_ignoring "statement CONTINUE"; None
  | RETURN ((_:expression), (_:cabsloc))                                           -> log_ignoring "statement RETURN"; None
  | SWITCH ((_:expression), (_:statement), (_:cabsloc))                            -> log_ignoring "statement SWITCH"; None
  | CASE ((_:expression), (_:statement), (_:cabsloc))                              -> log_ignoring "statement CASE"; None
  | CASERANGE ((_:expression), (_:expression), (_:statement), (_:cabsloc))         -> log_ignoring "statement CASERANGE"; None
  | DEFAULT ((_:statement), (_:cabsloc))                                           -> log_ignoring "statement DEFAULT"; None
  | LABEL ((_:string), (_:statement), (_:cabsloc))                                 -> log_ignoring "statement LABEL"; None
  | GOTO ((_:string), (_:cabsloc))                                                 -> log_ignoring "statement GOTO"; None
  | COMPGOTO ((_:expression), (_:cabsloc))                                         -> log_ignoring "statement COMPGOTO"; None
  | DEFINITION ((definition:definition))                                           -> log_ignoring "statement DEFINITION"; None
  | ASM ((_:attribute list), (_:string list), (_:asm_details option), (_:cabsloc)) -> log_ignoring "statement ASM"; None
  | TRY_EXCEPT ((_:block), (_:expression), (_:block), (_:cabsloc))                 -> log_ignoring "statement TRY_EXCEPT"; None
  | TRY_FINALLY ((_:block), (_:block), (_:cabsloc))                                -> log_ignoring "statement TRY_FINALLY"; None

and convert_sequential (statements:statement list) : program_aux option = 
  match statements with
  | [] -> None
  | h::t -> let first = convert_statement h in
            let second = convert_sequential t in
            compose_sequential first second
            
and convert_parallel (statements:statement list) : program_aux option = 
  match statements with
  | [] -> None
  | h::t -> let first = convert_statement h in
            let second = convert_parallel t in
            compose_parallel first second

and convert_block (block:block) : program_aux option =
  if block.blabels = [] then () else log_ignoring "block.blabels";
  if block.battrs = [] then () else log_ignoring "block.battrs";
  convert_sequential block.bstmts
 
let convert_toplevel_definition (definition:Cabs.definition) : program_aux option =
  match definition with 
  | FUNDEF ((_:single_name), (block:block), (_:cabsloc), (_:cabsloc)) -> log_converting "definition FUNDEF"; convert_block block
  | DECDEF ((_:init_name_group), (_:cabsloc))                         -> log_ignoring "definition DECDEF"; None
  | TYPEDEF ((_:name_group), (_:cabsloc))                             -> log_ignoring "definition TYPEDEF"; None
  | ONLYTYPEDEF ((_:specifier), (_:cabsloc))                          -> log_ignoring "definition ONLYTYPEDEF"; None
  | GLOBASM ((_:string), (_:cabsloc))                                 -> log_ignoring "definition GLOBASM"; None
  | PRAGMA ((_:expression), (_:cabsloc))                              -> log_ignoring "definition PRAGMA"; None
  | LINKAGE ((_:string), (_:cabsloc), (_:definition list))            -> log_ignoring "definition LINKAGE"; None
  | TRANSFORMER ((_:definition), (_:definition list), (_:cabsloc))    -> log_ignoring "definition TRANSFORMER"; None
  | EXPRTRANSFORMER ((_:expression), (_:expression), (_:cabsloc))     -> log_ignoring "definition EXPRTRANSFORMER"; None
  
let rec convert_toplevel_definitions (definitions:Cabs.definition list) : program_aux option = 
  match definitions with
  | [] -> None
  | h::t -> let program_option_1 = convert_toplevel_definition h in
            let program_option_2 = convert_toplevel_definitions t in
            if program_option_1 = None then
                program_option_2
            else
                ((if program_option_2 = None then () else log "definitions after the first converted definition");
                program_option_1)
                
(* Running the operational semantics *)

let rec run_opsem_aux (p:program) (s:state) (i:int) : bool =
  let indent = i * 2 in
  let transitions = Opsem.allowed_transitions p s in
  if Pset.is_empty transitions then
    (Printf.printf "%sNo further actions possible. Resulting registry: %s\n" (String.make indent ' ') (registry_to_string s.registry); true)
  else
    Pset.for_all (fun t -> Printf.printf "%s%s\n" (String.make indent ' ') (action_tostring t.action);
                           run_opsem_aux p t.state (i + 1))
                 transitions
   
let run_opsem (p:program) : unit = 
  run_opsem_aux p (Opsem.initial_state p) 0; ()
            
(* Top level - proc_file is called from other files *)

let proc_file ((_:string option), (cilf:Cabs.file)) = 
  let (filename, definitions) = cilf in 
  let program_option = convert_toplevel_definitions definitions in
  (match program_option with
  | None -> log "The converted program is empty\n"
  | Some program_aux -> log (Printf.sprintf "Converted program:\n%s" (program_tostring program_aux.program));
                        run_opsem program_aux.program
  );
  exit 0
