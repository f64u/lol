exception Not_implemented
exception Parse_exn

(* Data Definitions *)

type token
= LParen
| RParen
| TokTrue
| TokFalse
| TokZero
| TokIf
| TokSucc
| TokPred
| TokIsZero
| TokAnd
| TokOr
| TokNot

type term
= True
| False
| Zero
| If of term * term * term
| Succ of term
| Pred of term
| IsZero of term
| And of term * term
| Or of term * term
| Not of term

(* Utilities *) 

(* Strings in ocaml are not represented as lists of characters. For lexing and parsing purposes, it's easier to work
with lists of characters. You shouldn't need to touch these functions that convert between the two, but feel free to use them for debugging. *)
let string_to_char_list (s: string) : char list =
  s |> String.to_seq |> List.of_seq
  
let char_list_to_string (cl: char list) : string =
  cl |> List.to_seq |> String.of_seq
  
(* Value Judgements *)

(* Returns true if the term is a numeric value, false otherwise. *)
let rec is_num_val = function
  | Zero                     -> true
  | Succ v when is_num_val v -> true
  | _                        -> false 

(* Returns true if the term is a value, false otherwise. *)
let is_val = function
  | True | False -> true
  | v            -> is_num_val v

(* Lexical Scanner *)

(* nextToken should return the next token from a list of characters, along with the characters thereafter
   - return None if the list of chars is empty
   - skip whitespace characters
   - throw an exception if the characters cannot be tokenized 
  Some basic cases have been given for you. *)
let rec nextToken = function
  | []                               -> None
  | ' '::tl | '\t'::tl | '\n'::tl    -> nextToken tl
  | '('::tl                          -> Some (LParen, tl)
  | ')'::tl                          -> Some (RParen, tl)
  | 't'::'r'::'u'::'e'::tl           -> Some (TokTrue, tl)
  | 'f'::'a'::'l'::'s'::'e'::tl      -> Some (TokFalse, tl)
  | '0'::tl                          -> Some (TokZero, tl)
  | 'i'::'f'::tl                     -> Some (TokIf, tl)
  | 's'::'u'::'c'::'c'::tl           -> Some (TokSucc, tl)
  | 'p'::'r'::'e'::'d'::tl           -> Some (TokPred, tl)
  | 'i'::'s'::'z'::'e'::'r'::'o'::tl -> Some (TokIsZero, tl)
  | 'a'::'n'::'d'::tl                -> Some (TokAnd, tl)
  | 'o'::'r'::tl                     -> Some (TokOr, tl)
  | 'n'::'o'::'t'::tl                -> Some (TokNot, tl)
  | _                                -> raise Parse_exn

(* turn a string of code (like "(pred 0)" into a list of tokens (like [LParen, TokPred, TokZero, RParen]) *)
let rec scan (ls : char list) : token list =
  match nextToken ls with
  | None -> []
  | Some (tok, rest) -> tok :: scan rest

(* Parser *)

(* nextTerm should return the next term from a list of tokens, along with the tokens thereafter
   - return None if the list of tokens is empty
   - throw an exception if the characters cannot be tokenized *)
let rec nextTerm (tl: token list) : (term * token list) option =
  let parseIfTerms (tl : token list) : (term * token list) option = 
    match nextTerm tl with
      | None -> None
      | Some (cond, tl') -> (* I could really use monad support rn *)
        match nextTerm tl' with
          | None -> None
          | Some (ifTrue, tl'') -> 
            match nextTerm tl'' with
              | Some (ifFalse, RParen::tl''') -> Some (If (cond, ifTrue, ifFalse), tl''')
              | _                             -> None in

  let parseUnaryArg (tl : token list) (cons : term -> term) : (term * token list) option =
    match nextTerm tl with
      | Some (term, RParen::tl') -> Some (cons term, tl')
      | _                        -> None in

  let parseBinaryArgs (tl : token list) (cons : term * term -> term) : (term * token list) option =
    match nextTerm tl with
      | None             -> None
      | Some (left, tl') -> 
        match nextTerm tl' with
          | Some (right, RParen::tl'') -> Some (cons (left, right), tl'')
          | _                          -> None in
              
  match tl with
  | TokTrue::tl           -> Some (True, tl)
  | TokFalse::tl          -> Some (False, tl)
  | TokZero::tl           -> Some (Zero, tl)
  | LParen::TokIf::tl     -> parseIfTerms tl
  | LParen::TokSucc::tl   -> parseUnaryArg tl (fun t -> Succ t)
  | LParen::TokPred::tl   -> parseUnaryArg tl (fun t -> Pred t)
  | LParen::TokIsZero::tl -> parseUnaryArg tl (fun t -> IsZero t)
  | LParen::TokAnd::tl    -> parseBinaryArgs tl (fun (left, right) -> And (left, right))
  | LParen::TokOr::tl     -> parseBinaryArgs tl (fun (left, right) -> Or (left, right))
  | LParen::TokNot::tl    -> parseUnaryArg tl (fun t -> Not t)
  | _                     -> raise Parse_exn
    


(* turn a list of tokens (like [LParen ,TokPred, TokZero, RParen] into a term (like Pred 0) *)
let parse (tokens : token list) : term = 
  match nextTerm tokens with
    | Some (term, []) -> term
    | _               -> raise Parse_exn

(* Small Step evaluator *)

(* Implement the small-step evaluation relation from class. 
   For And, Or and Not, you should be able to determine 
   appropriate rules by extrapolating from the If rules.
   If a term is not a normal form, take the next possible step
   - i.e., if t -> u, then step(t) should return Some(u)
   if a term is a normal form, return None *)
let rec small_step (t : term) : term option = 
  let recurse (v : term) (cons : term -> term) =
    (match small_step v with None -> None | Some v' -> Some (cons v')) in

  match t with
  | True | False | Zero                 -> None
 
  | If (True, ifTrue, _)                -> Some ifTrue
  | If (False, _, ifFalse)              -> Some ifFalse
  | If (cond, ifTrue, ifFalse)          -> (match small_step cond with
                                                | None -> None 
                                                | Some cond' -> Some (If (cond', ifTrue, ifFalse)))

  | Succ t' when is_num_val t'          -> None
  | Succ t'                             -> recurse t' (fun t -> Succ t)

  | Pred Zero                           -> Some Zero
  | Pred (Succ t') when is_num_val t'   -> Some t'
  | Pred t'                             -> recurse t' (fun t -> Pred t)

  | IsZero Zero                         -> Some True
  | IsZero (Succ t') when is_num_val t' -> Some False
  | IsZero t'                           -> recurse t' (fun t -> IsZero t)

  | And (True, right)                   -> Some right
  | And (False, _)                      -> Some False
  | And (cond, right)                   -> (match small_step cond with
                                              | None -> None
                                              | Some cond' -> Some (And (cond', right)))

  | Or (True, _)                        -> Some True
  | Or (False, right)                   -> Some right
  | Or (cond, right)                    -> (match small_step cond with
                                              | None -> None
                                              | Some cond' -> Some (Or (cond', right)))

  | Not True                            -> Some False
  | Not False                           -> Some True
  | Not t'                              -> recurse t' (fun t -> Not t)
  

(* Returns true if the term is a normal form, false otherwise. *)
let is_normal (t: term) : bool = small_step t = None

(* Returns true if the term is stuck, false otherwise. *)
let is_stuck (t: term) : bool = not (is_val t) && is_normal t 

(* Given t, return t' such that t ->* t' and t' is a normal form. *)
let rec multistep_full (t : term) : term = match small_step t with
  | None    -> t
  | Some t' -> multistep_full t'

(* Returns true if a term steps to a value, and false otherwise. *)
let rec multisteps_to_value (t: term) : bool = is_val (multistep_full t)

(* Big Step evaluator *)

(* Now implement the big-step relation from class. 
   Again, return none if the program doesn't (big) step. *)
let rec big_step (t : term) : term option = 
  match t with
    | True -> Some True | False -> Some False | Zero -> Some Zero
    | If (cond, ifTrue, ifFalse) ->
      (match big_step cond with
        | Some True  -> big_step ifTrue
        | Some False -> big_step ifFalse
        | _          -> None)
    | Succ t' -> 
      (match big_step t' with
        | Some t'' when is_num_val t'' -> Some (Succ t'')
        | _                            -> None)
    | Pred t' -> 
      (match big_step t' with
        | Some Zero                           -> Some Zero
        | Some (Succ t'') when is_num_val t'' -> Some t''
        | _                                   -> None)
    | IsZero t' -> 
      (match big_step t' with
        | Some Zero                           -> Some True
        | Some (Succ t'') when is_num_val t'' -> Some False
        | _                                   -> None)
    | And (left, right) -> 
      (match big_step left with
        | Some True  -> big_step right
        | Some False -> Some False
        | _          -> None)
    | Or (left, right)  -> 
      (match big_step left with
        | Some True  -> Some True
        | Some False -> big_step right
        | _          -> None)
    | Not t' ->
      (match big_step t' with
        | Some True  -> Some False
        | Some False -> Some True
        | _ -> None)
 
(* Interpreter *)

(* You should not need to modify this code -- feel free to add statements for debugging,
   but remember to delete them before submitting. *)

let rec term_to_string (t : term) : string = match t with
| True -> "true"
| False -> "false"
| Zero -> "zero"
| If (t1, t2, t3) -> "(" ^ "if " ^ term_to_string t1 ^ " then " ^ term_to_string t2 ^ " else " ^ term_to_string t3  ^ ")"
| Succ (t1) -> "(" ^ "succ " ^ term_to_string t1 ^ ")"
| Pred (t1) -> "(" ^ "pred " ^ term_to_string t1 ^ ")"
| IsZero (t1) ->  "(" ^ "iszero " ^ term_to_string t1 ^ ")"
| And (t1, t2) -> "(" ^ term_to_string t1 ^ " and " ^ term_to_string t2 ^ ")"
| Or (t1, t2) -> "(" ^ term_to_string t1 ^ " or " ^ term_to_string t2 ^ ")"
| Not (t1) -> "(" ^ "not " ^ term_to_string t1 ^ ")"

let opt_term_to_string (o : term option) : string = 
  match o with
  | None -> " "
  | Some t -> term_to_string t 

let interpret (str : string) : unit =
  let chars = string_to_char_list str in
  let tokens = scan chars in
  let ast = parse tokens in
  let ss_term = small_step ast in
  let bs_term = big_step ast in
  let term_str = term_to_string ast in 
  let ss_term_str = opt_term_to_string ss_term in
  let bs_term_str = opt_term_to_string bs_term in
  let _ = print_endline ("----- Small Step Evaluation -----") in
  let _ = print_endline ("      " ^ term_str) in 
  let _ = print_endline ("->    " ^ ss_term_str) in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline ("----- Big Step Evaluation -----") in
  let _ = print_endline ("      " ^ term_str) in 
  print_endline ("||" ^ bs_term_str);;


interpret Sys.argv.(1)

