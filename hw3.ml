module SS = Set.Make (String)

exception Not_implemented
exception Parse_exn
exception CaptureException of string

(* Data Definitions *)

type token
= LParen
| RParen
| TokLam
| TokDot
| TokVar of string

type term
= TmVar of string
| TmAbs of string * term
| TmApp of term * term

(* Utilities *)

(* Strings in ocaml are not represented as lists of characters. For lexing and parsing purposes, it's easier to work
   with lists of characters. You shouldn't need to touch these functions that convert between the two, but feel free to use them for debugging. *)
let string_to_char_list (s : string) : char list =
  s |> String.to_seq |> List.of_seq

let char_list_to_string (cl : char list) : string =
  cl |> List.to_seq |> String.of_seq

(* Lexical Scanner *)

(* nextToken should return the next token from a list of characters, along with the characters thereafter
   - return None if the list of chars is empty
   - skip whitespace characters
   - throw an exception if the characters cannot be tokenized *)

let rec nextToken (cs : char list) : (token * char list) option =
  let is_alpha_num (c : char) : bool =
    match c with
    |'0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' -> true
    | _                                   -> false
  in

  let rec exhaustVar (cs : char list) : string * char list =
    match cs with
    | c :: tl when is_alpha_num c ->
        let str, tl' = exhaustVar tl in
        (String.make 1 c ^ str, tl')
    | _ -> ("", cs)
  in

  match cs with
  | [] -> None
  | '(' :: tl -> Some (LParen, tl)
  | '.' :: tl -> Some (TokDot, tl)
  | '&' :: tl -> Some (TokLam, tl)
  | ')' :: tl -> Some (RParen, tl)
  | c :: tl when is_alpha_num c ->
      let str, tl' = exhaustVar (c :: tl) in
      Some (TokVar str, tl')
  | ' ' :: tl | '\t' :: tl | '\n' :: tl -> nextToken tl
  | _ -> raise Parse_exn

(* turn a string of code (like "&x.x" into a list of tokens (like [TokLam, TokVar("x"), TokDot, TokVar("x")]) *)

let rec scan (cs : char list) : token list =
  match nextToken cs with
  | None             -> []
  | Some (tok, rest) -> tok :: scan rest

(* Parser *)

(* nextTerm should return the next term from a list of tokens, along with the tokens thereafter
   - return None if the list of tokens is empty
   - throw an exception if the characters cannot be tokenized *)
let rec nextTerm (ts : token list) : (term * token list) option =
  let rec parseApp (ts : token list) : (term * token list) option =
    match nextTerm ts with
    | None -> None
    | Some (func, RParen :: LParen :: ts') -> (
        match nextTerm ts' with
        | None -> None
        | Some (input, RParen :: ts'') -> Some (TmApp (func, input), ts'')
        | _ -> raise Parse_exn)
    | _ -> raise Parse_exn
  in

  match ts with
  | [] -> None
  | TokVar v :: ts -> Some (TmVar v, ts)
  | TokLam :: TokVar x :: TokDot :: ts -> (
      match nextTerm ts with
      | None -> None
      | Some (body, ts') -> Some (TmAbs (x, body), ts'))
  | LParen :: ts -> parseApp ts
  | _ -> raise Parse_exn

(* turn a list of tokens (like [TokLam, TokVar of "x", TokDot, TokVar of "x"] into a term (like TmAbs ("x", TmVar("x"))) *)
let parse (tokens : token list) : term =
  match nextTerm tokens with
  | Some (term, []) -> term
  | _               -> raise Parse_exn

(* Substitution *)

(* Implement the substitution function `[x |-> s] t` discussed in class.
   If substitution would result in variable capture, simply
   raise a CaptureException (with the message string of your choice). *)

(* Get the free variables of t as a string set . *)
let rec fv = function
  | TmVar x             -> SS.singleton x
  | TmAbs (v, body)     -> SS.diff  (fv body) (SS.singleton v)
  | TmApp (func, input) -> SS.union (fv func) (fv input)

let rec subst (x : string) (s : term) (t : term) : term =
  match t with
  | TmVar v when v = x -> s
  | TmVar v -> TmVar v
  | TmAbs (v, body) when v = x -> TmAbs (v, body)
  | TmAbs (v, body) ->
      if SS.mem v (fv s) then raise (CaptureException "error")
      else TmAbs (v, subst x s body)
  | TmApp (func, input) -> TmApp (subst x s func, subst x s input)

(* Small-step evaluation *)

(* Implement the small-step evaluation relations from class.
   We will implement both variants from class: call-by-name and
   call-by-value.
   We will also implement a third approach: Full beta reduction,
   which reduces terms under a lambda.
   Return none if a term doesn't step. *)
let rec cbn = function
  | TmApp (TmAbs (v, body), input) -> Some (subst v input body)
  | TmApp (func, input) -> (
      match cbn func with
      | None       -> None
      | Some func' -> Some (TmApp (func', input)))
  | _ -> None

let rec cbv = function
  | TmApp (TmAbs (v, body), (TmAbs (_, _) as value)) ->
      Some (subst v value body)
  | TmApp ((TmAbs (_, _) as func), input) -> (
      match cbv input with
      | None -> None
      | Some input' -> Some (TmApp (func, input')))
  | TmApp (func, input) -> (
      match cbv func with
      | None -> None
      | Some func' -> Some (TmApp (func', input)))
  | _ -> None

let rec beta = function
  | TmVar x -> None
  | TmAbs (v, body) -> (
      match beta body with
      | None -> None
      | Some body' -> Some (TmAbs (v, body')))
  | TmApp (TmAbs (v, body), input) -> Some (subst v input body)
  | TmApp (func, input) -> (
      match beta func with
      | None -> (
          match beta input with
          | None -> None
          | Some input' -> Some (TmApp (func, input')))
      | Some func' -> Some (TmApp (func', input)))

(* Given an evaluation strategy above and a term t, return t'
   such that t ->* t' and t' is a normal form for the given evaluation
   strategy. *)
let rec multistep (strat : term -> term option) (t : term) : term =
  match strat t with
  | None    -> t
  | Some t' -> multistep strat t'

(* Define the boolean terms true and false as given in class.
   (We'll use the book's `tru` and `fls` to avoid notation clashes.)
    Define a lambda term that implements an `xor` operation on bools. *)

let rec tru : term = parse (scan (string_to_char_list "&x.&y.x"))
let rec fls : term = parse (scan (string_to_char_list "&x.&y.y"))
let rec xor : term = parse (scan (string_to_char_list
"&a.&b.&t.&f.
((a)
  (((b) (f)) (t)))
  (((b) (t)) (f))"))

(* Interpreter *)

(* You should not need to modify this code -- feel free to add statements for debugging,
   but remember to delete them before submitting. *)

let rec term_to_string (t : term) : string =
  match t with
  | TmVar str -> str
  | TmAbs (var, body) -> "&" ^ var ^ "." ^ term_to_string body
  | TmApp (t1, t2) -> "(" ^ term_to_string t1 ^ ") (" ^ term_to_string t2 ^ ")"

let opt_term_to_string (o : term option) : string =
  match o with
  | None   -> " "
  | Some t -> term_to_string t

let interpret (str : string) : unit =
  let chars = string_to_char_list str in
  let tokens = scan chars in
  let ast = parse tokens in
  let term_str = term_to_string ast in
  let _ = print_endline "----- Call by Name Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline ("->    " ^ opt_term_to_string (cbn ast)) in
  let _ = print_endline "" in
  let _ = print_endline "-----------------------------------" in
  let _ = print_endline "" in
  let _ = print_endline "----- Call by Name Multistep Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline ("->    " ^ term_to_string (multistep cbn ast)) in
  let _ = print_endline "" in
  let _ = print_endline "-----------------------------------" in
  let _ = print_endline "" in
  let _ = print_endline "----- Call by Value Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline ("->    " ^ opt_term_to_string (cbv ast)) in
  let _ = print_endline "" in
  let _ = print_endline "-----------------------------------" in
  let _ = print_endline "" in
  let _ = print_endline "----- Call by Value Multistep Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline ("->    " ^ term_to_string (multistep cbv ast)) in
  let _ = print_endline "" in
  let _ = print_endline "-----------------------------------" in
  let _ = print_endline "" in
  let _ = print_endline "----- Full Beta Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline ("->    " ^ opt_term_to_string (beta ast)) in
  let _ = print_endline "" in
  let _ = print_endline "-----------------------------------" in
  let _ = print_endline "" in
  let _ = print_endline "----- Full Beta Multistep Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline ("->    " ^ term_to_string (multistep beta ast)) in
  print_endline ""
;;

interpret Sys.argv.(1)
