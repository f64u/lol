module SS = Set.Make (String)

exception Not_implemented
exception Parse_exn
exception NotAbs of string
exception NotFound of string
exception DuplicateVar of string

(* Data Definitions *)

type token =
  | LParen
  | RParen
  | TokLam
  | TokDot
  | TokVar of string
  | TokIf
  | TokThen
  | TokElse
  | TokZero
  | TokSucc
  | TokPred
  | TokIsZero
  | TokColon
  | TokBool
  | TokNat
  | TokArrow
  | TokTrue
  | TokFalse

type typ =
  | TBool
  | TNat
  | TFun of typ * typ

type term =
  | TmVar of string
  | TmAbs of string * typ * term
  | TmApp of term * term
  | TmTrue
  | TmFalse
  | TmZero
  | TmIf of term * term * term
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term

(* Utilities *)

(* Strings in ocaml are not represented as lists of characters. For lexing
   and parsing purposes, it's easier to work with lists of characters. You
   shouldn't need to touch these functions that convert between the two, but
   feel free to use them for debugging. *)
let string_to_char_list (s : string) : char list = s |> String.to_seq |> List.of_seq
let char_list_to_string (cl : char list) : string = cl |> List.to_seq |> String.of_seq

(* Lexical Scanner *)

(* nextToken should return the next token from a list of characters, along
   with the characters thereafter - return None if the list of chars is empty
   - skip whitespace characters (except inside strings) - throw an exception
   if the characters cannot be tokenized *)
let rec nextToken (cs : char list) : (token * char list) option =
  let is_alpha_num (c : char) : bool =
    match c with
    | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' -> true
    | _ -> false
  in
  let rec exhaustVar (cs : char list) : string * char list =
    match cs with
    | c :: tl when is_alpha_num c ->
      let str, tl' = exhaustVar tl in
      String.make 1 c ^ str, tl'
    | _ -> "", cs
  in
  match cs with
  | [] -> None
  | '(' :: tl -> Some (LParen, tl)
  | ')' :: tl -> Some (RParen, tl)
  | '.' :: tl -> Some (TokDot, tl)
  | '&' :: tl -> Some (TokLam, tl)
  | ('a' .. 'z' as c) :: tl ->
    let str, tl' = exhaustVar (c :: tl) in
    Some (TokVar str, tl')
  | 'I' :: 'f' :: tl -> Some (TokIf, tl)
  | 'T' :: 'h' :: 'e' :: 'n' :: tl -> Some (TokThen, tl)
  | 'E' :: 'l' :: 's' :: 'e' :: tl -> Some (TokElse, tl)
  | '0' :: tl -> Some (TokZero, tl)
  | 'S' :: 'u' :: 'c' :: 'c' :: tl -> Some (TokSucc, tl)
  | 'P' :: 'r' :: 'e' :: 'd' :: tl -> Some (TokPred, tl)
  | 'I' :: 's' :: 'Z' :: 'e' :: 'r' :: 'o' :: tl -> Some (TokIsZero, tl)
  | ':' :: tl -> Some (TokColon, tl)
  | 'B' :: 'o' :: 'o' :: 'l' :: tl -> Some (TokBool, tl)
  | 'N' :: 'a' :: 't' :: tl -> Some (TokNat, tl)
  | '-' :: '>' :: tl -> Some (TokArrow, tl)
  | 'T' :: 'r' :: 'u' :: 'e' :: tl -> Some (TokTrue, tl)
  | 'F' :: 'a' :: 'l' :: 's' :: 'e' :: tl -> Some (TokFalse, tl)
  | ' ' :: tl | '\t' :: tl | '\n' :: tl -> nextToken tl
  | _ -> raise Parse_exn
;;

(* turn a string of code (like "&x:Bool.x" into a list of tokens (like
   [TokLam, TokVar("x"), TokColon, TokBool, TokDot, TokVar("x")]) *)
let rec scan (cs : char list) : token list =
  match nextToken cs with
  | None -> []
  | Some (tok, rest) -> tok :: scan rest
;;

(* Parser *)

(* nextTerm should return the next term from a list of tokens, along with the
   tokens thereafter - return None if the list of tokens is empty - throw an
   exception if the characters cannot be tokenized *)
let rec nextTerm (ts : token list) : (term * token list) option =
  let rec nextTyp (ts : token list) : typ * token list =
    match ts with
    | LParen :: tl ->
      (match nextTyp tl with
       | (TFun (_, _) as left), RParen :: TokArrow :: tl' ->
         let right, tl'' = nextTyp tl' in
         TFun (left, right), tl''
       | _ -> raise Parse_exn)
    | TokBool :: TokArrow :: tl ->
      let right, tl' = nextTyp tl in
      TFun (TBool, right), tl'
    | TokBool :: tl -> TBool, tl
    | TokNat :: TokArrow :: tl ->
      let right, tl' = nextTyp tl in
      TFun (TNat, right), tl'
    | TokNat :: tl -> TNat, tl
    | _ -> raise Parse_exn
  in
  let rec nextApp (ts : token list) : term * token list =
    match nextTerm ts with
    | Some (func, RParen :: LParen :: tl) ->
      (match nextTerm tl with
       | Some (input, RParen :: tl') -> TmApp (func, input), tl'
       | _ -> raise Parse_exn)
    | _ -> raise Parse_exn
  in
  let nextIf (ts : token list) : term * token list =
    match nextTerm ts with
    | Some (cond, TokThen :: tl) ->
      (match nextTerm tl with
       | Some (ifTrue, TokElse :: tl') ->
         (match nextTerm tl' with
          | Some (ifFalse, tl'') -> TmIf (cond, ifTrue, ifFalse), tl''
          | _ -> raise Parse_exn)
       | _ -> raise Parse_exn)
    | _ -> raise Parse_exn
  in
  let nextLam (ts : token list) : term * token list =
    match ts with
    | TokVar v :: TokColon :: tl ->
      (match nextTyp tl with
       | typ, TokDot :: tl' ->
         (match nextTerm tl' with
          | Some (body, tl'') -> TmAbs (v, typ, body), tl''
          | _ -> raise Parse_exn)
       | _ -> raise Parse_exn)
    | _ -> raise Parse_exn
  in
  let nextUnaryArg (ts : token list) (constructor : term -> term) : term * token list =
    match nextTerm ts with
    | Some (term, tl) -> constructor term, tl
    | _ -> raise Parse_exn
  in
  match ts with
  | [] -> None
  | TokZero :: tl -> Some (TmZero, tl)
  | TokTrue :: tl -> Some (TmTrue, tl)
  | TokFalse :: tl -> Some (TmFalse, tl)
  | TokVar v :: tl -> Some (TmVar v, tl)
  | TokLam :: tl -> Some (nextLam tl)
  | LParen :: tl -> Some (nextApp tl)
  | TokIf :: tl -> Some (nextIf tl)
  | TokSucc :: tl -> Some (nextUnaryArg tl (fun t -> TmSucc t))
  | TokPred :: tl -> Some (nextUnaryArg tl (fun t -> TmPred t))
  | TokIsZero :: tl -> Some (nextUnaryArg tl (fun t -> TmIsZero t))
  | _ -> raise Parse_exn
;;

(* turn a list of tokens (like [TokLam, TokVar of "x", TokDot, TokVar of "x"]
   into a term (like TmAbs ("x", TmVar("x"))) *)
let parse (tokens : token list) : term =
  match nextTerm tokens with
  | Some (term, []) -> term
  | _ -> raise Parse_exn
;;

(* Alpha Conversion *)

(* takes a list of variable strings and produces a new string not in the
   set *)
let fresh_var (vars : SS.t) : string = SS.max_elt vars ^ "0"

(* takes a term of the form &x:T.t1 and turns it into an equivalent &y:T.t1',
   where y is a fresh variable and t1' is t1 with (free) x's replaced with
   ys. If t is not a lambda abstraction return a NotAbs exception*)
let rec alpha_convert (vars : SS.t) (t : term) : term =
  let rec rename (f : string) (t : string) (term : term) : term =
    match term with
    | TmFalse -> TmFalse
    | TmTrue -> TmTrue
    | TmZero -> TmZero
    | TmVar v when v = f -> TmVar t
    | TmVar v -> TmVar v
    | TmAbs (v, _, _) as term' when v = f -> term'
    | TmAbs (v, _, _) as term' when v = t ->
      term' |> alpha_convert (SS.singleton t) |> rename f t
    | TmAbs (v, typ, body) -> TmAbs (v, typ, rename f t body)
    | TmIf (cond, ifTrue, ifFalse) ->
      TmIf (rename f t cond, rename f t ifTrue, rename f t ifFalse)
    | TmSucc term' -> TmSucc (rename f t term')
    | TmPred term' -> TmPred (rename f t term')
    | TmIsZero term' -> TmIsZero (rename f t term')
    | TmApp (left, right) -> TmApp (rename f t left, rename f t right)
  in
  match t with
  | TmAbs (v, typ, body) ->
    let new_v = fresh_var (SS.add v vars) in
    TmAbs (new_v, typ, rename v new_v body)
  | _ -> raise (NotAbs "error")
;;

(* Typechecking *)

module SMap = Map.Make (String)

(* give a reasonable type to context *)
type ctx = typ SMap.t

(* define the empty context *)
let empty_ctx : ctx = SMap.empty

(* look up a given variable's typ, throw a NotFound exception if the variable
   is not found *)
let lookup (g : ctx) (x : string) : typ =
  try SMap.find x g with
  | Not_found -> raise (NotFound x)
;;

(* extend a context with a new variable-typ association *)
(* throw a DuplicateVar exception if the variable already exists in g *)
let extend (g : ctx) (x : string) (t : typ) : ctx = SMap.add x t g

(* return the type of a term in the given context *)
(* return None if the term is ill-typed *)
let rec type_of (g : ctx) (t : term) : typ option =
  match t with
  | TmTrue | TmFalse -> Some TBool
  | TmVar v ->
    (try Some (lookup g v) with
     | NotFound _ -> None)
  | TmZero -> Some TNat
  | (TmSucc n | TmPred n) when type_of g n = Some TNat -> Some TNat
  | TmIsZero n when type_of g n = Some TNat -> Some TBool
  | TmIf (cond, ifTrue, ifFalse) when type_of g cond = Some TBool ->
    let ifTrueT, ifFalseT = type_of g ifTrue, type_of g ifFalse in
    if ifTrueT = ifFalseT then ifTrueT else None
  | TmAbs (v, typ, body) ->
    (match type_of (extend g v typ) body with
     | Some res -> Some (TFun (typ, res))
     | None -> None)
  | TmApp (left, right) ->
    (match type_of g left with
     | Some (TFun (arg, ret)) when type_of g right = Some arg -> Some ret
     | _ -> None)
  | _ -> None
;;

(* Interpreter *)

(* This is for you to debug your code. *)
(* The current interpret function will parse a term and return its type in
   the empty context. *)
(* You're encouraged to add additional tests. *)

let rec typ_to_string (t : typ) : string =
  match t with
  | TBool -> "Bool"
  | TNat -> "Nat"
  | TFun (t1, t2) -> "(" ^ typ_to_string t1 ^ "->" ^ typ_to_string t2 ^ ")"
;;

let rec term_to_string (t : term) : string =
  match t with
  | TmVar str -> str
  | TmAbs (var, tp, body) ->
    "&" ^ var ^ ":" ^ typ_to_string tp ^ "." ^ term_to_string body
  | TmApp (t1, t2) -> "(" ^ term_to_string t1 ^ ") (" ^ term_to_string t2 ^ ")"
  | TmTrue -> "True"
  | TmFalse -> "False"
  | TmZero -> "0"
  | TmIf (t1, t2, t3) ->
    "If "
    ^ term_to_string t1
    ^ " Then "
    ^ term_to_string t2
    ^ " Else "
    ^ term_to_string t3
  | TmSucc t1 -> "Succ " ^ term_to_string t1
  | TmPred t1 -> "Pred " ^ term_to_string t1
  | TmIsZero t1 -> "IsZero " ^ term_to_string t1
;;

let opt_typ_to_string (o : typ option) : string =
  match o with
  | None -> " "
  | Some t -> typ_to_string t
;;

let interpret (str : string) : unit =
  let chars = string_to_char_list str in
  let tokens = scan chars in
  let ast = parse tokens in
  let term_str = term_to_string ast in
  let _ = print_endline "----- Type Checking -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline (": " ^ opt_typ_to_string (type_of empty_ctx ast)) in
  print_endline ""
;;

interpret Sys.argv.(1)
