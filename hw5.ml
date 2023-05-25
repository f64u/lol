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
  | LCurly
  | RCurly
  | LSquare
  | RSquare
  | TokLam
  | TokDot
  | TokVar of string
  | TokIf
  | TokThen
  | TokFst
  | TokSnd
  | TokElse
  | TokZero
  | TokSucc
  | TokPred
  | TokIsZero
  | TokColon
  | TokBool
  | TokTrue
  | TokFalse
  | TokOf
  | TokNat
  | TokArrow
  | TokFatArrow
  | TokCross
  | TokPlus
  | TokWith
  | TokNil
  | TokCons
  | TokIsNil
  | TokHead
  | TokUnit
  | TokTail
  | TokBar
  | TokCase
  | TokComma
  | TokInl
  | TokInr

type typ =
  | TUnit
  | TBool
  | TNat
  | TFun of typ * typ
  | TProd of typ * typ
  | TSum of typ * typ
  | TList of typ

type term =
  | TmVar of string
  | TmAbs of string * typ * term
  | TmApp of term * term
  | TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmSucc of term
  | TmZero
  | TmPred of term
  | TmIsZero of term
  | TmUnit
  | TmPair of term * term
  | TmFst of term
  | TmSnd of term
  | TmInl of typ * term
  | TmInr of typ * term
  | TmCase of
      term
      * string
      * term
      * string
      * term (* case term1 of inl string1 => term2 | inr string2 => term3 *)
  | TmNil of typ
  | TmCons of typ * term * term
  | TmIsNil of typ * term
  | TmHead of typ * term
  | TmTail of typ * term

(* Utilities *)

let string_to_char_list (s : string) : char list = s |> String.to_seq |> List.of_seq
let char_list_to_string (cl : char list) : string = cl |> List.to_seq |> String.of_seq

(* The tokenizer, lexer and parser are provided for you. *)

let varStart (c : char) : bool =
  match c with
  | 'a' .. 'z' -> true
  | _ -> false
;;

let validVar (c : char) : bool =
  match c with
  | 'a' .. 'z' -> true
  | 'A' .. 'Z' -> true
  | '0' .. '9' -> true
  | _ -> false
;;

let rec nextVar (cs : char list) : char list * char list =
  match cs with
  | [] -> [], []
  | c :: tl ->
    if validVar c
    then (
      match nextVar tl with
      | var, rem -> c :: var, rem)
    else [], c :: tl
;;

let rec nextToken (cs : char list) : (token * char list) option =
  match cs with
  | '0' :: tl -> Some (TokZero, tl)
  | 'X' :: tl -> Some (TokCross, tl)
  | '+' :: tl -> Some (TokPlus, tl)
  | 'o' :: 'f' :: tl -> Some (TokOf, tl)
  | 'u' :: 'n' :: 'i' :: 't' :: tl -> Some (TokUnit, tl)
  | 'c' :: 'a' :: 's' :: 'e' :: tl -> Some (TokCase, tl)
  | 'S' :: 'u' :: 'c' :: 'c' :: tl -> Some (TokSucc, tl)
  | 'P' :: 'r' :: 'e' :: 'd' :: tl -> Some (TokPred, tl)
  | 'T' :: 'r' :: 'u' :: 'e' :: tl -> Some (TokTrue, tl)
  | 'F' :: 'a' :: 'l' :: 's' :: 'e' :: tl -> Some (TokFalse, tl)
  | 'I' :: 'f' :: tl -> Some (TokIf, tl)
  | 'T' :: 'h' :: 'e' :: 'n' :: tl -> Some (TokThen, tl)
  | 'E' :: 'l' :: 's' :: 'e' :: tl -> Some (TokElse, tl)
  | 'I' :: 's' :: 'Z' :: 'e' :: 'r' :: 'o' :: tl -> Some (TokIsZero, tl)
  | 'B' :: 'o' :: 'o' :: 'l' :: tl -> Some (TokBool, tl)
  | 'N' :: 'a' :: 't' :: tl -> Some (TokNat, tl)
  | 'n' :: 'i' :: 'l' :: tl -> Some (TokNil, tl)
  | 'c' :: 'o' :: 'n' :: 's' :: tl -> Some (TokCons, tl)
  | 'w' :: 'i' :: 't' :: 'h' :: tl -> Some (TokWith, tl)
  | 'i' :: 's' :: 'n' :: 'i' :: 'l' :: tl -> Some (TokIsNil, tl)
  | 'h' :: 'e' :: 'a' :: 'd' :: tl -> Some (TokHead, tl)
  | 't' :: 'a' :: 'i' :: 'l' :: tl -> Some (TokTail, tl)
  | 'f' :: 's' :: 't' :: tl -> Some (TokFst, tl)
  | 's' :: 'n' :: 'd' :: tl -> Some (TokSnd, tl)
  | 'i' :: 'n' :: 'l' :: tl -> Some (TokInl, tl)
  | 'i' :: 'n' :: 'r' :: tl -> Some (TokInr, tl)
  | '-' :: '>' :: tl -> Some (TokArrow, tl)
  | '=' :: '>' :: tl -> Some (TokFatArrow, tl)
  | ':' :: tl -> Some (TokColon, tl)
  | '(' :: tl -> Some (LParen, tl)
  | '{' :: tl -> Some (LCurly, tl)
  | '[' :: tl -> Some (LSquare, tl)
  | ']' :: tl -> Some (RSquare, tl)
  | '}' :: tl -> Some (RCurly, tl)
  | ')' :: tl -> Some (RParen, tl)
  | '|' :: tl -> Some (TokBar, tl)
  | '&' :: tl -> Some (TokLam, tl)
  | '.' :: tl -> Some (TokDot, tl)
  | ',' :: tl -> Some (TokComma, tl)
  | ' ' :: tl -> nextToken tl
  | c :: tl ->
    if varStart c
    then (
      match nextVar (c :: tl) with
      | var, rem -> Some (TokVar (char_list_to_string var), rem))
    else raise Parse_exn
  | [] -> None
;;

let rec scan (ls : char list) : token list =
  match nextToken ls with
  | Some (tok, tl) -> tok :: scan tl
  | None -> []
;;

let rec nextType (ts : token list) : (typ * token list) option =
  match ts with
  | TokNat :: tl -> Some (TNat, tl)
  | TokBool :: tl -> Some (TBool, tl)
  | TokUnit :: tl -> Some (TUnit, tl)
  | LParen :: tl ->
    (match tl with
     | TokCross :: tl' ->
       (match nextType tl' with
        | Some (ty0, tl'') ->
          (match nextType tl'' with
           | Some (ty1, tl''') -> Some (TProd (ty0, ty1), tl''')
           | _ -> raise Parse_exn)
        | _ -> raise Parse_exn)
     | TokPlus :: tl' ->
       (match nextType tl' with
        | Some (ty0, tl'') ->
          (match nextType tl'' with
           | Some (ty1, tl''') -> Some (TSum (ty0, ty1), tl''')
           | _ -> raise Parse_exn)
        | _ -> raise Parse_exn)
     | TokArrow :: tl' ->
       (match nextType tl' with
        | Some (ty0, tl'') ->
          (match nextType tl'' with
           | Some (ty1, tl''') -> Some (TFun (ty0, ty1), tl''')
           | _ -> raise Parse_exn)
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | LSquare :: tl ->
    (match nextType tl with
     | Some (ty0, RSquare :: tl') -> Some (TList ty0, tl')
     | _ -> raise Parse_exn)
  | _ -> raise Parse_exn
;;

let rec nextTerm (ts : token list) : (term * token list) option =
  match ts with
  | TokVar var :: tks -> Some (TmVar var, tks)
  | LParen :: tks ->
    (match nextTerm tks with
     | Some (tm0, RParen :: LParen :: tks') ->
       (match nextTerm tks' with
        | Some (tm1, RParen :: tks'') -> Some (TmApp (tm0, tm1), tks'')
        | _ -> raise Parse_exn)
     | Some (tm1, TokComma :: tks'') ->
       (match nextTerm tks'' with
        | Some (tm2, RParen :: tks''') -> Some (TmPair (tm1, tm2), tks''')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokLam :: TokVar var :: TokColon :: tl ->
    (match nextType tl with
     | Some (ty0, TokDot :: tl') ->
       (match nextTerm tl' with
        | Some (tm0, tl'') -> Some (TmAbs (var, ty0, tm0), tl'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokTrue :: tl -> Some (TmTrue, tl)
  | TokFalse :: tl -> Some (TmFalse, tl)
  | TokIf :: tl ->
    (match nextTerm tl with
     | Some (tm0, TokThen :: tl') ->
       (match nextTerm tl' with
        | Some (tm1, TokElse :: tl'') ->
          (match nextTerm tl'' with
           | Some (tm2, tl''') -> Some (TmIf (tm0, tm1, tm2), tl''')
           | _ -> raise Parse_exn)
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokZero :: tl -> Some (TmZero, tl)
  | TokIsZero :: tl ->
    (match nextTerm tl with
     | Some (trm, tl0) -> Some (TmIsZero trm, tl0)
     | _ -> raise Parse_exn)
  | TokPred :: tl ->
    (match nextTerm tl with
     | Some (trm, tl0) -> Some (TmPred trm, tl0)
     | _ -> raise Parse_exn)
  | TokSucc :: tl ->
    (match nextTerm tl with
     | Some (trm, tl0) -> Some (TmSucc trm, tl0)
     | _ -> raise Parse_exn)
  | LCurly :: tks ->
    (match nextTerm tks with
     | Some (tm0, TokComma :: tks') ->
       (match nextTerm tks' with
        | Some (tm1, RCurly :: tks'') -> Some (TmPair (tm0, tm1), tks'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokUnit :: tl -> Some (TmUnit, tl)
  | TokFst :: tks ->
    (match nextTerm tks with
     | Some (tm0, tks') -> Some (TmFst tm0, tks')
     | _ -> raise Parse_exn)
  | TokSnd :: tks ->
    (match nextTerm tks with
     | Some (tm0, tks') -> Some (TmSnd tm0, tks')
     | _ -> raise Parse_exn)
  | TokHead :: tl ->
    (match nextType tl with
     | Some (TList ty0, tl') ->
       (match nextTerm tl' with
        | Some (tm0, tl'') -> Some (TmHead (ty0, tm0), tl'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokTail :: tl ->
    (match nextType tl with
     | Some (TList ty0, tl') ->
       (match nextTerm tl' with
        | Some (tm0, tl'') -> Some (TmTail (ty0, tm0), tl'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokNil :: tl ->
    (match nextType tl with
     | Some (TList ty0, tl') -> Some (TmNil ty0, tl')
     | _ -> raise Parse_exn)
  | TokCons :: tl ->
    (match nextType tl with
     | Some (TList ty0, tl') ->
       (match nextTerm tl' with
        | Some (tm0, tl'') ->
          (match nextTerm tl'' with
           | Some (tm1, tl''') -> Some (TmCons (ty0, tm0, tm1), tl''')
           | _ -> raise Parse_exn)
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokIsNil :: tl ->
    (match nextType tl with
     | Some (TList ty0, tl') ->
       (match nextTerm tl' with
        | Some (tm0, tl'') -> Some (TmIsNil (ty0, tm0), tl'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokInl :: tl ->
    (match nextTerm tl with
     | Some (tm0, TokWith :: tl') ->
       (match nextType tl' with
        | Some (ty0, tl'') -> Some (TmInl (ty0, tm0), tl'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokInr :: tl ->
    (match nextTerm tl with
     | Some (tm0, TokWith :: tl') ->
       (match nextType tl' with
        | Some (ty0, tl'') -> Some (TmInr (ty0, tm0), tl'')
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | TokCase :: tl ->
    (match nextTerm tl with
     | Some (tm0, TokOf :: TokInl :: TokVar x1 :: TokFatArrow :: tl') ->
       (match nextTerm tl' with
        | Some (tm1, TokBar :: TokInr :: TokVar x2 :: TokFatArrow :: tl'') ->
          (match nextTerm tl'' with
           | Some (tm2, tl''') -> Some (TmCase (tm0, x1, tm1, x2, tm2), tl''')
           | _ -> raise Parse_exn)
        | _ -> raise Parse_exn)
     | _ -> raise Parse_exn)
  | _ -> raise Parse_exn
;;

let parse (tokens : token list) : term =
  match nextTerm tokens with
  | Some (trm, []) -> trm
  | _ -> raise Parse_exn
;;

(* Derived forms *)

let rec fv = function
  | TmTrue | TmFalse | TmUnit | TmZero | TmNil _ -> SS.empty
  | TmIf (x, y, z) -> SS.union (SS.union (fv x) (fv y)) (fv z)
  | TmSucc t
  | TmPred t
  | TmIsZero t
  | TmFst t
  | TmSnd t
  | TmHead (_, t)
  | TmTail (_, t)
  | TmInl (_, t)
  | TmIsNil (_, t)
  | TmInr (_, t) -> fv t
  | TmPair (t0, t1) | TmApp (t0, t1) | TmCons (_, t0, t1) -> SS.union (fv t0) (fv t1)
  | TmCase (t0, s1, t1, s2, t2) ->
    SS.union
      (fv t0)
      (SS.union (SS.diff (fv t1) (SS.singleton s1)) (SS.diff (fv t2) (SS.singleton s1)))
  | TmVar x -> SS.singleton x
  | TmAbs (v, _, body) -> SS.diff (fv body) (SS.singleton v)
;;

let fresh_var (vars : SS.t) : string =
  match SS.max_elt_opt vars with
  | Some v -> v ^ "0"
  | None -> "x"
;;

(* Implement the derived forms t;t, let x : T = t in t, option T
   and option case from the book and class. *)
(* In t;t, the first t should have type unit. *)
(* In let, note that x is annotated with a type.  *)
(* option T use a sum type to encode an option type *)
(* option case should case on None and Some t, returning a term for each case *)

let tm_seq (t1 : term) (t2 : term) : term =
  TmApp (TmAbs (fresh_var (fv t2), TUnit, t2), t1)
;;

let tm_let (x : string) (tp : typ) (t1 : term) (t2 : term) : term =
  TmApp (TmAbs (x, tp, t2), t1)
;;

let tp_opt (tp : typ) : typ = TSum (TUnit, tp)
let tm_some (t : term) : term = TmInr (TUnit, t)
let tm_none (t : typ) : term = TmInl (t, TmUnit)

let tm_opt_case (t : term) (t_some : string -> term) (t_none : term) : term =
  let fresh_v = fresh_var (fv t_none) in
  TmCase (t, fresh_v, t_none, "x", t_some "x")
;;

(* Small-step evaluation *)

let ( <$> ) (f : term -> term) (t : term) : term =
  match t with
  | TmFalse -> TmFalse
  | TmTrue -> TmTrue
  | TmZero -> TmZero
  | TmUnit -> TmUnit
  | TmNil _ as t0 -> t0
  | TmVar _ as t0 -> t0
  | TmAbs (v, typ, t0) -> TmAbs (v, typ, f t0)
  | TmIf (t0, t1, t2) -> TmIf (f t0, f t1, f t2)
  | TmSucc t0 -> TmSucc (f t0)
  | TmPred t0 -> TmPred (f t0)
  | TmIsZero t0 -> TmIsZero (f t0)
  | TmApp (t0, t1) -> TmApp (f t0, f t1)
  | TmHead (tp, t0) -> TmHead (tp, f t0)
  | TmTail (tp, t0) -> TmTail (tp, f t0)
  | TmIsNil (tp, t0) -> TmIsNil (tp, f t0)
  | TmCons (tp, t0, t1) -> TmCons (tp, f t0, f t0)
  | TmPair (t0, t1) -> TmPair (f t0, f t1)
  | TmFst t0 -> TmFst (f t0)
  | TmSnd t0 -> TmSnd (f t0)
  | TmInl (tp, t0) -> TmInl (tp, f t0)
  | TmInr (tp, t0) -> TmInr (tp, f t0)
  | TmCase (t0, s1, t1, s2, t2) -> TmCase (f t0, s1, f t1, s2, f t2)
;;

let rec rename (f : string) (t : string) (term : term) : term =
  match term with
  | TmVar v when v = f -> TmVar t
  | TmAbs (v, _, _) as t0 when v = f -> t0
  | TmAbs (v, _, _) as t0 when v = t -> t0 |> alpha_convert (SS.singleton t) |> rename f t
  | TmCase (t0, s1, t1, s2, t2) ->
    let s1', t1' =
      if s1 = t
      then (
        let new_s = fresh_var (SS.singleton t) in
        new_s, t1 |> rename t new_s |> rename f t)
      else s1, t1
    in
    let s2', t2' =
      if s2 = t
      then (
        let new_s = fresh_var (SS.singleton t) in
        new_s, t2 |> rename t new_s |> rename f t)
      else s2, t2
    in
    TmCase (rename f t t0, s1', t1', s2', t2')
  | t0 -> rename f t <$> t0

and alpha_convert (vars : SS.t) (t : term) : term =
  match t with
  | TmAbs (v, typ, body) ->
    let v' = fresh_var (SS.add v vars) in
    TmAbs (v', typ, rename v v' body)
  | TmCase (t0, s1, t1, s2, t2) ->
    let s1' = fresh_var (SS.add s1 vars) in
    let s2' = fresh_var (SS.add s2 vars) in
    TmCase (t0, s1', rename s1 s1' t1, s2', rename s2 s2' t2)
  | _ -> raise (NotAbs "error")
;;

let rec subst (x : string) (s : term) (t : term) : term =
  let free_vars = fv s in
  match t with
  | TmVar v when v = x -> s
  | TmAbs (v, _, _) as t0 when v = x -> t0
  | TmAbs (v, _, _) as t0 when SS.mem v free_vars ->
    t0 |> alpha_convert SS.empty |> subst x s
  | TmCase (t0, s1, t1, s2, t2) as case' when SS.mem s1 free_vars || SS.mem s2 free_vars
    -> case' |> alpha_convert SS.empty |> subst x s
  | TmCase (t0, s1, t1, s2, t2) ->
    TmCase
      ( subst x s t0
      , s1
      , (if s1 = x then Fun.id else subst x s) t1  (* for when x bounds are already captured by the case's var *)
      , s2
      , (if s2 = x then Fun.id else subst x s) t2 )
  | t0 -> subst x s <$> t
;;

(* Implement the small-step evaluation relations from class. 
   Note that we're only concerned with call-by-value for this homework. 
   Feel free to reuse code from homework 3. 
   (Implementing capture-avoiding substitution is encouraged, but not what we 
   will be grading this on) *)


let rec is_num_val = function
  | TmZero -> true
  | TmSucc v when is_num_val v -> true
  | _ -> false

let rec is_list_val = function
  | TmNil _ -> true
  | TmCons (_, h, tail) -> is_val h && is_list_val tail
  | _ -> false

and is_val = function
  | TmTrue | TmFalse | TmUnit | TmAbs (_, _, _) -> true
  | TmPair (t0, t1) -> is_val t0 && is_val t1
  | TmInl (_, t0) | TmInr (_, t0) -> is_val t0
  | v            -> is_num_val v || is_list_val v


let rec cbv (t : term) : term option =
  let ( >> ) (t : term) (constructor : term -> term) : term option =
    match cbv t with
    | None -> None
    | Some t0' -> Some (constructor t0') in
  match t with
  | TmApp (TmAbs (x, _, body), t0) when is_val t0 ->
      Some (subst x t0 body)
  | TmApp ((TmAbs (_, _, _) as func), input) ->
    (match cbv input with
    | None -> None
    | Some input' -> Some (TmApp (func, input')))
  | TmApp (func, input) -> (
      match cbv func with
      | None -> None
      | Some func' -> Some (TmApp (func', input)))

  | TmIf (TmTrue, t1, _) -> Some t1
  | TmIf (TmFalse, _, t2) -> Some t2
  | TmIf (t0, t1, t2) -> t0 >> (fun t0' -> TmIf (t0', t1, t2))

  | TmSucc t0 -> t0 >> (fun t0' -> TmSucc t0')

  | TmPred TmZero -> Some TmZero
  | TmPred (TmSucc t0) when is_num_val t0 -> Some t0
  | TmPred t0 -> t0 >> (fun t0' -> TmPred t0')

  | TmIsZero TmZero -> Some TmTrue
  | TmIsZero (TmSucc t0) when is_num_val t0 -> Some TmFalse
  | TmIsZero t0 -> t0 >> (fun t0' -> TmIsZero t0')

  | TmPair (t0, t1) ->
    if is_val t0 then (
      if is_val t1 then None
      else t1 >> (fun t1' -> TmPair (t0, t1'))
    ) else t0 >> (fun t0' -> TmPair (t0', t1))

  | TmFst (TmPair (t0, t1) as pair) when is_val pair -> Some t0
  | TmFst t0 -> t0 >> (fun t0' -> TmFst t0')

  | TmSnd (TmPair (t0, t1) as pair) when is_val pair -> Some t1
  | TmSnd t0 -> t0 >> (fun t0' -> TmSnd t0')

  | TmInl (tp, t0) -> t0 >> (fun t0' -> TmInl (tp, t0'))

  | TmInr (tp, t0) -> t0 >> (fun t0' -> TmInr (tp, t0'))

  | TmCase (TmInl (_, s), s1, t1, _, _) when is_val s -> Some (subst s1 s t1)
  | TmCase (TmInr (_, s), _, _, s2, t2) when is_val s -> Some (subst s2 s t2)
  | TmCase (t0, s1, t1, s2, t2) ->
    t0 >> (fun t0' -> TmCase (t0', s1, t1, s2, t2))

  | TmCons (_, _, _) as lst when is_list_val lst -> None
  | TmCons (tp, t0, t1) when is_val t0 ->
    t1 >> (fun t1' -> TmCons (tp, t0, t1'))
  | TmCons (tp, t0, t1) -> t0 >> (fun t0' -> TmCons (tp, t0', t1))

  | TmIsNil (_, TmNil _) -> Some TmTrue
  | TmIsNil (_, plst) when is_list_val plst -> Some TmFalse

  | TmHead (_, TmNil tp) -> Some (tm_none tp)
  | TmHead (_, (TmCons (_, h, _) as plst)) when is_list_val plst -> Some (tm_some h)
  | TmHead (tp, t0) -> t0 >> (fun t0' -> TmHead (tp, t0'))

  | TmTail (_, (TmNil _ as nil)) -> Some nil
  | TmTail (_, (TmCons (_, _, t) as plst)) when is_list_val plst -> Some t
  | TmTail (tp, t0) -> t0 >> (fun t0' -> TmTail (tp, t0'))
  | _ -> None
 
  
let multistep (t : term) : term option =
  let rec normal_multistep (t : term) : term =
    match cbv t with
    | None -> t
    | Some t' -> normal_multistep t'
  in Some (normal_multistep t)

(* Typechecking utilities *)

(* These first few functions can be copied from prior homeworks. 
   We will try to give solutions shortly after the late deadline. *)

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
let extend (g : ctx) (x : string) (t : typ) : ctx = SMap.add x t g

(* return the type of a term in the given context *)
(* return None if the term is ill-typed *)
let rec type_of (g : ctx) (t : term) : typ option =
  match t with
  | TmVar v ->
    (try Some (lookup g v) with
    | NotFound _ -> None)
  | TmAbs (v, typ, body) ->
    (match type_of (extend g v typ) body with
    | Some res -> Some (TFun (typ, res))
    | None -> None)
  | TmApp (left, right) ->
    (match type_of g left with
    | Some (TFun (arg, ret)) when type_of g right = Some arg -> Some ret
    | _ -> None)
  | TmIf (cond, ifTrue, ifFalse) when type_of g cond = Some TBool ->
    let ifTrueT, ifFalseT = type_of g ifTrue, type_of g ifFalse in
    if ifTrueT = ifFalseT then ifTrueT else None
  | TmTrue | TmFalse -> Some TBool
  | TmZero -> Some TNat
  | (TmSucc n | TmPred n) when type_of g n = Some TNat -> Some TNat
  | TmIsZero n when type_of g n = Some TNat -> Some TBool
  | TmUnit -> Some TUnit
  | TmPair (left, right) ->
    (match (type_of g left, type_of g right) with
    | (Some t_left, Some t_right) -> Some (TProd (t_left, t_right))
    | _ -> None)
  | TmFst pair -> 
    (match type_of g pair with
    | Some (TProd (t_left, _)) -> Some t_left
    | _ -> None)
  | TmSnd pair -> 
    (match type_of g pair with
    | Some (TProd (_, t_right)) -> Some t_right
    | _ -> None)
  | TmInl (tp, v) ->
    (match type_of g v with
    | Some o -> Some (TSum (o, tp))
    | _ -> None)
  | TmInr (tp, v) ->
    (match type_of g v with
    | Some o -> Some (TSum (tp, o))
    | _ -> None)
  | TmCase (t0, s1, t1, s2, t2) -> 
    let t = type_of g t0 in
    (match t with
    | Some (TSum (tl, tr)) -> 
      (match (type_of (extend g s1 tl) t1, type_of (extend g s2 tr) t2) with
      | (Some a, Some b) when a = b -> Some a
      | _ -> None)
    | _ -> None)
  | TmNil tp -> Some (TList tp)
  | TmCons (tp, h, t) when type_of g h = Some tp && type_of g t = Some (TList tp) -> Some (TList tp)
  | TmIsNil (tp, t) when type_of g t = Some (TList tp) -> Some TBool
  | TmHead (tp, t) when type_of g t = Some (TList tp) -> Some (tp_opt tp)
  | TmTail (tp, t) when type_of g t = Some (TList tp) -> Some (TList tp)
  | _ -> None
;;

(* Interpreter *)

(* This is for you to debug your code. *)
(* The current interpret function will parse a term and return its
  type in the empty context. *)
(* You're encouraged to add additional tests. *)

let rec typ_to_string (t : typ) : string =
  match t with
  | TBool -> "Bool"
  | TNat -> "Nat"
  | TFun (t1, t2) -> "(" ^ typ_to_string t1 ^ "->" ^ typ_to_string t2 ^ ")"
  | TList t1 -> "[" ^ typ_to_string t1 ^ "]"
  | TProd (t1, t2) -> typ_to_string t1 ^ " X " ^ typ_to_string t2
  | TSum (t1, t2) -> typ_to_string t1 ^ " + " ^ typ_to_string t2
  | TUnit -> "Unit"
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
  | TmCase (t0, x1, t1, x2, t2) ->
    "case "
    ^ term_to_string t0
    ^ " of inl "
    ^ x1
    ^ " => "
    ^ term_to_string t1 ^
    " | inr "
    ^ x2
    ^ " => "
    ^ term_to_string t2
  | TmInl (ty, tm) -> "inl " ^ term_to_string tm ^ " with " ^ typ_to_string ty
  | TmInr (ty, tm) -> "inr " ^ term_to_string tm ^ " with " ^ typ_to_string ty
  | TmNil ty -> "nil[" ^ typ_to_string ty ^ "]"
  | TmCons (ty, tm1, tm2) ->
    "cons[" ^ typ_to_string ty ^ "] " ^ term_to_string tm1 ^ " " ^ term_to_string tm2
  | TmIsNil (ty, tm) -> "isnil[" ^ typ_to_string ty ^ "] " ^ term_to_string tm
  | TmHead (ty, tm) -> "head[" ^ typ_to_string ty ^ "] " ^ term_to_string tm
  | TmTail (ty, tm) -> "tail[" ^ typ_to_string ty ^ "] " ^ term_to_string tm
  | TmFst tm -> "fst " ^ term_to_string tm
  | TmSnd tm -> "snd " ^ term_to_string tm
  | TmUnit -> "unit"
  | TmPair (tm1, tm2) -> "{ " ^ term_to_string tm1 ^ " , " ^ term_to_string tm2 ^ " }"
;;

let opt_typ_to_string (o : typ option) : string =
  match o with
  | None -> " "
  | Some t -> typ_to_string t
;;

let convert (s : string) : term =
  let chars = string_to_char_list s in
  let tokens = scan chars in
  let ast = parse tokens in
  ast
;;

let opt_term_to_string (o : term option) : string = 
  match o with
  | None -> " "
  | Some t -> term_to_string t 
;;

let interpret (str : string) : unit =
  let ast = convert str in
  let term_str = term_to_string ast in
  let _ = print_endline "----- Type Checking -----" in
  let _ = print_endline ("      " ^ term_str) in
  let _ = print_endline (": " ^ opt_typ_to_string (type_of empty_ctx ast)) in
  print_endline ""
;;

let execute (str : string) : unit =
  let ast = convert str in
  let term_str = term_to_string ast in
  let ss_term_str = opt_term_to_string (cbv ast) in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline ("----- Small Step Evaluation -----") in
  let _ = print_endline ("      " ^ term_str) in 
  let _ = print_endline ("->    " ^ ss_term_str) in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline "-----" in
  let _ = print_endline "----- Big Step Evaluation -----" in
  let _ = print_endline ("      " ^ term_str) in 
  let _ = print_endline (": " ^ opt_term_to_string (multistep ast)) in
  print_endline ""
;;

(*
let quit_loop = ref false in
  while not !quit_loop do
    print_string "> ";
    let str = read_line () in
      if str = "" then quit_loop := true
      else (interpret str);execute str
  done;;
*)

interpret Sys.argv.(1)
