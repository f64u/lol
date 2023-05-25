module SS = Set.Make (String)
module SMap = Map.Make (String)
module IMap = Map.Make (Int)

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

type label = string

type typ =
  | TUnit
  | TBool
  | TNat
  | TFun of typ * typ
  | TVariant of (label * typ) list
  | TRef of typ

type term =
  | TmVar of string
  | TmAbs of string * typ * term
  | TmApp of term * term
  | TmUnit
  | TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVariant of label * term * typ (* eg. red 6 as [red:Nat; blue:Nat] *)
  | TmCase of
      term
      * (label * string * term) list (* eg. case red 2 of [red x => 5 | blue y => 9] *)
  | TmRef of term
  | TmLoc of int
  | TmBang of term (* !t *)
  | TmAssn of term * term
  | TmRaise of term
  | TmTry of term * term
  | TmNull
  | TmIsNull of typ * term

(* Utilities *)

let string_to_char_list (s : string) : char list = s |> String.to_seq |> List.of_seq
let char_list_to_string (cl : char list) : string = cl |> List.to_seq |> String.of_seq

(* The tokenizer, lexer and parser are provided for you. *)

let rec nextToken (cs : char list) : (token * char list) option = raise Not_implemented
let rec scan (ls : char list) : token list = raise Not_implemented
let rec nextTerm (ts : token list) : (term * token list) option = raise Not_implemented
let parse (tokens : token list) : term = raise Not_implemented

(* Variants *)

(* Implement an option type, some and none as variants *)

let tp_opt (tp : typ) : typ = TVariant [ "some", tp; "none", TUnit ]
let tm_some (t : term) (tp : typ) : term = TmVariant ("some", t, tp_opt tp)
let tm_none (tp : typ) : term = TmVariant ("none", TmUnit, tp_opt tp)

(* Implement an exception type as a variant. 
   There are at least three possible exceptions that you should be able to handle. 
   (These should become clear as you progress through the homework, but feel free to start
    with some obvious candidates.) *)

let tp_exn : typ =
  TVariant
    [ "null_pointer_exception", TUnit
    ; "location_not_found", TUnit
    ; "no_matching_case", TUnit
    ]
;;

let tm_raise_null : term = TmRaise (TmVariant ("null_pointer_exception", TmUnit, tp_exn))
let tm_raise_nopat : term = TmRaise (TmVariant ("no_matching_case", TmUnit, tp_exn))
let tm_raise_invmem : term = TmRaise (TmVariant ("location_not_found", TmUnit, tp_exn))

(* Small-step evaluation *)

module SSS = Set.Make (SS)

let rec fv = function
  | TmTrue | TmFalse | TmUnit | TmZero | TmNull | TmLoc _ -> SS.empty
  | TmVar x -> SS.singleton x
  | TmSucc t0
  | TmPred t0
  | TmIsZero t0
  | TmVariant (_, t0, _)
  | TmRef t0
  | TmBang t0
  | TmRaise t0
  | TmIsNull (_, t0) -> fv t0
  | TmApp (t0, t1) | TmAssn (t0, t1) | TmTry (t0, t1) -> SS.union (fv t0) (fv t1)
  | TmAbs (x, _, body) -> SS.diff (fv body) (SS.singleton x)
  | TmIf (t0, t1, t2) -> SS.union (SS.union (fv t0) (fv t1)) (fv t2)
  | TmCase (t0, lst) ->
    SS.union
      (fv t0)
      (lst
       |> List.map (fun (_, x, t') -> SS.diff (fv t0) (SS.singleton x))
       |> SSS.of_list
       |> fun s -> SSS.fold SS.union s SS.empty)
;;

let fresh_var (vars : SS.t) : string =
  match SS.max_elt_opt vars with
  | Some v -> v ^ "0"
  | None -> "x"
;;

let ( <$> ) (f : term -> term) (t : term) : term =
  match t with
  | (TmFalse | TmTrue | TmZero | TmUnit | TmNull | TmVar _ | TmLoc _) as t0 -> t0
  | TmAbs (v, typ, t0) -> TmAbs (v, typ, f t0)
  | TmIf (t0, t1, t2) -> TmIf (f t0, f t1, f t2)
  | TmSucc t0 -> TmSucc (f t0)
  | TmPred t0 -> TmPred (f t0)
  | TmIsZero t0 -> TmIsZero (f t0)
  | TmApp (t0, t1) -> TmApp (f t0, f t1)
  | TmVariant (lbl, t0, typ) -> TmVariant (lbl, f t0, typ)
  | TmBang t0 -> TmBang (f t0)
  | TmRaise t0 -> TmRaise (f t0)
  | TmAssn (t0, t1) -> TmAssn (f t0, f t1)
  | TmIsNull (typ, t0) -> TmIsNull (typ, f t0)
  | TmRef t0 -> TmRef (f t0)
  | TmTry (t0, t1) -> TmTry (f t0, f t1)
  | TmCase (t0, lst) -> TmCase (f t0, List.map (fun (lbl, x, t') -> lbl, x, f t') lst)
;;

let rec rename (f : string) (t : string) (term : term) : term =
  match term with
  | TmVar x when x = f -> TmVar t
  | TmAbs (x, _, _) as t0 when x = f -> t0
  | TmAbs (x, _, _) as t0 when x = t -> t0 |> alpha_convert (SS.singleton t) |> rename f t
  | TmCase (t0, lst) ->
    TmCase
      ( rename f t t0
      , lst
        |> List.map (fun (lbl, x, t') ->
             if x = t
             then (
               let new_x = fresh_var (SS.singleton t) in
               let t'' = t' |> rename t new_x |> rename f t in
               lbl, new_x, t'')
             else if x = f
             then lbl, x, t'
             else lbl, x, rename f t t') )
  | t0 -> rename f t <$> t0

and alpha_convert (vars : SS.t) (t : term) : term =
  match t with
  | TmAbs (v, typ, body) ->
    let v' = fresh_var (SS.add v vars) in
    TmAbs (v', typ, rename v v' body)
  | _ -> raise (NotAbs "error")
;;

let rec subst (v : string) (s : term) (t : term) : term =
  let free_vars = fv s in
  match t with
  | TmVar x when x = v -> s
  | TmAbs (x, _, _) as t0 when x = v -> t0
  | TmAbs (x, _, _) as t0 when SS.mem x free_vars ->
    t0 |> alpha_convert SS.empty |> subst v s
  | TmCase (t0, lst) ->
    TmCase
      ( subst v s t
      , List.map
          (fun (lbl, x, t') ->
            if SS.mem x free_vars
            then (
              let new_x = fresh_var (SS.singleton x) in
              lbl, new_x, t' |> rename x new_x |> subst v s)
            else if x = v
            then lbl, x, t'
            else lbl, x, subst v s t')
          lst )
  | t0 -> subst v s <$> t
;;

(* Implement the small-step evaluation relations from class. 
   Note the presence of a store and the possibility of encountering 
   raise and null. *)

type store = term IMap.t

let rec is_num_val (t : term) : bool =
  match t with
  | TmZero -> true
  | TmSucc t' -> is_num_val t'
  | _ -> false
;;

let rec is_val (t : term) (mu : store) : bool =
  match t with
  | TmTrue | TmFalse | TmUnit | TmAbs (_, _, _) | TmNull -> true
  | TmLoc n -> IMap.mem n mu
  | TmVariant (lbl, t', typ) -> is_val t' mu (* should I care about type? *)
  | t' -> is_num_val t'
;;

let rec cbv (t : term) (mu : store) : (term * store) option =
  let ( >> ) ((t, mu) : term * store) (constructor : term -> term) : (term * store) option
    =
    match cbv t mu with
    | None -> None
    | Some ((TmRaise t0' as err), mu') -> Some (err, mu')
    | Some (t0', mu') -> Some (constructor t0', mu')
  in
  let ( >>+ ) ((t, mu) : term * store) (constructor : term -> term)
    : (term * store) option
    =
    if t = TmNull
    then
      Some (tm_raise_null, mu)
      (* t is what is tucked under something. If it's null, we don't want to step it *)
    else (t, mu) >> constructor
  in
  match t with
  | TmRaise (TmRaise t0) -> Some (TmRaise t0, mu)
  | TmRaise t0 when not (is_val t0 mu) -> (t0, mu) >> fun t0' -> TmRaise t0'
  | TmApp ((TmRaise t0 as err), _) when is_val t0 mu -> Some (err, mu)
  | TmApp (t0, (TmRaise t1 as err)) when is_val t0 mu && is_val t1 mu -> Some (err, mu)
  | TmApp (TmAbs (x, _, body), t0) when is_val t0 mu -> Some (subst x t0 body, mu)
  | TmApp ((TmAbs (_, _, _) as t0), t1) ->
    (t1, mu) >>+ (* it's never null but jic :) *) fun t1' -> TmApp (t0, t1')
  | TmApp (t0, t1) -> (t0, mu) >>+ fun t0' -> TmApp (t0', t1)
  | TmIf (TmTrue, t1, _) -> Some (t1, mu)
  | TmIf (TmFalse, _, t2) -> Some (t2, mu)
  | TmIf (t0, t1, t2) -> (t0, mu) >>+ fun t0' -> TmIf (t0', t1, t2)
  | TmSucc t0 -> (t0, mu) >>+ fun t0' -> TmSucc t0'
  | TmPred TmZero -> Some (TmZero, mu)
  | TmPred (TmSucc t0) when is_num_val t0 -> Some (t0, mu)
  | TmPred t0 -> (t0, mu) >>+ fun t0' -> TmPred t0'
  | TmIsZero TmZero -> Some (TmTrue, mu)
  | TmIsZero (TmSucc t0) when is_num_val t0 -> Some (TmFalse, mu)
  | TmIsZero t0 -> (t0, mu) >>+ fun t0' -> TmIsZero t0'
  | TmVariant (lbl, t0, typ) -> (t0, mu) >>+ fun t0' -> TmVariant (lbl, t0', typ)
  | TmCase (TmVariant (lbl, t0, _), lst) ->
    let matches = List.find_all (fun (lbl', _, _) -> lbl = lbl') lst in
    let length = List.length matches in
    if length = 0
    then Some (tm_raise_nopat, mu)
    else (
      let _, x, t' = List.hd matches in
      Some (subst x t0 t', mu))
  | TmCase (t0, lst) -> (t0, mu) >> fun t0' -> TmCase (t0', lst)
  | TmRef t0 when is_val t0 mu ->
    (match IMap.max_binding_opt mu with
     | Some (n, _) -> Some (TmLoc (n + 1), IMap.add (n + 1) t0 mu)
     | None -> Some (TmLoc 0, IMap.singleton 0 t0))
  | TmRef t0 ->
    (t0, mu)
    >> (* also shouldn't null, but *if* it does we want it *) fun t0' -> TmRef t0'
  | TmBang (TmLoc n) ->
    (match IMap.find_opt n mu with
     | None -> Some (tm_raise_invmem, mu)
     | Some t' -> Some (t', mu))
  | TmBang t0 -> (t0, mu) >>+ fun t0' -> TmBang t0'
  | TmAssn (TmLoc n, t1) when is_val t1 mu -> Some (TmUnit, IMap.add n t1 mu)
  | TmTry (t0, t1) when is_val t0 mu -> Some (t0, mu)
  | TmTry (TmRaise t0, t1) when is_val t0 mu -> Some (TmApp (t1, t0), mu)
  | TmTry (t0, t1) -> (t0, mu) >>+ fun t0' -> TmTry (t0', t1)
  | TmIsNull (_, TmNull) -> Some (TmTrue, mu)
  | TmIsNull (_, t0) when is_val t0 mu -> Some (TmFalse, mu)
  | TmIsNull (typ, t0) -> (t0, mu) >> (* :) *) fun t0' -> TmIsNull (typ, t0')
  | _ -> None
;;

let multistep (t : term) : term =
  let rec multistep_rec (t : term) (mu : store) : term =
    match cbv t mu with
    | Some (t', mu') -> multistep_rec t' mu'
    | None -> t
  in
  multistep_rec t IMap.empty
;;

(* Typechecking utilities *)

type ctx = typ SMap.t
type typ_store = typ IMap.t

let empty_ctx : ctx = SMap.empty
let empty_store : typ_store = IMap.empty

(* look up a given variable's typ, throw a NotFound exception if the variable is not found *)
let lookup (g : ctx) (x : string) : typ =
  match SMap.find_opt x g with
  | Some t -> t
  | None -> raise (NotFound x)
;;

(* extend a context with a new variable-typ association *)
let extend (g : ctx) (x : string) (t : typ) : ctx =
  if SMap.mem x g then raise (DuplicateVar x) else SMap.add x t g
;;

(* Typechecking *)

(* check if a term has the given type. *)
(* Takes in a context and a store, as well as a term t and type T *)
(* Returns true iff gamma | sigma |- t : T *)

let rec type_check (g : ctx) (s : typ_store) (t : term) (tp : typ) : bool =
  match t with
  | TmNull -> true
  | TmRaise t0 -> type_check g s t0 tp_exn
  | TmRef t0 ->
    (match tp with
     | TRef tp' -> type_check g s t0 tp'
     | _ -> false)
  | TmBang t0 -> type_check g s t0 (TRef tp)
  | TmAssn (left, right) ->
    (match type_infer g s left with
     | Some (TRef tp') -> type_check g s right tp' && tp = TUnit
     | Some _ -> false
     | None ->
       (match type_infer g s right with
        | Some tp' -> type_check g s left (TRef tp') && tp' = TUnit
        | _ -> false))
  | TmApp (left, right) ->
    (match type_infer g s left with
     | Some (TFun (argt, rett)) -> type_check g s right argt && rett = tp
     | None ->
       type_check g s left TUnit (* i.e., it type checks against (some|any)thing *)
       &&
       (match type_infer g s right with
        | Some _ -> true
        | None -> false)
     | _ -> false)
  | t' -> type_infer g s t' = Some tp

(* This should infer the type of a term in the given context *)
(* return None if the term is ill-typed OR the type cannot be inferred *)
(* You may want to use type_check or other helper functions in writing this. *)
and type_infer (g : ctx) (s : typ_store) (t : term) : typ option =
  match t with
  | TmNull | TmRaise _ -> None
  | TmVar x ->
    (try Some (lookup g x) with
     | NotFound _ -> None)
  | TmAbs (v, typ, body) ->
    (match type_infer (extend g v typ) s body with
     | Some res -> Some (TFun (typ, res))
     | None -> None)
  | TmApp (left, right) ->
    (match type_infer g s left with
     | Some (TFun (argt, rett)) when type_check g s right argt -> Some rett
     | _ -> None)
  | TmIf (cond, ifTrue, ifFalse) when type_check g s cond TBool ->
    (match type_infer g s ifTrue, type_infer g s ifFalse with
     | Some t0, Some t1 -> if t0 = t1 then Some t0 else None
     | Some t0, None -> if type_check g s ifFalse t0 then Some t0 else None
     | None, Some t1 -> if type_check g s ifTrue t1 then Some t1 else None
     | None, None -> None)
  | TmTrue | TmFalse -> Some TBool
  | TmZero -> Some TNat
  | (TmSucc n | TmPred n) when type_check g s n TNat -> Some TNat
  | TmIsZero n when type_check g s n TNat -> Some TBool
  | TmUnit -> Some TUnit
  | TmIsNull (typ, t0) (* type_check g s t0 typ ???*) -> Some TBool
  | TmRef t0 ->
    (match type_infer g s t0 with
     | Some tp' -> Some (TRef tp')
     | None -> None)
  | TmLoc i ->
    (match IMap.find_opt i s with
     | Some tp' -> Some (TRef tp')
     | None -> None)
  | TmBang t0 ->
    (match type_infer g s t0 with
     | Some (TRef tp') -> Some tp'
     | _ -> None)
  | TmAssn (t0, t1) ->
    (match type_infer g s t0, type_infer g s t1 with
     | (Some (TRef _) | None), Some tp' ->
       if type_check g s t0 (TRef tp') then Some TUnit else None
     | Some (TRef tp'), None -> if type_check g s t1 tp' then Some TUnit else None
     | _ -> None)
  | TmVariant (lbl, t0, tp') ->
    (match tp' with
     | TVariant lst ->
       if List.exists (fun (lbl', tp'') -> lbl = lbl' && type_check g s t0 tp'') lst
       then Some tp'
       else None
     | _ -> None)
  | TmTry (t0, t1) ->
    (match type_infer g s t0 with
     | Some tp' -> if type_check g s t1 (TFun (tp_exn, tp')) then Some tp' else None
     | None ->
       (match type_infer g s t1 with
        | Some (TFun (argt, rett)) -> if type_check g s t0 argt then Some rett else None
        | _ -> None))
  | TmCase (t0, lst) ->
    let l = List.length lst in
    if l = 0
    then None
    else (
      match type_infer g s t0 with
      | Some (TVariant lst') when List.length lst' = l ->
        let r =
          List.map
            (fun (lbl, x, t') ->
              let v = List.find_opt (fun (l, _) -> l = lbl) lst' in
              match v with
              | Some (lbl', tp) -> Some lbl', t', type_infer (extend g x tp) s t'
              | None -> None, t', None)
            lst
        in
        (match
           List.fold_left
             (fun (clbl, ct, ctp) (lbl, t, tp) ->
               if clbl = None || lbl = None
               then None, ct, None
               else if match ctp, tp with
                       | Some ctp', Some tp' -> ctp' = tp'
                       | None, Some tp' -> type_check g s ct tp'
                       | Some ctp', None -> type_check g s t ctp'
                       | None, None -> false
               then lbl, t, tp
               else None, t, None)
             (List.hd r)
             (List.tl r)
         with
         | Some _, _, Some tp -> Some tp
         | _, _, _ -> None)
      | None -> (* fr fr *) None
      | _ -> None)
  | _ -> None
;;

(* Checks if the given store is well typed with respect to the given type_store
   and typing context. *)
(* Returns true iff gamma | sigma |- mu *)
let store_well_typed (g : ctx) (s : typ_store) (mu : store) : bool =
  IMap.for_all
    (fun i t0 ->
      match IMap.find_opt i s with
      | None -> false
      | Some tp' -> type_check g s t0 tp')
    mu
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
  | TRef t0 -> "Ref " ^ typ_to_string t0
  | TFun (t0, t1) -> "(" ^ typ_to_string t0 ^ "->" ^ typ_to_string t1 ^ ")"
  | TUnit -> "()"
  | TVariant lst ->
    "["
    ^ String.concat ", " (List.map (fun (l, t) -> l ^ ":" ^ typ_to_string t) lst)
    ^ "]"
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
  | TmUnit -> "()"
  | TmNull -> "null"
  | TmIsNull (tp, t1) -> "IsNull " ^ term_to_string t1
  | TmVariant (label, t1, tp) ->
    label ^ " " ^ term_to_string t1 ^ " as " ^ typ_to_string tp
  | TmRef t1 -> "Ref " ^ term_to_string t1
  | TmLoc l1 -> "loc " ^ string_of_int l1
  | TmAssn (t1, t2) -> term_to_string t1 ^ " := " ^ term_to_string t2
  | TmBang t1 -> "!(" ^ term_to_string t1 ^ ")"
  | TmRaise t1 -> "raise (" ^ term_to_string t1 ^ ")"
  | TmTry (t1, t2) -> "try " ^ term_to_string t1 ^ " failwith (" ^ term_to_string t2 ^ ")"
  | TmCase (t1, lst) ->
    "case "
    ^ term_to_string t1
    ^ " of ["
    ^ String.concat
        " | "
        (List.map
           (fun (str, lab, t') -> str ^ " " ^ lab ^ " => " ^ term_to_string t')
           lst)
    ^ "]"
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
  print_endline "----- Type Inference -----";
  print_endline ("      " ^ term_str);
  print_endline (": " ^ opt_typ_to_string (type_infer empty_ctx empty_store ast));
  print_endline ""
;;

interpret Sys.argv.(1)
