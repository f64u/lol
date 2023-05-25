exception No_solution 
exception Invalid_argument

(* Problem 1: The Collatz Sequence *)

(* Let f(n) = n/2     if n is even
              3n+1    otherwise     *)

(* The Collatz conjecture states that every n > 0, 
   repeated application of f to n terminates in 1. 
   Compute the Collatz sequence [n, f(n), ..., 1] for arbitrary n. 
   Throw an Invalid_argument exception if a number less than 1 is provided. *)

(** [collatz_list n] gives the a list representing Collatz sequnce starting from [n].
    Raises: [Invalid_argument] if [n] is an invalid start number (i.e. <1) *)
let rec collatz_list (n : int) : int list =
  if n < 1 then raise Invalid_argument
  else if n = 1 then [1]
  else n :: collatz_list (if n mod 2 = 0 then n / 2
                          else 3 * n + 1)

(* Now compute the length of the Collatz sequence. *)

(** [collatz_length n] gives the length of the Collatz sequnce starting from [n].
  Raises: [Invalid_argument "n"] if [n] is an invalid start number (i.e. <1) *)
let rec collatz_length (n : int) : int = List.length (collatz_list n)

(* Problem 2: Binary search trees *)

(* Consider the following tree type *)
type 'a tree = Nil | Node of 'a tree * 'a * 'a tree

(* Write a function that tests whether a tree is a valid binary search tree using the built-in '<' operation *)


 (** [valid_bst t] returns whether [t] is a valid binary search tree or not *)
let rec valid_bst (t : 'a tree) : bool =
  (** [leftmost tree] optionally finds the left-most node value; otherwise [None] if the [tree] is [Nil] *)
  let rec leftmost = function
  | Nil                  -> None
  | Node (Nil, value, _) -> Some value
  | Node (path, _, _)    -> leftmost path in
  (** [rightmost tree] optionally finds the right-most node value; otherwise [None] if the [tree] is [Nil] *)
  let rec rightmost = function 
  | Nil                  -> None
  | Node (_, value, Nil) -> Some value
  | Node (_, _, path)    -> rightmost path in
   match t with
    | Nil -> true (* an empty tree is a valid bst *)
    | Node (left, value, right) -> 
        valid_bst left &&
        valid_bst right &&
        (match rightmost left with | Some left  -> left < value  | _ -> true) && (* the max value is less than us *)
        (match leftmost right with | Some right -> value < right | _ -> true) (* we're less than the min value *)
  

(* Problem 3: Searching a tree *)

(* We define directions as follows *)

type direction = Left | Right

(* These direction can be used to traverse the trees above. 
   Write a function to return the element at the indicated spot. 
   The end of the input list means to stop. 
   
   Since this will often fail, write versions that 
   1. raise a Not_found exception, and
   2. return a default element,
   3. return an option type.
   *)

(** [search_tree_exn t ds] returns the value in the tree [t] after traversing 
    it according to the list of [direction]s present in [ds]. Raises: [Not_found] 
    if the list of [direction]s [ds] cannot be followed thoroughtly. *)
let rec search_tree_exn (t : 'a tree) (ds : direction list) : 'a = match (t, ds) with
  | (Nil               , _)           -> raise Not_found
  | (Node (_, value, _), [])          -> value
  | (Node (left, _, _), Left::rest)   -> search_tree_exn left  rest
  | (Node (_, _, right), Right::rest) -> search_tree_exn right rest

(** [search_tree_def t ds d] returns the value in the tree [t] after traversing 
    it according to the list of [direction]s present in [ds]. If the list of [direction]s [ds]
    cannot be followed thoroughtly, the value [d] is returned instead. *)
let rec search_tree_def (t : 'a tree) (ds : direction list) (d : 'a) : 'a = match (t, ds) with
  | (Nil               , _)           -> d
  | (Node (_, value, _), [])          -> value
  | (Node (left, _, _), Left::rest)   -> search_tree_def left  rest d
  | (Node (_, _, right), Right::rest) -> search_tree_def right rest d
 
(** [search_tree_opt t ds] optionally returns [Some value] in the tree [t] after traversing 
    it according to the list of [direction]s present in [ds]; otherwise [None]. *)
 let rec search_tree_opt (t : 'a tree) (ds : direction list) : 'a option = match (t, ds) with
  | (Nil               , _)           -> None
  | (Node (_, value, _), [])          -> Some value
  | (Node (left, _, _),  Left::rest)  -> search_tree_opt left  rest
  | (Node (_, _, right), Right::rest) -> search_tree_opt right rest
 

(* Problem 4: Summing tree values *)
  
(* For each of the methods above, write a function that takes a list of trees of integers and 
   returns the sum of the values at the given directions. *)

(* throw an exception if any of the trees are missing the desired element *)

(** [sum_tree_exn ts ds] returns the sum of the values found after following the list of
    [direction]s [ds] in each tree present in [ts]. Raises: [Not_found] if the list of [direction]s 
    cannot be fulfilled in any of the trees. *)
let rec sum_tree_exn (ts : int tree list) (ds : direction list) : int = 
  List.fold_left (+) 0 (List.map ((Fun.flip search_tree_exn) ds) ts)

(* Use 0 as the default here *)

(** [sum_tree_def ts ds] returns the sum of the values found after following the list of
    [direction]s [ds] in each tree present in [ts]. If the list of [direction]s 
    cannot be fulfilled in any of the trees, the value [0] is used instead. *)
let rec sum_tree_def (ts : int tree list) (ds : direction list) : int = 
  List.fold_left (+) 0 (List.map (fun t -> search_tree_def t ds 0) ts)


(* Return None if any of the trees do. *)

(** [sum_tree_opt ts ds] optionally returns [Some acc] representing the sum
    of the values found after following the list of
    [direction]s [ds] in each tree present in [ts]; otherwise, [None]. *)
let rec sum_tree_opt (ts : int tree list) (ds : direction list) : 'a option = 
  List.fold_left (fun acc v -> match (acc, v) with
                               | (None, _) | (_, None) -> None
                               | (Some acc, Some v)    -> Some (acc + v))
                 (Some 0)
                 (List.map ((Fun.flip search_tree_opt) ds) ts) 


(* Problem 5: Reversing Lists *)

(* Here is a simple definition of reverse: *)

let rec reverse (l : 'a list) = 
  match l with
  | [] -> []
  | h::t -> reverse t @ [ h ]

(* though correct, this function reverses a list
   in O(n^2) time, since appending to the end of
   a list is done in O(n). It is possible to write
   an alternate definition which can reverse a list
   in linear time. Write such a definition.

   Hint: It will be necessary to write a helper function.
 *)

(** [reverse_fast l] returns the list [l] reversed by [fold]ing it [_left]-wise. *)
let reverse_fast (l : 'a list) = List.fold_left (fun acc v -> v::acc) [] l


(* Problem 6: Binary Numbers *)

(* The following is a representation of a binary digit: *)

type digit = Zero | One

(* We can represent a natural number in binary as a list of
   binary digits. Write digits_of_int which converts a machine integer
   into a list of binary digits, where the least significant
   digit is at the head of the list. Raise Negative if the input
   is negative. *)

exception Negative

(** [digits_of_int n] returns the binary representation of [n] in the form of a 
    list of [One]s and [Zero]s. Raises: [Negative] if [n] is a negative number. *)
let rec digits_of_int (n : int) : digit list = 
  if n < 0 then raise Negative
  else if n = 0 then []
  else (if n mod 2 = 0 then Zero else One) :: digits_of_int (n / 2) 

(* int_of_digits converts a list of digits into a machine integer *)

(** [int_of_digits digits] returns the number represented by the binary sequence of [digits]. *)
let rec int_of_digits (digits : digit list) : int = match digits with
  | []          -> 0
  | digit::rest -> (if digit = Zero then 0 else 1) + 2 * int_of_digits rest

(* succ computes the successor of the binary number. For example,
   succ [Zero]      = [One]
   succ [Zero; One] = [One; One]
   succ [One; One]  = [Zero; Zero; One]

   Don't use digits_of_int or int_of_digits in the definition of this function! *)

(** [succ digit] returns the binary representation of the number (represented by [digit] + 1). *)
let rec succ (digits : digit list) : digit list = match digits with
  | []         -> [One]
  | Zero::rest -> One::rest 
  | One::rest  -> Zero::succ rest



(* Problem 7: Tic-Tac-Toe *)

exception Invalid_input

type player = X | O

(* 
  Read the final board of a tic-tac-toe game from a file. Valid input will be of the format:
  `---
   ---
   ---` 
   where each `-` should be `X` or `O`. Raise Invalid_input if input does not match this format.
   Only considering cases where an `X` or an `O` populates every place on the board (so no blank spaces), 
   raise Invalid_input if the board is not a valid end state for a tic-tac-toe game:
    - if there are multiple winners
   Return the winner of this game, if any, as Some winner, where winner : player. 
   If there is no winner, return None.
   You may want to write at least one helper function for this.
 *)

(** [same_row p grid] returns whether player [p] wins row-wise in the game-snapshot represented
    by [grid]. *)
let same_row (p : player) (grid : player array array) : bool = 
  grid |> 
  Array.map (fun row ->
    row |> 
    Array.map (fun turn -> Bool.to_int (p = turn)) |>
    Array.fold_left (+) 0
  ) |>
  Array.mem 3

(* from https://stackoverflow.com/questions/3989776/transpose-of-a-list-of-lists; otherwise available in Seq.transpose but version issues *)
let rec transpose list = match list with
  | []             -> []
  | []      :: xss -> transpose xss
  | (x::xs) :: xss ->
      List.(
        (x :: map hd xss) :: transpose (xs :: map tl xss)
      )

(** [same_col p grid] returns whether player [p] wins column-wise in the game-snapshot 
    represented by [grid]. *)
let same_col (p : player) (grid : player array array): bool =
  grid |>
  Array.map (Array.to_list) |>
  Array.to_list |>
  transpose |>
  List.map (Array.of_list) |>
  Array.of_list |>
  same_row p

(** [same_diag p grid] returns whether player [p] wins diagonal-wise in the game-snapshot 
    represented by [grid]. *)
let same_diag (p : player) (grid : player array array) : bool =
  grid.(0).(0) = p && grid.(1).(1) = p && grid.(2).(2) = p ||
  grid.(0).(2) = p && grid.(1).(1) = p && grid.(2).(0) = p

(** [x_wins grid] returns whether player [X] wins in the game-snapshot 
    represented by [grid]. *)
let x_wins (grid : player array array) : bool = same_row X grid || same_col X grid || same_diag X grid

(** [o_wins grid] returns whether player [O] wins in the game-snapshot 
    represented by [grid]. *)
let o_wins (grid : player array array) : bool = same_row O grid || same_col O grid || same_diag O grid

(** [get_winner filename] returns which player wins, if any, in the file of the name [filename].
    Riases: [Invalid_input] if both players win, or [Sys_error] if [filename] is inaccessible. *)
let get_winner (filename : string) : player option = 
  let lines = Array.to_seq (Arg.read_arg filename) in
  let flat_grid = lines |>
      Seq.flat_map String.to_seq |>
      Seq.map (fun c -> match c with | 'X' -> X | 'O' -> O | _ -> raise Invalid_input) |>
      Array.of_seq in
  let matrix = Array.make_matrix 3 3 0 |>
               Array.mapi (fun i row -> row |>
                               Array.mapi (fun j _ -> flat_grid.(i * 3 + j))) in
    match (x_wins matrix, o_wins matrix) with
      | (true, true) -> raise Invalid_input
      | (true, false) -> Some X
      | (false, true) -> Some O
      | (false, false) -> None

