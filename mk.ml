(* represent a constant value *)
type const_value =
  | Bool of bool
  | Int of int
  | String of string
  | Char of char
  | Float of float

let string_of_const_value v =
  match v with
    | Int i -> string_of_int i
    | String s -> s
    | Bool b -> string_of_bool b
    | Char c -> Char.escaped c
    | Float f -> string_of_float f

type var_id = int

(* represent a logic term *)
type logic_term =
  | Var of var_id
  | Constant of const_value
  | List of (logic_term list)

let is_var t = match t with Var _ -> true | _ -> false

(* helper functions for using Constant *)
let const_bool b = Constant (Bool b)
let const_int i = Constant (Int i)
let const_char c = Constant (Char c)
let const_float f = Constant (Float f)
let const_str s = Constant (String s)


type substitutions = (logic_term * logic_term) list
type domains = (var_id * (int list)) list
type constraints = (string * logic_term) list
type store = substitutions * domains * constraints

let empty_s : substitutions = []
let empty_d : domains = []
let empty_c : constraints = []
let make_a s d c = (s, d, c)
let empty_a = make_a empty_s empty_d empty_c

let rec string_of_logic_term t =
  match t with
    | Var i -> "var_" ^ string_of_int i
    | Constant v -> string_of_const_value v
    | List l ->
      "(" ^ (String.concat ", " (List.map string_of_logic_term l)) ^ ")"

let string_of_constraint (x, l) =
  Printf.sprintf "(%s, %s" x (string_of_logic_term l)

(* walk *)
let rec walk v s =
  match v with
    | Var _ ->
      begin
        try walk (List.assoc v s) s
        with Not_found -> v
      end
    | _ -> v

(* occurs_check *)
let rec occurs_check x v s =
  let v = walk v s in
  match v with
    | Var _ -> v = x
    | List lst ->
      List.exists (fun v -> occurs_check x v s) lst
    | _ -> false

(* ext_s *)
let ext_s x v s = (x, v)::s

(* ext_s_check: check for cycles before extending *)
let ext_s_check x v s =
  if occurs_check x v s then None
  else Some (ext_s x v s)

(* unify *)
let rec unify lst s =
  match lst with
  | [] -> Some s
  | (u, v)::rest ->
    let rec helper u v rest =
      let u = walk u s in
      let v = walk v s in
      if u == v then unify rest s
      else match (u, v) with
        | Var _, _ ->
          if occurs_check u v s then None
          else unify rest (ext_s u v s)

        | _, Var _ ->
          if occurs_check v u s then None
          else unify rest (ext_s v u s)

        | List (u::ulst), List (v::vlst) ->
          helper u v ((List.combine ulst vlst)@rest)

        | _ ->
          if u = v then (unify rest s) else None
    in helper u v rest

(* walk* *)
let rec walk_all v s =
  let v = walk v s in
  match v with
    | List lst -> List (List.map (fun v -> walk_all v s) lst)
    | _ -> v

(* reify-n *)
let reify_name n = Constant (String ("_" ^ (string_of_int n)))

(* reify-s *)
let rec reify_s v s =
  let v = walk v s in
  match v with
    | Var _ -> ext_s v (reify_name (List.length s)) s
    | List lst -> List.fold_right reify_s lst s
    | _ -> s

type 'a stream =
  | MZero
  | Func of (unit -> ('a stream))
  | Choice of 'a * (unit -> ('a stream))
  | Unit of 'a

let empty_f () = MZero

(* mplus *)
let rec mplus a_inf f =
  match a_inf with
    | MZero -> f ()
    | Func f2 -> Func (fun () -> mplus (f ()) f2)
    | Unit a -> Choice (a, f)
    | Choice (a, f2) -> Choice (a, (fun () -> mplus (f ()) f2))

(* mplus* *)
let rec mplus_all lst =
  match lst with
    | hd::tl -> mplus hd (fun () -> mplus_all tl)
    | [] -> MZero

(* bind *)
let rec bind a_inf g =
  match a_inf with
    | MZero -> MZero
    | Func f -> Func (fun () -> bind (f ()) g)
    | Unit a -> g a
    | Choice (a, f) -> mplus (g a) (fun () -> bind (f ()) g)

(* bind*: short-circuiting implementation *)
let rec bind_all e lst =
  match (e, lst) with
    | (MZero, _) -> MZero
    | (_, []) -> e
    | (_, hd::tl) -> bind_all (bind e hd) tl

(* We do not have exist/fresh construct,
 * the equivalent construct is:
 * let x = fresh () in [...]
 *)
(* fresh: create a fresh variable *)
let var_counter = ref 0
let fresh () =
  begin
    var_counter := !var_counter + 1;
    Var !var_counter
  end

(* all: combine a sequence (list) of clauses *)
let all lst a = bind_all (Unit a) lst

(* conde *)
let conde lst s =
  let lst = List.map all lst in
  Func (fun () -> mplus_all (List.map (fun f -> (f s)) lst))

(* take *)
let rec take n a_inf =
  if n = 0 then []
  else match a_inf with
    | MZero -> []
    | Func f -> (take n (f ()))
    | Choice (a, f) -> a::(take (n - 1) (f ()))
    | Unit a -> [a]

(* ifu *)
let rec ifu lst =
  match lst with
    | [] -> MZero
    | (e, glst)::tl ->
      let rec helper a_inf =
        match a_inf with
          | MZero -> ifu tl
          | Func f -> Func (fun () -> helper (f ()))
          | Choice (a, _) | Unit a -> bind_all (Unit a) glst
      in helper e

(* condu *)
let condu lst a =
  Func (fun () ->
    ifu (List.map (fun l -> ((List.hd l) a, List.tl l)) lst))

(* onceo *)
let onceo g = condu [g]
