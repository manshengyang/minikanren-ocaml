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

(* represent a logic term *)
type logic_term =
  | Var of int
  | Constant of const_value
  | List of (logic_term list)

let rec string_of_logic_term t =
  match t with
    | Var i -> "var_" ^ string_of_int i
    | Constant v -> string_of_const_value v
    | List [] -> ""
    | List (hd::tl) ->
        List.fold_left
          (fun str t -> str ^ ", " ^ (string_of_logic_term t))
          (string_of_logic_term hd)
          tl

(* empty_s *)
let empty_s () = Hashtbl.create 100

(* ext_s *)
let ext_s x v s =
  let _ = Hashtbl.add s x v in s

(* walk *)
let rec walk v s =
  match v with
    | Var _ ->
      begin
        try walk (Hashtbl.find s v) s
        with Not_found -> v
      end
    | _ -> v

(* occurs_check *)
let rec occurs_check x v s =
  let v = walk v s in
  match v with
    | Var _ -> v = x
    | List lst ->
      List.fold_left (fun checked v -> checked || (occurs_check x v s)) false lst
    | _ -> false

(* ext_s_check *)
let ext_s_check x v s =
  if occurs_check x v s then None
  else Some (ext_s x v s)

(* unify_g: general unification function *)
let rec unify_g ext_s u v s =
  let u = walk u s in
  let v = walk v s in
  if u == v then Some s
  else match (u, v) with
    | (Var _, _) -> ext_s u v s
    | (_, Var _) -> ext_s v u s
    | (List ulst, List vlst) ->
      List.fold_right2
        (fun u v s -> match s with Some s -> (unify_g ext_s u v s) | _ -> None)
        ulst vlst (Some s)
    | _ -> if u = v then Some s else None

(* unify_check *)
let unify_check u v s = unify_g ext_s_check u v s

(* unify *)
let unify u v s = unify_g (fun x v s -> Some (ext_s x v s)) u v s

(* walk* *)
let rec walk_all v s =
  let v = walk v s in
  match v with
    | List lst -> List (List.map (fun v -> walk_all v s) lst)
    | _ -> v

(* reify_name *)
let reify_name n = Constant (String ("_" ^ (string_of_int n)))

(* reify_s *)
let rec reify_s v s =
  let v = walk v s in
  match v with
    | Var _ -> ext_s v (reify_name (Hashtbl.length s)) s
    | List lst -> List.fold_right reify_s lst s
    | _ -> s

(* reify *)
let reify v s =
  let v = walk_all v s in
  walk_all v (reify_s v (empty_s ()))

type 'a stream =
  | MZero
  | Func of (unit -> ('a stream))
  | Choice of 'a * (unit -> ('a stream))
  | Unit of 'a

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

(* =check *)
let eq_check u v a =
  let s = (unify_check u v a) in
  match s with
    | Some s -> Unit s
    | None -> MZero

(* = *)
let eq u v a =
  let s = (unify u v a) in
  match s with
    | Some s -> Unit s
    | None -> MZero

(* We do not have exist construct,
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
  Func (fun () -> mplus_all (List.map (fun f -> (f (Hashtbl.copy s))) lst))

let rec take n a_inf =
  if n = 0 then []
  else match a_inf with
    | MZero -> []
    | Func f -> (take n (f ()))
    | Choice (a, f) -> a::(take (n - 1) (f ()))
    | Unit a -> [a]

let run n x f =
  let f = all f in
  let ss = take n (Func (fun () -> f (empty_s ()))) in
  List.map (fun s -> reify x s) ss

let run_all = run (-1)

let succeed s = Unit s
let fail s = MZero

let _ =
  begin
    let q = (fresh ()) in
    let x = (fresh ()) in
    let s = run_all q [
      conde [
        [succeed];
        [eq q (Constant (Bool true))];
        [
          (eq q (List [Constant (Bool true); Constant (Int 1); x]));
          (eq x (Constant (Int 10)))
        ];
        (let x = (fresh ()) in [eq q x]);
        [(eq x q); (eq x (Constant (String "x")));];
        [fail; (eq q (Constant (Int 1)))]
      ]
    ]
    in List.iter (fun t -> print_string ((string_of_logic_term t) ^ "\n")) s
  end
