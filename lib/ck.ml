open Mk

let op_map = Hashtbl.create 100
let get_op (op : string) : (logic_term -> store -> store option) =
  Hashtbl.find op_map op
let add_op = Hashtbl.replace op_map

(* identitym *)
let identitym a = Some a

(* composem *)
let composem f g a =
  match f a with
    | None -> None
    | Some b -> g b

(* goal-construct *)
let goal_construct f a =
  match f a with
    | None -> MZero
    | Some x -> Unit x

(* process-prefix *)
let process_prefix = ref (fun _ _ a -> identitym a)
(* enforce-constraints*)
let enforce_constraints = ref (fun _ a -> Unit a)
(* reify-constraints*)
let reify_constraints = ref (fun m _ _ -> Unit m)

(* oc->proc *)
let proc_of_oc (x, args) = get_op x args
(* oc->rands *)
let rands_of_oc (_, x) = x

(* any/var? *)
let rec any_var p =
  match p with
    | Var _ -> true
    | Cons (a, b) -> (any_var a) && (any_var b)
    | List ls -> List.exists any_var ls
    | _ -> false

(* ext-d *)
let ext_d x fd d : domains = (x, fd)::d

(* ext-c *)
let ext_c oc c : constraints =
  if any_var (rands_of_oc oc) then oc::c
  else c

type constraint_op = logic_term -> store -> (store option)
let constraint_op2 f ls a =
  match ls with
  | List [u; v] -> f u v a
  | _ -> failwith "number of operands is not 2"
let constraint_op3 f ls a =
  match ls with
  | List [u; v; w] -> f u v w a
  | _ -> failwith "number of operands is not 3"

(* build-oc *)
let build_oc op terms = (op, terms)

(* rem/run *)
let rem_run oc a =
  let (s, d, c) = a in
  if List.mem oc c then
    let c2 = List.filter (fun x -> x <> oc) c in
    (proc_of_oc oc) (make_a s d c2)
  else Some a

(* any-relevant/var? *)
let rec any_relevant_var t x =
  match t with
    | Var _ -> List.mem t x
    | Cons (a, b) -> (any_relevant_var a x) && (any_relevant_var b x)
    | List ls ->
      List.exists (fun a -> any_relevant_var a x) ls
    | _ -> false

(* run-constraints *)
let rec run_constraints x_all c =
  match c with
  | [] -> identitym
  | hd::tl ->
    if any_relevant_var (rands_of_oc hd) x_all then
      (composem (rem_run hd) (run_constraints x_all tl))
    else (run_constraints x_all tl)

(* reify *)
let reify (x : logic_term) a =
  let a2 = bind a (!enforce_constraints x) in
  let helper a =
    let (s, _, c) = a in
    let v = walk_all x s in
    let r = reify_s v empty_s in
    if r = [] then Unit v
    else
      let v = walk_all v r in
      if c = [] then Unit v
      else (!reify_constraints v r) a
  in bind a2 helper

(* run *)
let run n x f =
  let f = all f in
  take n (Func (fun () -> reify x (f empty_a)))

(* run* *)
let run_all x f = run (-1) x f


(* prefix-s *)
let prefix_s s s2 =
  if s = [] then s2
  else
    let rec helper s2 =
      if s2 = s then []
      else match s2 with
        | hd::tl -> hd::(helper tl)
        | [] -> []
    in helper s2

(* ==-c *)
let eq_c : constraint_op =
  let helper u v a =
    let (s, d, c) = a in
    match unify [(u, v)] s with
      | Some s2 ->
        if s = s2 then Some (s, d, c)
        else
          let p = prefix_s s s2 in
          let a = make_a s2 d c in
          (!process_prefix p c) a
      | None -> None
  in constraint_op2 helper

(* == *)
let eq u v = goal_construct (eq_c (List [u; v]))

(*
let succeed = eq (const_bool false) (const_bool false)
let fail = eq (const_bool true) (const_bool false)
*)
let succeed a = Unit a
let fail _ = MZero
