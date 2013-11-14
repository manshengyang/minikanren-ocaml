open Mk

let unitg s = Unit s
let mzerog s = MZero

(* identitym *)
let identitym a = Some a

(* composem *)
let composem f g a =
  let b = f a in b && g b

(* goal-construct *)
let goal_construct f a =
  match f a with
  | None -> MZero
  | Some x -> Unit x

(* process-prefix *)
let process_prefix = (fun p c -> identitym)
(* enforce-constraints*)
let enforce_constraints = (fun x -> unitg)
(* reify-constraints*)
let reify_constraints = (fun m r a -> Unit m)

(* oc->proc *)
let proc_of_oc (x, _, _) = x
(* oc->rands *)
let rands_of_oc (_, x, _) = x
(* oc->rator *)
let rator_of_oc (_, _, x) = x

(* any/var? *)
let rec any_var p =
  match p with
    | Var _ -> true
    | List lst -> List.exists any_var lst
    | _ -> false

(* ext-d *)
let ext_d x fd d = (x, fd)::d

(* ext-c *)
let ext_c oc c =
  if any_var (rands_of_oc oc) then oc::c
  else c

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
let eq_c u v (s, d, c) =
  match unify [(u, v)] s with
    | Some s2 ->
      if s = s2 then Some (s, d, c)
      else
        let p = prefix_s s s2 in
        let a = make_a s2 d c in
        (process_prefix p c) a
    | None -> None

(* == *)
let eq u v = goal_construct (eq_c u v)

(*
let succeed s = eq (const_bool false) (const_bool false)
let fail s = eq (const_bool true) (const_bool false)
*)
let succeed s = Unit s
let fail s = MZero

(* reify *)
let reify (x : logic_term) a =
  let a2 = bind a (enforce_constraints x) in
  let helper a =
    let (s, d, c) = a in
    let v = walk_all x s in
    let r = reify_s v empty_s in
    if r = [] then Unit v
    else
      let v = walk_all v r in
      if c = [] then Unit v
      else (reify_constraints v r) a
  in bind a2 helper

(* run *)
let run n x f =
  let f = all f in
  take n (Func (fun () -> reify x (f empty_a)))

(* run* *)
let run_all x f = run (-1) x f

let _ =
  begin
    let q = (fresh ()) in
    let x = (fresh ()) in
    let s = run_all q [
      conde [
        [succeed];
        [eq q (const_bool true)];
        [
          (eq q (List [(const_bool true); (const_int 1); x]));
          (eq x (const_int 10))
        ];
        (let x = (fresh ()) in [eq q x]);
        [(eq x q); (eq x (const_str "x"));];
        [fail; (eq q (const_int 1))]
      ]
    ]
    in List.iter (fun t -> print_string ((string_of_logic_term t) ^ "\n")) s
  end
