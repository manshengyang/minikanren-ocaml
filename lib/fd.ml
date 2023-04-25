open Mk
open Ck

type dom = int list

let logic_term_to_int t =
  match t with
    | Constant (Int i) -> i
    | _ -> failwith "given logic term is not an int "

let logic_term_to_list l =
  match l with
    | List l -> l
    | _ -> failwith "give logic term is not a list"

let logic_term_to_var v =
  match v with
    | Var v -> v
    | _ -> failwith "give logic term is not a var"

let rec range l r =
  if l <= r then l::(range (l + 1) r)
  else []

(* make-dom *)
let make_dom n = n

(* list-sorted *)
let rec list_sorted pred ls =
  match ls with
    | x::(y::tl) ->
      (pred x y) && list_sorted pred (y::tl)
    | _ -> true

(* list-insert *)
let rec list_insert pred x ls =
  match ls with
    | [] -> [x]
    | y::tl ->
      if pred x y then x::ls
      else y::(list_insert pred x tl)

(* map-sum *)
let map_sum f =
  let rec helper ls =
    match ls with
      | [] -> fail
      | hd::tl -> conde [[f hd]; [helper tl]]
  in helper


let null_dom x = x = []
let singleton_dom x = (List.length x) = 1
let singleton_element_dom x = List.hd x
let min_dom dom = List.hd dom
let max_dom dom = List.hd (List.rev dom)
let mem_dom = List.mem

let rec intersection_dom dom1 dom2 =
  match (dom1, dom2) with
    | (hd1::tl1, hd2::tl2) ->
      if hd1 = hd2 then hd1::(intersection_dom tl1 tl2)
      else if hd1 < hd2 then intersection_dom tl1 dom2
      else intersection_dom dom1 tl2
    | _ -> []

let rec diff_dom dom1 dom2 =
  match (dom1, dom2) with
    | (hd1::tl1, hd2::tl2) ->
      if hd1 = hd2 then diff_dom tl1 tl2
      else if hd1 < hd2 then hd1::(diff_dom tl1 dom2)
      else diff_dom dom1 tl2
    | _ -> dom1

let rec copy_before pred dom =
  match dom with
    | [] -> []
    | hd::tl ->
      if pred hd then []
      else hd::(copy_before pred tl)

let rec drop_before pred dom =
  match dom with
    | [] -> []
    | hd::tl ->
      if pred hd then dom
      else drop_before pred tl

let rec disjoint_dom dom1 dom2 =
  match (dom1, dom2) with
    | (hd1::tl1, hd2::tl2) ->
      if hd1 = hd2 then false
      else if hd1 < hd2 then disjoint_dom tl1 dom2
      else disjoint_dom dom1 tl2
    | _ -> true

let get_dom x d : dom option =
  if List.mem_assoc x d then Some (List.assoc x d)
  else None

let resolve_storable_dom dom x (s, d, c) =
  let var_x = Var x in
  if singleton_dom dom then
    let n = singleton_element_dom dom in
    let a = make_a (ext_s var_x (const_int n) s) d c in
    run_constraints [var_x] c a
  else
    Some (make_a s (ext_d x dom d) c)

let update_var_dom x dom a =
  let (_, d, _) = a in
  match get_dom x d with
  | Some xdom ->
    let i = intersection_dom xdom dom in
    if null_dom i then None
    else resolve_storable_dom i x a
  | _ -> resolve_storable_dom dom x a

let process_dom v dom a =
  match v with
    | Var i -> update_var_dom i dom a
    | Constant (Int i) ->
      if mem_dom i dom then Some a
      else None
    | _ -> None

let rec force_ans (x : logic_term) (a : store) =
  let (s, d, _) = a in
  let x = walk x s in
  let f = match x with
    | Var v ->
      begin
        match get_dom v d with
          | Some ls ->
            map_sum (fun v -> (eq x (const_int v))) ls
          | None -> succeed
      end
    | List ls ->
      all (List.map force_ans ls)
    | _ -> succeed
  in f a

let get_walk_dom u (s, d, _) =
  let u = walk u s in
  match u with
  | Var i -> (u, get_dom i d)
  | Constant (Int i) -> (u, Some (make_dom [i]))
  | _ -> (u, None)

(* =/=fd-c *)
let neqfd_c : constraint_op =
  let helper u v a =
    let (u, udom) = get_walk_dom u a in
    let (v, vdom) = get_walk_dom v a in
    let (s, d, c) = a in
    let oc = build_oc "=/=fd" (List [u; v]) in
    match (udom, vdom) with
      | (Some udom, Some vdom) ->
        if (singleton_dom udom) && (singleton_dom vdom) && udom = vdom then
          None
        else if disjoint_dom udom vdom then
          Some a
        else
          let a = make_a s d (ext_c oc c) in
          if singleton_dom udom then
            process_dom v (diff_dom vdom udom) a
          else if singleton_dom vdom then
            process_dom u (diff_dom udom vdom) a
          else Some a
      | _ -> Some (make_a s d (ext_c oc c))
  in constraint_op2 helper

let exclude_from_dom dom1 d x_all =
  let x_all = List.map logic_term_to_var x_all in
  let rec helper x_all =
    match x_all with
      | [] -> identitym
      | xhd::xtl ->
        match get_dom xhd d with
          | Some dom2 ->
            composem
              (process_dom (Var xhd) (diff_dom dom2 dom1))
              (helper xtl)
          | None -> helper xtl
  in helper x_all


(* all-diff/fd-c *)
let all_diff_fd_c : constraint_op =
  let helper y_all n_all a =
    let (s, d, c) = a in
    let rec loop y_all n_all xls =
      let yls = logic_term_to_list y_all in
      let nls = logic_term_to_list n_all in
      let n_val_all = List.map logic_term_to_int nls in
      match yls with
        | [] ->
          let oc = build_oc "all-diff/fd" (List [List xls; n_all]) in
          let a = make_a s d (ext_c oc c) in
          exclude_from_dom (make_dom n_val_all) d xls a
        | yhd::ytl ->
          let y = walk yhd s in
          match y with
            | Var _ -> loop (List ytl) n_all (y::xls)
            | Constant (Int i) ->
              if mem_dom i n_val_all then None
              else
                let n_val_all = list_insert (<) i n_val_all in
                let nls = List.map const_int n_val_all in
                loop (List ytl) (List nls) xls
            | _ -> None
    in loop y_all n_all []
  in constraint_op2 helper

(* all-difffd-c *)
let all_difffd_c ls a =
  let (s, d, c) = a in
  let ls = walk ls s in
  match ls with
    | Var _ ->
      let oc = build_oc "all-difffd" ls in
      Some (make_a s d (ext_c oc c))
    | List ls ->
      let (x_all, n_all) = List.partition is_var ls in
      let n_val_all = List.sort compare (List.map logic_term_to_int n_all) in
      if list_sorted (<) n_val_all then (* all_diff n_all *)
        let n_all = List.map const_int n_val_all in
        all_diff_fd_c (List [(List x_all); (List n_all)]) a
      else None
    | _ -> Some a

(* process-prefixfd *)
let rec process_prefixfd p c =
  match p with
    | [] -> identitym
    | (x, v)::tl ->
      let t = composem (run_constraints [x] c) (process_prefixfd tl c) in
      fun a ->
        let (_, d, _) = a in
        match get_dom (logic_term_to_var x) d with
          | Some dom ->
            composem (process_dom v dom) t a
          | None -> t a

let rec verify_all_bound c bounds =
  match c with
    | [] -> ()
    | hd::tl ->
      try
        let rands = logic_term_to_list (rands_of_oc hd) in
        let all_vars = List.filter is_var rands in
        let x = List.find (fun x -> not (List.mem x bounds)) all_vars in
        failwith (Printf.sprintf "Constrained variable %s without domain"
          (string_of_logic_term x))
      with _ -> verify_all_bound tl bounds

(* enfore-constraintsfd *)
let enforce_constraintsfd x =
  all [
    force_ans x;
    (fun a ->
      let (_, d, c) = a in
      let bounds = List.map (fun x -> Var x) (List.map fst d) in
      let _ = verify_all_bound c bounds in
      onceo [force_ans (List bounds)] a)
  ]

(* reify-constraintsfd *)
let reify_constraintsfd _ _ =
  failwith "Unbound vars at end"

(* c-op *)
let c_op op ls f a =
  let get_val d =
    match d with
      | Some v -> v
      | None -> failwith "option has no value"
  in let (s, d, c) = a in
  let ls = List.map (fun x -> get_walk_dom x a) ls in
  let (vls, domls) = List.split ls in
  let c = ext_c (build_oc op (List vls)) c in
  let a = make_a s d c in
  if List.mem None domls then Some a
  else f vls (List.map get_val domls) a

(* <=fd-c *)
let lefd_c : constraint_op =
  let f vls domls =
    match (vls, domls) with
      | ([u; v], [udom; vdom]) ->
        let umin = min_dom udom in
        let vmax = max_dom vdom in
          composem
            (process_dom u (copy_before (fun u -> vmax < u) udom))
            (process_dom v (drop_before (fun v -> umin <= v) vdom))
      | _ -> failwith "invalid args" (* should never happens*)
  in let helper u v a = c_op "<=fd" [u; v] f a
  in constraint_op2 helper

(* +fd-c *)
let plusfd_c : constraint_op =
  let f vls domls =
    match (vls, domls) with
      | ([u; v; w], [udom; vdom; wdom]) ->
        let wmin = min_dom wdom in
        let wmax = max_dom wdom in
        let umin = min_dom udom in
        let umax = max_dom udom in
        let vmin = min_dom vdom in
        let vmax = max_dom vdom in
        composem
          (process_dom w (range (umin + vmin) (umax + vmax)))
          (composem
            (process_dom u (range (wmin - vmax) (wmax - vmin)))
            (process_dom v (range (wmin - umax) (wmax - umin))))
      | _ -> failwith "invalid args" (* should never happens*)
  in let helper u v w a = c_op "+fd" [u; v; w] f a
  in constraint_op3 helper

(* domfd-c *)
let domfd_c x n_all a =
  let (s, _, _) = a in
  process_dom (walk x s) (make_dom n_all) a

(* domfd: (domfd x [1; 2; 3] *)
let domfd x n_all = goal_construct (domfd_c x n_all)

(* infd: (infd [x; y;] [1; 2; 3]) *)
let infd ls e =
  all (List.map (fun x -> domfd x e) ls)

(* =/=fd: (neqfd x y) *)
let neqfd u v = goal_construct (neqfd_c (List [u; v]))

(* <=fd: (lefd x y) *)
let lefd u v = goal_construct (lefd_c (List [u; v]))

(* <fd: (ltfd x y) *)
let ltfd u v = all [lefd u v; neqfd u v]

(* +fd: (plusfd x y sum) *)
let plusfd u v w = goal_construct (plusfd_c (List [u; v; w]))

(* all-difffd: (all_difffd ls) *)
let all_difffd ls = goal_construct (all_difffd_c ls)

let use_fd () =
  let _ = add_op "=/=fd" neqfd_c in
  let _ = add_op "all-difffd" all_difffd_c in
  let _ = add_op "all-diff/fd" all_diff_fd_c in
  let _ = add_op "<=fd" lefd_c in
  let _ = add_op "+fd" plusfd_c in
  let _ = process_prefix := process_prefixfd in
  let _ = enforce_constraints := enforce_constraintsfd in
  let _ = reify_constraints := reify_constraintsfd in
  ()
