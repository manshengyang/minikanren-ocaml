open Mk

(* = *)
let eq u v a =
  let s = (unify [(u, v)] a) in
  match s with
    | Some s -> Unit s
    | None -> MZero

(* reify *)
let reify v s =
  let v = walk_all v s in
  walk_all v (reify_s v (empty_s ()))

(* run *)
let run n x f =
  let f = all f in
  let ss = take n (Func (fun () -> f (empty_s ()))) in
  List.map (fun s -> reify x s) ss

(* run* *)
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
