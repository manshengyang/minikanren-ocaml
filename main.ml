(* TODO List.memq/==/!= correct? *)

open Mk
open Ck
open Fd

let print_sep () = print_string "===============\n"

let _ =
  let q = fresh () in
  let x = fresh () in
  let s = run_all q [
    conde [
      [succeed];
      [eq q (const_bool true)];
      [
        eq q (List [const_bool true; const_int 1; x]);
        eq x (const_int 10)
      ];
      (let x = fresh () in [eq q x]);
      [eq x q; eq x (const_str "x");];
      [fail; eq q (const_int 1)]
    ]
  ]
  in List.iter (fun t -> print_string ((string_of_logic_term t) ^ "\n")) s

let _ = use_fd ()
let _ = print_sep ()

let _ =
  let q = fresh () in
  let x = fresh () in
  let y = fresh () in
  let s = run_all q [
    all_difffd q;
    eq q (List [x; y]);
    eq x (const_int 1);
    eq y (const_int 2);
  ]
  in List.iter (fun t -> print_string ((string_of_logic_term t) ^ "\n")) s
