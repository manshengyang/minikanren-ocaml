(* TODO List.memq/==/!= correct? *)

open Mk
open Ck
open Fd

let print_sep name =
  print_string (Printf.sprintf "=========%s========\n" name)

let print_s = List.iter (fun t -> print_string ((string_of_logic_term t) ^ "\n"))

let test name f print =
  let _ = print_sep name in
  let q = fresh () in
  let s = run_all q (f q) in
  print s

let _ = test "miniKanren" (fun q ->
  let x = fresh () in
  [
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
) print_s


let _ = use_fd ()

let _ = test "infd" (fun q -> [infd [q] [1; 2; 3]]) print_s

let _ = test "neqfd" (fun q ->
  let x = fresh () in
  [
    infd [q] [2; 3; 4];
    infd [x] [1; 2; 3];
    neqfd q x
  ]
) print_s

let _ = test "lefd" (fun q ->
  let x = fresh () in
  [
    infd [q] [2; 3; 4];
    infd [x] [1; 2; 3];
    lefd q x
  ]
) print_s

let _ = test "plusfd" (fun q ->
  let x = fresh () in
  let y = fresh () in
  [
    infd [q] (range 2 8);
    infd [x] (range 1 3);
    infd [y] [5];
    plusfd q x y
  ]
) print_s

let _ = test "all_difffd" (fun q ->
  let x = fresh () in
  let y = fresh () in
  let z = fresh () in
  [
    eq q (List [x; y; z]);
    infd [x] (range 1 3);
    infd [y] (range 1 2);
    infd [z] (range 1 1);
    all_difffd q
  ]
) print_s
