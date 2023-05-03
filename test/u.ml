open Minikanren.Mk
open Minikanren.Ck
open Minikanren.Fd

let print_sep name =
  print_string (Printf.sprintf "=========%s========\n" name)

let print_s = List.iter (fun t -> print_string ((string_of_logic_term t) ^ "\n"))

let test ?limit:(limit = -1) name f =
  let _ = print_sep name in
  let time = Sys.time() in
  let q = fresh () in
  let s = run limit q (f q) in
  print_string (Printf.sprintf "Execution time: %f\n" (Sys.time() -. time));
  print_s s

let rec appendo l s out : 'a -> 'a stream =
  conde [
    [eq l (List []); eq s out];
    [
      fun ss ->
        let a, d = fresh (), fresh () in
        all [
          eq (Cons (a, d)) l;
          (fun ss ->
            let res = fresh () in
            all [
              eq (Cons (a, res)) out;
              appendo d s res;
            ] ss)
        ] ss
    ]
  ]

let l =
  (Cons ((const_int 1),
    (Cons ((const_int 2),
      (Cons ((const_int 3),
        (Cons ((const_int 4), List []))))))))

let _lst len sym = List.fold_right (fun _ acc -> Cons (const_char sym , acc)) (List.init len (fun _ -> sym )) (List [])

let _ = 
  test ~limit:5 "appendo" (fun q ->
  let a, b = fresh (), fresh () in
  [
    appendo a l l;
    eq q (Cons (a, b))
  ]
)

let rec reverso xy yx = 
  conde [
    [eq xy (List []); eq yx xy];
    [
      fun ss ->
        let h, t = fresh(), fresh() in
        all [
          eq xy (Cons (h, t));
          fun ss ->
            let tr = fresh() in
            all [
              reverso t tr;
              fun ss -> 
                all [
                  appendo tr (Cons (h, List[])) yx;
                ] ss
            ] ss
        ] ss
    ]
  ]

let task_2rev q = [conde [[reverso (_lst 150 'x') q]; [reverso (_lst 150 'a') q]]]
let task_2rev_par q = [condePar [[reverso (_lst 150 'x') q]; [reverso (_lst 150 'a') q]]]


let _ = test ~limit:(5) "reverso" (fun q -> task_2rev q)


let _ = test ~limit:(5) "reverso-parallel" (fun q -> task_2rev_par q)




(* 
let _ = Eio_main.run @@ fun env ->
  test ~limit:(-1) "2reverso with domain manager" 
  (fun q -> [conde ~mgr:(Eio.Stdenv.domain_mgr env) [[reverso (_lst 10 'x') q]; [reverso (_lst 10 'x') q]]])  *)


(* ----------------------- external attempt 


let _paraltest ~domain_mgr q = 
  let term1 = Eio.Domain_manager.run domain_mgr (fun () -> reverso (_lst 50 'x') q) in
  let term2 = Eio.Domain_manager.run domain_mgr (fun () -> reverso (_lst 50 'x') q) in
  [conde [[term1]; [term2]]]

let _nonparaltest ~domain_mgr q = [
conde [
  [reverso (_lst 100 'x') q];
  [reverso (_lst 100 'x') q]
]
]
let _ = Eio_main.run @@ fun env ->
  test ~limit:(-1) "reverso paral" (fun q -> _paraltest ~domain_mgr:(Eio.Stdenv.domain_mgr env) q)
*)


(* --------------------------- interleaving


let rec anyo t = 
  conde [
    [t];
    [fun ss -> all [anyo t] ss]
  ]

let _ = test ~limit:10 "interleaving with anyo" (fun q ->
  [
    anyo (
      conde (
        [
        [eq (const_int 1) q];
        [eq (const_int 2) q];
        [eq (const_int 3) q];
        [anyo succeed]
      ])
    )
]) *)

