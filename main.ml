let bdd_tests () =
  let builder = Bdd.builder () in
  let t, f, var = (Bdd.leaf_true, Bdd.leaf_false, Bdd.var builder) in
  let ( && ), ( || ), ( ^ ), ( ! ), ite, subs =
    ( Bdd.op_and builder,
      Bdd.op_or builder,
      Bdd.op_xor builder,
      Bdd.op_not builder,
      Bdd.if_then_else builder,
      Bdd.subs builder )
  in
  print_endline "Basic boolean operators on atoms";
  [ t ^ t; f ^ f; t ^ f; f ^ t ]
  @ [ t && t; f && f; t && f; f && t ]
  @ [ t || t; f || f; t || f; f || t ]
  @ [ !t; !f ]
  |> List.iter (fun x -> Bdd.sat x |> Printf.printf "%b\n");
  print_endline "ITE constructions and variable substitutions";
  subs (var 0) 0 t |> Bdd.sat |> string_of_bool |> print_endline;
  ite (var 0) t f |> ( = ) (var 0) |> string_of_bool |> print_endline

let zdd_tests () = ()

let () =
  print_endline "Testing Binary Decision Diagrams          ...";
  bdd_tests ();
  print_endline "Testing Zero-Suppressed Decision Diagrams ...";
  zdd_tests ();
  ()
