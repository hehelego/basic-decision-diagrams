module TruthTable = struct
  let lim = 9
  let inputs = 1 lsl lim
  let const_true = Array.make inputs true
  let const_false = Array.make inputs false
  let var x = Array.init inputs (fun i -> (i lsr x) land 1 = 1)
  let lift2 op f g = Array.init inputs (fun i -> op f.(i) g.(i))
  let lift1 op f = Array.init inputs (fun i -> op f.(i))

  let op_and, op_or, op_xor, op_nor, op_nand, op_imply, op_equiv =
    ( lift2 ( && ),
      lift2 ( || ),
      lift2 (fun x y -> (x && not y) || (y && not x)),
      lift2 (fun x y -> not (x || y)),
      lift2 (fun x y -> not (x && y)),
      lift2 (fun x y -> y || not x),
      lift2 (fun x y -> (x || not y) && (y || not x)) )

  let op_not = lift1 not

  let op_ite cond f g =
    let l = op_and cond f in
    let r = op_and (op_not cond) g in
    op_or l r

  let subs f x g =
    Array.init inputs (fun i ->
        let t' = if g.(i) then 1 else 0 in
        let t = (i lsr x) land 1 in
        let i' = i - (t lsl x) + (t' lsl x) in
        f.(i'))

  let forall x f =
    Array.init inputs (fun i ->
        let i' = i lxor (1 lsl x) in
        f.(i) && f.(i'))

  let exists x f =
    Array.init inputs (fun i ->
        let i' = i lxor (1 lsl x) in
        f.(i) || f.(i'))

  let sat = Array.fold_left ( || ) false
  let unsat f = sat f |> not
end

let bdd_tests iters () =
  Random.init 0;

  let builder = Bdd.builder () in
  let buf = Dynarray.create () in
  Dynarray.ensure_capacity buf (iters * 15);
  let add dd tt =
    let tt' = Bdd.truth_table builder TruthTable.lim dd in
    assert (tt = tt');
    Dynarray.add_last buf (dd, tt)
  in
  let pick () = Dynarray.length buf |> Random.int |> Dynarray.get buf in
  let draw_var () = Random.int TruthTable.lim in

  print_endline "[BDD] constants";
  add Bdd.leaf_true TruthTable.const_true;
  add Bdd.leaf_false TruthTable.const_false;

  print_endline "[BDD] variables";
  for i = 0 to TruthTable.lim - 1 do
    let node = Bdd.var builder i in
    let tt = TruthTable.var i in
    add node tt
  done;

  print_endline "[BDD] manipulation";
  for _ = 1 to iters do
    let p, p' = pick () in
    let q, q' = pick () in
    let r, r' = pick () in
    let x = draw_var () in
    (* binary logical connectives *)
    add (Bdd.op_and builder p q) (TruthTable.op_and p' q');
    add (Bdd.op_or builder p q) (TruthTable.op_or p' q');
    add (Bdd.op_xor builder p q) (TruthTable.op_xor p' q');
    add (Bdd.op_nor builder p q) (TruthTable.op_nor p' q');
    add (Bdd.op_nand builder p q) (TruthTable.op_nand p' q');
    add (Bdd.op_imply builder p q) (TruthTable.op_imply p' q');
    add (Bdd.op_equiv builder p q) (TruthTable.op_equiv p' q');
    (* unary operator *)
    add (Bdd.op_not builder p) (TruthTable.op_not p');
    (* ternary if-then-else *)
    add (Bdd.if_then_else builder r p q) (TruthTable.op_ite r' p' q');
    (* substitution *)
    add (Bdd.subs builder p x q) (TruthTable.subs p' x q');
    (* quantification *)
    add (Bdd.forall builder x p) (TruthTable.forall x p');
    add (Bdd.exists builder x p) (TruthTable.exists x p');
    (* satisfiability *)
    assert (Bdd.sat p = TruthTable.sat p');
    assert (Bdd.unsat q = TruthTable.unsat q');
    ()
  done

module SetFamily = struct
  let lim = 9

  module S = Set.Make (struct
    type t = int

    let compare = compare
  end)

  let to_bitmask = List.fold_left (fun acc x -> acc lor (1 lsl x)) 0
  let from_list_list xs = List.map to_bitmask xs |> S.of_list
  let empty = S.empty
  let singleton x = S.singleton (1 lsl x)
  let single_set xs = to_bitmask xs |> S.singleton
  let insert x = S.map (( lor ) (1 lsl x))
  let remove x xs = S.map (( land ) (lnot (1 lsl x))) xs
  let filter0 x xs = S.filter (fun xs -> (xs lsr x) land 1 = 0) xs
  let filter1 x xs = S.filter (fun xs -> (xs lsr x) land 1 = 1) xs |> remove x
  let union = S.union
  let inter = S.inter
  let diff = S.diff
  let sym_diff xs ys = union (diff xs ys) (diff ys xs)
  let count = S.cardinal
  let is_subset xs ys = S.for_all (fun x -> S.mem x ys) xs
  let equal xs ys = is_subset xs ys && is_subset ys xs
end

let zdd_tests iters () =
  Random.init 0;

  let builder = Zdd.builder () in
  let buf = Dynarray.create () in
  Dynarray.ensure_capacity buf (iters * 15);
  let add dd set =
    let set' = Zdd.family builder dd |> SetFamily.from_list_list in
    assert (SetFamily.equal set set');
    Dynarray.add_last buf (dd, set)
  in
  let pick () = Dynarray.length buf |> Random.int |> Dynarray.get buf in
  let draw_var () = Random.int TruthTable.lim in

  print_endline "[ZDD] empty family";
  add Zdd.empty SetFamily.empty;

  print_endline "[ZDD] singleton families";
  for i = 0 to SetFamily.lim - 1 do
    add (Zdd.singleton builder i) (SetFamily.singleton i)
  done;

  print_endline "[ZDD] single set special case";
  add (Zdd.single_set builder []) (SetFamily.single_set []);
  add (Zdd.single_set builder [ 0 ]) (SetFamily.single_set [ 0 ]);
  let all = List.init SetFamily.lim (fun x -> x) in
  add (Zdd.single_set builder all) (SetFamily.single_set all);

  print_endline "[ZDD] manipulations";
  for _ = 1 to iters do
    let p, p' = pick () in
    let q, q' = pick () in
    let x = draw_var () in
    (* set operations *)
    add (Zdd.union builder p q) (SetFamily.union p' q');
    add (Zdd.inter builder p q) (SetFamily.inter p' q');
    add (Zdd.diff builder p q) (SetFamily.diff p' q');
    add (Zdd.sym_diff builder p q) (SetFamily.sym_diff p' q');
    (* filtering *)
    add (Zdd.filter0 builder x p) (SetFamily.filter0 x p');
    add (Zdd.filter1 builder x q) (SetFamily.filter1 x q');
    (* insert/remove *)
    add (Zdd.insert builder x p) (SetFamily.insert x p');
    add (Zdd.remove builder x q) (SetFamily.remove x q');
    (* counting *)
    assert (Zdd.count builder p = SetFamily.count p');
    assert (Zdd.count builder q = SetFamily.count q');
    (* from list *)
    let len = Random.int (SetFamily.lim * 4) in
    let xs = List.init len (fun _ -> Random.int SetFamily.lim) in
    add (Zdd.single_set builder xs) (SetFamily.single_set xs);
    ()
  done

let () =
  print_endline "Testing Binary Decision Diagrams          ...";
  bdd_tests 100000 ();
  print_endline "Testing Zero-Suppressed Decision Diagrams ...";
  zdd_tests 100000 ();
  ()
