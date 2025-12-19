module CustomTactics

open FStar.Tactics

#push-options "--ifuel 1"
private
let rec __assumption_aux' (bs : list binding) : Tac unit =
    match bs with
    | [] ->
        fail "no assumption matches goal"
    | b::bs ->
        let t = binder_to_term b in
        let typ = tc (cur_env()) t in
        try (
          t_exact false false t
        ) with | _ ->
        try (
          apply (`FStar.Squash.return_squash);
          if tmatch typ (cur_goal ()) then
          t_exact false false t
          else fail ""
        ) with | _ ->
        __assumption_aux' bs
#pop-options

let assumption' () : Tac unit =
    __assumption_aux' (cur_vars ())

let grewrite' = grewrite

(*let grewrite' (t1 t2 : term) : Tac unit =
    let e = tcut (mk_sq_eq t1 t2) in
    let e = pack_ln (Tv_Var (bv_of_binder e)) in
    pointwise (fun () ->
      (* If the LHS is a uvar, do nothing, so we do not instantiate it. *)
      let is_uvar =
        match term_as_formula (cur_goal()) with
        | Comp (Eq _) lhs rhs ->
          (match inspect_ln lhs with
           | Tv_Uvar _ _ -> true
           | _ -> false)
        | _ -> false
      in
      if is_uvar
      then trefl ()
      else try t_exact false false e with | _ -> trefl ())
*)