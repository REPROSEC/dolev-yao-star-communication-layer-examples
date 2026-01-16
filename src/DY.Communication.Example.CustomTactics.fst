module DY.Communication.Example.CustomTactics

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
