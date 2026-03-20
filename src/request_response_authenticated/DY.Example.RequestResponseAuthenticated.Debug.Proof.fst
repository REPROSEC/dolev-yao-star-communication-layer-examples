module DY.Example.RequestResponseAuthenticated.Debug.Proof

open DY.Core
open DY.Lib
open DY.Example.RequestResponseAuthenticated.Protocol.Total
open DY.Example.RequestResponseAuthenticated.Protocol.Stateful
open DY.Example.RequestResponseAuthenticated.Protocol.Stateful.Proof
open DY.Example.RequestResponseAuthenticated.Debug

/// This module proves that the debug function
/// fulfills the trace invariants.
///
/// The proof works automatically because each
/// stateful proof as a SMTPat (`[SMTPat (trace_invariant tr); SMTPat (protocol_function)]`).
/// Another way to do this proof is to basically
/// duplicate the code from the debug function and
/// call all the lemmas for the stateful code manually.

#set-options "--fuel 0 --ifuel 5 --z3rlimit 100 --z3cliopt 'smt.qi.eager_threshold=100'"
val debug_proof:
  tr:trace ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = debug () tr in
    trace_invariant tr_out
    )
  )
let debug_proof tr =
  let (_, tr_out) = debug () tr in

  (* debug_print_string is non-traceful *)
  let client = "client" in
  let server = "server" in

  let (x_init, tr_init) = initialize_communication_reqres message_t client server tr
  in
  assert(trace_invariant tr_init);
  match x_init with
  | None ->
      assert(tr_init == tr_out)
  | Some (client_comm_keys_sess_ids, server_comm_keys_sess_ids) ->

      let (x_req, tr_req) =
        client_send_request
          client_comm_keys_sess_ids client server tr_init
      in
      assert(trace_invariant tr_req);
      match x_req with
      | None ->
          assert(tr_req == tr_out)
      | Some (sid, msg_id) ->

          let (x_srv, tr_srv) =
            server_receive_request_send_response
              server_comm_keys_sess_ids server msg_id tr_req
          in
          assert(trace_invariant tr_srv);
          match x_srv with
          | None ->
              assert(tr_srv == tr_out)
          | Some msg_id ->

              let (x_cli, tr_cli) =
                client_receive_response client sid msg_id tr_srv
              in
              assert(trace_invariant tr_cli);
              match x_cli with
              | None ->
                  assert(tr_cli == tr_out)
              | Some () ->
                  assert(tr_cli == tr_out)
