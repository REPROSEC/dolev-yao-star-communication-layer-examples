module DY.Example.RequestResponse.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib

open DY.Example.RequestResponse.Protocol.Total
open DY.Example.RequestResponse.Protocol.Total.Proof
open DY.Example.RequestResponse.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** State Predicates ***)

#push-options "--ifuel 3 --z3rlimit 20"
let state_predicates_protocol: local_state_predicate protocol_state = {
  pred = (fun tr prin sess_id st -> 
    match st with
    | ClientSendRequest {server; cmeta_data; nonce} -> (
      let client = prin in
      comm_meta_data_knowable tr client cmeta_data /\
      is_secret (comm_label client server) tr nonce
    )
    | ServerReceiveRequest {client; nonce} -> (
      let server = prin in
      is_knowable_by (comm_label client server) tr nonce
    )
    | ClientReceiveResponse {server; cmeta_data; nonce} -> (
      let client = prin in
      comm_meta_data_knowable tr client cmeta_data /\
      is_secret (comm_label client server) tr nonce
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id state -> ());
  pred_knowable = (fun tr prin sess_id state -> ());
}
#pop-options

val protocol_state_tag: string
let protocol_state_tag = "Protocol.State"

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  state_predicates_communication_layer_and_tag;
  (|protocol_state_tag, local_state_predicate_to_local_bytes_state_predicate state_predicates_protocol|);
]

(*** Event Predicates ***)

#push-options "--ifuel 2"
val comm_layer_event_preds: comm_reqres_higher_layer_event_preds message_t
let comm_layer_event_preds = {
  default_comm_reqres_higher_layer_event_preds message_t with
  send_request = (fun tr client server (payload:message_t) key_label ->
    match payload with
    | Request {client; nonce} -> (
      is_secret (comm_label client server) tr nonce
    )
    | Response {b} -> True
  );
  send_request_later = (fun tr1 tr2 client server payload key_label -> ())
}
#pop-options

let all_events = event_predicate_communication_layer_reqres_and_tag comm_layer_event_preds

(*** Combine all Invariants ***)

/// Create the global trace invariants.

let trace_invariants_protocol: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP has_local_bytes_state_predicate all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map dfst (all_sessions)));
  mk_state_pred_correct all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP has_local_bytes_state_predicate all_sessions)

val protocol_invariants_protocol_has_pki_invariant: squash has_pki_invariant
let protocol_invariants_protocol_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_private_keys_invariant: squash has_private_keys_invariant
let protocol_invariants_protocol_has_private_keys_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_communication_layer_state_invariant: squash (has_local_state_predicate state_predicates_communication_layer)
let protocol_invariants_protocol_has_communication_layer_state_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_protocol_state_invariant: squash (has_local_state_predicate state_predicates_protocol)
let protocol_invariants_protocol_has_protocol_state_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP has_compiled_event_pred all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events))

val protocol_invariants_has_communication_layer_event_invariants: squash (has_event_pred (event_predicate_communication_layer request_response_event_preconditions))
let protocol_invariants_has_communication_layer_event_invariants = all_events_has_all_events ()

#push-options "--fuel 1"
val protocol_invariants_protocol_communication_layer_reqres_event_invariant: squash (has_event_pred (event_predicate_communication_layer_reqres comm_layer_event_preds))
let protocol_invariants_protocol_communication_layer_reqres_event_invariant = all_events_has_all_events ()
#pop-options

(*** Proofs ***)

#push-options "--z3rlimit 10"
val client_send_request_proof:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_send_request comm_keys_ids client server tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (client_send_request comm_keys_ids client server tr)]
let client_send_request_proof tr comm_keys_ids client server =
  assert(apply_com_layer_lemmas comm_layer_event_preds);
  ()
#pop-options

#push-options "--ifuel 1 --z3rlimit 85"
val server_receive_request_send_response_proof:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  server:principal ->
  msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = server_receive_request_send_response comm_keys_ids server msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (server_receive_request_send_response comm_keys_ids server msg_id tr)]
let server_receive_request_send_response_proof tr comm_keys_ids server msg_id =
  assert(apply_com_layer_lemmas comm_layer_event_preds);
  let (_, tr_out) = server_receive_request_send_response comm_keys_ids server msg_id tr in
  match receive_request comm_keys_ids server msg_id tr with
  | (None, tr) -> assert(tr == tr_out)
  | (Some (Request req, cmeta_data), tr) -> (
    let send_event client = CommClientSendRequest client server (serialize message_t (Request req)) cmeta_data.key in
    assert(trace_invariant tr);
    eliminate (exists client. event_triggered tr client (send_event client)) \/
              is_publishable tr cmeta_data.key
    returns is_knowable_by (comm_label req.client server) tr req.nonce
    with _. eliminate exists client. event_triggered tr client (send_event client)
      returns _
      with _. (
        let i = find_event_triggered_at_timestamp tr client (send_event client) in
        // Triggers event_triggered_at_implies_pred
        assert(event_triggered_at tr i client (send_event client));
        // From protocol event predicate
        assert(is_knowable_by (comm_label req.client server) tr req.nonce)
      )
    and _. assert(is_well_formed message_t (is_publishable tr) (Request req));
    ()
  )
  | (Some _, tr) -> assert(tr == tr_out)
#pop-options

#push-options "--ifuel 4 --z3rlimit 40"
val client_receive_response_proof:
  tr:trace ->
  client:principal ->
  sid:state_id -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_receive_response client sid msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (client_receive_response client sid msg_id tr)]
let client_receive_response_proof tr client sid msg_id =
  assert(apply_com_layer_lemmas comm_layer_event_preds);
  ()
#pop-options
