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
      comm_meta_data_knowable tr message_t client cmeta_data /\
      is_secret (comm_label client server) tr nonce
    )
    | ServerReceiveRequest {client; nonce} -> (
      let server = prin in
      is_knowable_by (comm_label client server) tr nonce
    )
    | ClientReceiveResponse {server; cmeta_data; nonce} -> (
      let client = prin in
      comm_meta_data_knowable tr message_t client cmeta_data /\
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
  state_predicates_communication_layer_reqres_and_tag message_t;
  mk_local_state_tag_and_pred state_predicates_protocol;
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
    | Response b -> True
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

/// Lemmas that the global predicates contain all the local ones

let fst_dtuple (x: dtuple2 'a 'b) : 'a = Mkdtuple2?._1 x

#push-options "--fuel 4"
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst_dtuple (all_sessions)));
  do_split_boilerplate mk_state_pred_correct all_sessions
)
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  do_split_boilerplate mk_event_pred_correct all_events
)
#pop-options

(*** Proofs ***)

#push-options "--ifuel 3 --fuel 1"
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
  enable_reqres_comm_layer_lemmas comm_layer_event_preds;
  ()
#pop-options

#push-options "--ifuel 3 --fuel 1 --z3rlimit 50"
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
  enable_reqres_comm_layer_lemmas comm_layer_event_preds;
  ()
#pop-options

#push-options "--ifuel 4 --fuel 1 --z3rlimit 40"
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
  enable_reqres_comm_layer_lemmas comm_layer_event_preds;
  ()
#pop-options
