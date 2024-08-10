module DY.Example.SingleAuthMessage.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleAuthMessage.Protocol.Total
open DY.Example.SingleAuthMessage.Protocol.Total.Proof
open DY.Example.SingleAuthMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

let state_predicate_protocol: local_state_predicate single_message_state = {
  pred = (fun tr prin state_id st ->
    match st with
    | SenderState sender' secret -> (
      let sender = prin in
      sender == sender' /\
      event_triggered tr sender (SenderSendMsg sender secret) /\
      is_publishable tr secret
    )
    | ReceiverState sender secret payload -> (
      let receiver = prin in
      (exists sender. event_triggered tr receiver (ReceiverReceivedMsg sender receiver secret payload)) /\
      is_publishable tr secret /\
      is_publishable tr payload
    )
  );
  pred_later = (fun tr1 tr2 sender state_id st -> ());
  pred_knowable = (fun tr sender state_id st -> ());
}

let event_predicate_protocol: event_predicate single_message_event =
  fun tr prin e ->
    match e with
    | SenderSendMsg sender secret -> True
    | ReceiverReceivedMsg sender receiver secret payload -> (
      event_triggered tr receiver (CommAuthReceiveMsg sender receiver payload)
    )

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (local_state_single_message_state.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_protocol);
]

/// List of all local event predicates.


val comm_layer_event_preds: comm_higher_layer_event_preds
let comm_layer_event_preds = {
  default_comm_higher_layer_event_preds with
  send_auth = (fun tr sender payload -> 
    exists secret.
      event_triggered tr sender (SenderSendMsg sender secret) /\
      decode_message payload == Some {secret}
  )
}

let all_events = [
  event_predicate_communication_layer_and_tag comm_layer_event_preds;
  (event_protocol_event.tag, compile_event_pred event_predicate_protocol)
]

/// Create the global trace invariants.

let trace_invariants_protocol: trace_invariants (crypto_invariants_protocol) = {
  state_pred = mk_state_pred crypto_invariants_protocol all_sessions;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}

/// Lemmas that the global state predicate contains all the local ones

val all_sessions_has_all_sessions: unit -> Lemma (norm [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate protocol_invariants_protocol) all_sessions))
let all_sessions_has_all_sessions () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_sessions)));
  mk_state_pred_correct protocol_invariants_protocol all_sessions;
  norm_spec [delta_only [`%all_sessions; `%for_allP]; iota; zeta] (for_allP (has_local_bytes_state_predicate protocol_invariants_protocol) all_sessions)

val protocol_invariants_protocol_has_pki_invariant: squash (has_pki_invariant protocol_invariants_protocol)
let protocol_invariants_protocol_has_pki_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_private_keys_invariant: squash (has_private_keys_invariant protocol_invariants_protocol)
let protocol_invariants_protocol_has_private_keys_invariant = all_sessions_has_all_sessions ()

val protocol_invariants_protocol_has_nsl_session_invariant: squash (has_local_state_predicate protocol_invariants_protocol state_predicate_protocol)
let protocol_invariants_protocol_has_nsl_session_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct protocol_invariants_protocol all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP (has_compiled_event_pred protocol_invariants_protocol) all_events))

val protocol_invariants_has_communication_layer_event_invariants: squash (has_event_pred protocol_invariants_protocol (event_predicate_communication_layer comm_layer_event_preds))
let protocol_invariants_has_communication_layer_event_invariants = all_events_has_all_events ()

val protocol_invariants_protocol_has_protocol_event_invariant: squash (has_event_pred protocol_invariants_protocol event_predicate_protocol)
let protocol_invariants_protocol_has_protocol_event_invariant = all_events_has_all_events ()

(*** Proofs ***)

val prepare_message_proof:
  tr:trace -> sender:principal -> receiver:principal ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = prepare_message sender receiver tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (prepare_message sender receiver tr)]
let prepare_message_proof tr sender receiver = ()


val send_message_proof:
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> sender:principal -> receiver:principal -> state_id:state_id ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = send_message comm_keys_ids sender receiver state_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (send_message comm_keys_ids sender receiver state_id tr)]
let send_message_proof tr comm_keys_ids sender receiver state_id =
  match send_message comm_keys_ids sender receiver state_id tr with
  | (None, tr_out) -> ()
  | (Some msg_id, tr_out) -> (
    let (Some (SenderState sender' secret), tr) = get_state sender state_id tr in
    assert(is_publishable tr secret);
    assert(event_triggered tr sender (SenderSendMsg sender secret));
    compute_message_proof tr sender receiver secret;
    let payload = compute_message secret in  
    send_authenticated_proof tr comm_layer_event_preds comm_keys_ids sender receiver payload;
    let (Some msg_id, tr) = send_authenticated comm_keys_ids sender receiver payload tr in
    assert(tr_out == tr);
    assert(event_predicate_protocol tr sender (SenderSendMsg sender secret));
    ()
  )

#push-options "--fuel 0 --ifuel 1 --z3rlimit 10"
val receive_message_proof:
  tr:trace -> comm_keys_ids:communication_keys_sess_ids -> receiver:principal -> msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = receive_message comm_keys_ids receiver msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (receive_message comm_keys_ids receiver msg_id tr)]
let receive_message_proof tr comm_keys_ids receiver msg_id =
  receive_authenticated_proof tr comm_layer_event_preds comm_keys_ids receiver msg_id;
  match receive_message comm_keys_ids receiver msg_id tr with
  | (None, tr_out) -> ()
  | (Some state_id, tr_out) -> (
    let (Some {sender; receiver=receiver'; payload}, tr) = receive_authenticated comm_keys_ids receiver msg_id tr in
    assert(is_publishable tr payload);
    decode_message_proof tr sender receiver payload;
    let Some {secret} = decode_message payload in
    let ((), tr) = trigger_event receiver (ReceiverReceivedMsg sender receiver secret payload) tr in
    assert(event_triggered tr receiver (ReceiverReceivedMsg sender receiver secret payload));
    let (state_id, tr) = new_session_id receiver tr in
    let ((), tr) = set_state receiver state_id (ReceiverState sender secret payload) tr in
    assert(tr_out == tr);
    ()
  )
#pop-options