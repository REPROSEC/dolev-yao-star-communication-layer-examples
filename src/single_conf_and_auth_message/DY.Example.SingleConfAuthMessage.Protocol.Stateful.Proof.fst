module DY.Example.SingleConfAuthMessage.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleConfAuthMessage.Protocol.Total
open DY.Example.SingleConfAuthMessage.Protocol.Total.Proof
open DY.Example.SingleConfAuthMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

(**** State Predicates ****)

let state_predicate_protocol: local_state_predicate single_message_state = {
  pred = (fun tr prin state_id st ->
    match st with
    | SenderState receiver msg -> (
      let sender = prin in
      event_triggered tr sender (SenderSendMsg sender receiver msg) /\
      get_label tr msg.secret == join (principal_label sender) (principal_label receiver) /\
      is_knowable_by (join (principal_label sender) (principal_label receiver)) tr msg.secret
    )
    | ReceiverState sender msg -> (
      let receiver = prin in
      event_triggered tr receiver (ReceiverReceivedMsg sender receiver msg) /\
      is_knowable_by (principal_label receiver) tr msg.secret
    )
  );
  pred_later = (fun tr1 tr2 sender state_id st -> ());
  pred_knowable = (fun tr sender state_id st -> ());
}

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  (|local_state_single_message_state.tag, local_state_predicate_to_local_bytes_state_predicate state_predicate_protocol|);
]

(**** Event Predicates ****)

let event_predicate_protocol: event_predicate single_message_event =
  fun tr prin e ->
    match e with
    | SenderSendMsg sender receiver msg -> (
      is_secret (join (principal_label sender) (principal_label receiver)) tr msg.secret
    )
    | ReceiverReceivedMsg sender receiver msg -> (
      (exists payload. event_triggered tr receiver (CommConfAuthReceiveMsg sender receiver payload)) /\
      (
        event_triggered tr sender (SenderSendMsg sender receiver msg) \/ 
        is_corrupt tr (long_term_key_label sender)
      )
    )

val comm_layer_event_preds: comm_higher_layer_event_preds single_message
let comm_layer_event_preds = {
  default_comm_higher_layer_event_preds single_message with
  send_conf = (fun tr sender receiver payload -> True);
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ());
  send_conf_auth = (fun tr sender receiver payload -> (
    event_triggered tr sender (SenderSendMsg sender receiver payload)

  ));
  send_conf_auth_later = (fun tr1 tr2 sender receiver payload -> ())
}

/// List of all local event predicates.

let all_events = [
  event_predicate_communication_layer_and_tag comm_layer_event_preds;
  (event_single_message_event.tag, compile_event_pred event_predicate_protocol)
]

(**** Create the global trace invariants ****)

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

val protocol_invariants_protocol_has_nsl_session_invariant: squash (has_local_state_predicate state_predicate_protocol)
let protocol_invariants_protocol_has_nsl_session_invariant = all_sessions_has_all_sessions ()

/// Lemmas that the global event predicate contains all the local ones

val all_events_has_all_events: unit -> Lemma (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events))
let all_events_has_all_events () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  mk_event_pred_correct all_events;
  norm_spec [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events);
  let dumb_lemma (x:prop) (y:prop): Lemma (requires x /\ x == y) (ensures y) = () in
  dumb_lemma (for_allP has_compiled_event_pred all_events) (norm [delta_only [`%all_events; `%for_allP]; iota; zeta] (for_allP has_compiled_event_pred all_events))

val protocol_invariants_has_communication_layer_event_invariants: squash (has_event_pred (event_predicate_communication_layer comm_layer_event_preds))
let protocol_invariants_has_communication_layer_event_invariants = all_events_has_all_events ()

val protocol_invariants_protocol_has_protocol_event_invariant: squash (has_event_pred event_predicate_protocol)
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
  match get_state sender state_id tr with
  | (Some (SenderState receiver msg), tr) -> (
    send_confidential_authenticated_proof tr comm_layer_event_preds comm_keys_ids sender receiver msg;
    ()
  )
  | _ -> ()

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
  receive_confidential_authenticated_proof tr comm_layer_event_preds comm_keys_ids receiver msg_id;
  match receive_message comm_keys_ids receiver msg_id tr with
  | (None, tr) -> ()
  | (Some state_id, tr_out) -> (
    let (Some msg, tr) = receive_confidential_authenticated #single_message comm_keys_ids receiver msg_id tr in
    let ((), tr) = trigger_event receiver (ReceiverReceivedMsg msg.sender receiver msg.payload) tr in
    assert(event_triggered tr receiver (ReceiverReceivedMsg msg.sender receiver msg.payload));
    let (state_id, tr) = new_session_id receiver tr in
    let ((), tr) = set_state receiver state_id (ReceiverState msg.sender msg.payload) tr in
    assert(is_knowable_by (principal_label receiver) tr msg.payload.secret);
    assert(is_secret (join (principal_label msg.sender) (principal_label receiver)) tr msg.payload.secret \/
            is_corrupt tr (long_term_key_label msg.sender)
    );
    assert(trace_invariant tr);
    assert(tr == tr_out);
    ()
  )
