module DY.Example.SingleAuthMessage.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleAuthMessage.Protocol.Total
open DY.Example.SingleAuthMessage.Protocol.Total.Proof
open DY.Example.SingleAuthMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

(**** State Predicates ****)

#push-options "--fuel 0 --ifuel 1"
let state_predicate_protocol: local_state_predicate single_message_state = {
  pred = (fun tr prin state_id st ->
    match st with
    | SenderState msg -> (
      let sender = prin in
      event_triggered tr sender (SenderSendMsg sender msg) /\
      is_publishable tr msg.secret
    )
    | ReceiverState sender msg -> (
      let receiver = prin in
      (exists sender. event_triggered tr receiver (ReceiverReceivedMsg sender receiver msg)) /\
      is_publishable tr msg.secret
    )
  );
  pred_later = (fun tr1 tr2 sender state_id st -> ());
  pred_knowable = (fun tr sender state_id st -> ());
}

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  mk_local_state_tag_and_pred state_predicate_protocol;
]

(**** Event Predicates ****)

let event_predicate_protocol: event_predicate single_message_event =
  fun tr prin e ->
    match e with
    | SenderSendMsg sender msg -> (
      rand_just_generated tr msg.secret
    )
    | ReceiverReceivedMsg sender receiver msg -> (
      event_triggered tr receiver (CommAuthReceiveMsg sender receiver (serialize single_message msg))
    )
#pop-options

/// List of all local event predicates.

val comm_layer_event_preds: comm_higher_layer_event_preds single_message
let comm_layer_event_preds = {
  default_comm_higher_layer_event_preds single_message with
  send_auth = (fun tr sender payload ->
      event_triggered tr sender (SenderSendMsg sender payload)
  );
  send_auth_later = (fun tr1 tr2 sender payload -> ())
}

let all_events = [
  event_predicate_communication_layer_and_tag comm_layer_event_preds;
  mk_event_tag_and_pred event_predicate_protocol
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

/// Lemmas that the global predicates contain all the local ones

let _ = do_split_boilerplate mk_state_pred_correct all_sessions
let _ = do_split_boilerplate mk_event_pred_correct all_events

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

#push-options "--ifuel 3"
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
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  ()
#pop-options

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
  enable_core_comm_layer_lemmas comm_layer_event_preds;
  ()
