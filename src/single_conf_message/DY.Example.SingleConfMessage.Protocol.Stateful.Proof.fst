module DY.Example.SingleConfMessage.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleConfMessage.Protocol.Total
open DY.Example.SingleConfMessage.Protocol.Total.Proof
open DY.Example.SingleConfMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 1 --z3rlimit 25  --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Trace invariants ***)

let state_predicate_protocol: local_state_predicate single_message_state = {
  pred = (fun tr prin state_id st ->
    match st with
    | SenderState receiver msg -> (
      let sender = prin in
      is_secret (comm_label sender receiver) tr msg.secret /\
      is_knowable_by (comm_label sender receiver) tr msg.secret
    )
    | ReceiverState msg -> (
      let receiver = prin in
      is_knowable_by (principal_label receiver) tr msg.secret
    )
  );
  pred_later = (fun tr1 tr2 prin state_id st -> ());
  pred_knowable = (fun tr prin state_id st -> ());
}

let event_predicate_protocol: event_predicate single_message_event =
  fun tr prin e ->
    match e with
    | SenderSendMsg sender receiver msg -> True
    | ReceiverReceivedMsg receiver msg -> (
      (exists sender. is_knowable_by (comm_label sender receiver) tr msg.secret) /\
      event_triggered tr receiver (CommConfReceiveMsg receiver (serialize single_message msg))
    )

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  mk_local_state_tag_and_pred state_predicate_protocol;
]

/// List of all local event predicates.

// This is just a demonstration how to use the `comm_higher_layer_event_preds`.
// If you don't need them you can just initialize them with
// `default_comm_higher_layer_event_preds`.
#push-options "--fuel 0 --ifuel 2"
val comm_layer_event_preds: comm_higher_layer_event_preds single_message
let comm_layer_event_preds = {
  default_comm_higher_layer_event_preds single_message with
  send_conf = (fun tr sender receiver (payload:single_message) ->
    event_triggered tr sender (SenderSendMsg sender receiver payload) /\

    // The user of the communication layer can
    // also use this function to demand specific
    // labels from parts of the payload. These
    // labels can then be used on the receiver
    // side. With the following requirement on
    // `secret`, we can assert the following on
    // the receiver side: `assert(is_secret
    // (comm_label sender receiver) tr secret \/
    // is_publishable tr payload);`
    is_secret (comm_label sender receiver) tr payload.secret
  );
  send_conf_later = (fun tr1 tr2 sender receiver payload -> ())
}
#pop-options

let all_events = [
  event_predicate_communication_layer_and_tag comm_layer_event_preds;
  mk_event_tag_and_pred event_predicate_protocol
]

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
