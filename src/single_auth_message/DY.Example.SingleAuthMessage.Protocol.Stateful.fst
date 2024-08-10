module DY.Example.SingleAuthMessage.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleAuthMessage.Protocol.Total

(*** State type ***)

[@@with_bytes bytes]
type single_message_state =
  | SenderState: sender:principal -> secret:bytes -> single_message_state
  | ReceiverState: sender:principal -> secret:bytes -> payload:bytes -> single_message_state

%splice [ps_single_message_state] (gen_parser (`single_message_state))
%splice [ps_single_message_state_is_well_formed] (gen_is_well_formed_lemma (`single_message_state))

instance parseable_serializeable_bytes_single_message_state: parseable_serializeable bytes single_message_state
 = mk_parseable_serializeable ps_single_message_state

instance local_state_single_message_state: local_state single_message_state = {
  tag = "SingleAuthMessage.State";
  format = parseable_serializeable_bytes_single_message_state;
}

(*** Event type ***)

[@@with_bytes bytes]
type single_message_event =
  | SenderSendMsg: sender:principal -> secret:bytes -> single_message_event
  | ReceiverReceivedMsg: sender:principal -> receiver:principal -> secret:bytes -> payload:bytes -> single_message_event

%splice [ps_single_message_event] (gen_parser (`single_message_event))
%splice [ps_single_message_event_is_well_formed] (gen_is_well_formed_lemma (`single_message_event))

instance event_protocol_event: event single_message_event = {
  tag = "SingleAuthMessage.Event";
  format = mk_parseable_serializeable ps_single_message_event;
}

(*** Stateful code ***)

val prepare_message: principal -> principal -> traceful state_id
let prepare_message sender receiver =
  let* secret = mk_rand NoUsage public 32 in
  trigger_event sender (SenderSendMsg sender secret);*
  let* state_id = new_session_id sender in
  set_state sender state_id (SenderState sender secret <: single_message_state);*
  return state_id

val send_message: communication_keys_sess_ids -> principal -> principal -> state_id -> traceful (option timestamp)
let send_message comm_keys_ids sender receiver state_id =
  let*? st:single_message_state = get_state sender state_id in
  match st with
  | SenderState sender secret -> (
    let msg = compute_message secret in
    let*? msg_id = send_authenticated comm_keys_ids sender receiver msg in
    return (Some msg_id)
  )
  | _ -> return None

val receive_message: communication_keys_sess_ids -> principal -> timestamp -> traceful (option state_id)
let receive_message comm_keys_ids receiver msg_id =
  let*? msg:communication_message_base = receive_authenticated comm_keys_ids receiver msg_id in
  let*? single_msg:single_message = return (decode_message msg.payload) in
  trigger_event receiver (ReceiverReceivedMsg msg.sender receiver single_msg.secret msg.payload);*
  let* state_id = new_session_id receiver in
  set_state receiver state_id (ReceiverState msg.sender single_msg.secret msg.payload <: single_message_state);*
  return (Some state_id)