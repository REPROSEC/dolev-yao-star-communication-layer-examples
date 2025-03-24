module DY.Example.SingleConfMessage.Debug

open DY.Core
open DY.Lib
open DY.Example.SingleConfMessage.Protocol.Stateful

(*** Example Protocol Run with Trace Printing ***)

let debug () : traceful (option unit) =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  (*** Initialize protocol run ***)
  let sender = "sender" in
  let receiver = "receiver" in

  let*? sender_comm_keys_sess_ids, receiver_comm_keys_sess_ids = initialize_communication sender receiver in

  // sender prepare message
  let* sender_session_id = prepare_message sender receiver in

  // sender send message
  let*? msg_id = send_message sender_comm_keys_sess_ids sender receiver sender_session_id in

  // receiver receive message
  let*? receiver_session_id = receive_message receiver_comm_keys_sess_ids receiver msg_id in

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string default_trace_to_string_printers tr
    ) in

  return (Some ())

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug () Nil
#pop-options
