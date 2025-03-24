module DY.Example.RequestResponse.Debug

open DY.Core
open DY.Lib

open DY.Example.RequestResponse.Protocol.Stateful

let debug () : traceful (option unit) =
  let _ = IO.debug_print_string "************* Trace *************\n" in
  (*** Initialize protocol run ***)
  let client = "client" in
  let server = "server" in

  let*? client_comm_keys_sess_ids, server_comm_keys_sess_ids = initialize_communication client server in

  let*? (sid, msg_id) = client_send_request client_comm_keys_sess_ids client server in

  let*? msg_id = server_receive_request_send_response server_comm_keys_sess_ids server msg_id in

  client_receive_response client sid msg_id;*?

  let* tr = get_trace in
  let _ = IO.debug_print_string (
      trace_to_string default_trace_to_string_printers tr
    ) in

  return (Some ())

//Run ``debug ()`` when the module loads
#push-options "--warn_error -272"
let _ = debug () Nil
#pop-options
