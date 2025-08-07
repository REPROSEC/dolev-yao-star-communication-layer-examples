module DY.Example.RequestResponse.Protocol.Stateful

open Comparse
open DY.Core
open DY.Lib

open DY.Example.RequestResponse.Protocol.Total

instance comm_layer_reqres_tag_protocol: comm_layer_reqres_tag = {
  tag = "DY.Lib.Communication.Layer.Reqres.Protocol"
}

instance parser_serializer_protocol: comparse_parser_serializer message_t = {
  ps_a = ps_message_t;
  ps_able = mk_parseable_serializeable ps_message_t;
  eq_property = ();
}

[@@with_bytes bytes]
type client_state = {
  server: principal;
  cmeta_data: comm_meta_data message_t;
  nonce: bytes;
}

%splice [ps_client_state] (gen_parser (`client_state))
%splice [ps_client_state_is_well_formed] (gen_is_well_formed_lemma (`client_state))

[@@with_bytes bytes]
type server_state = {
  client: principal;
  nonce: bytes;
}

%splice [ps_server_state] (gen_parser (`server_state))
%splice [ps_server_state_is_well_formed] (gen_is_well_formed_lemma (`server_state))

[@@with_bytes bytes]
type protocol_state =
  | ClientSendRequest: client_state -> protocol_state
  | ServerReceiveRequest: server_state -> protocol_state
  | ClientReceiveResponse: client_state -> protocol_state


%splice [ps_protocol_state] (gen_parser (`protocol_state))
%splice [ps_protocol_state_is_well_formed] (gen_is_well_formed_lemma (`protocol_state))

instance parseable_serializeable_bytes_protocol_state: parseable_serializeable bytes protocol_state
  = mk_parseable_serializeable ps_protocol_state

instance local_state_protocol_state: local_state protocol_state = {
  tag = "Protocol.State";
  format = parseable_serializeable_bytes_protocol_state;
}

(*** Protocol Functions ***)

val client_send_request:
  communication_keys_sess_ids ->
  principal -> principal ->
  traceful (option (state_id & timestamp))
let client_send_request comm_keys_ids client server =
  let* nonce = mk_rand NoUsage (join (principal_label client) (principal_label server)) 32 in
  let payload = Request {client; nonce} in
  let*? (msg_id, cmeta_data) = send_request comm_keys_ids client server payload in
  let* sid = new_session_id client in
  set_state client sid (ClientSendRequest { server; cmeta_data; nonce } <: protocol_state);*
  return (Some (sid, msg_id))

val server_receive_request_send_response:
  communication_keys_sess_ids ->
  principal -> timestamp ->
  traceful (option timestamp)
let server_receive_request_send_response comm_keys_ids server msg_id =
  let*? (msg, req_meta_data) = receive_request comm_keys_ids server msg_id in
  guard_tr (Request? msg);*?
  let Request req = msg in
  let* sid = new_session_id server in
  set_state server sid (ServerReceiveRequest { client=req.client; nonce=req.nonce } <: protocol_state);*
  let*? msg_id = send_response server req_meta_data (Response {b=req.nonce}) in
  return (Some msg_id)

val client_receive_response:
  principal -> state_id -> timestamp ->
  traceful (option unit)
let client_receive_response client sid msg_id =
  let*? cstate = get_state client sid in
  guard_tr (ClientSendRequest? cstate);*?
  let ClientSendRequest { server; cmeta_data; nonce } = cstate in
  let*? (msg, _) = receive_response client cmeta_data msg_id in
  guard_tr (Response? msg);*?
  let Response res = msg in
  guard_tr (res.b = nonce);*?
  set_state client sid (ClientReceiveResponse { server; cmeta_data; nonce } <: protocol_state);*
  return (Some ())
