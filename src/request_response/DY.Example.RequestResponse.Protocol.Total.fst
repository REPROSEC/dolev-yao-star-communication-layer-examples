module DY.Example.RequestResponse.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

(*
  Client -> Server: enc{client, nonce}
  Server -> Client: enc{nonce}
*)

[@@with_bytes bytes]
type request = {
  client: principal;
  nonce: bytes;
}

%splice [ps_request] (gen_parser (`request))
%splice [ps_request_is_well_formed] (gen_is_well_formed_lemma (`request))

[@@with_bytes bytes]
type message_t =
  | Request: request -> message_t
  | Response: com_send_byte -> message_t

%splice [ps_message_t] (gen_parser (`message_t))
%splice [ps_message_t_is_well_formed] (gen_is_well_formed_lemma (`message_t))

instance parseable_serializeable_message_t: parseable_serializeable bytes message_t
  = mk_parseable_serializeable ps_message_t
