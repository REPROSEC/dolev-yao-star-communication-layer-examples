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

instance parseable_serializeable_bytes_request: parseable_serializeable bytes request
  = mk_parseable_serializeable ps_request

val compute_message: principal -> bytes -> bytes
let compute_message client nonce =
  let req = { client; nonce } in
  serialize request req

val decode_message: bytes -> option request
let decode_message msg =
  parse request msg
