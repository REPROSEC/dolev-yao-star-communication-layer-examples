module DY.Example.SingleConfMessage.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

(*
  C -> S: pkenc(pk_server, nonce, {sender; receiver; {secret}})
*)

[@@with_bytes bytes]
type single_message = {
  secret:bytes;
}

%splice [ps_single_message] (gen_parser (`single_message))
%splice [ps_single_message_is_well_formed] (gen_is_well_formed_lemma (`single_message))

instance parseable_serializeable_bytes_message: parseable_serializeable bytes single_message
  = mk_parseable_serializeable ps_single_message
