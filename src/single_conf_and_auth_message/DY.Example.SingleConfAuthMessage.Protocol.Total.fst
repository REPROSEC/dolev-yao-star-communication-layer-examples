module DY.Example.SingleConfAuthMessage.Protocol.Total

open Comparse
open DY.Core
open DY.Lib

(*
  C -> S: {sender; receiver; pkenc(pk_server, enc_nonce, {secret}); sign(sk_sender, sign_nonce, {sender; receiver; pkenc(pk_server, enc_nonce, {secret})})}
*)

[@@with_bytes bytes]
type single_message = {
  secret:bytes;
}

%splice [ps_single_message] (gen_parser (`single_message))
%splice [ps_single_message_is_well_formed] (gen_is_well_formed_lemma (`single_message))

instance parseable_serializeable_bytes_single_message: parseable_serializeable bytes single_message
  = mk_parseable_serializeable ps_single_message
