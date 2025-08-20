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

instance comm_layer_core_config_protocol: comm_layer_core_config single_message = {
  core_tag = "DY.Lib.Communication.Layer.Core.Protocol";
  core_ps_a = ps_single_message;
}
