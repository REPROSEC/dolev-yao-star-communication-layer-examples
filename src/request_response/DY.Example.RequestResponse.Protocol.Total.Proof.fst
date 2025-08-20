module DY.Example.RequestResponse.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.RequestResponse.Protocol.Total
open DY.Example.RequestResponse.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val crypto_usages_protocol: crypto_usages
instance crypto_usages_protocol = default_crypto_usages

val pke_pred_list_protocol: list (string & pke_crypto_predicate)
let pke_pred_list_protocol = [
  pke_crypto_predicate_and_tag_communication_layer_reqres message_t;
]

val sign_pred_list_protocol: list (string & sign_crypto_predicate)
let sign_pred_list_protocol = [
  sign_crypto_predicate_and_tag_communication_layer_reqres message_t;
]

val aead_pred_list_protocol: list (string & aead_crypto_predicate)
let aead_pred_list_protocol = [
  aead_crypto_predicate_and_tag_communication_layer_reqres message_t;
]

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_protocol: crypto_predicates
let crypto_predicates_protocol = {
  default_crypto_predicates with

  pke_pred = mk_pke_predicate pke_pred_list_protocol;

  sign_pred = mk_sign_predicate sign_pred_list_protocol;

  aead_pred = mk_aead_predicate aead_pred_list_protocol;
}
#pop-options

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}

let _ = do_split_boilerplate mk_pke_predicate_correct pke_pred_list_protocol
let _ = do_split_boilerplate mk_sign_predicate_correct sign_pred_list_protocol
let _ = do_split_boilerplate mk_aead_predicate_correct aead_pred_list_protocol
