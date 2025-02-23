module DY.Example.SingleConfMessage.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleConfMessage.Protocol.Total
open DY.Example.SingleConfMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val crypto_usages_protocol: crypto_usages
instance crypto_usages_protocol = default_crypto_usages

val pke_pred_list_protocol: list (string & pke_crypto_predicate)
let pke_pred_list_protocol = [
  pke_crypto_predicates_communication_layer_and_tag
]

val sign_pred_list_protocol: list (string & sign_crypto_predicate)
let sign_pred_list_protocol = [
  sign_crypto_predicates_communication_layer_and_tag;
]

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_protocol: crypto_predicates
let crypto_predicates_protocol = {
  default_crypto_predicates with

  pke_pred = mk_pke_predicate pke_pred_list_protocol;

  sign_pred = mk_sign_predicate sign_pred_list_protocol;
}
#pop-options

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}

#push-options "--ifuel 0 --fuel 1"
val pke_pred_has_all_pke_preds: 
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%pke_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_pke_predicate pke_pred_list_protocol
    )
  )
let pke_pred_has_all_pke_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (pke_pred_list_protocol)));
  mk_pke_predicate_correct pke_pred_list_protocol;
  norm_spec [delta_only [`%pke_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_pke_predicate pke_pred_list_protocol);
  ()

val sign_pred_has_all_sign_preds:
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%sign_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_sign_predicate sign_pred_list_protocol
    )
  )
let sign_pred_has_all_sign_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (sign_pred_list_protocol)));
  mk_sign_predicate_correct sign_pred_list_protocol;
  norm_spec [delta_only [`%sign_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_sign_predicate sign_pred_list_protocol);
  ()
#pop-options

val protocol_crypto_invariants_has_communication_layer_crypto_predicates: squash has_communication_layer_crypto_predicates
let protocol_crypto_invariants_has_communication_layer_crypto_predicates =
  pke_pred_has_all_pke_preds ();
  sign_pred_has_all_sign_preds ();
  ()
