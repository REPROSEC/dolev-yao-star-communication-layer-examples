module DY.Example.SingleAuthMessage.Protocol.Total.Proof

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleAuthMessage.Protocol.Total
open DY.Example.SingleAuthMessage.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** Cryptographic invariants ***)

val crypto_usages_protocol: crypto_usages
instance crypto_usages_protocol = default_crypto_usages

val pkenc_pred_list_protocol: list (string & pkenc_crypto_predicate)
let pkenc_pred_list_protocol = [
  pkenc_crypto_predicates_communication_layer_and_tag
]

val sign_pred_list_protocol: list (string & sign_crypto_predicate)
let sign_pred_list_protocol = [
  sign_crypto_predicates_communication_layer_and_tag;
]

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_protocol: crypto_predicates
let crypto_predicates_protocol = {
  default_crypto_predicates with

  pkenc_pred = mk_pkenc_predicate pkenc_pred_list_protocol;

  sign_pred = mk_sign_predicate sign_pred_list_protocol;
}

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}
#pop-options

#push-options "--ifuel 0 --fuel 1"
val pkenc_pred_has_all_pkenc_preds: 
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%pkenc_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_pkenc_predicate pkenc_pred_list_protocol
    )
  )
let pkenc_pred_has_all_pkenc_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (pkenc_pred_list_protocol)));
  mk_pkenc_predicate_correct pkenc_pred_list_protocol;
  norm_spec [delta_only [`%pkenc_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_pkenc_predicate pkenc_pred_list_protocol);
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

val protocol_crypto_invariants_has_communication_layer_invariants: squash has_communication_layer_invariants
let protocol_crypto_invariants_has_communication_layer_invariants =
  pkenc_pred_has_all_pkenc_preds ();
  sign_pred_has_all_sign_preds ();
  ()

(*** Proofs ***)

val compute_message_proof:
  tr:trace ->
  sender:principal -> receiver:principal ->
  secret:bytes ->
  Lemma
  (requires
    event_triggered tr sender (SenderSendMsg sender secret) /\
    is_publishable tr secret
  )
  (ensures
    is_publishable tr (compute_message secret)
  )
let compute_message_proof tr sender receiver secret =
  serialize_wf_lemma single_message (is_publishable tr) {secret;};
  ()

val decode_message_proof:
  tr:trace ->
  sender:principal -> receiver:principal ->
  msg_bytes:bytes ->
  Lemma
  (requires
    is_publishable tr msg_bytes
  )
  (ensures (
    match decode_message msg_bytes with
    | Some msg -> (
      is_publishable tr msg.secret
    )
    | None -> True
  )
  )
let decode_message_proof tr sender receiver msg_bytes =
  match decode_message msg_bytes with
  | Some msg -> (
    parse_wf_lemma single_message (is_publishable tr) msg_bytes;
    ()
  )
  | None -> ()
