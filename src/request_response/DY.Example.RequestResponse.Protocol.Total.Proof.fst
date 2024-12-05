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

val pkenc_pred_list_protocol: list (string & pkenc_crypto_predicate)
let pkenc_pred_list_protocol = [
  pkenc_crypto_predicates_communication_layer_and_tag
]

val sign_pred_list_protocol: list (string & sign_crypto_predicate)
let sign_pred_list_protocol = [
  sign_crypto_predicates_communication_layer_and_tag;
]

val aead_pred_list_protocol: list (string & aead_crypto_predicate)
let aead_pred_list_protocol = [
  aead_crypto_predicates_communication_layer_and_tag;
]

#push-options "--ifuel 2 --fuel 0"
val crypto_predicates_protocol: crypto_predicates
let crypto_predicates_protocol = {
  default_crypto_predicates with

  pkenc_pred = mk_pkenc_predicate pkenc_pred_list_protocol;

  sign_pred = mk_sign_predicate sign_pred_list_protocol;

  aead_pred = mk_aead_predicate aead_pred_list_protocol;
}
#pop-options

instance crypto_invariants_protocol: crypto_invariants = {
  usages = crypto_usages_protocol;
  preds = crypto_predicates_protocol;
}

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

val aead_pred_has_all_aead_preds:
  unit ->
  Lemma
  (ensures
    norm [delta_only [`%aead_pred_list_protocol; `%for_allP]; iota; zeta] (
      for_allP has_aead_predicate aead_pred_list_protocol
    )
  )
let aead_pred_has_all_aead_preds () =
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (aead_pred_list_protocol)));
  mk_aead_predicate_correct aead_pred_list_protocol;
  norm_spec [delta_only [`%aead_pred_list_protocol; `%for_allP]; iota; zeta] (for_allP has_aead_predicate aead_pred_list_protocol);
  ()
#pop-options

val protocol_crypto_invariants_has_communication_layer_crypto_predicates: squash has_communication_layer_reqres_crypto_predicates
let protocol_crypto_invariants_has_communication_layer_crypto_predicates =
  pkenc_pred_has_all_pkenc_preds ();
  sign_pred_has_all_sign_preds ();
  aead_pred_has_all_aead_preds ();
  ()

(*** Proofs ***)

val compute_message_proof:
  tr:trace ->
  client:principal -> server:principal ->
  nonce:bytes ->
  Lemma
  (requires
    is_knowable_by (join (principal_label client) (principal_label server)) tr nonce
  )
  (ensures
    is_knowable_by (join (principal_label client) (principal_label server)) tr (compute_message client nonce)
  )
let compute_message_proof tr client server nonce =
  let req:request = { client; nonce } in
  serialize_wf_lemma request (is_knowable_by (join (principal_label client) (principal_label server)) tr) req;
  ()

val decode_message_proof:
  tr:trace ->
  server:principal ->
  req_bytes:bytes -> req_label:label ->
  Lemma
  (requires
    is_knowable_by req_label tr req_bytes
  )
  (ensures (
    match decode_message req_bytes with
    | None -> True
    | Some {client=client'; nonce} -> is_knowable_by req_label tr nonce
  ))
let decode_message_proof tr server req_bytes req_label =
  match decode_message req_bytes with
  | None -> ()
  | Some {client; nonce} -> (    
    parse_wf_lemma request (is_knowable_by req_label tr) req_bytes;
    ()
  )
