module DY.Example.RequestResponse.Protocol.Stateful.Proof

open Comparse
open DY.Core
open DY.Lib

open DY.Communication.Example.CustomTactics

open DY.Example.RequestResponse.Protocol.Total
open DY.Example.RequestResponse.Protocol.Total.Proof
open DY.Example.RequestResponse.Protocol.Stateful

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

(*** State Predicates ***)

#push-options "--ifuel 3 --z3rlimit 100"
let state_predicates_protocol: local_state_predicate protocol_state = {
  pred = (fun tr prin sess_id st ->
    match st with
    | ClientSendRequest {server; cmeta_data; nonce} -> (
      let client = prin in
      comm_meta_data_knowable tr message_t client cmeta_data /\
      is_secret (comm_label client server) tr nonce
    )
    | ServerReceiveRequest {client; nonce} -> (
      let server = prin in
      is_knowable_by (principal_label server) tr nonce /\
      (is_secret (comm_label client server) tr nonce \/
        is_well_formed message_t (is_publishable tr) (Request {client; nonce}))
    )
    | ClientReceiveResponse {server; cmeta_data; nonce} -> (
      let client = prin in
      comm_meta_data_knowable tr message_t client cmeta_data /\
      is_secret (comm_label client server) tr nonce
    )
  );
  pred_later = (fun tr1 tr2 prin sess_id st -> ());
  pred_knowable = (fun tr prin sess_id st -> (
    let lab = principal_typed_state_content_label prin (DY.Lib.State.Typed.tag #protocol_state) sess_id st in
    match st with
    | ClientSendRequest {server; cmeta_data; nonce} -> (
      assert(is_knowable_by lab tr nonce);
      comm_meta_data_knowable_proof tr message_t protocol_state sess_id st prin cmeta_data;
      ()
    )
    | ServerReceiveRequest {client; nonce} -> (
      assert(is_knowable_by lab tr nonce);
      ()
    )
    | ClientReceiveResponse {server; cmeta_data; nonce} -> (
      assert(is_knowable_by lab tr nonce);
      comm_meta_data_knowable_proof tr message_t protocol_state sess_id st prin cmeta_data;
      ()
    )
  ));
}
#pop-options

val protocol_state_tag: string
let protocol_state_tag = "Protocol.State"

let all_sessions = [
  pki_tag_and_invariant;
  private_keys_tag_and_invariant;
  state_predicate_and_tag_communication_layer_reqres message_t;
  mk_local_state_tag_and_pred state_predicates_protocol;
]

let state_update_predicate_protocol: local_state_update_predicate #crypto_invariants_protocol protocol_state = {
  update_pred = (fun tr prin sess_id b1 b2 -> True);
  update_pred_later = (fun tr1 tr2 prin sess_id b1 b2 -> ());
  update_pred_trans = (fun tr prin sess_id b1 b2 b3 -> ());
}

let all_state_update_preds = [
  pki_tag_and_state_update_pred;
  private_keys_tag_and_state_update_pred;
  state_update_predicates_communication_layer_and_tag message_t;
  mk_local_state_tag_and_update_pred state_update_predicate_protocol;
]

(*** Event Predicates ***)

#push-options "--ifuel 2"
instance crpreds: comm_reqres_preds message_t = {
  send_request_pred = (fun tr client server (payload:message_t) key_label ->
    match payload with
    | Request {client; nonce} -> (
      is_secret (comm_label client server) tr nonce
    )
    | Response b -> True
  );
  send_request_pred_later = (fun tr1 tr2 client server payload key_label -> ());
  send_response_pred = (fun tr server request response key_label -> True);
  send_response_pred_later = (fun tr1 tr2 server request response key_label -> ())
}
#pop-options

let all_events = event_predicate_communication_layer_reqres_and_tag message_t

(*** Combine all Invariants ***)

/// Create the global trace invariants.

let trace_invariants_protocol: trace_invariants = {
  state_pred = mk_state_pred all_sessions;
  state_update_pred = mk_state_update_pred all_state_update_preds;
  event_pred = mk_event_pred all_events;
}

instance protocol_invariants_protocol: protocol_invariants = {
  crypto_invs = crypto_invariants_protocol;
  trace_invs = trace_invariants_protocol;
}

/// Lemmas that the global predicates contain all the local ones

let fst_dtuple (x: dtuple2 'a 'b) : 'a = Mkdtuple2?._1 x

#push-options "--fuel 4"
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst_dtuple (all_sessions)));
  do_split_boilerplate mk_state_pred_correct all_sessions
)
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst_dtuple (all_state_update_preds)));
  do_split_boilerplate mk_state_update_pred_correct all_state_update_preds
)
let _ = (
  assert_norm(List.Tot.no_repeats_p (List.Tot.map fst (all_events)));
  do_split_boilerplate mk_event_pred_correct all_events
)

let _:squash (has_communication_layer_reqres_predicates message_t) = ()
#pop-options

(*** Proofs ***)

#push-options "--ifuel 0 --fuel 0 --z3rlimit 100"
val client_send_request_proof:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  client:principal -> server:principal ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_send_request comm_keys_ids client server tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (client_send_request comm_keys_ids client server tr)]
let client_send_request_proof tr comm_keys_ids client server =
  let (nonce, tr_nc) = mk_rand NoUsage (comm_label client server) 32 tr in
  assert(trace_invariant tr_nc);
  let payload = Request {client; nonce} in
  let (x_snd, tr_snd) = send_request Unauthenticated comm_keys_ids client server payload tr_nc in
  
  send_request_proof tr_nc Unauthenticated comm_keys_ids client server payload;
  assert(trace_invariant tr_snd);
  match x_snd with
  | None -> ()
  | Some (msg_id, cmeta_data) -> (
    let (sid, tr_sid) = new_session_id client tr_snd in
    assert(trace_invariant tr_sid);
    let (x_st, tr_st) = set_state client sid (ClientSendRequest { server; cmeta_data; nonce } <: protocol_state) tr_sid in
    derive_comm_meta_data_knowable tr_sid Unauthenticated cmeta_data client;
    assert(trace_invariant tr_st);
    ()
  )
#pop-options

#push-options "--ifuel 0 --fuel 0 --z3rlimit 100"
val server_receive_request_send_response_proof:
  tr:trace ->
  comm_keys_ids:communication_keys_sess_ids ->
  server:principal ->
  msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = server_receive_request_send_response comm_keys_ids server msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (server_receive_request_send_response comm_keys_ids server msg_id tr)]
let server_receive_request_send_response_proof tr comm_keys_ids server msg_id =
  let (_, tr_out) = server_receive_request_send_response comm_keys_ids server msg_id tr in
  let (x_recv, tr_recv) = receive_request Unauthenticated comm_keys_ids server msg_id tr in
  receive_request_proof message_t tr Unauthenticated comm_keys_ids server msg_id;
  
  assert(trace_invariant tr_recv);
  match x_recv with
  | None -> assert(tr_recv == tr_out)
  | Some (msg, req_meta_data) -> (
    let (x_gd, tr_gd) = guard_tr (Request? msg) tr_recv in
    assert(trace_invariant tr_gd);
    match x_gd with
    | None -> assert(tr_gd == tr_out)
    | Some () -> (
      receive_request_unauthenticated_properties message_t tr comm_keys_ids server msg_id;
      let Request req = msg in
      let (sid, tr_sid) = new_session_id server tr_gd in
      assert(trace_invariant tr_sid);
      let ((), tr_st) = set_state server sid (ServerReceiveRequest { client=req.client; nonce=req.nonce } <: protocol_state) tr_sid in
      assert(trace_invariant tr_st) by (
        let open FStar.Tactics in
        let _ = tcut (quote (squash (
          let (_, tr_st) = set_state #protocol_state #local_state_protocol_state server sid (ServerReceiveRequest { client=req.client; nonce=req.nonce } <: protocol_state) tr_sid in
          trace_invariant tr_st
        ))) in

        smt ();

        apply_lemma (`set_state_invariant);
        exact (`state_predicates_protocol);
        exact (`state_update_predicate_protocol);
        let _ = repeatn 4 split in

        norm [delta_only [`%Mklocal_state_predicate?.pred; `%state_predicates_protocol]; iota];
        let _ = pose_lemma (quote request_message_unauthenticated_properties_send_request tr_sid req_meta_data) in
        let _ = repeatn 3 smt in
        assumption' ();
        let _ = repeatn 2 smt in

        dump "";
        ()
      );
      let (x_snd, tr_snd) = send_response server req_meta_data (Response req.nonce) tr_st in
      assert(trace_invariant tr_snd) by (
        let open FStar.Tactics in
        let _ = tcut (quote (squash (
            let (_, tr_snd) = send_response server req_meta_data (Response req.nonce) tr_st in
            trace_invariant tr_snd
        ))) in

        smt ();

        apply_lemma (`send_response_proof);
        exact (`crpreds);

        let _ = repeatn 4 split in
        assumption' ();
        smt ();
        smt ();

        norm [delta_only [`%Mkcomm_reqres_preds?.send_response_pred; `%crpreds]; iota];
        exact (`());

        let _ = pose_lemma (quote request_message_unauthenticated_properties_request' tr_st req_meta_data) in
        let _ = repeatn 2 smt in

        dump "";
        ()
      );
      assert(tr_snd == tr_out);
      ()
    )
  )
#pop-options


#push-options "--ifuel 0 --fuel 0 --z3rlimit 30"
val client_receive_response_proof:
  tr:trace ->
  client:principal ->
  sid:state_id ->
  msg_id:timestamp ->
  Lemma
  (requires
    trace_invariant tr
  )
  (ensures (
    let (_, tr_out) = client_receive_response client sid msg_id tr in
    trace_invariant tr_out
  ))
  [SMTPat (trace_invariant tr); SMTPat (client_receive_response client sid msg_id tr)]
let client_receive_response_proof tr client sid msg_id =
  let (_, tr_out) = client_receive_response client sid msg_id tr in

  let (x_st, tr_st) = get_state client sid tr in
  assert(trace_invariant tr_st);
  match x_st with
  | None -> assert(tr_st == tr_out)
  | Some cstate ->
    let (x_gd1, tr_gd1) = guard_tr (ClientSendRequest? cstate) tr_st in
    assert(trace_invariant tr_gd1);
    match x_gd1 with
    | None -> assert(tr_gd1 == tr_out)
    | Some () ->
      let ClientSendRequest { server; cmeta_data; nonce } = cstate in

      let (x_recv, tr_recv) = receive_response client cmeta_data msg_id tr_gd1 in
      receive_response_proof tr_gd1 client cmeta_data msg_id;
      assert(trace_invariant tr_recv);
      match x_recv with
      | None -> assert(tr_recv == tr_out)
      | Some (msg, _) ->
        let (x_gd2, tr_gd2) = guard_tr (Response? msg) tr_recv in
        assert(trace_invariant tr_gd2);
        match x_gd2 with
        | None -> assert(tr_gd2 == tr_out)
        | Some () ->
          let Response res = msg in
          let (x_gd3, tr_gd3) = guard_tr (res = nonce) tr_gd2 in
          assert(trace_invariant tr_gd3);
          match x_gd3 with
          | None -> assert(tr_gd3 == tr_out)
          | Some () ->
            let ((), tr_set) = set_state client sid (ClientReceiveResponse { server; cmeta_data; nonce } <: protocol_state) tr_gd3 in
            assert(trace_invariant tr_set) by (
              let open FStar.Tactics in
              let _ = tcut (quote (squash (
                let (_, tr_set) = set_state #protocol_state #local_state_protocol_state client sid (ClientReceiveResponse { server; cmeta_data; nonce } <: protocol_state) tr_gd3 in
                trace_invariant tr_set
              ))) in

              smt ();

              apply_lemma (`set_state_invariant);
              exact (`state_predicates_protocol);
              exact (`state_update_predicate_protocol);
              let _ = repeatn 4 split in

              norm [ delta_only [`%Mklocal_state_predicate?.pred; `%state_predicates_protocol]; iota];

              split ();
              let _ = repeatn 3 smt in
              assumption' ();
              let _ = repeatn 2 smt in

              dump "";
              ()
            );
            
            assert(tr_set == tr_out);
            ()
#pop-options
