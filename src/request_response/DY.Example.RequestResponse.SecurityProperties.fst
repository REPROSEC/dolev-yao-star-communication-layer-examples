module DY.Example.RequestResponse.SecurityProperties

open DY.Core
open DY.Lib

open DY.Example.RequestResponse.Protocol.Total
open DY.Example.RequestResponse.Protocol.Stateful
open DY.Example.RequestResponse.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

val nonce_secrecy_client:
  tr:trace ->
  client:principal -> server:principal -> cmeta_data:comm_meta_data message_t -> nonce:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr nonce /\
    (
      (exists sid. state_was_set tr client sid (ClientSendRequest {server; cmeta_data; nonce})) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {server; cmeta_data; nonce}))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let nonce_secrecy_client tr client server cmeta_data nonce =
  attacker_only_knows_publishable_values tr nonce


#push-options "--fuel 1"
val server_authentication:
  tr:trace -> i:timestamp ->
  client:principal -> server:principal -> response:bytes -> key:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i client (CommClientReceiveResponse client server response key)    
  )
  (ensures
    (exists request.
      event_triggered (prefix tr i) server (CommServerSendResponse server request response)) \/
    is_corrupt (prefix tr i) (principal_label client) \/ 
    is_corrupt (prefix tr i) (principal_label server)
  )
let server_authentication tr i client server response key = ()
#pop-options
