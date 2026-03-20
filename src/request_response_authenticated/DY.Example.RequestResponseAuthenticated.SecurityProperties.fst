module DY.Example.RequestResponseAuthenticated.SecurityProperties

open DY.Core
open DY.Lib

open DY.Example.RequestResponseAuthenticated.Protocol.Total
open DY.Example.RequestResponseAuthenticated.Protocol.Stateful
open DY.Example.RequestResponseAuthenticated.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3cliopt 'smt.qi.eager_threshold=100'"

val nonce_secrecy:
  tr:trace ->
  client:principal -> server:principal -> cmeta_data:comm_meta_data message_t -> nonce:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr nonce /\
    (
      (exists sid. state_was_set tr client sid (ClientSendRequest {server; cmeta_data; nonce})) \/
      (exists sid. state_was_set tr server sid (ServerReceiveRequest {client; nonce})) \/
      (exists sid. state_was_set tr client sid (ClientReceiveResponse {server; cmeta_data; nonce}))
    )
  )
  (ensures
    is_corrupt tr (principal_label client) \/ is_corrupt tr (principal_label server)
  )
let nonce_secrecy tr client server cmeta_data nonce =
  attacker_only_knows_publishable_values tr nonce


#push-options "--fuel 1"
val server_authentication:
  tr:trace -> i:timestamp ->
  client:principal -> response:message_t -> cmeta_data:comm_meta_data message_t ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i client (CommClientReceiveResponse client response cmeta_data <: communication_reqres_event message_t)    
  )
  (ensures
    event_triggered (prefix tr i) cmeta_data.server (CommServerSendResponse cmeta_data.client cmeta_data.server cmeta_data.request response cmeta_data.key <: communication_reqres_event message_t) \/
    is_corrupt (prefix tr i) (principal_label client) \/ 
    is_corrupt (prefix tr i) (principal_label cmeta_data.server)
  )
let server_authentication tr i client response cmeta_data = ()
#pop-options
