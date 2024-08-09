module DY.Example.SingleConfMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleConfMessage.Protocol.Total
open DY.Example.SingleConfMessage.Protocol.Total.Proof
open DY.Example.SingleConfMessage.Protocol.Stateful
open DY.Example.SingleConfMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10  --z3cliopt 'smt.qi.eager_threshold=100'"

val receiver_authentication:
  tr:trace ->
  sender:principal -> receiver:principal ->
  secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr receiver (ReceiverReceivedMsg sender receiver secret (compute_message secret))
  )
  (ensures
    event_triggered tr sender (SenderSendMsg sender receiver secret) \/
    is_publishable tr (compute_message secret)
  )
let receiver_authentication tr sender receiver secret = ()

val secret_secrecy_sender:
  tr:trace -> sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr secret /\
    (exists sess_id. state_was_set tr sender sess_id (SenderState receiver secret))
  )
  (ensures
    is_corrupt tr (principal_label sender) \/ is_corrupt tr (principal_label receiver)
  )
let secret_secrecy_sender tr sender receiver secret =
  attacker_only_knows_publishable_values tr secret;
  ()
