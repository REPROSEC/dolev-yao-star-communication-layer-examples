module DY.Example.SingleConfAuthMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleConfAuthMessage.Protocol.Total.Proof
open DY.Example.SingleConfAuthMessage.Protocol.Stateful
open DY.Example.SingleConfAuthMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10  --z3cliopt 'smt.qi.eager_threshold=100'"

// Since the message is authenticated we can prove on the receiver side that
// either the sender triggered a send event or the sender is corrupt.
val sender_authentication:
  tr:trace -> i:timestamp ->
  sender:principal -> receiver:principal ->
  secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i receiver (ReceiverReceivedMsg sender receiver secret)
  )
  (ensures
    event_triggered tr sender (SenderSendMsg sender receiver secret) \/
    is_corrupt tr (long_term_key_label sender)
  )
let sender_authentication tr i sender receiver secret = ()


// Secrecy property of the secret from the sender's perspective
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

// Since the message is authenticated we can prove from the receiver's
// perspective that if the attacker knows the secret, either the sender or the
// receiver is corrupt.
val secret_secrecy_receiver:
  tr:trace -> sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr secret /\
    event_triggered tr receiver (ReceiverReceivedMsg sender receiver secret)
  )
  (ensures
    is_corrupt tr (principal_label sender) \/
    is_corrupt tr (principal_label receiver) \/
    is_corrupt tr (long_term_key_label sender)
  )
let secret_secrecy_receiver tr sender receiver secret =
  attacker_only_knows_publishable_values tr secret;
  ()
