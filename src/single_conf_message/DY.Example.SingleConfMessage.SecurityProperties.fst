module DY.Example.SingleConfMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleConfMessage.Protocol.Total
open DY.Example.SingleConfMessage.Protocol.Total.Proof
open DY.Example.SingleConfMessage.Protocol.Stateful
open DY.Example.SingleConfMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10  --z3cliopt 'smt.qi.eager_threshold=100'"

// This is the main security property of a
// confidential message. It states from the sender
// perspective that the secret is not leaked to
// the attacker as long as the sender and receiver
// are honest.
//
// **Note:** We know that if the receiver is
// honest only the receiver can decrypt the
// secret. This allows us to argue from the
// sender's perspective that if the attacker knows
// the secret either the sender or the receiver is
// corrupt.
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

// On the receiver side we don't have any
// guarantees on the secrecy of the secret. We can
// only prove that if the attacker knows the
// secret, it is publishable.
val secret_secrecy_receiver:
  tr:trace -> sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    attacker_knows tr secret
  )
  (ensures
    is_publishable tr secret
  )
let secret_secrecy_receiver tr sender receiver secret =
  attacker_only_knows_publishable_values tr secret;
  ()

// We can also not authenticate the sender because
// the attacker could write an arbitrary sender in
// the message. The only thing we can prove is
// that if the secret is not publisable, there
// exists a sender that triggered the send event.
val sender_authentication:
  tr:trace ->
  receiver:principal ->
  secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr receiver (ReceiverReceivedMsg receiver secret (compute_message secret))
  )
  (ensures
    (exists sender. event_triggered tr sender (SenderSendMsg sender receiver secret)) \/
    is_publishable tr (compute_message secret)
    // We cannot prove `is_corrupt tr
    // (principal_label sender)` because the
    // sender is not authenticated. If the
    // attacker creates this message, they can
    // choose an arbitrary sender for the sender
    // field.
  )
let sender_authentication tr receiver secret = ()

(*

// This is not provable because the receiver event
// is in the future, and it is not guaranteed that
// it is ever triggered.

val recever_authentication:
  tr:trace ->
  sender:principal -> receiver:principal ->
  secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr sender (SenderSendMsg sender receiver secret)
    
  )
  (ensures
    event_triggered tr receiver (ReceiverReceivedMsg sender receiver secret (compute_message secret)) \/
    is_corrupt tr (principal_label receiver)
    //is_publishable tr (compute_message secret)
  )
let recever_authentication tr sender receiver secret = ()
*)
