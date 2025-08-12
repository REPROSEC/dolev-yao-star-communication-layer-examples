module DY.Example.SingleAuthMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleAuthMessage.Protocol.Total
open DY.Example.SingleAuthMessage.Protocol.Total.Proof
open DY.Example.SingleAuthMessage.Protocol.Stateful
open DY.Example.SingleAuthMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10 --z3cliopt 'smt.qi.eager_threshold=100'"

// For authenticated messages we can prove on the receiver side that either the
// sender triggered a send event or the sender is corrupt.
val sender_authentication:
  tr:trace -> i:timestamp ->
  sender:principal -> receiver:principal ->
  msg:single_message ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i receiver (ReceiverReceivedMsg sender receiver msg)
  )
  (ensures
    event_triggered tr sender (SenderSendMsg sender msg) \/
    is_corrupt tr (long_term_key_label sender)
  )
let sender_authentication tr i sender receiver secret = ()

// This is the same securtiy lemma as above but with the events from the
// communication layer. This allows us to argue with the `(prefix tr i)`
// function. (Not sure why this does not work in the lemma above)
val sender_authentication':
  tr:trace -> i:timestamp ->
  sender:principal -> receiver:principal ->
  payload:single_message ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered_at tr i receiver (CommAuthReceiveMsg sender receiver payload <: communication_core_event single_message)
  )
  (ensures
    event_triggered (prefix tr i) sender (CommAuthSendMsg sender payload <: communication_core_event single_message) \/
    is_corrupt (prefix tr i) (long_term_key_label sender)
  )
let sender_authentication' tr i sender receiver payload = ()
