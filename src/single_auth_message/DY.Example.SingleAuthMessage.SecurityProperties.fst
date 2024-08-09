module DY.Example.SingleAuthMessage.SecurityProperties

open Comparse
open DY.Core
open DY.Lib
open DY.Example.SingleAuthMessage.Protocol.Total
open DY.Example.SingleAuthMessage.Protocol.Total.Proof
open DY.Example.SingleAuthMessage.Protocol.Stateful
open DY.Example.SingleAuthMessage.Protocol.Stateful.Proof

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10  --z3cliopt 'smt.qi.eager_threshold=100'"

val sender_authentication:
  tr:trace -> sender:principal -> receiver:principal -> secret:bytes ->
  Lemma
  (requires
    trace_invariant tr /\
    event_triggered tr receiver (ReceiverReceivedMsg sender receiver secret (compute_message secret))
  )
  (ensures
    event_triggered tr sender (SenderSendMsg sender secret) \/
    (exists vk_sender. event_triggered tr receiver (CommAuthReceiveMsg sender receiver vk_sender (compute_message secret)) /\
      is_corrupt tr (get_signkey_label vk_sender))
  )
let sender_authentication tr sender receiver secret = ()
