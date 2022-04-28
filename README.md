# Execution Environment
The states of our protocol were implemented as Tamarin rules, and the security features were represented as Tamarin lemmas. The investigation was performed on an Ubuntu Linux machine with 4 CPU cores and 8 gigabytes of RAM. The findings and outcomes of formal verification in the classical scenario using the Tamarin prover are described in the following sections.

**1) Correctness:** Two lemmas are defined to demonstrate the soundness of our model, proving that the protocol can be completed successfully. This property is required for the analysis since if it is not met, all subsequent proofs will fail because the automated solver will never be able to meet their criteria.

```
lemma executable_1: exists-trace
"Ex PIDV V1 V3 T1 #i #j.
Send(<PIDV,V1,V3,T1>)@i &
Receive(<PIDV,V1,V3,T1>) @j &
#i < #j"

lemma executable_2:
exists-trace
"Ex PIDA1 A1 A2 A4 V1 T2 #i #j.
Send(<PIDA1, A1, A2, A4, V1, T2>)@i &
Receive(<PIDA1, A1, A2, A4, V1, T2>)@j &
#i < #j
"

lemma executable_3:
exists-trace
"Ex PIDS S1 S2 S3 S5 T3 #i #j.
Send(<PIDS,S1,S2,S3,S5,T3>) @i &
Receive(<PIDS,S1,S2,S3,S5,T3>) @j &
#i < #j"

lemma executable_4:
exists-trace
"Ex PIDA2 A1 A2 A6 T4 S1 S2 #i #j.
Send(<PIDA2,A1,A2,A6,T4,S1,S2>) @i &
Receive(<PIDA2,A1,A2,A6,T4,S1,S2>) @j &
#i < #j"
```

These lemmas demonstrate that anytime an Initiator sends a message, a Responder must receive that message in order for the protocol to continue. All four lemmas are satisfied by our suggested model.

# Threat Model and Security Properties Modeling
Security attributes are represented in TAMARIN as (temporal) first-order logical equations. The protocol model generates so-called action traces, which are then examined.
Protocol rules have a multiset of actions as their second argument, which are appended to the action trace when the rewrite system executes a transition based on a ground rule instance. As a result, the action trace may be thought of as a log of the transition rules-defined actions in a given execution. The modeller determines what is logged, allowing us to log appropriate events that allow us to specify the necessary attributes.
1) Adversary Capabilities Modeling: We take it for granted that communication channels aren't secure.We assume that communication channels are insecure, so we assume the worst: the adversary has complete network control, including the ability to drop and inject arbitrary messages as well as eavesdrop on all outgoing communications.
The network part of the Dolev-Yao attacker model is how this model is known in symbolic security verification.
The following rule is used to mimic the dynamic compromise of long-term private keys. It reads a private-key database entry and sends it to the attacker, as it should. Agent A's long-term key has been compromised, according to this rule's observable LtkReveal action.
```
rule Reveal_ltk:
[ !Ltk($A, ltkA, K , P) ]
--[ Reveal($A) ]->
[ Out(ltkA) ]
```

2) Aliveness Authentication: We claim that a protocol guarantees the aliveness of another agent B to an initiator A if, whenever A (as initiator) completes a run of the protocol, ostensibly with responder B, then B had previously run the protocol.
It's worth noting that B may not have realized he was running the protocol with A. Also, it's possible that B hasn't executed the procedure in a while. Even this rudimentary kind of authentication is a challenge for many systems. This is due to an intruder performing a mirror attack, merely reflecting an agent's messages back at himself in a number of circumstances.
