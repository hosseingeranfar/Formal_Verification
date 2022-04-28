# Execution Environment
The states of our protocol were implemented as Tamarin rules, and the security features were represented as Tamarin lemmas. The investigation was performed on an Ubuntu Linux machine with 4 CPU cores and 8 gigabytes of RAM. The findings and outcomes of formal verification in the classical scenario using the Tamarin prover are described in the following sections.

1) Correctness: Two lemmas are defined to demonstrate the soundness of our model, proving that the protocol can be completed successfully. This property is required for the analysis since if it is not met, all subsequent proofs will fail because the automated solver will never be able to meet their criteria.

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
```
lemma aliveness_V_A:
"All V A V3 #i.
Commit(A,V,V3)@i
==> (Ex V id #j. Create(V, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
lemma aliveness_A_S:
"All A S A4 #i.
Commit(S,A,A4)@i
==> (Ex A id #j. Create(A, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
lemma aliveness_S_A:
"All A S S5 #i.
Commit(A,S,S5)@i
==> (Ex S id #j. Create(S, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
lemma aliveness_A_V:
"All V A A6 #i.
Commit(V,A,A6)@i
==> (Ex A id #j. Create(A, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"
```

3) Perfect Forward Secrecy: According to this lemma, when a secret action Secret(x) occurs at time point #I the adversary is unaware of x or an agent who claimed to be honest at time point I has been compromised at time point #r. Before a compromise, messages classified with a Secret action must remain secret.

```
lemma secrecy_PFS_Nonces:
"All Nv Na Ns #i #j #k.
Secret(Nv) @i &
Secret(Na) @j &
Secret(Ns) @k ==>
not (Ex #m. K(Nv)@m) &
not (Ex #n. K(Na)@n) &
not (Ex #o. K(Ns)@o)
| (Ex A #r. Reveal(A)@r & Honest(A) @i
& Honest(A) @j & Honest(A) @k
& #r < #i
& #r < #j
& #r < #k)"
```

4) Session key secrecy: In this part, we show that session keys issued by entities such as the Vehicle-Aggregator and the Aggregator-Server are kept private from an  Adversary. We believe it is impossible for a Server'S' to set up a session key 'SKas1' and 'SKav2' with Aggregator'A' and for the adversary to know 'SKas1' and 'SKav2' without doing a long-term key reveal on 'S'.

```
lemma Server_Aggregator_session_key_secrecy:
not(
Ex S A SKas1 SKas2 #i #j #k #l.
S_create_session(S, A, SKas1) @ #i
& A_create_session1(A, S, SKas2) @ #j
& K(SKas1) @ #k
& K(SKas2) @ #l
& not(Ex #r. Reveal(S) @ r)
& not(Ex #s. Reveal(A) @ s)
)
"
```

Furthermore, an Aggregator'A' cannot have established up a session key 'SKav1' and 'SKav2' with Vehicle'V' and the adversary knows 'SKav1' and 'SKav2' without doing a long-term key reveal on 'A'.

```
lemma Aggregator_Vehicle_session_key_secrecy:
"
not(
Ex V A SKav1 SKav2 #i #j #k #l.
A_create_session2(A,V,SKav1) @ #i
& V_create_session(V, A, SKav2) @ #j
& K(SKav1) @ #k
& K(SKav2) @ #l
& not(Ex #r. Reveal(A) @ r)
& not(Ex #s. Reveal(V) @ s)
)
"

5) MITM:

```
lemma Man_in_the_middle:
"
All V A S SKav1 SKav2 SKas1 SKas2 #i #j #k #l.
(S_create_session(S, A, SKas1) @ #i &
A_create_session1(A, S, SKas2) @j &
A_create_session2(A,V,SKav1) @k &
V_create_session(V, A, SKav2) @ #l &
#i < #j &
#j < #k &
12
#k < #l &
not(V= A)&
not(A= S)
)
==> not(Ex #m. K(SKav1) @ #m)
| not(Ex #n. K(SKas1) @ #n)
| not(Ex #o. K(SKav2) @ #o)
| not(Ex #p. K(SKas2) @ #p)
"

6) Identity Protection: The purpose of this lemma is to protect identities from passive attacks while also protecting identity peers from active attacker exposure.


```
lemma Identity_hiding_V_A :
" All V A SKav2 #i .
V_create_session(V, A, SKav2) @ #i
& not ( Ex #k . Reveal (V) @ #k)
& not ( Ex #k . Reveal (A) @ #k)
==> not ( Ex #j . K(V) @ #j)
& not ( Ex #l . K(A) @ #l) "
lemma Identity_hiding_A_S :
" All A S SKas2 #i .
A_create_session1(A, S, SKas2) @ #i
& not ( Ex #k . Reveal (A) @ #k)
& not ( Ex #k . Reveal (S) @ #k)
==> not ( Ex #j . K(A) @ #j)
& not ( Ex #l . K(S) @ #l) "
```
# Formal Analysis using Tamarin :

```
/*
 *  Author: Hossein Geranfar
 *  Model Name: test2.spthy
 *  Status: DEVELOPMENTAL
 *
 *  Comments:
 */

theory TVT
begin

functions:  Mul/2
builtins: xor , hashing, asymmetric-encryption




// Public key infrastructure
rule Register_pk:
[ Fr(~ltkA),Fr(~K),Fr(~P) ]
-->
[ !PrivKey($A, ~ltkA, ~K, ~P)
, !PubKey($A, pk(~ltkA))
, Out(pk(~ltkA))
]

rule Reveal_ltk:
[ !PrivKey($A, ltkA, K , P) ] --[ Reveal($A) ]-> [ Out(ltkA) ]

// Initialize Role V
rule Init_V:
[ Fr(~id)
, !PrivKey(V, Sv, K, P)
, !PubKey(A, pkA)
, !PubKey(S, pkS)
]
--[ Create(V, ~id), Role('V') ]->
[ 
]

// Initialize Role A
rule Init_A:
[ Fr(~id)
, !PrivKey(A, Sa, K, P)
, !PubKey(V, pkV)
, !PubKey(S, pkS)
]
--[ Create(A, ~id), Role('A') ]->
[ St_A_1(A, ~id, Sa, pkV, pkS, V, S, K, P)
]


// Initialize Role S
rule Init_S:
[ Fr(~id)
, !PrivKey(S, Ss, K, P)
, !PubKey(A, pkA)
, !PubKey(V, pkV)
]
--[ Create(S, ~id), Role('S') ]->
[ St_S_1(S, ~id, Ss, pkA, A, V, K, P)
]




// Role V sends first message
rule V_1_send:
  let
        V1=Mul(~Nv,P)
        V2=Mul(~Nv,pkA)
        PIDV=(<V,K>) XOR V2
        V3=h(<PIDV, V2, ~T1>)  
  in

    [!Ltk(V, Sv, K, P),
    St_V_1(V, ~id, Sv, pkA, A, K, P),
    Fr(~Nv), Fr(~T1)  ]
  --[Send(<PIDV,V1,V3,~T1>)
,	 Secret(~Nv), Honest(V), Honest(A), Running(V,A,V3), Role('V')  ]->
    [St_V_2(V, ~id, Sv, pkA, A, K, P, ~Nv, V1),
    Out(<PIDV,V1,V3,~T1>)	  ]


// Role A receives first message
rule A_1_receive:

let
	V2=Mul(Sa,V1)
  V3=h(<PIDV,V2,T1>)
in

[ St_A_1(A, ~id, Sa, pkV, pkS, V, S, K, P)
, In(<PIDV,V1,V3,T1>)
]
--[ Receive(<PIDV,V1,V3,T1>)
, Honest(A), Honest(V), Commit(A,V,V3), Role('A')
]->
[ St_A_2(A, ~id, Sa, pkV,pkS, V, S, K, P, PIDV, V1, V3, T1)
]

// Role A sends first message
rule A_1_send:
  let
        auth1=PIDV XOR V2
        A1=Mul(~Na,V1)
        A2=Mul(~Na,P)
        A3=Mul(~Na,pkS)
        PIDA1=<A,V,K> XOR A3
        A4=h(PIDA1,V1,A1,A3,~T2)
  in

    [St_A_2(A, ~id, Sa, pkV, pkS, V, S, K, P, PIDV, V1, V3_2, T1),
    Fr(~Na),Fr(~T2)  ]
  --[Send(<PIDA1,A1,A2,A4,V1,~T2>)	
,	 Secret(~Na),Running(A,S,A4), Honest(A), Honest(S), Role('A')  ]->
    [St_A_3(A, ~id, Sa, pkV, pkS, V, S, K, P, T1, PIDV, V1,~T2, ~Na, A1, A2, A3),
    Out(<PIDA1,A1,A2,A4,V1,~T2>)	  ]


// Role S receives first message 
rule S_1_receive_Session:

let
    A3=Mul(Ss,A2)
    auth2=PIDA1 XOR A3

in

[ St_S_1(S, ~id, Ss, pkA, A,V, K, P)
, In(<PIDA1,A1,A2,A4,V1,T2>)
]
--[ Receive(<PIDA1,A1,A2,A4,V1,T2>)
, Commit(S,A,A4), Honest(S), Honest(A), Role('S')
]->
[ St_S_2(S, ~id, Ss, pkA, A, V, K, P, T2, PIDA1, A1, V1, A3)
]

// Role S sends first message Computes session
rule S_1_send:
  let
    S1=Mul(~Ns,V1)
    S2=Mul(~Ns,A1)
    S3=Mul(~Ns,P)
    S4=Mul(~Ns,pkA)
    PIDS=<S, A, V, K> XOR S4
    S5=h(<PIDS,A1,S1,S4,~T3>)
    Ks=Mul(~Ns,A1)
    SKas1=h(<V1,A1,S1,Ks,A3>)

  in

    [St_S_2(S, ~id, Ss, pkA, A, V, K, P, T2, PIDA1, A1, V1, A3), 
    Fr(~Ns),Fr(~T3)  ]
  --[Send(<PIDS,S1,S2,S3,S5,~T3>)	 	
,	 Running(S,A,S5), Secret(~Ns), Honest(S), Honest(A), Role('S'), S_create_session(S, A, SKas1)  ]->
    [St_S_3(S, ~id, Ss, pkA, A, V, K, P, T2, PIDA1, A1, V1, A3, ~T3),
    Out(<PIDS,S1,S2,S3,S5,~T3>)	  ]

// Role A receives second message computes session keys
rule A_2_receive_session:

let
	S4=Mul(Sa,S3)
	auth3=PIDS XOR S4
	Ka=Mul(Na,S1)
    SKas2=h(<V1,A1,S1,Ka,A3>)
    A5=Mul(Na,pkV)
    PIDA2=<A,V,S,K> XOR A5
    A6=h(<PIDA2,A1,S1,A5,~T4>)
    SKav1=h(<V1,A1,S1,Ka,A5>)
in

[ St_A_3(A, ~id, Sa, pkV, pkS, V, S, K, P, T1, PIDV, V1, T2, Na, A1, A2, A3),
    In(<PIDS,S1,S2,S3,S5,T3>),
    Fr(~T4)
]
--[ Receive(<PIDS,S1,S2,S3,S5,T3>),Send(<PIDA2,A1,A2,A6,~T4,S1,S2>)
,Commit(A,S,S5), Honest(A), Honest(S), Role('A')
,A_create_session1(A, S, SKas2),A_create_session2(A,V,SKav1)
]->
[ St_A_4(A, ~id, Sa, pkV,pkS, V, S, K, P, T1, PIDV, V1, T2, Na, A1, A2, A3, ~T4),
	Out(<PIDA2,A1,A2,A6,~T4,S1,S2>)
]


// Role V receives second message computes session keys
rule V_2_receive_session:

let
    A5=Mul(Sv,A2)
    auth4= PIDA2 XOR A5
    Kv=Mul(Nv,S2)
    SKav2=h(<V1,A1,S1,Kv,A5>)
in

[ St_V_2(V, ~id, Sv, pkA, A, K, P, Nv, V1),
    In(<PIDA2,A1,A2,A6,~T4,S1,S2>)
]
--[ Receive(<PIDA2,A1,A2,A6,~T4,S1,S2>), Commit(V,A,A6)
, Honest(V), Honest(A), Role('V'),  V_create_session(V, A, SKav2)
]->
[ St_V_3(V, ~id, Sv, pkA, A, K, P, Nv, V1, 'Done'),
	Out(<PIDA2,A1,A2,A6,~T4,S1,S2>)
]

//////////////Lemmas//////////////////////////////////////



lemma executable_1:
exists-trace
"Ex PIDV V1 V3 T1  #i #j.
 Send(<PIDV,V1,V3,T1>)@i & Receive(<PIDV,V1,V3,T1>) @j &
  #i < #j"

lemma executable_2:
exists-trace
"Ex PIDA1 A1 A2 A4 V1 T2 #i #j.
  Send(<PIDA1, A1, A2, A4, V1, T2>)@i & Receive(<PIDA1, A1, A2, A4, V1, T2>)@j &
  #i < #j
"
 
lemma executable_3:
exists-trace
"Ex PIDS S1 S2 S3 S5 T3 #i #j.
  Send(<PIDS,S1,S2,S3,S5,T3>) @i & Receive(<PIDS,S1,S2,S3,S5,T3>) @j &
  #i < #j"

lemma executable_4:
exists-trace
"Ex PIDA2 A1 A2 A6 T4 S1 S2 #i #j.
  Send(<PIDA2,A1,A2,A6,T4,S1,S2>) @i & Receive(<PIDA2,A1,A2,A6,T4,S1,S2>) @j &
  #i < #j"


lemma Identity_hiding_V_A :
" All V A SKav2  #i .
V_create_session(V, A, SKav2) @ #i
& not ( Ex #k . Reveal (V) @ #k)
& not ( Ex #k . Reveal (A) @ #k)
==> not ( Ex #j . K(V) @ #j)
&   not ( Ex #l . K(A) @ #l) "

lemma Identity_hiding_A_S :
" All A S SKas2  #i .
A_create_session1(A, S, SKas2) @ #i
& not ( Ex #k . Reveal (A) @ #k)
& not ( Ex #k . Reveal (S) @ #k)
==> not ( Ex #j . K(A) @ #j)
&   not ( Ex #l . K(S) @ #l) "


lemma secrecy_PFS_Nonces:
"All Nv Na Ns  #i #j #k.
Secret(Nv) @i &
Secret(Na) @j &
Secret(Ns) @k ==>
not (Ex #m. K(Nv)@m) &
not (Ex #n. K(Na)@n) &
not (Ex #o. K(Ns)@o)
| (Ex A #r. Reveal(A)@r & Honest(A) @i & Honest(A) @j & Honest(A) @k
& #r < #i
& #r < #j
& #r < #k)"



lemma Server_Aggregator_session_key_secrecy:
  " /* It cannot be that a  */
    not(
      Ex S A SKas1 SKas2 #i #j #k #l.
        /* Server'S' has set up a session key 'SKas1' and 'SKav2' with  Aggregator'A' */
        S_create_session(S, A, SKas1) @ #i 
        & A_create_session1(A, S, SKas2) @ #j
        /* and the adversary knows 'SKas1' and 'SKas2' */
      & K(SKas1) @ #k
      & K(SKas2) @ #l
        /* without having performed a long-term key reveal on 'S'. */
      & not(Ex #r. Reveal(S) @ r)
      & not(Ex #s. Reveal(A) @ s)
    )
  "

lemma Aggregator_Vehicle_session_key_secrecy:
  " /* It cannot be that a  */
    not(
      Ex V A SKav1 SKav2 #i #j #k #l.
        /* Aggregator'A' has set up a session key 'SKav1' and 'SKav2 'with  Vehicle'V' */
        A_create_session2(A,V,SKav1) @ #i 
        & V_create_session(V, A, SKav2) @ #j
        /* and the adversary knows 'SKav1' and 'SKav2' */
      & K(SKav1) @ #k
      & K(SKav2) @ #l
        /* without having performed a long-term key reveal on 'A'. */
      & not(Ex #r. Reveal(A) @ r)
      & not(Ex #s. Reveal(V) @ s)
    )
  "

// lemma session_uniqueness :
// " All A S  SKas1 SKas2 #i #j.
// S_create_session(S, A, SKas1) @ #i
// & A_create_session1(A, S, SKas2) @ #j 
// ==> (#i = #j ) "

// lemma session_key_agreement :
//   "All  A S  SKas1 SKas2  #i #j.
//     S_create_session(S, A, SKas1) @i &
//     A_create_session1(A, S, SKas2) @j &
//    not (Ex #r. Reveal(A)@r & #r < #i) 

//       ==>
//        SKas1 = SKas2"

// lemma consistency :
// " All A S SKas1 SKas2 #i #j.
// S_create_session(S, A, SKas1) @i
// & A_create_session1(A, S, SKas2) @j
// & not ( Ex #k . Reveal(S) @k)
// ==>  SKas1 = SKas2 "


lemma Man_in_the_middle: 
"
  All V A S SKav1 SKav2 SKas1 SKas2 #i #j #k #l .
   (S_create_session(S, A, SKas1) @ #i &
    A_create_session1(A, S, SKas2) @j &
    A_create_session2(A,V,SKav1) @k &
    V_create_session(V, A, SKav2) @ #l &
    
    #i < #j  &
    #j < #k  &
    #k < #l  &

    not(V= A)&
    not(A= S)
    )
   ==> not(Ex #m. K(SKav1) @ #m)
    | not(Ex #n. K(SKas1) @ #n) 
    | not(Ex #o. K(SKav2) @ #o)
    | not(Ex #p. K(SKas2) @ #p)

"


lemma session_key_agreement_Veicle_Aggregator :
  "All V A SKav2 SKav1 #i #j.
     V_create_session(V, A, SKav2) @i &
     A_create_session2(A,V,SKav1) @j &
   
      not (Ex #r. Reveal(V)@r & #r < #i) &
      not (Ex #r. Reveal(A)@r & #r < #i & #r < #j)
      ==>
       SKav1 = SKav2"


lemma session_key_agreement_Server_Aggregator :
  "All S A SKas2 SKas1 #i #j.
     S_create_session(S, A, SKas1) @i &
     A_create_session1(A,S,SKas2) @j &
   
      not (Ex #r. Reveal(S)@r & #r < #i) &
      not (Ex #r. Reveal(A)@r & #r < #i & #r < #j)
      ==>
       SKas1 = SKas2"

//////////////////////////////////////////////////Aliveness
lemma aliveness_V_A:
"All V A V3 #i.
Commit(A,V,V3)@i
==> (Ex V id #j. Create(V, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"

lemma aliveness_A_S:
"All A S A4 #i.
Commit(S,A,A4)@i
==> (Ex A id #j. Create(A, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"

lemma aliveness_S_A:
"All A S S5 #i.
Commit(A,S,S5)@i
==> (Ex S id #j. Create(S, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"

lemma aliveness_A_V:
"All V A A6 #i.
Commit(V,A,A6)@i
==> (Ex A id #j. Create(A, id) @ j)
| (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"

////////////////////////////////////////////////////weak_agreement
// lemma weak_agreement_V_A:
// "All V A t1 #i.
// Commit(A,V,t1) @i
// ==> (Ex t2 #j. Running(V,A,t2) @j)
// | (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"


// lemma noninjective_agreement:
// "All V A V3 #i.
// Commit(A,V,V3) @i
// ==> (Ex #j. Running(V,A,V3) @j)
// | (Ex C #r. Reveal(C) @ r & Honest(C) @ i)"

// lemma injectiveagreement:
// "All V A T1 #i.
// Commit(A,V,T1) @i
// ==> (Ex #j. Running(V,A,T1) @j
// & j < i
// & not (Ex V2 A2 #i2. Commit(A2,V2,T11) @i2
// & not (#i2 = #i)))
// | (Ex C #r. Reveal(C)@r & Honest(C) @i)"
end    

```
