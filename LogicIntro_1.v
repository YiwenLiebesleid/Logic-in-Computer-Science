
(** * Notation
 *)
(**

- [->] means "if .. then"

- [/\] means "and"

- [\/] means "or"

 *)


(** * Main Idea: Constructive Interpretation of Logic

- Evidence for [A /\ B] is a pair: evidence for [A] paired with
  evidence for [B]

- Evidence for [A \/ B] is evidence for [A] or evidence for [B]

- Evidence for [A \/ B] is a function, carrying for [A] into evidence
  for [B]

- There cannot be an evidence of [False]

- Negation [~ A] is viewed as shorthand for [A -> False]

- [forall (x:A), B] is treated like a giant [/\] taken over all
  elements of [A]

- [forall (x:A), B] is treated like a giant [\/] taken over all
  elements of [A]

 *)


(** *   Constructive Proving with Easy Connectives
 *)

(**

- To _prove_ [A -> B] as a goal, build a function that carries proofs of
  [A] into proofs of [B].

  Tactic: [intro]

- To _prove_ [A /\ B] as a goal, build two proofs, one for [A] and one
  for [B].

  Tactic: [split]

- To _prove_ [A \/ B] as a goal, build one proof, a proof of [A] or a
  proof of [B] 

  Tactic: [left] or [right]

- To _use_ [A->B] as a hypothesis, apply the associated function.

  Tactic:  [apply]

- To _use_ [A /\ B] as a hypothesis, break it down into two hypotheses.

  Tactic: [destruct]

- To _use_ [A \/ B] as a hypothesis, break the whole proof down,  into two cases.

  Tactic: [destruct]

 *)


(** *   Constructive Proving with Negation
 *)
(** 

- [~ A] is an abbreviation for [A -> False]

- To _prove_ [False]: impossible, unless some hypothesis is equivalent
  to False

- To _use_ [False] as a hypothesis: easy!    False entails anything.
  
  Tactic: [contradict]

 *)


(** *   Constructive Proving  with Quantifiers *)

(**

- To _prove_ [forall (x : A), B] as a goal, build a function that
  carries elements of [A] into proofs of [B].

  Tactic: [intro]

- To _prove_ [exists (x : A), B] as a goal, build an element [a : A]
  and a proof of [B(a)]

  Tactic: exists

  (No that's not a typo, the name of the tactic is the same as the
  name of the quantifier.  Sigh.)

- To _use_ [forall (x : A), B] as a hypothesis, apply it like a
  function.  

  Tactic: [apply]

-  Those are HINTS ONLY, not rules or promises.  In a given specific
 situation:

  - other tactics might work besides the above

  - in some complex situations, you might need to do something trickier
    than the above.

 *)



(** * Pure if-then *)

Theorem eg1_backwards (A B C : Prop) :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros h1 h2 h3.
  apply h2.
  apply h1.
  apply h3.
Qed.



Theorem eg1_forwards (A B C : Prop) : 
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  intros h1 h2 h3.
  apply h1 in h3.
  apply h2 in h3.
  apply h3.
Qed.


Theorem eg_backwards (A B C : Prop) : 
  (A -> B -> C) -> B -> (A -> C).
Proof.
  intros h1 h2 h3.
  apply h1.
  - apply h3.
  - apply h2.
Qed.

(** ** Using [apply in] for forward reasoning *)

Theorem eg2_forwards (A B C : Prop) : 
  (A -> B -> C) -> B -> (A -> C).
Proof.
  intros h1 h2 h3.
  apply h1 in h3.
  apply h3.
  apply h2.
Qed.

(** really take seriously the fact that [apply] is function application:
 multiple arguments are ok! *)

Theorem eg2_forwards' (A B C : Prop) : 
  (A -> B -> C) -> B -> (A -> C).
Proof.
  intros h1 h2 h3.
  apply (h1 h3 h2).
Qed.


(** * Conjunction *)

Theorem conjI (A B : Prop) :  A -> B -> (A /\ B).
Proof.
  intros h0 h1.
  split.
  - apply h0.
  - apply h1.
Qed.

(** Don't forget to do your own naming, in [destruct] *)

Theorem conjE1 (A B : Prop) :  (A /\ B) -> A .
Proof.
  intros h.
  destruct h as [h1  h2].
  apply h1.  
Qed.

Theorem conj3 (A B C : Prop) :  A -> B -> C -> (A /\ B /\ C).
Proof.
  intros h0 h1 h2.
  split.
  - apply h0.
  - split.
    -- apply h1.
    -- apply h2.
Qed.

Theorem and_commutes (A B : Prop) :  (A /\ B) -> (B /\ A) .
Proof.
  intros h. destruct h as [h1 h2].
  split.
  - apply h2.
  - apply h1.
Qed.

Theorem curry (A B C : Prop) :  ((A /\ B) ->  C) -> (A -> B -> C) .
Proof.
  intros h0 h1 h2.
  apply h0.
  split.
  - apply h1.
  - apply h2.
Qed.


Theorem uncurry (A B C : Prop) :  (A -> B -> C) -> (A /\ B) ->  C.
Proof.
	intros h0 h1.
	apply h0.
	- apply h1.
	- apply h1.
Qed.

(** * Disjunction *)

Theorem or_swap (A B : Prop) :   (A \/ B) -> (B \/ A).
Proof.
  intros h. destruct h as [hA | hB].
  - right. apply  hA.
  - left. apply hB.
Qed.


Theorem or_arrow (A B C : Prop) :  ( (A \/ B) -> C ) ->
                                   (A -> C) /\ (B -> C) .
Proof.
  intros h1.
  split .
  - intros hA. apply h1.
    left. apply hA.
  - intros hB. apply h1.
    right. apply hB.
Qed.


Theorem arrow_or (A B C : Prop) : 
  (A -> C) /\ (B -> C) ->  ( (A \/ B) -> C ) .
Proof.
	intros h1 h2.
	destruct h1 as [h11 h12].
	destruct h2 as [h2A | h2B].
	- apply h11. apply h2A.
	- apply h12. apply h2B.
Qed.

Theorem and_distrib_or (A B C : Prop) :  (A /\ (B \/ C)) -> (A /\ B) \/ (A /\ C).
Proof.
  intros h.
  destruct h as [h1  [h21 | h22]].
  - left. split. apply h1. apply h21.
  - right. split. apply h1. apply h22.
Qed.

(** Note the use of nested patterns in the destruct, a time-saver *)

Theorem or_distrib_and (A B C : Prop) :  (A \/ (B /\ C)) -> (A \/ B) /\ (A \/ C).
Proof.
	intros h.
	destruct h as [h1 | h2].
	- split. left. apply h1. left. apply h1.
	- destruct h2 as [hB hC]. split.
		-- right. apply hB.
		-- right. apply hC.
Qed.


(** * If-and-only-if *)

(** The connective [<->], pronounced "if and only if" is nothing
special; it's just the conjunction of the two [->] directions. So
[split] usually is the strategy.  *)


(** Here we take the opportunity to [apply] a previous result, not
just a current hypothesis.  *)

Theorem and_commutes_iff (A B : Prop) :
  (A /\ B) <-> (B /\ A).
Proof.
  split.
  - apply and_commutes.
  - apply and_commutes.
Qed.



(** * Negation *)

(** CAUTION: even though [~ P] is really just [P -> False], doing
intros (without a name) will not do anything.  There's no good reason
for this, it's an interface bug, in my opinion.  You 
force Coq to make [ ~ ] explicit by the tactic 
[unfold not] .  *)


Theorem false_to_anything ( B: Prop) :
  False -> B.
Proof.
  intros.
  contradict H.  
Qed.

Theorem A_false_to_A_B (A B: Prop) :
  (A -> False) -> (A -> B).
Proof.
  intros h1 h2.
  apply h1 in h2.  contradict h2.
Qed.

Theorem not_False : ~ False.
Proof. 
  unfold not. intros h. apply h. 
Qed. 

Theorem contr_implies_anything (A B : Prop) : 
  (A /\ ~A) -> B.
Proof.
	intros h.
  destruct  h as [hA hnA].
  apply hnA in hA.
(*	contradict hA.*)
  destruct  hA.
Qed.

(** ** Double Negation *)

(** You are used to treating a double-negation [~ ~ P] as being
equivalent to simply [P], but that isn't true constructively.  It's
half-true though: *)

(** *** double-negation introduction *)

Theorem double_neg_I (A : Prop) :  A -> ~ ~ A.
Proof.
	unfold not.
	intros h1 h2.
	apply h2 in h1.
	contradict h1.
Qed.

(** By the way, double-negation not really about negation!  To see
this, note that the following proof is word-for-word the same as for
double-negation introduction! *)

Theorem double_neg_I' (A B : Prop) :  A -> ( (A -> B) -> B).
Proof.
	intros.
	apply H0 in H.
	apply H.
Qed.
    
(** The converse, double-negation-elimination,  does not hold in
constructive logic.  We'll come back to this. *)


(** *** Triple-negation Elimination. *)

(* 
In classical logic we never need to deal with more than one negation
in a row, since we can cancel out two negations in a row.

When you hear that we can't do that cancellation constructively, you
might suppose that negation could proliferate all over the place.  But
in fact we never have to deal more than TWO negations.  *)

Theorem triple_neg_intro_naive (A : Prop) :  ~ A -> ~ ~ ~ A.
Proof.
  unfold not.
  intros h1 h2.  
  apply h2 in h1.
  apply h1.
Qed.

(** Why did we call that "naive"?  Because a better point of view is
that triple negation intro is just a special case of double negation
intro!   Do you see? *)

Theorem triple_neg_intro (A : Prop) :  ~ A -> ~ ~ ~ A.
Proof.
	apply double_neg_I.
Qed.

(** Triple negation elimination isn't quite that easy...after all, we
don't have a double negation elimination result to rely on.  But
magically, all is well.  Double negation _introduction_ is the key to triple negation _elimination_ !! *)

Theorem triple_neg_elim (A : Prop) :  ~ ~ ~ A -> ~ A.
Proof.
	unfold not.
	intros h1 h2.
	contradict h1.
	intros h3.
	apply h3 in h2. apply h2.
Qed.


(** ** Negation and propositional connectives *)


(** You are used to treating an implication as being equivalent to its
contrapositive, but that isn't true constructively.  It's half-true
though:
 *)

Theorem contrapositive (A B : Prop) :  (A -> B) -> ~B -> ~A.
Proof.
  intros h1 h2 h3.
  apply h2.  apply h1. apply h3.
Qed.


(** In reasoning intuitively we can define [/\] in terms of [\/], and
vice versa, by treating [P /\ Q ] as equivalent to [~ ( ~ P \/ ~ Q) ],
and by treating [P \/ Q] as equivalent to [~ ( ~ P /\ ~Q) ].

But these equivalences do not hold constructively.
 *)

(* Let's look individually at the four implications that arise as we
consider pushing negations through connectives...it will turrn out
that exactly three of them are constructively ok.  *)

Theorem or_to_not (A B : Prop) : 
  (A \/ B) -> ~ ( ~A /\ ~B).
Proof.
  intros h hf. destruct hf as [hf1 hf2].
  destruct  h as [ha | hb].
  destruct  (hf1 ha).
  destruct  (hf2 hb).
Qed.

Theorem not_or (A B : Prop) : 
  ~ ( A \/ B) ->  ( ~ A /\ ~ B) .
Proof.
	unfold not. intros h.
	split.
	- intros h1. destruct h. left. apply h1.
	- intros h2. destruct h. right. apply h2.
Qed.

 
Theorem arrow_to_not (A B  : Prop) : 
  (A -> B) -> ~ ( A /\ ~B).
Proof.
  intros h hf. destruct hf as [hf1  hf2].
  apply h in hf1.
  apply hf2 in hf1.
  apply hf1.
Qed.


Theorem not_to_arrow (A B : Prop) : 
  ~A -> ( A -> B).
Proof.
  intros h1 h2 . destruct (h1 h2).
Qed.


Theorem and_to_not (A B : Prop) : 
  (A /\ B) -> ~ ( ~A \/ ~B).
Proof.
  intros h hf. destruct  h as [ha  hb].
  destruct hf as [hf1 | hf2].
  - destruct  (hf1 ha).
  - destruct  (hf2 hb).
Qed.

Theorem iff_to_not (A B : Prop) : 
  (A <-> B) -> ( ~A <-> ~B).
Proof.
	intros h. destruct h as [h1 h2].
	split.
	- apply contrapositive. apply h2.
	- apply contrapositive. apply h1.
Qed.
    
Theorem and_one_not (A B  : Prop) : 
  A /\ ~B -> ~ ( A -> B).
Proof.
  intros h f. destruct h as [hA hnB].
  apply (hnB (f hA)).
Qed.

Theorem or_one_not (A B : Prop) : 
  ~A \/ B -> (A -> B).
Proof.
	intros h1 h2. destruct h1 as [hnA | hB].
	- destruct (hnA h2).
	- apply hB.
Qed.
    
(* *********************************************************** *)
(* *********************************************************** *)

(** * Quantifiers *)

(** Declare a type T that variables will range over *)

Parameter T : Type.



(** ** Quantifier swapping *)

(** the [specialize] tactic instantiates a universal quant *)

Theorem exists_forall_1 (P : (T * T) -> Prop):
  (exists x, forall y, (P (x , y) ) ) ->
  (forall y, exists x, (P (x , y) ) ) .
Proof.
  intros h y0.
  destruct h as [x0 h1].
  exists x0.
  specialize (h1 y0) as h1y0.
  apply h1.
Qed.

 
(** good old [apply] can automatically specialize as needed *)

Theorem exists_forall (P : (T * T) -> Prop):
  (exists x, forall y, (P (x , y) ) ) ->
  (forall y, exists x, (P (x , y) ) ) .
Proof.
  intros h y0.
  destruct h as [x0 h1].
  exists x0.
  apply h1.
Qed.


(** *** converse fails *)

(** The converse certainly doesn't hold in general.

Let's see where the proof breaks down.
 *)

Theorem  forall_exists_fail (P : (T * T) -> Prop) :
  (forall y, exists x, (P (x , y) ) ) ->
  (exists x, forall y, (P (x , y) ) ).
Proof.
  intros h.

  (** no terms in sight to suggest for [exists] tactic. *)

  (** no terms in sight to suggest for [specialize] tactic. *)

  (** maybe [apply] can magically work? *)

  Fail apply h.

  Abort.


(** A counterxample: suppose [(P x y)] is interpreted as 
    [(y < x)] over [nat].  Then for every y there is an x such that 
    [y  < x] but there is no single x that is bigger than every y.
*)


(** ** [forall] and conjunction *)

Theorem and_forall (U V : T -> Prop) : 
  (forall x, (U x)) /\ (forall x, (V x)) ->
  (forall x , (U x) /\ (V x)) .
Proof.
  intros h x.
  split.
  - destruct h as [h1 h2]. apply h1.
  - destruct h as [h1 h2]. apply h2.
Qed.
 
Theorem forall_and_naive (U V : T -> Prop) : 
  (forall x , (U x) /\ (V x)) ->
  (forall x,  (U x)) /\ (forall x, (V x)).
Proof.
  intros h.
  split.
  - intros z.
    assert (a1 := h z).
    destruct a1 as [a11 a12].
    apply a11.

  - intros z.
    assert (a1 := h z).
    destruct a1 as [a11 a12].
    apply a12.
Qed.

(** The above proof is fine.  But the [apply] tactic can
auto-magically do some of the bookkeeping for you.  Look how simple
the script can be. *)

Theorem forall_and (U V : T -> Prop) : 
  (forall x , (U x) /\ (V x)) ->
  (forall x, (U x)) /\ (forall x, (V x)).
Proof.
  intros h.
  split.
  - intros z. apply h.  
  - intros z. apply h. 
Qed.

(** ** [forall] and disjunction *)

(** *** one direction is ok ... *)

Theorem or_forall (U V : T -> Prop) : 
  (forall x, (U x)) \/ (forall x, (V x)) ->
  (forall x , (U x) \/ (V x)) .
Proof.
  intros h x.
  destruct h as [h1 | h2].
  - left.  apply h1.
  - right. apply h2.
Qed.

(** *** ... but the converse of or_forall is NOT provable.
 *)

(* A good exercise: come up with a counterexample, either from math or
  from real life.  This is not about clasical/constructive, by the
  way.  It just ain't so.  *)

(** ** [exists] and conjunction *)

Theorem exists_and (U V : T -> Prop) :
  (exists x , (U x) /\ (V x)) ->
  (exists x, (U x)) /\ (exists x, (V x)).
Proof.
	intros h.
	destruct h as [z h1].
	split.
	- exists z. apply h1.
	- exists z. apply h1.
Qed.
    
(** The converse of exists_and doesn't hold.  It is instructive to see
    what goes wrong if you _try_ to prove it.  We do so below; we walk
    through the obvious steps until we get stuck.  Looking at the
    proof state at that point gives insight into what is wrong.  I
    recommend doing this.  The takewaya lesson is that trying and
    failing to prove something can help you understand why something
    isn't true.

   Of course a failed proof isn't a proof that the result doesn't hold
(maybe you just didn't see the right approach).  You need a
counterxample to demonstrate that there _can't_ be a proof...

 *)
Theorem and_exists_fail (U V : T -> Prop) :
  (exists x, (U x)) /\ (exists x, (V x)) ->
  (exists x , (U x) /\ (V x)) .
Proof.
  intros.
  destruct H as [h1 h2]. 
  destruct h1 as [x1 h11].
  destruct h2 as [x2 h21].
Abort.


(** ** [exists] and disjunction *)

(** *** everything goes smoothly *)

Theorem or_exists (U V : T -> Prop) :
  (exists x, (U x)) \/ (exists x, (V x)) ->
  (exists x , (U x) \/ (V x)) .
Proof.
  intros h .
  destruct h as [h1 | h2].
  - destruct h1 as [x0 h1'].
    exists x0. left. apply h1'.
  - destruct h2 as [x0 h2'].
    exists x0. right. apply h2'.
Qed.

Theorem exists_or (U V : T -> Prop) :
  (exists x , (U x) \/ (V x))  ->
  (exists x, (U x)) \/ (exists x, (V x)) .
Proof.
	intros h.
	destruct h as [x0 h1].
	destruct h1 as [h11 | h12].
	- left. exists x0. apply h11.
	- right. exists x0. apply h12.
Qed.

(** **  Quantifiers and negation *)

(** In reasoning intuitively we can define forall in terms of exists, and vice versa, 
by treating [forall x, whatever] as equivalent  to [~ (exists x, ~ whatever], and
by treating [exists x, whatever] as equivalent  to [~ (forall x, ~ whatever].   

But these equivalences do not hold constructively.

Let's look individually at the four implications that arise as we
consider pushing negations through quantifiers...it will turrn out
that exactly three of them are constructively ok.  *)


Theorem forall_not_exists (U : T -> Prop) :
  ( forall x, (U x) ) ->
  ~ (exists x, ~ (U x)).
Proof.
  intros h hf. 
  destruct hf as [a h1].
  specialize (h a) as ha.
  auto.
Qed.

Theorem exists_not_forall (U : T -> Prop) :
  ( exists x, (U x) ) ->
  ~ (forall x, ~ (U x)).
Proof.
  intros h hf.
  destruct h as [x h1].
  assert (a:= (hf x)).
  apply (a h1).
Qed.

Theorem not_exists_forall (U : T -> Prop) :
  ~ (exists x, (U x) ) ->
  (forall x, ~ (U x)).
Proof.
	intros h x.
	contradict h.
	exists x. apply h.
Qed.

(** The "missing" implication is the one that would go from
[~ (forall x, something)] to [exists x, ~ something] .

This implication holds classically but not constructively.
See below, [not_forall_exists_cl].

 *)


(* ******************************************************** *)

(** * Classical vs Constructive *)

(** Classical logic is the logic you are used to, it's the logic you
use when you are walking own the street discussing something with a
friend.  Constructive reasoning is not some dubious or controversial
way of thinking, it's just a bit more careful.  Any correct
constructive argument is a correct classical argument; some correct
classical arguments are not allowed in constructive reasoning.

Rather than define the differences here at the beginning, we'll just
dive in with proofs, and will indicate when we are being
non-construtive.  (It really isn't that often.)

Why would we constrain ourselves as restrict to constructive
reasoning?  We can't give a detailed answer here but can give some
hints.

First, for some people the principles of constructive reasoning are
philosophically compelling; they consider a constructive argument to
have greater force than one using "no-constructive" inferences.

Second, if a result is proved constructively then one can mechanixally
extract a program withnessing that result.  Thus theorem proving leads
to code generation.  This is fascinating use-case for provers like
Coq.  Search for Extraction in the Coq documentation.

As a final, informal, observation: if a theorem holds constructively
then a proof can be found just by "following your nose".  At any point
in the proof if you just to the splits or intros or destructs that are
available to you, the proof will emerge.  Once classical resoning is
required, you may need some cleverness to discover proofs.

 *)



(** * Classical Axioms *)

(** Here are two famous facts that are provable classically but not
constructively.  It turns out that assuming either one of these
principles is sufficient to capture all of classical reasoning.  We
won't ptove that fact but we will do some "classical" proofs, that is,
somce proofs that employ these axions.

- double_negation_elimination is the principle that for all P, [~ ~ P
    -> P ] holds.

 The fact that [P -> ~ ~ P] was constructively proven above.

- double_negation_elimination is the principle that for all P [P \/ ~P
    ] holds.

 *)

    
(** ** Some Classical-only results *)

Section Classical.


  (** Coq note: when we create a "[Section]" we can declare axioms
that are in force (only) in the scope of the Section.  This means that
the axioms [dne] and [exm] below can be used in proofs if desired.

The "[Section]" mechanism has other features (eg introducing local
variables, notations, etc ... read about it in the Coq documentation
*)   

  (** Here we make two classical-only axioms available, to see some
  new things that can be proven with them.  As we showed above, they
  are equivalent, thus only really need one, but sometimes one is more
  convenient to use than the other so we provide them both for
  convenience. *)

  (** *** double-negation elimination axiom *)

  Axiom dne : forall (P : Prop), ~ ~ P -> P.

  (** *** the excluded middle  axiom *)

  Axiom exm : forall (P : Prop), (P \/ ~ P).

  (** *** A few classical-only results *)
   
  Theorem contrapositive_cl (A B : Prop) :
    (~ A -> ~ B) -> ( B -> A).
  Proof.
    intros h1 h2.
    apply (dne A).  intros h3.  apply (h1 h3 h2).  Qed.


  (** Compare that to [contrapositive] earlier.  Moral: it is easy to
  introduce negations, constructively, but to _remove_ negations you
  often have to work classically. *)

  Theorem not_and_cl (A B : Prop) :
    ~ ( A /\ B) -> ~A \/ ~B.
  Proof.
    intros h.

    (** stop and note:  if you did [left] or did  [right] you would lose the game!
     *)

    apply dne.
    intros hn.
    apply not_or in hn.
    destruct hn as [hn1 hn2].
    apply dne in hn1.
    apply dne in hn2.
    apply h.
    split.
    apply hn1.
    apply hn2.
  Qed.

  (** Here's one where excluded-middle is most convenient *)
  
  Theorem not_arrow_cl (A B : Prop):
    ~ (A -> B) -> ( A /\ ~ B) .
  Proof.
    intros h.
    split.
    - assert (a:= exm A).
      destruct a as [yesA | noA].
      + auto.
      + destruct h . 
        apply A_false_to_A_B. auto.
    - intros h1.
      destruct h. auto.      
  Qed.

  (** For this one, do not get all involved in new "quantifier
  reasoning".  Just use a previous result (about quantifiers) and
  classical contrapositive.  *)

  Theorem not_forall_exists_cl (U : T -> Prop) :
    ~ (forall x, ~ (U x)) ->
    (exists x, (U x) ) .
  Proof.
		intros h.
		apply dne. intros hn.
		apply h. apply not_exists_forall.
		apply hn.
	Qed.

  (** * Pierce's formula *)

  (** The classical-vs-constructive distinction is not just about
     quantifiers and connectives, it arises even with [->] alone.

Here is a proposition, called Pierce's formula, that is provable in
classical logic, but not provable in constructive logic :

  [Definition Pierce (A B : Prop) := ((A -> B) -> A) -> A.]
  
   *)
  
  (** A classical proof of Pierce's formula *)

      (** hint: use excluded-middle *)
      
  Theorem Pierce_cl (A B : Prop) :
    (((A -> B) -> A) -> A).
  Proof.
  	intros h.
		assert (a := exm A).
		destruct a as [yesA | noA].
		- apply yesA.
		- apply h. intros ha. destruct (noA ha).
	Qed.
      
  (** * Relationship between classical and constructive provability *)

  (** It can be hard to remember which of the classical logic laws you
know hold constructively.  But a very good exercise at this point is
to try to get some intuition about which laws do and don't hold
constructively, by taking to heart the interpretations we have made
about the connectives and how they correspond to "evidence" (ie,
evidence for a conjunction is a pair, evidence for an implication is a
function, etc).

Can we say anything precise about the relationship between
constructive and classical validity?  Yes we can.

(i) if a proposition P is provable constructively, then P is provable
classically.  This is obvious, because a constructive proof IS a
classical proof!

(ii) if a proposition P that does not use quantifiers is provable
classically, then [~ ~ P] is provable classically.  This is not so
obvious; it is known as Glivenko's Theorem.

(iii) what about classically provable propositions that involve
quantifiers?  There is a transformation called the "negative
translation" that operates on a proposition x[P] and returns a
proposition [P'] which is equivalent to [P] classically, and which is
constructively provable whenever the original [P] is classically
provable.  Actually, there are several such transformations.  We won't
study them here.

   *)

  End Classical.


(** * Equivalence of  excluded-middle and double-negation-elimination *)

(** 
It's interesting to realize that introducing EITHER ONE of excluded-middle or 
double-negation-elim gives us all of classical reasoning. That's an elaborate claim, which we won't gointo much here.  One thing we can do is to demonstrate that adding 
double-negation-elimination and excluded-middle are equivalent: we do this bt shoing that each of these implied the other.
*)

(** These are _constructive_ proofs!  *)

Theorem dnE_implies_excluded_middle :
  (forall (P : Prop), ( ~ ~ P -> P) ) ->
  (forall (P : Prop),  (P \/ ~ P) ).
Proof.
  intros h P.
  apply h.
  intros h1 .
  apply not_or in h1.
  destruct h1 as [h11  h12].
  apply h12 in h11. apply h11.
Qed.

Theorem excluded_middle_implies_dnE :
  (forall (P : Prop),  (P \/ ~ P) ) ->
  (forall (P : Prop), ( ~ ~ P -> P) ) .
Proof.
  intros h1 P h2.
  assert (a := h1 P).
  destruct a as [a1 | a2].
  - apply a1.
  - destruct (h2 a2).
Qed.

(** *** another result reflecting the relationship betwen dnE and exclude middle:  *)

Lemma not_not_exm : forall P,
    ~ ~ (P \/ ~P).
Proof.
	intros P.
	assert (a := exm P).
	destruct a as [yesA | noA].
	- intros h1. apply h1. left. apply yesA.
	- intros h1. apply h1. right. apply noA.
Qed.


(**
A thought experiment: suppose you hadn't already proved
[dnE_implies_excluded_middle] and [excluded_middle_implies_dnE].  The
lemma [not_not_exm] easily implies one of those.  Which one?  Explain.
*)
