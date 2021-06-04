(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
From Coq Require Export Lia.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductive definitions_.

    _Note_: For the sake of simplicity, most of this chapter uses an
    inductive definition of "evenness" as a running example.  You may
    find this confusing, since we already have a perfectly good way of
    defining evenness as a proposition ([n] is even if it is equal to
    the result of doubling some number); if so, rest assured that we
    will see many more compelling examples of inductively defined
    propositions toward the end of this chapter and in future
    chapters. *)

(** In past chapters, we have seen two ways of stating that a number
    [n] is even: We can say

      (1) [evenb n = true], or

      (2) [exists k, n = double k].

    Yet another possibility is to say that [n] is even if we can
    establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation.  (We'll
    use [ev] for the name of this property, since [even] is already
    used.)

                              ------------             (ev_0)
                                 ev 0

                                 ev n
                            ----------------          (ev_SS)
                             ev (S (S n))
*)

(** Each of the textual rules that we started with is
    reformatted here as an inference rule; the intended reading is
    that, if the _premises_ above the line all hold, then the
    _conclusion_ below the line follows.  For example, the rule
    [ev_SS] says that, if [n] satisfies [ev], then [S (S n)] also
    does.  If a rule has no premises above the line, then its
    conclusion holds unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even:

                             --------  (ev_0)
                              ev 0
                             -------- (ev_SS)
                              ev 2
                             -------- (ev_SS)
                              ev 4
*)

(** (Why call this a "tree", rather than a "stack", for example?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly.) *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** This definition is interestingly different from previous uses of
    [Inductive].  For one thing, we are defining not a [Type] (like
    [nat]) or a function yielding a [Type] (like [list]), but rather a
    function from [nat] to [Prop] -- that is, a property of numbers.
    But what is really new is that, because the [nat] argument of
    [ev] appears to the _right_ of the colon on the first line, it
    is allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].  Accordingly, the type of each constructor must be
    specified explicitly (after a colon), and each constructor's type
    must have the form [ev n] for some natural number [n].

    In contrast, recall the definition of [list]:

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

   This definition introduces the [X] parameter _globally_, to the
   _left_ of the colon, forcing the result of [nil] and [cons] to be
   the same (i.e., [list X]).  Had we tried to bring [nat] to the left
   of the colon in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type constructor
    on the left of the colon is called a "parameter", whereas an
    argument on the right is called an "index" or "annotation."

    For example, in [Inductive list (X : Type) := ...], the [X] is a
    parameter; in [Inductive ev : nat -> Prop := ...], the unnamed
    [nat] argument is an index. *)

(** We can think of the definition of [ev] as defining a Coq
    property [ev : nat -> Prop], together with "evidence constructors"
    [ev_0 : ev 0] and [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** Such "evidence constructors" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [ev] for particular numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
	intros n. induction n.
	- simpl. apply ev_0.
	- simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _destruct_ such evidence, which amounts to reasoning about how it
    could have been built.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is [ev], but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are [ev]. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must be one of two things:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [ev n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [ev n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [ev n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'] eqn:EE.
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with just
    [destruct]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** If we [remember] that term [S (S n)], the proof goes
    through.  (We'll discuss [remember] in more detail below.) *)

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. remember (S (S n)) as k eqn:Hk. destruct E as [|n' E'] eqn:EE.
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which [k = S (S n)] has been
       rewritten as [0 = S (S n)] by [destruct]. That assumption
       gives us a contradiction. *)
    discriminate Hk.
  - (* E = ev_S n' E' *)
    (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
    injection Hk as Heq. rewrite <- Heq. apply E'.
Qed.

(** Alternatively, the proof is straightforward using our inversion
    lemma. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
 intros n H. apply ev_inversion in H.
 destruct H as [H0|H1].
 - discriminate H0.
 - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
   rewrite Heq. apply Hev.
Qed.

(** Note how both proofs produce two subgoals, which correspond
    to the two ways of proving [ev].  The first subgoal is a
    contradiction that is discharged with [discriminate].  The second
    subgoal makes use of [injection] and [rewrite].  Coq provides a
    handy tactic called [inversion] that factors out that common
    pattern.

    The [inversion] tactic can detect (1) that the first case ([n =
    0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' Heq].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice) 

    Prove the following result using [inversion].  (For extra practice,
    you can also prove it using the inversion lemma.) *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
	intros n H. apply evSS_ev in H. apply evSS_ev in H.
	inversion H.
	- rewrite H0. apply H.
	- rewrite H1. apply H.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (ev5_nonsense) 

    Prove the following result using [inversion]. *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
	intros. inversion H. inversion H1. inversion H3.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied, more generally,
    to analyze evidence for inductively defined propositions.  As
    examples, we'll use it to reprove some theorems from chapter
    [Tactics].  (Here we are being a bit lazy by omitting the [as]
    clause from [inversion], thereby asking Coq to choose names for
    the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_even_firsttry : forall n,
  ev n -> even n.
Proof.
  (* WORKED IN CLASS *)

(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would
    probably lead to a dead end, because (as we've noted before) the
    induction hypothesis will talk about n-1 (which is _not_ even!).
    Thus, it seems better to first try [inversion] on the evidence for
    [ev].  Indeed, the first case can be solved trivially. And we can
    seemingly make progress on the second case with a helper lemma. *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't
    directly useful, it seems that we are stuck and that performing
    case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [ev]:
    namely [E'].  More formally, we can finish our proof by showing
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    (** Unforunately, now we are stuck. To make that apparent, let's move
        [E'] back into the goal from the hypotheses. *)

    generalize dependent E'.

    (** Now it is clear we are trying to prove another instance of the
        same theorem we set out to prove.  This instance is with [n'],
        instead of [n], where [n'] is a smaller natural number than [n]. *)
Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to
    use case analysis to prove results that required induction.  And
    once again the solution is... induction! *)

(** The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypothesis for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [ev
    n] holds, we can use induction on [ev n]. This requires us to
    prove two things, corresponding to the two ways in which [ev n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [ev n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [ev n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : even E' *)
    unfold even in IH.
    destruct IH as [k Hk].
    rewrite Hk. exists (S k). simpl. reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  ev n <-> even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) unfold even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
	intros n m E0 E1.
	induction E0 as [| n' E0' IHn].
	- simpl. apply E1.
	- simpl. destruct IHn.
		+ apply ev_SS. apply ev_0.
		+ apply ev_SS. apply ev_SS. apply IHn.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ev'_ev) 

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** Prove that this definition is logically equivalent to the old one.
    To streamline the proof, use the technique (from [Logic]) of
    applying theorems to arguments, and note that the same technique
    works with constructors of inductively defined propositions. *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
	intros n. split.
	- intros H1. induction H1.
		+ apply ev_0.
		+ apply ev_SS. apply ev_0.
		+ apply ev_sum. { apply IHev'1. } { apply IHev'2. }
	- intros H2. induction H2.
		+ apply ev'_0.
		+ apply (ev'_sum 2 n).
			{ apply ev'_2. } { apply IHev. }
Qed.

(* reduced by 1 *)
Theorem ev'_ev_auto : forall n, ev' n <-> ev n.
Proof.
	intros n. split.
	- intros H1. induction H1;
		try ( try apply ev_SS; try apply ev_0; try apply ev_sum;
					try apply IHev'1; try apply IHev'2 ).
	- intros H2. induction H2.
		+ apply ev'_0.
		+ apply (ev'_sum 2 n).
			{ apply ev'_2. } { apply IHev. }
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, especially useful (ev_ev__ev) 

    There are two pieces of evidence you could attempt to induct upon
    here. If one doesn't work, try the other. *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
	intros n m H0 H1.
	induction H1.
	- simpl in H0. apply H0.
	- apply IHev. assert (a: S (S n) + m = S (S (n + m))). { reflexivity. }
		rewrite a in H0. apply evSS_ev. apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus) 

    This exercise can be completed without induction or case analysis.
    But, you will need a clever assertion and some tedious rewriting.
    Hint:  is [(n+m) + (n+p)] even? *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
	intros n m p H0 H1.
	apply ev_ev__ev with (n := double n) (m := m + p).
	- rewrite double_plus. rewrite plus_assoc.
		assert (a: n + n + m + p = n + m + n + p).
		{ rewrite plus_comm with (n + m) (n). rewrite plus_assoc. reflexivity. }
		rewrite a. assert (a1: n + m + n + p = (n + m) + (n + p)).
		{ rewrite plus_assoc. reflexivity. }
		rewrite a1. apply ev_sum.
		+ apply H0. + apply H1.
	- apply ev_double.
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** Just like properties, relations can be defined inductively.  One
    useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation) 

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop :=
	| pr : forall n1 n2, total_relation n1 n2.

(* FILL IN HERE

    [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation) 

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop :=
	| natfalse : forall n1 n2, 0 = 1 -> empty_relation n1 n2.

(* FILL IN HERE

    [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises) 

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
	intros m n o H0 H1.
	induction H1.
	- apply H0.
	- apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
	intros n.
	induction n.
	- apply le_n.
	- apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
	intros n m H0.
	induction H0.
	- apply le_n.
	- apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
	intros n m H.
	inversion H.
	- apply le_n.
	- apply le_trans with (S n).
		+ apply le_S. apply le_n.
		+ apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
	intros a b.
	induction b.
	- rewrite PeanoNat.Nat.add_0_r. apply le_n.
	- rewrite PeanoNat.Nat.add_succ_r. apply le_S. apply IHb.
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
	intros n1 n2 m H. split.
	- induction H.
		+ apply le_plus_l.
		+ apply le_S. apply IHle.
	- induction H.
		+ rewrite plus_comm. apply le_plus_l.
		+ apply le_S. apply IHle.
Qed.

(** Hint: the next one may be easiest to prove by induction on [n]. *)

Theorem n_le_m__Sn_le_Sm_eq : forall n m,
  n <= m <-> S n <= S m.
Proof.
	intros n m. split.
	- apply n_le_m__Sn_le_Sm.
	- apply Sn_le_Sm__n_le_m.
Qed.

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
	intros n m.
	induction n.
	- left. apply O_le_n.
	- intros p q H. destruct p.
		+ right. simpl in H. rewrite <- PeanoNat.Nat.add_succ_l in H.
			apply plus_le in H. destruct H. apply H0.
		+ simpl in H. apply Sn_le_Sm__n_le_m in H.
			rewrite <- n_le_m__Sn_le_Sm_eq. apply IHn. apply H.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
	intros n m H. unfold lt. apply le_S.
	unfold lt in H. apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
	intros n1 n2 m H. split.
	- unfold lt in H. unfold lt. rewrite <- PeanoNat.Nat.add_succ_l in H.
		apply plus_le in H. destruct H. apply H.
	- unfold lt in H. unfold lt. rewrite <- PeanoNat.Nat.add_succ_r in H.
		apply plus_le in H. destruct H. apply H0.
Qed.

(* reduced by 2 *)
Theorem plus_lt_auto : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
	intros n1 n2 m H. split;
	try (unfold lt in H; unfold lt).
	try (rewrite <- PeanoNat.Nat.add_succ_l in H; apply plus_le in H; destruct H). apply H.
	try (rewrite <- PeanoNat.Nat.add_succ_r in H; apply plus_le in H; destruct H). apply H0.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
	intros n.
	induction n.
	- intros. apply O_le_n.
	- intros. destruct m.
		+ inversion H.
		+ apply n_le_m__Sn_le_Sm. apply IHn. simpl in H. apply H.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
	intros n m H.
	generalize dependent n.
	induction m.
	- intros n H. inversion H. simpl. reflexivity.
	- intros n H. destruct n.
		+ simpl. reflexivity.
		+ simpl. apply Sn_le_Sm__n_le_m in H. apply IHm. apply H.
Qed.

Hint Resolve leb_complete : core.
Hint Resolve leb_correct : core.

(** Hint: The next one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
	intros.
	apply leb_complete in H. apply leb_complete in H0.
	apply leb_correct. apply le_trans with (m).
	- apply H. - apply H0.
Qed.

(* reduced by 1 *)
Theorem leb_true_trans_auto : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
	intros.
	apply leb_complete in H. apply leb_complete in H0.
	apply leb_correct. apply le_trans with (m); auto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
	intros. split.
	- apply leb_complete.
	- apply leb_correct.
Qed.

(* reduced by 1 *)
Theorem leb_iff_auto : forall n m,
  n <=? m = true <-> n <= m.
Proof.
	intros. split; auto.
Qed.
(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, especially useful (R_provability) 

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2]
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. *)

(*
	[R 1 1 2] is provable, while [R 2 2 6] is not provable.
	no changes will occur.
	[R 1 1 2] will become not provable.
*)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact) 

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat :=
	fun (n1 : nat) (n2 : nat) => n1 + n2.

Theorem f_eq : forall n m, S n = S m -> n = m.
Proof.
	intros. inversion H. reflexivity.
Qed.

Theorem R_0_n_n : forall n, R 0 n n.
Proof.
	intros.
	induction n.
	- apply c1.
	- apply c3. apply IHn.
Qed.

Hint Constructors R : core.

(* reduced by 2 *)
Theorem R_0_n_n_auto : forall n, R 0 n n.
Proof.
	intros.
	induction n; auto.
Qed.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
	intros. split.
	- intros H. unfold fR. induction H.
		+ reflexivity.
		+ simpl. rewrite IHR. reflexivity.
		+ rewrite PeanoNat.Nat.add_succ_r. rewrite IHR. reflexivity.
		+ rewrite PeanoNat.Nat.add_succ_r in IHR.
			rewrite PeanoNat.Nat.add_succ_l in IHR.
			apply f_eq in IHR. apply f_eq in IHR. apply IHR.
		+ rewrite plus_comm. apply IHR.
	- generalize dependent m. generalize dependent n. induction o.
		+ intros. unfold fR in H. induction m.
			* destruct n. { apply c1. } { simpl in H. inversion H. }
			* destruct n. { inversion H. } { inversion H. }
		+ intros. unfold fR. induction m.
			* simpl. unfold fR in H. simpl in H. rewrite <- H. apply R_0_n_n.
			* unfold fR in H. unfold fR in IHm. apply c2. apply IHo.
				unfold fR. rewrite PeanoNat.Nat.add_succ_l in H.
				apply f_eq. apply H.
Qed.
(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence) 

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq : list nat -> list nat -> Prop :=
| sub_nil l : subseq [] l
| sub_take x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
| sub_skip x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
	intros.
	induction l.
	- apply sub_nil.
	- apply sub_take. apply IHl.
Qed.

Hint Constructors subseq : core.
(* reduced by 2 *)
Theorem subseq_refl_auto : forall (l : list nat), subseq l l.
Proof.
	intros.
	induction l; auto.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
	intros.
	induction H.
	- apply sub_nil.
	- simpl. apply sub_take. apply IHsubseq.
	- simpl. apply sub_skip. apply IHsubseq.
Qed.

(* reduced by 5 *)
Theorem subseq_app_auto : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
	intros.
	induction H; simpl; auto.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
	intros l1 l2 l3 H0 H1.
	generalize dependent l1.
	induction H1.
	- intros. inversion H0. apply sub_nil.
	- intros. inversion H0.
		+ apply sub_nil.
		+ apply sub_take. apply IHsubseq. apply H3.
		+ apply sub_skip. rewrite <- H2. apply IHsubseq.
			rewrite H2. apply H3.
	- intros. apply sub_skip. apply IHsubseq. apply H0.
Qed.

(* reduced by 11 *)
Theorem subseq_trans_auto : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
	intros l1 l2 l3 H0 H1.
	generalize dependent l1.
	induction H1; intros; try inversion H0; auto.
	apply sub_skip. apply IHsubseq. rewrite H2. apply H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2) 

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 n l (H: R n l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 n l (H: R n l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n l.

(*
	R 2 [1;0] is provable.
	R 1 [1;2;1;0] is provable.
	R 6 [3;2;1;0] is not provable.
*)

Hint Constructors R : core.

Lemma R_0_nil : R 2 [1; 0].
Proof.
	apply c2. apply c2. apply c1.
Qed.

(* reduced by 2 *)
Lemma R_0_nil_auto : R 2 [1; 0].
Proof.
	auto.
Qed.


Lemma R_1_1210 : R 1 [1; 2; 1; 0].
Proof.
	apply c3. apply c2. apply c3. apply c3. apply c2. apply R_0_nil.
Qed.

Hint Resolve R_0_nil : core.
(* reduced by 5 *)
Lemma R_1_1210_auto : R 1 [1; 2; 1; 0].
Proof.
	auto 6.
Qed.

(* [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        In particular, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows.  We use the notation [s =~ re] in
    place of [exp_match s re]; by "reserving" the notation before
    defining the [Inductive], we can use it in the definition! *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.
(** Again, for readability, we display this definition using
    inference-rule notation. *)

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the string
    [[1]] directly.  Since the goal mentions [[1; 2]] instead of 
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split 
    the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1) 

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
	intros. unfold not. intros H.
	inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
	intros T s re1 re2 [H1 | H2].
	- apply MUnionL. apply H1.
	- apply MUnionR. apply H2.
Qed.

Hint Constructors exp_match : core.
(* reduced by 3 *)
Lemma MUnion'_auto : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
	intros T s re1 re2 [H1 | H2]; auto.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
	intros. induction ss. 
	- apply MStar0.
	- apply MStarApp.
		+ apply H. simpl. left. reflexivity.
		+ apply IHss. intros.
			apply H. simpl. right. apply H0.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec) 

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
	intros. split. 
	- generalize dependent s1. induction s2.
		+ intros. inversion H. reflexivity.
		+ intros. inversion H. apply IHs2 in H4. rewrite H4.
			inversion H3. simpl. reflexivity.
	- generalize dependent s1. induction s2.
		+ intros. inversion H. simpl. apply MEmpty.
		+ intros. rewrite H. simpl.
			assert (a: x :: s2 = [x] ++ s2). { reflexivity. }
			rewrite a. apply MApp.
			{ apply MChar. } { apply IHs2. reflexivity. }
Qed.

(* reduced by 13 *)
Lemma reg_exp_of_list_spec_auto : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
	intros. split;
	generalize dependent s1; induction s2;
		intros; try inversion H; simpl;
		try ( apply IHs2 in H4; rewrite H4;
			inversion H3; simpl);  try reflexivity;
		auto. assert (a: x :: s2 = [x] ++ s2). { reflexivity. }
		rewrite a. auto.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** Here again we get two induction hypotheses, and they illustrate
    why we need induction on evidence for [exp_match], rather than
    induction on the regular expression [re]: The latter would only
    provide an induction hypothesis for strings that match [re], which
    would not allow us to reason about the case [In x s2]. *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty) 

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
	match re with
	| EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => re_not_empty re1 && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 || re_not_empty re2
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
	intros. split.
	- intros. destruct H. induction H.
		+ simpl. reflexivity.
		+ simpl. reflexivity.
		+ simpl. rewrite IHexp_match1. rewrite IHexp_match2. reflexivity.
		+ simpl. rewrite IHexp_match. simpl. reflexivity.
		+ simpl. rewrite IHexp_match. simpl. 
			apply orb_true_iff. right. reflexivity.
		+ simpl. reflexivity.
		+ simpl. reflexivity.
	- intros. induction re.
		+ simpl in H. inversion H.
		+ exists []. apply MEmpty.
		+ exists [t]. apply MChar.
		+ simpl in H. apply andb_true_iff in H. destruct H.
			apply IHre1 in H. apply IHre2 in H0. destruct H.
			destruct H0. exists (x ++ x0). apply MApp.
			* apply H. * apply H0.
		+ simpl in H. apply orb_true_iff in H. destruct H.
			* apply IHre1 in H. destruct H. exists x.
				apply MUnionL. apply H.
			* apply IHre2 in H. destruct H. exists x.
				apply MUnionR. apply H.
		+ exists []. apply MStar0.
Qed.

(* reduced by 21 *)
Lemma re_not_empty_correct_auto : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
	intros. split.
	- intros. destruct H. induction H; simpl;
		try rewrite IHexp_match1; try rewrite IHexp_match2;
		try rewrite IHexp_match; try reflexivity; simpl;
		try (apply orb_true_iff; right);
		try reflexivity.
	- intros. induction re.
		+ simpl in H. inversion H.
		+ exists []. apply MEmpty.
		+ exists [t]. apply MChar.
		+ simpl in H. apply andb_true_iff in H. destruct H.
			apply IHre1 in H. apply IHre2 in H0. destruct H.
			destruct H0. exists (x ++ x0). auto.
		+ simpl in H. apply orb_true_iff in H. destruct H;
			try apply IHre1 in H; try apply IHre2 in H; destruct H;
			exists x; auto.
		+ exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt: *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. *) intros s2 H. simpl. (* Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    An awkward way to solve this problem is "manually generalizing"
    over the problematic expressions by adding explicit equality
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre' as Heqre''. intros s H. apply H.

  - (* MStarApp *)
    injection Heqre' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
	intros.
	remember (Star re) as re'.
	induction H.
	- discriminate.
	- discriminate.
	- discriminate.
	- discriminate.
	- discriminate.
	- injection Heqre' as Heqre''. exists []. split.
		+ simpl. reflexivity.
		+ intros. destruct H.
	- inversion Heqre'. apply IHexp_match2 in Heqre'. destruct Heqre'.
		destruct H1. exists (s1 :: x). split.
		+ simpl. rewrite H1. reflexivity.
		+ simpl. intros. destruct H4.
			* rewrite <- H4. rewrite <- H2. apply H.
			* apply H3. apply H4.
Qed.

(* reduced by 5 *)
Lemma MStar''_auto : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
	intros. remember (Star re) as re'.
	induction H;
	try discriminate.
	- injection Heqre' as Heqre''. exists []. split.
		+ simpl. reflexivity.
		+ intros. destruct H.
	- inversion Heqre'. apply IHexp_match2 in Heqre'. destruct Heqre'.
		destruct H1. exists (s1 :: x). split; simpl.
		+ rewrite H1. reflexivity.
		+ intros. destruct H4.
			* rewrite <- H4. rewrite <- H2. apply H.
			* apply H3. apply H4.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced (weak_pumping) 

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].  (For the sake of simplicity in this
    exercise, we consider a slightly weaker theorem than is usually
    stated in courses on automata theory.)

    To get started, we need to define "sufficiently long."  Since we
    are working in a constructive logic, we actually need to be able
    to calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** You may find these lemmas about the pumping constant useful when
    proving the pumping lemma below. *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* Emptyset *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** This auxiliary lemma might also be useful in your proof of the
    pumping lemma. *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

(** The (weak) pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= Poly.length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
	- simpl. intros. rewrite app_length in H. apply add_le_cases in H.
		inversion H.
		+ destruct (IH1 H0) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
			exists ss1, ss2, (ss3 ++ s2). rewrite <- app_assoc.
			rewrite <- app_assoc. split.
			* simpl. reflexivity.
			* split. { apply H12. } { intros. rewrite app_assoc.
				rewrite app_assoc. apply MApp. { rewrite <- app_assoc. apply H13. } 
				{ apply Hmatch2. } }
		+ destruct (IH2 H0) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
			exists (s1 ++ ss1), ss2, ss3. rewrite <- app_assoc. split.
			* reflexivity.
			* split. { apply H12. } { intros. rewrite <- app_assoc. apply MApp.
				{ apply Hmatch1. } { apply H13. }}
	- simpl. intros. apply plus_le in H. destruct H.
		destruct (IH H) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
		exists ss1, ss2, ss3. split.
		+ reflexivity.
		+ split. * apply H12.
			* intros. apply MUnionL. apply H13.
	- simpl. intros. apply plus_le in H. destruct H.
		destruct (IH H0) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
		exists ss1, ss2, ss3. split.
		+ reflexivity.
		+ split. * apply H12.
			* intros. apply MUnionR. apply H13.
	- simpl. intros. inversion H.
		apply pumping_constant_0_false in H1. destruct H1.
	- simpl. intros. exists [], (s1 ++ s2), []. split.
		+ simpl. rewrite <- app_assoc. rewrite app_nil_r. reflexivity.
		+ split. * destruct (s1 ++ s2). { simpl in H. inversion H.
				apply pumping_constant_0_false in H1. destruct H1. }
				{ unfold not. intros. inversion H0. }
			* intros. simpl. rewrite app_nil_r. induction m.
				{ simpl. apply MStar0. } { simpl. apply star_app.
					{ apply star_app. { apply MStar1. apply Hmatch1. }
						{ apply Hmatch2. }}
					{ apply IHm. } }
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (pumping) 

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)

Lemma plus_another : forall n m p q,
	n + m <= p -> n + m <= p + q.
Proof.
	intros. apply le_trans with p.
	- apply H.
	- apply le_plus_l.
Qed.

Lemma plus_another_r : forall n m p q,
	n + m <= q -> n + m <= p + q.
Proof.
	intros. apply le_trans with q.
	- apply H.
	- rewrite plus_comm. apply le_plus_l.
Qed.

Lemma plus_another_single : forall n m p : nat,
	n <= m -> n <= m + p.
Proof.
  induction p.
  - rewrite plus_comm. simpl. intros H. apply H.
  - intros. apply IHp in H. rewrite <- plus_n_Sm.
		apply le_S. apply H.
Qed.

Lemma le_plus_trans : forall n m p q : nat,
	n <= m -> p <= q -> n + p <= m + q.
Proof.
  intros n m p q H1. induction H1.
  - intros H2. apply leb_iff. induction n. simpl.
		apply <- leb_iff. apply H2. simpl. apply IHn.
  - intros H2. apply IHle in H2. simpl. apply le_S. apply H2.
Qed.

Lemma le_false_lt_true : forall n m : nat,
	n <=? m = false ->
	m <? n = true.
Proof.
  induction n.
  - intros. discriminate.
  - intros. induction m.
    + reflexivity.
    + simpl. apply IHn. simpl in H. apply H.
Qed.

Lemma lt_true_le_true : forall n m : nat,
	n <? m = true ->
	n <=? m = true.
Proof.
  induction n.
  - intros. reflexivity.
  - intros. induction m.
    + discriminate H.
    + simpl. apply IHn. simpl in H. apply H.
Qed.

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= Poly.length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    Poly.length s1 + Poly.length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
	- simpl. intros. rewrite app_length in H. apply add_le_cases in H.
		inversion H.
		+ destruct (IH1 H0) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
			exists ss1, ss2, (ss3 ++ s2). rewrite <- app_assoc.
			rewrite <- app_assoc. split.
			* simpl. reflexivity.
			* split. { apply H12. } { split. { destruct H13.
				inversion H1. { rewrite H4. apply le_plus_l. }
				{ rewrite H3. apply plus_another. apply H1. }
				} { intros. rewrite app_assoc, app_assoc. apply MApp.
					{ destruct H13 as [H13 H14]. rewrite <- app_assoc.
						apply H14. } { apply Hmatch2. }}}
		+ apply IH2 in H0.
			destruct H0 as [ss3 [ss4 [ss5 [H11 [H12 [H13 H14]]]]]].
			destruct (Poly.length s1 <=? pumping_constant re1) eqn:E.
			{ exists (s1 ++ ss3), ss4, ss5. split. rewrite H11.
				rewrite app_assoc. reflexivity. split.
				{ apply H12. } { split.
				rewrite app_length. rewrite <- plus_assoc.
				apply leb_iff in E. apply le_plus_trans. apply E.
				apply H13. intros m. rewrite <- app_assoc.
				apply MApp. apply Hmatch1. apply H14. } }
			{ apply le_false_lt_true in E. apply lt_true_le_true in E.
				apply leb_iff in E. apply IH1 in E.
				destruct E as [ss6 [ss7 [ss8 [H15 [H16 [H17 H18]]]]]].
				exists ss6, ss7, (ss8 ++ s2). split. rewrite H15.
				rewrite <- app_assoc, <- app_assoc. reflexivity. split.
				{ apply H16. } { split.
						{ apply plus_another_single. apply H17. }
						{ intros. rewrite app_assoc, app_assoc. apply MApp.
				rewrite <- app_assoc. apply H18. apply Hmatch2. } } }
	- simpl. intros. apply plus_le in H. destruct H.
		destruct (IH H) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
		exists ss1, ss2, ss3. split.
		+ reflexivity.
		+ split. * apply H12.
			* split. { lia. } { intros. apply MUnionL.
					destruct H13. apply H2. }
	- simpl. intros. apply plus_le in H. destruct H.
		destruct (IH H0) as [ss1 [ss2 [ss3 [H11 [H12 H13]]]]]. rewrite H11.
		exists ss1, ss2, ss3. split.
		+ reflexivity.
		+ split. * apply H12.
			* split. { lia. } { intros. apply MUnionR.
					destruct H13. apply H2. }
	- simpl. intros. inversion H.
		apply pumping_constant_0_false in H1. destruct H1.
	- simpl. intros. rewrite app_length in H.
    destruct s1.
    + simpl in *. apply IH2 in H.
			destruct H as [ss1 [ss3 [ss4 [H11 [H12 [H13 H14]]]]]].
			exists ss1, ss3, ss4. split. { apply H11. }
			{ split. { apply H12. } { split. { apply H13. } 
						{ apply H14. }}}
    + destruct ( pumping_constant re <=? Poly.length (x :: s1) ) eqn:E.
      * apply leb_iff in E. apply IH1 in E.
				destruct E as [ss3 [ss4 [ss5 [H11 [H12 [H13 H14]]]]]].
				exists ss3, ss4, (ss5 ++ s2). split. 
				{ rewrite H11. rewrite <- app_assoc, <- app_assoc.
					reflexivity. } { split. { apply H12. } { split.
					{ apply H13. } { intros. rewrite app_assoc, app_assoc.
						apply MStarApp. rewrite <- app_assoc.
						apply H14. apply Hmatch2. }}}
      * apply le_false_lt_true in E. apply lt_true_le_true in E.
				apply leb_iff in E. exists [], (x :: s1), s2.
				split. { reflexivity. } { split. { discriminate. }
						{ split. { apply E. } { intros m. simpl.
							apply napp_star. apply Hmatch1. apply Hmatch2. }}}
Qed.
End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].
    Instead of generating an equation such as [(n =? m) = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence for
    [reflect P true] is by showing [P] and then using the [ReflectT]
    constructor.  If we invert this statement, this means that it
    should be possible to extract evidence for [P] from a proof of
    [reflect P true].  Similarly, the only way to show [reflect P
    false] is by combining evidence for [~ P] with the [ReflectF]
    constructor.

    It is easy to formalize this intuition and show that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, especially useful (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
	intros. destruct b.
	- split. + intros. reflexivity.
		+ intros. inversion H. apply H1.
	- split. + intros. inversion H. unfold not in H1.
		apply H1 in H0. destruct H0.
		+ intros. inversion H0.
Qed.

(* reduced by 5 *)
Theorem reflect_iff_auto : forall P b, reflect P b -> (P <-> b = true).
Proof.
	intros. destruct b;
	split; intros; try reflexivity; try inversion H;
	try inversion H0; auto.
	unfold not in H1. apply H1 in H0. destruct H0.
Qed.
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [rewrite] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, especially useful (eqbP_practice) 

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
	intros. unfold not. intros. induction l.
	- simpl in *. destruct H0.
	- simpl in *. destruct (eqbP n x).
		+ rewrite H1 in *. simpl in H. inversion H.
		+ simpl in H. apply IHl in H.
			* destruct H.
			* destruct H0.  { unfold not in H1. symmetry in H0.
				apply H1 in H0. destruct H0. } { apply H0. }
Qed.
(** [] *)

(** This small example shows how reflection gives us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (nostutter_defn) 

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
| Empty : nostutter []
| OneElem (x : X) : nostutter [x]
| TwoElem (x1 : X) (x2 : X) (l : list X) : x1 <> x2 ->
									nostutter (x2 :: l) -> nostutter (x1 :: x2 :: l)
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_2:  nostutter (@nil nat).
Proof. repeat constructor; apply eqb_neq; auto.
Qed.

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) 

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

Inductive merge_two_lists {X:Type} : list X -> list X -> list X -> Prop :=
| Emptylists : merge_two_lists [] [] []
| InL1 (h : X) (l1 : list X) (l2 : list X) (l : list X) :
		merge_two_lists l1 l2 l -> merge_two_lists (h :: l1) l2 (h :: l)
| InL2 (h : X) (l1 : list X) (l2 : list X) (l : list X) :
		merge_two_lists l1 l2 l -> merge_two_lists l1 (h :: l2) (h :: l)
.

Theorem merge_filter_good {X: Type} (test: X -> bool) (l1 l2 l: list X):
  merge_two_lists l1 l2 l->
  forallb test l1 = true ->
  forallb (fun x => negb (test x)) l2 = true ->
  filter test l = l1.
Proof.
	intros. induction H.
	- simpl. reflexivity.
	- simpl. destruct (test h) eqn:E.
		+ assert (a: forall (X: Type) (h: X) (l1 l2: list X),
							l1 = l2 -> h :: l1 = h :: l2).
				{ intros. rewrite H2. reflexivity. }
			apply a. apply IHmerge_two_lists.
			* simpl in *. apply andb_true_iff in H0.
				destruct H0 as [H01 H02]. apply H02.
			* simpl in *. apply H1.
		+ simpl in *. apply andb_true_iff in H0.
			destruct H0 as [H01 H02]. rewrite H01 in E. inversion E.
	- 
			destruct (test h) eqn:E.
		+ simpl in *. apply andb_true_iff in H1.
			destruct H1 as [H11 H12].
			assert (a1: negb (test h) = true -> test h = false).
			{ intros Ha1. destruct (test h). discriminate. reflexivity. }
			apply a1 in H11. rewrite H11 in E. inversion E.
		+ simpl in H1. apply andb_true_iff in H1.
			destruct H1 as [H11 H12]. simpl. rewrite E.
			apply IHmerge_two_lists. * apply H0. * apply H12.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) 

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)


(** xs is a subsequence of host that is good for test *)


Definition good_subseq (test: nat -> bool) (host: list nat) 
           (xs : list nat) : Prop :=
  subseq xs host /\   forallb test xs = true.

Lemma subseq_filter_good  (test: nat -> bool) (host: list nat) :
  good_subseq test host  (filter test host).
Proof.
	unfold good_subseq. split.
	- induction (filter test host). apply sub_nil. destruct host.  Admitted.


(** filter includes any good subsequence *)

Definition includes_all_good (test: nat -> bool) (host: list nat)
 (lmax : list nat) :=
  forall (xs : list nat),
    good_subseq test host xs ->
    subseq xs lmax.


Theorem filter_includes_all_good (test: nat -> bool) (host: list nat) :
  includes_all_good test host (filter test host).
Proof.
	unfold includes_all_good. intros. unfold good_subseq in H. destruct H.
	induction xs. - apply sub_nil. - Admitted.


(** next want to prove there is only ONE subseq that satisfies
includes_all_good *)


(** An easy basic fact about subseq *)

Lemma subseq_len (xs ys : list nat) :
  subseq xs ys -> Poly.length xs <= Poly.length ys.
Proof.
	intros. induction H.
	- simpl. lia.
	- simpl. lia.
	- simpl. lia.
Qed.

(* reduced by 4 *)
Lemma subseq_len_auto (xs ys : list nat) :
  subseq xs ys -> Poly.length xs <= Poly.length ys.
Proof.
	intros. induction H; simpl; lia.
Qed.

(** A useful fact for flagging inconsistent hypotheses, used below in
    subseq_eq .  This seems surprisingly hard to prove directly.  But
subseq_len provides the way to an easy proof. *)

Lemma not_subseq_tl (u : nat) (us : list nat) :
  ~ subseq (u::us) us.  
Proof. 
	intros. unfold not. intros. apply subseq_len in H.
	simpl in H. lia.
Qed.

(** Together with subseq_refl and subseq_trans from earlier, this
shows that subseq makes a partial order relation on lists *)

Lemma subseq_antisym (xs : list nat) :
  forall ys, 
  subseq xs ys ->
  subseq ys xs ->
  xs = ys.
Proof.
	intros . induction H.
	- inversion H0. reflexivity. 
	- f_equal. apply IHsubseq. inversion H0. subst.
		+ apply H2. + subst. apply subseq_len in H3. apply subseq_len in H. simpl in *. lia.
	- apply subseq_len in H. apply subseq_len in H0. simpl in *. lia.
Qed.

(** filter makes the unique subseq that includes all good ones.
   To prove this we just prove that there is only one subseq that 
   includes all the good ones.
*)

Theorem all_good_uniqueness  (test: nat -> bool) (host: list nat)
        (lmax1 lmax2 : list nat) :
  good_subseq test host lmax1 ->
  good_subseq test host lmax2 ->
  includes_all_good test host lmax1 -> 
  includes_all_good test host lmax2 -> 
  lmax1 = lmax2.
Proof.
	intros. apply subseq_antisym.
	- apply H2. apply H.
	- apply H1. apply H0.
Qed.

(* Just to be explicit *)
Corollary all_good_uniqueness'  (test: nat -> bool) (host: list nat) :
  forall (lmax : list nat),
  good_subseq test host lmax ->
  includes_all_good test host lmax -> 
  lmax = filter test host.
Proof.
	intros. apply filter_includes_all_good in H. unfold includes_all_good in *. apply subseq_antisym in H.
	- rewrite H. reflexivity.
	- apply H0. apply subseq_filter_good.
Qed.

(** **** Exercise: 4 stars, standard, optional (palindromes) 

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)


Inductive palindrome {X : Type} : list X -> Prop :=
	| Pnil : palindrome []
	| Psingle (x : X) : palindrome [x]
	| Pheadtail (x : X) (l : list X) : palindrome l -> palindrome ( x :: l ++ [x] )
. 

Theorem pal_app_rev : forall X (l : list X),
	palindrome (l ++ rev l).
Proof.
  intros. induction l.
  - simpl. apply Pnil.
  - simpl. rewrite app_assoc. apply Pheadtail. apply IHl.
Qed.

Hint Constructors palindrome : core.
(* reduced by 3 *)
Theorem pal_app_rev_auto : forall X (l : list X),
	palindrome (l ++ rev l).
Proof.
  intros. induction l; simpl; try rewrite app_assoc; auto.
Qed.

Theorem pal_rev : forall X (l : list X),
	palindrome l -> l = rev l.
Proof.
  intros. induction H.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite <- IHpalindrome.
    simpl. reflexivity.
Qed.

(* reduced by 3 *)
Theorem pal_rev_auto : forall X (l : list X),
	palindrome l -> l = rev l.
Proof.
  intros. induction H; simpl;
	try (rewrite rev_app_distr, <- IHpalindrome); try reflexivity.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse) 

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)

Lemma palindrome_converse_length: forall X (n : nat) (l : list X),
	Poly.length l <= n /\ l = rev l -> palindrome l.
Proof.
  intros X n. induction n.
  - intros. inversion H. inversion H0.
		assert (a: Poly.length l = 0 -> l = [] ).
		{ intros. destruct l. * reflexivity. * simpl in H3. inversion H3. }
		apply a in H3. rewrite H3. apply Pnil.
  - intros. destruct l.
			+ apply Pnil.
			+ simpl in *. destruct (rev l) as [|x' l']  eqn:E.
      	* destruct H. rewrite H0. simpl. apply Psingle.
      	* destruct H. injection H0 as Hx. rewrite H0. apply Pheadtail.
		      assert (a: Poly.length l' <= n).
					{ apply leb_iff in H. simpl in H. apply leb_iff in H.
	        	rewrite H0 in H. rewrite app_length in H.
						simpl in H. rewrite plus_comm in H. apply Le.le_Sn_le.  apply H. }
		      assert (a1: l' = rev l').
					{ rewrite <- Hx in *. rewrite H0 in E.
						rewrite rev_app_distr in E. simpl in E. injection E as E1.
						rewrite E1. reflexivity. }
	      	apply IHn. split. { apply a. } { apply a1. }
Qed.


Theorem palindrome_converse: forall X (l : list X),
	l = rev l -> palindrome l.
Proof.
  intros.
	apply (palindrome_converse_length X (Poly.length l)).
	split.
	- apply le_n.
	- apply H.
Qed.


(* [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup) 

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

(*
Fixpoint disjoint {X : Type} (l1 : list X) (l2 : list X) : Prop :=
	match l1, l2 with
	| [], _ => True
	| _ , [] => True
	| h1 :: t1, h2 :: t2 => (( ~ In h1 t2 ) /\ ( ~ In h2 t1 )) /\
													disjoint t1 t2
	end.
*)

Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | Disnil : forall l, disjoint [] l
  | Disnil1 : forall l, disjoint l []
  | Disleft: forall l1 l2 x, disjoint l1 l2 -> ~ In x l2 -> disjoint (x :: l1) l2  
  | Disright: forall l1 l2 x, disjoint l1 l2 -> ~ In x l1 -> disjoint l1 (x :: l2)
.

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup {X: Type} : list X -> Prop :=
	| Nodupnil : NoDup []
	| Nodupl (x : X) (l : list X) : ~ In x l -> NoDup l -> NoDup (x :: l)
.

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Lemma app_not_in :
	forall X x (l1 l2 : list X),
  ~ In x l1 -> ~ In x l2 -> ~ In x (l1 ++ l2).
Proof.
	intros X x l1 l2 H1 H2 H.
  rewrite In_app_iff in H. destruct H.
  - apply H1. apply H.
  - apply H2. apply H.
Qed.
(* reduced by 3 *)
Lemma app_not_in_auto :
	forall X x (l1 l2 : list X),
  ~ In x l1 -> ~ In x l2 -> ~ In x (l1 ++ l2).
Proof.
	intros X x l1 l2 H1 H2 H.
  rewrite In_app_iff in H. destruct H; auto.
Qed.

Lemma app_not_in_not :
	forall X x (l1 l2 : list X),
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof.
	intros. rewrite In_app_iff in H.
	unfold not in *. intros. destruct H.
  left. apply H0.
Qed.

Lemma mid_app_Nodup :
	forall X x (l1 l2 : list X),
  NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> NoDup (l1 ++ (x :: l2)).
Proof.
	intros. induction l1.
 - constructor.
	+ apply H0.
	+ apply H.
 - assert (a: x <> x0). { intros Hx. apply H0. left. rewrite Hx. easy. }
   inversion H. constructor. 
   + apply app_not_in. 
     * apply app_not_in_not with (l2). apply H3.
     * unfold not. intros. destruct H5.
				{ apply a.  apply H5. }
				{ apply H3. rewrite In_app_iff. right. apply H5. }
   + apply IHl1. * apply H4.
     * unfold not. intros. apply H0. right. apply H5.
Qed.

Theorem NoDup_disjoint_app_forward :
	forall X (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
	intros X l1 l2 Hl1 Hl2 H1. induction H1.
  - simpl. apply Hl2.
  - rewrite app_nil_r. apply Hl1.  
  - inversion Hl1. constructor. 
    + apply app_not_in.
			* apply H3.
			* apply H.
    + apply IHdisjoint.
			* apply H4.
			* apply Hl2.
  - inversion Hl2. apply mid_app_Nodup. 
    + apply IHdisjoint.
			* apply Hl1.
			* apply H4.
    + apply app_not_in.
			* apply H.
			* apply H3.
Qed.
(* reduced by 4 *)
Theorem NoDup_disjoint_app_forward_auto :
	forall X (l1 l2: list X),
  NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
	intros X l1 l2 Hl1 Hl2 H1. induction H1.
  - simpl. apply Hl2.
  - rewrite app_nil_r. apply Hl1.  
  - inversion Hl1. constructor. 
    + apply app_not_in; auto.
    + apply IHdisjoint; auto.
  - inversion Hl2. apply mid_app_Nodup. 
    + apply IHdisjoint; auto.
    + apply app_not_in; auto.
Qed.

Theorem NoDup_disjoint_app_back : forall X (l1 l2: list X),
  NoDup (l1++l2) -> NoDup l1 /\ NoDup l2 /\ disjoint l1 l2.
Proof. intros. split. inversion H.
  - induction l1. + apply Nodupnil. + simpl in *. inversion H1.
	- induction l1. + apply Nodupnil. + apply Nodupl.
		* unfold not. intros. apply H1.
Admitted.


Theorem NoDup_disjoint_app : forall {X:Type} (l1 l2: list X),
  NoDup (l1++l2) <-> (NoDup l1 /\ NoDup l2 /\ disjoint l1 l2).
Proof.
	intros. split.
	- apply NoDup_disjoint_app_back.
	- intros. apply NoDup_disjoint_app_forward. destruct H. destruct H0.
		+ apply H. + destruct H as [_ [H1 _]]. apply H1.
		+ destruct H as [_ [_ H2]]. apply H2.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle) 

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
	intros. induction l.
	- inversion H.
	- simpl in *. destruct H.
		+ rewrite H. exists [], l. reflexivity.
		+ apply IHl in H. destruct H. destruct H.
			exists (x0 :: x1), x2. simpl.
			rewrite <- H. reflexivity.
Qed.

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
	| Repadd : forall l x, In x l -> repeats (x :: l)
	| Repnew : forall l x, repeats l -> repeats (x :: l)
.

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   Poly.length l2 < Poly.length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
	- intros. inversion H1.
	- intros. destruct (H (In x l1')).
		+ simpl in *. apply Repadd. apply H2.
		+ simpl in *. apply Repnew.
			assert (a: In x l2). { apply H0. left. reflexivity. }
			apply in_split in a.
			destruct a. destruct H3. apply IHl1' with (x1 ++ x0).
			* apply H. * intros.
				assert (a0: forall X x (l1 l2: list X), In x (l1 ++ l2) ->
					In x (l2 ++ l1)).
				{ intros. rewrite In_app_iff in *. inversion H5.
				 	** right. apply H6. ** left. apply H6. }
				assert (a1: In x2 ((x :: x1) ++ x0)).
				{ apply a0. rewrite <- H3. apply H0. right. apply H4. }
				destruct a1.
				{ exfalso. apply H2. rewrite H5. apply H4. }
				{ apply H5. }
			* rewrite H3 in H1. rewrite app_length in *.
				rewrite plus_comm in H1. simpl in *.
				apply Sn_le_Sm__n_le_m in H1. apply H1.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function that reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Import Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne) 

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
	intros. split.
	- intros. apply app_exists in H. destruct H  as [x0 [x1 [H1 [H2 H3]]]]. destruct x0.
		+ left. split.	* apply H2. * simpl in *. rewrite H1. apply H3.
		+ right. inversion H1.
			exists x0, x1. split.
			* reflexivity. * split. { apply H2. } { apply H3. }
	- intros. destruct H. destruct H.
		+ assert (a1: [] ++ a :: s = a :: s). { simpl. reflexivity. }
			rewrite <- a1. apply MApp.
			* apply H. * apply H0.
		+ inversion H. inversion H0. destruct H1. destruct H2.
			rewrite H1.
			assert (a2: a :: x ++ x0  = (a :: x) ++ x0 ).
			{ simpl. reflexivity. }
			rewrite a2. apply MApp.
			* apply H2. * apply H3.
Qed.
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne) 

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)


Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
	intros. split.
	- intros. remember (a :: s). remember (Star re).
		induction H.
		+ inversion Heql.
		+ inversion Heqr.
		+ inversion Heqr.
		+ inversion Heqr.
		+ inversion Heqr.
		+ inversion Heql.
		+ destruct s1.
			* inversion Heqr. rewrite H2 in *.
			apply IHexp_match2 in Heqr.
				** destruct Heqr. destruct H1. destruct H1. 
					destruct H3. exists x, x0. split.
					{ apply H1. } { split. apply H3. apply H4. }
				** simpl in Heql. apply Heql.
			* inversion Heql. rewrite H3 in *. inversion Heqr.
				rewrite H4 in *. exists s1, s2. split.
				** symmetry. apply H3.
				** split.	{ rewrite <- H2. apply H. } { apply H0. }
	- intros. destruct H. destruct H.
		destruct H. destruct H0.
		rewrite H.
		assert (a1: a :: x ++ x0 = (a :: x) ++ x0).
		{ reflexivity. } rewrite a1. apply MStarApp.
		+ apply H0.
		+ apply H1.
Qed.

(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps) 

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: reg_exp ascii) : bool :=
	match re with
  | EmptySet => false
  | EmptyStr => true
	| Char _ => false
	| App x1 x2  => andb (match_eps x1) (match_eps x2)
	| Union x1 x2 => orb (match_eps x1) (match_eps x2)
	| Star re => true
end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl) 

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
	unfold refl_matches_eps.
	intros.
	induction re.
	- simpl. apply ReflectF. unfold not. intros.
		inversion H.
	- simpl. apply ReflectT. apply MEmpty.
	- simpl. apply ReflectF. unfold not. intros.
		inversion H.
	- simpl. apply iff_reflect.
		split.
		+ intros. rewrite andb_true_iff. admit.
		+ rewrite andb_true_iff. intros. destruct H. admit.
	- simpl in *. apply iff_reflect. rewrite orb_true_iff. split.
		+ intros. inversion H.
			* left. apply reflect_iff in IHre1. apply IHre1. apply H2.
			* right. apply reflect_iff in IHre2. apply IHre2. apply H1.
		+ intros. destruct H. * apply MUnionL.
				apply reflect_iff in IHre1. apply IHre1. apply H.
			* apply MUnionR. apply reflect_iff in IHre2.
				apply IHre2. apply H.
	- simpl in *. apply ReflectT. apply reflect_iff in IHre.
		apply MStar0.
Admitted.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive) 

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if ascii_dec a x then EmptyStr
								else EmptySet
  | App x1 x2 => if (match_eps x1)
								then Union (derive a x2) (App (derive a x1) x2)  
               	else App (derive a x1) x2
  | Union x1 x2 => Union (derive a x1) (derive a x2)
  | Star re => App (derive a re) (Star re)
  end.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof. auto. Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof. auto. Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof. auto. Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof. auto. Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof. auto. Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof. auto. Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof. auto. Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof. auto. Qed.

(** **** Exercise: 4 stars, standard, optional (derive_corr) 

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
	unfold derives.
	intros. unfold is_der. intros.
	split.
	
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match) 

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
	match s with
		| [] => match_eps re
		| h :: t => regex_match t (derive h re)
	end.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl) 

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
	unfold matches_regex. intros. generalize dependent re.
	induction s.
	- intros. simpl. apply iff_reflect. split.
		+ intros. rewrite reflect_iff in H. * apply H.
				* simpl. apply match_eps_refl.
		+ intros. rewrite reflect_iff. * apply H.
				* simpl. apply match_eps_refl.
	- intros. simpl in *.
		destruct (derive_corr x re s).
    destruct (IHs (derive x re)).
    + constructor. apply H0. apply H1.
    + constructor. unfold not.
			intros. apply H1. apply H. apply H2.
Qed.
(** [] *)

(* 2020-09-09 20:51 *)
