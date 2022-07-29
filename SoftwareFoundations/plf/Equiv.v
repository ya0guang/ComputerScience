(** * Equiv: Program Equivalence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.

(** *** Before you Get Started:

    - Create a fresh directory for this volume. (Do not try to mix the
      files from this volume with files from _Logical Foundations_ in
      the same directory: the result will not make you happy.)

    - The new directory should contain at least the following files:
         - [Imp.v] (make sure it is the one from the PLF distribution,
           not the one from LF: they are slightly different);
         - [Maps.v] (ditto)
         - [Equiv.v] (this file)
         - [_CoqProject], containing the following line:

           -Q . PLF

    - Reminder: If you see errors like this...

             Compiled library PLF.Maps (in file
             /Users/.../plf/Maps.vo) makes inconsistent assumptions
             over library Coq.Init.Logic

      ... it may mean something went wrong with the above steps.
      Doing "[make clean]" (or manually removing everything except
      [.v] and [_CoqProject] files) may help. *)

(** *** Advice for Working on Exercises:

    - Most of the Coq proofs we ask you to do are similar to proofs
      that we've provided.  Before starting to work on exercises
      problems, take the time to work through our proofs (both
      informally and in Coq) and make sure you understand them in
      detail.  This will save you a lot of time.

    - The Coq proofs we're doing now are sufficiently complicated that
      it is more or less impossible to complete them by random
      experimentation or following your nose.  You need to start with
      an idea about why the property is true and how the proof is
      going to go.  The best way to do this is to write out at least a
      sketch of an informal proof on paper -- one that intuitively
      convinces you of the truth of the theorem -- before starting to
      work on the formal one.  Alternately, grab a friend and try to
      convince them that the theorem is true; then try to formalize
      your explanation.

    - Use automation to save work!  The proofs in this chapter can get
      pretty long if you try to write out all the cases explicitly. *)

(* ################################################################# *)
(** * Behavioral Equivalence *)

(** In an earlier chapter, we investigated the correctness of a very
    simple program transformation: the [optimize_0plus] function.  The
    programming language we were considering was the first version of
    the language of arithmetic expressions -- with no variables -- so
    in that setting it was very easy to define what it means for a
    program transformation to be correct: it should always yield a
    program that evaluates to the same number as the original.

    To talk about the correctness of program transformations for the
    full Imp language, in particular assignment, we need to consider
    the role of variables and state. *)

(* ================================================================= *)
(** ** Definitions *)

(** For [aexp]s and [bexp]s with variables, the definition we want is
    clear: Two [aexp]s or [bexp]s are _behaviorally equivalent_ if
    they evaluate to the same result in every state. *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.

(** Here are some simple examples of equivalences of arithmetic
    and boolean expressions. *)

Theorem aequiv_example: aequiv <{ X - X }> <{ 0 }>.
Proof.
  intros st. simpl. lia.
Qed.

Theorem bequiv_example: bequiv <{ X - X = 0 }> <{ true }>.
Proof.
  intros st. unfold beval.
  rewrite aequiv_example. reflexivity.
Qed.

(** For commands, the situation is a little more subtle.  We can't
    simply say "two commands are behaviorally equivalent if they
    evaluate to the same ending state whenever they are started in the
    same initial state," because some commands, when run in some
    starting states, don't terminate in any final state at all!  What
    we need instead is this: two commands are behaviorally equivalent
    if, for any given starting state, they either (1) both diverge
    or (2) both terminate in the same final state.  A compact way to
    express this is "if the first one terminates in a particular state
    then so does the second, and vice versa." *)

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

(* ================================================================= *)
(** ** Simple Examples *)

(** For examples of command equivalence, let's start by looking at
    some trivial program transformations involving [skip]: *)

Theorem skip_left : forall c,
  cequiv
    <{ skip; c }>
    c.
Proof.
  (* WORKED IN CLASS *)
  intros c st st'.
  split; intros H.
  - (* -> *)
    inversion H. subst. 
    inversion H2. subst.
    assumption.
  - (* <- *)
    apply E_Seq with st.
    apply E_Skip.
    assumption.
Qed.

(** **** Exercise: 2 stars, standard (skip_right)

    Prove that adding a [skip] after a command results in an
    equivalent program *)

Theorem skip_right : forall c,
  cequiv
    <{ c ; skip }>
    c.
Proof.
  intros.
  intros st st'.
  split.
  - intros H.
    inversion H. subst.
    inversion H5. subst.
    assumption.
  - intros H.
    apply E_Seq with st'.
    assumption.
    constructor.
Qed.
(** [] *)

(** Similarly, here is a simple transformation that optimizes [if]
    commands: *)

Theorem if_true_simple : forall c1 c2,
  cequiv
    <{ if true then c1 else c2 end }>
    c1.
Proof.
  intros c1 c2.
  split; intros H.
  - (* -> *)
    inversion H; subst. assumption. discriminate.
  - (* <- *)
    apply E_IfTrue. reflexivity. assumption.  Qed.

(** Of course, no (human) programmer would write a conditional whose
    guard is literally [true].  But they might write one whose guard
    is _equivalent_ to true:

    _Theorem_: If [b] is equivalent to [true], then [if b then c1
    else c2 end] is equivalent to [c1].
   _Proof_:

     - ([->]) We must show, for all [st] and [st'], that if [st =[
       if b then c1 else c2 end ]=> st'] then [st =[ c1 ]=> st'].

       Proceed by cases on the rules that could possibly have been
       used to show [st =[ if b then c1 else c2 end ]=> st'], namely
       [E_IfTrue] and [E_IfFalse].

       - Suppose the final rule in the derivation of [st =[ if b
         then c1 else c2 end ]=> st'] was [E_IfTrue].  We then have,
         by the premises of [E_IfTrue], that [st =[ c1 ]=> st'].
         This is exactly what we set out to prove.

       - On the other hand, suppose the final rule in the derivation
         of [st =[ if b then c1 else c2 end ]=> st'] was [E_IfFalse].
         We then know that [beval st b = false] and [st =[ c2 ]=> st'].

         Recall that [b] is equivalent to [true], i.e., forall [st],
         [beval st b = beval st <{true}> ].  In particular, this means
         that [beval st b = true], since [beval st <{true}> = true].  But
         this is a contradiction, since [E_IfFalse] requires that
         [beval st b = false].  Thus, the final rule could not have
         been [E_IfFalse].

     - ([<-]) We must show, for all [st] and [st'], that if
       [st =[ c1 ]=> st'] then
       [st =[ if b then c1 else c2 end ]=> st'].

       Since [b] is equivalent to [true], we know that [beval st b] =
       [beval st <{true}> ] = [true].  Together with the assumption that
       [st =[ c1 ]=> st'], we can apply [E_IfTrue] to derive
       [st =[ if b then c1 else c2 end ]=> st'].  []

   Here is the formal version of this proof: *)

Theorem if_true: forall b c1 c2,
  bequiv b <{true}>  ->
  cequiv
    <{ if b then c1 else c2 end }>
    c1.
Proof.
  intros b c1 c2 Hb.
  split; intros H.
  - (* -> *)
    inversion H. subst.
    + (* b evaluates to true *)
      assumption.
    + (* b evaluates to false (contradiction) *)
      unfold bequiv in Hb. simpl in Hb.
      rewrite Hb in H5.
      discriminate.
  - (* <- *)
    apply E_IfTrue; try assumption.
    unfold bequiv in Hb. simpl in Hb.
    apply Hb. Qed.

(** **** Exercise: 2 stars, standard, especially useful (if_false) *)
Theorem if_false : forall b c1 c2,
  bequiv b <{false}> ->
  cequiv
    <{ if b then c1 else c2 end }>
    c2.
Proof.
  intros.
  split.
  - (* -> *)
    intros. inversion H0. subst.
    unfold bequiv in H. simpl in H.
    + rewrite H in H6. discriminate.
    + subst. assumption.
  - (* <- *)
    intros. apply E_IfFalse.
    unfold bequiv in H. simpl in H.
    apply H. assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (swap_if_branches)

    Show that we can swap the branches of an [if] if we also negate its
    guard. *)

Theorem swap_if_branches : forall b c1 c2,
  cequiv
    <{ if b then c1 else c2 end }>
    <{ if ~ b then c2 else c1 end }>.
Proof.
  intros. split.
  - (* -> *)
    intros. inversion H. subst.
    + apply E_IfFalse with (b:= <{~b}>) (c1:=c2) in H6. assumption.
      simpl. rewrite H5. reflexivity.
    + subst. apply E_IfTrue with (b:= <{~b}>) (c2:=c1) in H6. assumption.
      simpl. rewrite H5. reflexivity.
  - intros.
    inversion H. subst.
    + apply E_IfFalse with (b:=b) (c1:=c1) in H6. assumption.
      simpl in H5. apply negb_true_iff in H5. assumption.
    + subst. apply E_IfTrue with (b:=b) (c2:=c2) in H6. assumption.
      simpl in H5. apply negb_false_iff in H5. assumption.
Qed.
(** [] *)

  (** For [while] loops, we can give a similar pair of theorems.  A loop
    whose guard is equivalent to [false] is equivalent to [skip],
    while a loop whose guard is equivalent to [true] is equivalent to
    [while true do skip end] (or any other non-terminating program).
    The first of these facts is easy. *)

Theorem while_false : forall b c,
  bequiv b <{false}> ->
  cequiv
    <{ while b do c end }>
    <{ skip }>.
Proof.
  intros b c Hb. split; intros H.
  - (* -> *)
    inversion H. subst.
    + (* E_WhileFalse *)
      apply E_Skip.
    + (* E_WhileTrue *)
      rewrite Hb in H2. discriminate.
  - (* <- *)
    inversion H. subst.
    apply E_WhileFalse.
    apply Hb.  Qed.

(** **** Exercise: 2 stars, advanced, optional (while_false_informal)

    Write an informal proof of [while_false].

(* FILL IN HERE *)
*)
(** [] *)

(** To prove the second fact, we need an auxiliary lemma stating that
    [while] loops whose guards are equivalent to [true] never
    terminate. *)

(** _Lemma_: If [b] is equivalent to [true], then it cannot be
    the case that [st =[ while b do c end ]=> st'].

    _Proof_: Suppose that [st =[ while b do c end ]=> st'].  We show,
    by induction on a derivation of [st =[ while b do c end ]=> st'],
    that this assumption leads to a contradiction. The only two cases
    to consider are [E_WhileFalse] and [E_WhileTrue], the others
    are contradictory.

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileFalse].  Then by assumption [beval st b = false].  But
      this contradicts the assumption that [b] is equivalent to
      [true].

    - Suppose [st =[ while b do c end ]=> st'] is proved using rule
      [E_WhileTrue].  We must have that:

      1. [beval st b = true],
      2. there is some [st0] such that [st =[ c ]=> st0] and
         [st0 =[ while b do c end ]=> st'],
      3. and we are given the induction hypothesis that
         [st0 =[ while b do c end ]=> st'] leads to a contradiction,

      We obtain a contradiction by 2 and 3. [] *)

Lemma while_true_nonterm : forall b c st st',
  bequiv b <{true}> ->
  ~( st =[ while b do c end ]=> st' ).
Proof.
  (* WORKED IN CLASS *)
  intros b c st st' Hb.
  intros H.
  remember <{ while b do c end }> as cw eqn:Heqcw.
  induction H;
  (* Most rules don't apply; we rule them out by inversion: *)
  inversion Heqcw; subst; clear Heqcw.
  (* The two interesting cases are the ones for while loops: *)
  - (* E_WhileFalse *) (* contradictory -- b is always true! *)
    unfold bequiv in Hb.
    (* [rewrite] is able to instantiate the quantifier in [st] *)
    rewrite Hb in H. discriminate.
  - (* E_WhileTrue *) (* immediate from the IH *)
    apply IHceval2. reflexivity.  Qed.

(** **** Exercise: 2 stars, standard, optional (while_true_nonterm_informal)

    Explain what the lemma [while_true_nonterm] means in English.

(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, especially useful (while_true)

    Prove the following theorem. _Hint_: You'll want to use
    [while_true_nonterm] here. *)

Theorem while_true : forall b c,
  bequiv b <{true}>  ->
  cequiv
    <{ while b do c end }>
    <{ while true do skip end }>.
Proof.
  intros. split; intros.
  - assert (H':=H).
    apply while_true_nonterm with b <{c}> st st' in H.
    unfold bequiv in H'. unfold not in H. apply H in H0. destruct H0.
  - inversion H0. subst.
    + unfold beval in H5. discriminate.
    + assert (H':=H). subst. exfalso.
      apply while_true_nonterm with <{true}> <{skip}> st st'.
      unfold bequiv. reflexivity. assumption.
Qed.
(** [] *)

(** A more interesting fact about [while] commands is that any number
    of copies of the body can be "unrolled" without changing meaning.

    Loop unrolling is an important transformation in real compilers! *)

Theorem loop_unrolling : forall b c,
  cequiv
    <{ while b do c end }>
    <{ if b then c ; while b do c end else skip end }>.
Proof.
  (* WORKED IN CLASS *)
  intros b c st st'.
  split; intros Hce.
  - (* -> *)
    inversion Hce; subst.
    + (* loop doesn't run *)
      apply E_IfFalse. assumption. apply E_Skip.
    + (* loop runs *)
      apply E_IfTrue. assumption.
      apply E_Seq with (st' := st'0). assumption. assumption.
  - (* <- *)
    inversion Hce; subst.
    + (* loop runs *)
      inversion H5; subst.
      apply E_WhileTrue with (st' := st'0).
      assumption. assumption. assumption.
    + (* loop doesn'ct run *)
      inversion H5. subst. apply E_WhileFalse. assumption.  Qed.

(** **** Exercise: 2 stars, standard, optional (seq_assoc) *)
Theorem seq_assoc : forall c1 c2 c3,
  cequiv <{(c1;c2);c3}> <{c1;(c2;c3)}>.
Proof.
  intros. split; intros.
  - inversion H. inversion H2. subst.
    apply E_Seq with st'1. assumption.
    apply E_Seq with st'0. assumption. assumption.
  - inversion H. inversion H5. subst.
    apply E_Seq with st'1. apply E_Seq with st'0.
    assumption. assumption. assumption.
Qed.
(** [] *)

(** Proving program properties involving assignments is one place
    where the fact that program states are treated
    extensionally (e.g., [x !-> m x ; m] and [m] are equal maps) comes
    in handy. *)

Theorem identity_assignment : forall x,
  cequiv
    <{ x := x }>
    <{ skip }>.
Proof.
  intros.
  split; intro H; inversion H; subst; clear H.
  - (* -> *)
    rewrite t_update_same.
    apply E_Skip.
  - (* <- *)
    assert (Hx : st' =[ x := x ]=> (x !-> st' x ; st')).
    { apply E_Asgn. reflexivity. }
    rewrite t_update_same in Hx.
    apply Hx.
Qed.

(** **** Exercise: 2 stars, standard, especially useful (assign_aequiv) *)
Theorem assign_aequiv : forall (x : string) a,
  aequiv x a ->
  cequiv <{ skip }> <{ x := a }>.
Proof.
  intros. split; intros.
  - (* -> *)
    unfold aequiv in H. inversion H0. subst.
    assert (Hx : st' =[ x := a ]=> (x !-> st' x ; st')).
    {apply E_Asgn. rewrite <- H with st'. reflexivity. }
    rewrite t_update_same in Hx. assumption.
  - (* <_ *)
    inversion H0. subst. unfold aequiv in H. rewrite <- H in *. simpl in *.
    rewrite t_update_same in *. constructor.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (equiv_classes) *)

(** Given the following programs, group together those that are
    equivalent in Imp. Your answer should be given as a list of lists,
    where each sub-list represents a group of equivalent programs. For
    example, if you think programs (a) through (h) are all equivalent
    to each other, but not to (i), your answer should look like this:

       [ [prog_a;prog_b;prog_c;prog_d;prog_e;prog_f;prog_g;prog_h] ;
         [prog_i] ]

    Write down your answer below in the definition of
    [equiv_classes]. *)

Definition prog_a : com :=
  <{ while ~(X <= 0) do
       X := X + 1
     end }>.

Definition prog_b : com :=
  <{ if (X = 0) then
       X := X + 1;
       Y := 1
     else
       Y := 0
     end;
     X := X - Y;
     Y := 0 }>.

Definition prog_c : com :=
  <{ skip }> .

Definition prog_d : com :=
  <{ while ~(X = 0) do
       X := (X * Y) + 1
     end }>.

Definition prog_e : com :=
  <{ Y := 0 }>.

Definition prog_f : com :=
  <{ Y := X + 1;
     while ~(X = Y) do
       Y := X + 1
     end }>.

Definition prog_g : com :=
  <{ while true do
       skip
     end }>.

Definition prog_h : com :=
  <{ while ~(X = X) do
       X := X + 1
     end }>.

Definition prog_i : com :=
  <{ while ~(X = Y) do
       X := Y + 1
     end }>.

Definition equiv_classes : list (list com).
   Admitted.

(* Do not modify the following line: *)
Definition manual_grade_for_equiv_classes : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Properties of Behavioral Equivalence *)

(** We next consider some fundamental properties of program
    equivalence. *)

(* ================================================================= *)
(** ** Behavioral Equivalence Is an Equivalence *)

(** First, we verify that the equivalences on [aexps], [bexps], and
    [com]s really are _equivalences_ -- i.e., that they are reflexive,
    symmetric, and transitive.  The proofs are all easy. *)

Lemma refl_aequiv : forall (a : aexp), aequiv a a.
Proof.
  intros a st. reflexivity. Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp),
  aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros a1 a2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
Proof.
  unfold aequiv. intros a1 a2 a3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_bequiv : forall (b : bexp), bequiv b b.
Proof.
  unfold bequiv. intros b st. reflexivity.  Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp),
  bequiv b1 b2 -> bequiv b2 b1.
Proof.
  unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
Proof.
  unfold bequiv. intros b1 b2 b3 H12 H23 st.
  rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof.
  unfold cequiv. intros c st st'. reflexivity.  Qed.

Lemma sym_cequiv : forall (c1 c2 : com),
  cequiv c1 c2 -> cequiv c2 c1.
Proof.
  unfold cequiv. intros c1 c2 H st st'.
  rewrite H. reflexivity.
Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
  rewrite H12. apply H23.
Qed.

(* ================================================================= *)
(** ** Behavioral Equivalence Is a Congruence *)

(** Less obviously, behavioral equivalence is also a _congruence_.
    That is, the equivalence of two subprograms implies the
    equivalence of the larger programs in which they are embedded:

                 aequiv a a'
         -------------------------
         cequiv (x := a) (x := a')

              cequiv c1 c1'
              cequiv c2 c2'
         --------------------------
         cequiv (c1;c2) (c1';c2')

    ... and so on for the other forms of commands. *)

(** (Note that we are using the inference rule notation here not
    as part of a definition, but simply to write down some valid
    implications in a readable format. We prove these implications
    below.) *)

(** We will see a concrete example of why these congruence
    properties are important in the following section (in the proof of
    [fold_constants_com_sound]), but the main idea is that they allow
    us to replace a small part of a large program with an equivalent
    small part and know that the whole large programs are equivalent
    _without_ doing an explicit proof about the non-varying parts --
    i.e., the "proof burden" of a small change to a large program is
    proportional to the size of the change, not the program. *)

Theorem CAsgn_congruence : forall x a a',
  aequiv a a' ->
  cequiv <{x := a}> <{x := a'}>.
Proof.
  intros x a a' Heqv st st'.
  split; intros Hceval.
  - (* -> *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.
  - (* <- *)
    inversion Hceval. subst. apply E_Asgn.
    rewrite Heqv. reflexivity.  Qed.

(** The congruence property for loops is a little more interesting,
    since it requires induction.

    _Theorem_: Equivalence is a congruence for [while] -- that is, if
    [b] is equivalent to [b'] and [c] is equivalent to [c'], then
    [while b do c end] is equivalent to [while b' do c' end].

    _Proof_: Suppose [b] is equivalent to [b'] and [c] is
    equivalent to [c'].  We must show, for every [st] and [st'], that
    [st =[ while b do c end ]=> st'] iff [st =[ while b' do c'
    end ]=> st'].  We consider the two directions separately.

      - ([->]) We show that [st =[ while b do c end ]=> st'] implies
        [st =[ while b' do c' end ]=> st'], by induction on a
        derivation of [st =[ while b do c end ]=> st'].  The only
        nontrivial cases are when the final rule in the derivation is
        [E_WhileFalse] or [E_WhileTrue].

          - [E_WhileFalse]: In this case, the form of the rule gives us
            [beval st b = false] and [st = st'].  But then, since
            [b] and [b'] are equivalent, we have [beval st b' =
            false], and [E_WhileFalse] applies, giving us
            [st =[ while b' do c' end ]=> st'], as required.

          - [E_WhileTrue]: The form of the rule now gives us [beval st
            b = true], with [st =[ c ]=> st'0] and [st'0 =[ while
            b do c end ]=> st'] for some state [st'0], with the
            induction hypothesis [st'0 =[ while b' do c' end ]=>
            st'].

            Since [c] and [c'] are equivalent, we know that [st =[
            c' ]=> st'0].  And since [b] and [b'] are equivalent,
            we have [beval st b' = true].  Now [E_WhileTrue] applies,
            giving us [st =[ while b' do c' end ]=> st'], as
            required.

      - ([<-]) Similar. [] *)

Theorem CWhile_congruence : forall b b' c c',
  bequiv b b' -> cequiv c c' ->
  cequiv <{ while b do c end }> <{ while b' do c' end }>.
Proof.
  (* WORKED IN CLASS *)

  (* We will prove one direction in an "assert"
     in order to reuse it for the converse. *)
  assert (A: forall (b b' : bexp) (c c' : com) (st st' : state),
             bequiv b b' -> cequiv c c' ->
             st =[ while b do c end ]=> st' ->
             st =[ while b' do c' end ]=> st').
  { unfold bequiv,cequiv.
    intros b b' c c' st st' Hbe Hc1e Hce.
    remember <{ while b do c end }> as cwhile
      eqn:Heqcwhile.
    induction Hce; inversion Heqcwhile; subst.
    + (* E_WhileFalse *)
      apply E_WhileFalse. rewrite <- Hbe. apply H.
    + (* E_WhileTrue *)
      apply E_WhileTrue with (st' := st').
      * (* show loop runs *) rewrite <- Hbe. apply H.
      * (* body execution *)
        apply (Hc1e st st').  apply Hce1.
      * (* subsequent loop execution *)
        apply IHHce2. reflexivity. }

  intros. split.
  - apply A; assumption.
  - apply A.
    + apply sym_bequiv. assumption.
    + apply sym_cequiv. assumption.
Qed.

(** **** Exercise: 3 stars, standard, optional (CSeq_congruence) *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ c1;c2 }> <{ c1';c2' }>.
Proof.
  assert (A : forall (c1 c2 c1' c2': com) (st st': state),
             cequiv c1 c1' -> cequiv c2 c2' ->
             st =[ c1; c2 ]=> st' ->
             st =[ c1'; c2' ]=> st').
  { unfold cequiv. intros.
    inversion H1. subst.
    apply E_Seq with st'0. apply H. assumption.
    apply H0. assumption. }
  intros. split; intros.
  - apply A with c1 c2; repeat assumption.
  - apply A with c1' c2'; repeat (apply sym_cequiv; assumption).
    assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (CIf_congruence) *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv <{ if b then c1 else c2 end }>
         <{ if b' then c1' else c2' end }>.
Proof.
  assert (A: forall (b b' : bexp) (c1 c1' c2 c2' : com) (st st' : state),
             bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
             st =[ if b then c1 else c2 end ]=> st' ->
                                               st =[ if b' then c1' else c2' end ]=> st').
  { unfold bequiv, cequiv. intros.
    remember <{ if b then c1 else c2 end }> as cif.
    induction H2; inversion Heqcif; subst.
    - (* if true *)
      apply E_IfTrue. rewrite <- H. assumption.
      apply H0. assumption.
    - (* if false *)
      apply E_IfFalse. rewrite <- H. assumption.
      apply H1. assumption.
  }

  intros. split; intros.
  - apply A with b c1 c2; repeat assumption.
  - apply A with b' c1' c2'.
    apply sym_bequiv. assumption.
    apply sym_cequiv. assumption.
    apply sym_cequiv. assumption.
    assumption.
Qed.
(** [] *)

(** For example, here are two equivalent programs and a proof of their
    equivalence... *)

Example congruence_example:
  cequiv
    (* Program 1: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := 0
       else
         Y := 42
       end }>
    (* Program 2: *)
    <{ X := 0;
       if (X = 0)
       then
         Y := X - X   (* <--- Changed here *)
       else
         Y := 42
       end }>.
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    + apply refl_bequiv.
    + apply CAsgn_congruence. unfold aequiv. simpl.
      symmetry. apply minus_diag.
    + apply refl_cequiv.
Qed.

(** **** Exercise: 3 stars, advanced, optional (not_congr)

    We've shown that the [cequiv] relation is both an equivalence and
    a congruence on commands.  Can you think of a relation on commands
    that is an equivalence but _not_ a congruence? *)

(* FILL IN HERE
    skip
    x := x
    [] *)

(* ################################################################# *)
(** * Program Transformations *)

(** A _program transformation_ is a function that takes a program as
    input and produces some variant of the program as output.
    Compiler optimizations such as constant folding are a canonical
    example, but there are many others. *)

(** A program transformation is _sound_ if it preserves the
    behavior of the original program. *)

Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
  forall (a : aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
  forall (b : bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans : com -> com) : Prop :=
  forall (c : com),
    cequiv c (ctrans c).

(* ================================================================= *)
(** ** The Constant-Folding Transformation *)

(** An expression is _constant_ when it contains no variable
    references.

    Constant folding is an optimization that finds constant
    expressions and replaces them by their values. *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't eliminate
    trivial additions, etc. -- we are focusing attention on a single
    optimization for the sake of simplicity.  It is not hard to
    incorporate other ways of simplifying expressions; the definitions
    and proofs just get longer. *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq] and [BLe] cases); we can also look for constant _boolean_
    expressions and evaluate them in-place. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end
  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Soundness of Constant Folding *)

(** Now we need to show that what we've done is correct. *)

(** Here's the proof for arithmetic expressions: *)

Theorem fold_constants_aexp_sound :
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros st.
  induction a; simpl;
    (* ANum and AId follow immediately *)
    try reflexivity;
    (* APlus, AMinus, and AMult follow from the IH
       and the observation that
              aeval st (<{ a1 + a2 }>)
            = ANum ((aeval st a1) + (aeval st a2))
            = aeval st (ANum ((aeval st a1) + (aeval st a2)))
       (and similarly for AMinus/minus and AMult/mult) *)
    try (destruct (fold_constants_aexp a1);
         destruct (fold_constants_aexp a2);
         rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(** **** Exercise: 3 stars, standard, optional (fold_bexp_Eq_informal)

    Here is an informal proof of the [BEq] case of the soundness
    argument for boolean expression constant folding.  Read it
    carefully and compare it to the formal proof that follows.  Then
    fill in the [BLe] case of the formal proof (without looking at the
    [BEq] case, if possible).

   _Theorem_: The constant folding function for booleans,
   [fold_constants_bexp], is sound.

   _Proof_: We must show that [b] is equivalent to [fold_constants_bexp b],
   for all boolean expressions [b].  Proceed by induction on [b].  We
   show just the case where [b] has the form [a1 = a2].

   In this case, we must show

       beval st <{ a1 = a2 }>
     = beval st (fold_constants_bexp <{ a1 = a2 }>).

   There are two cases to consider:

     - First, suppose [fold_constants_aexp a1 = ANum n1] and
       [fold_constants_aexp a2 = ANum n2] for some [n1] and [n2].

       In this case, we have

           fold_constants_bexp <{ a1 = a2 }>
         = if n1 =? n2 then <{true}> else <{false}>

       and

           beval st <{a1 = a2}>
         = (aeval st a1) =? (aeval st a2).

       By the soundness of constant folding for arithmetic
       expressions (Lemma [fold_constants_aexp_sound]), we know

           aeval st a1
         = aeval st (fold_constants_aexp a1)
         = aeval st (ANum n1)
         = n1

       and

           aeval st a2
         = aeval st (fold_constants_aexp a2)
         = aeval st (ANum n2)
         = n2,

       so

           beval st <{a1 = a2}>
         = (aeval a1) =? (aeval a2)
         = n1 =? n2.

       Also, it is easy to see (by considering the cases [n1 = n2] and
       [n1 <> n2] separately) that

           beval st (if n1 =? n2 then <{true}> else <{false}>)
         = if n1 =? n2 then beval st <{true}> else beval st <{false}>
         = if n1 =? n2 then true else false
         = n1 =? n2.

       So

           beval st (<{ a1 = a2 }>)
         = n1 =? n2.
         = beval st (if n1 =? n2 then <{true}> else <{false}>),

       as required.

     - Otherwise, one of [fold_constants_aexp a1] and
       [fold_constants_aexp a2] is not a constant.  In this case, we
       must show

           beval st <{a1 = a2}>
         = beval st (<{ (fold_constants_aexp a1) =
                         (fold_constants_aexp a2) }>),

       which, by the definition of [beval], is the same as showing

           (aeval st a1) =? (aeval st a2)
         = (aeval st (fold_constants_aexp a1)) =?
                   (aeval st (fold_constants_aexp a2)).

       But the soundness of constant folding for arithmetic
       expressions ([fold_constants_aexp_sound]) gives us

         aeval st a1 = aeval st (fold_constants_aexp a1)
         aeval st a2 = aeval st (fold_constants_aexp a2),

       completing the case.  [] *)

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros b. unfold bequiv. intros st.
  induction b;
    (* true and false are immediate *)
    try reflexivity.
  - (* BEq *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn:Heqa1'.
    remember (fold_constants_aexp a2) as a2' eqn:Heqa2'.
    replace (aeval st a1) with (aeval st a1') by
       (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
       (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    (* The only interesting case is when both a1 and a2
       become constants after folding *)
      simpl. destruct (n =? n0); reflexivity.
  - (* BLe *)
    simpl.
    remember (fold_constants_aexp a1) as a1' eqn: Ha1.
    remember (fold_constants_aexp a2) as a2' eqn: Ha2.
    replace (aeval st a1) with (aeval st a1') by
      (subst a1'; rewrite <- fold_constants_aexp_sound; reflexivity).
    replace (aeval st a2) with (aeval st a2') by
      (subst a2'; rewrite <- fold_constants_aexp_sound; reflexivity).
    destruct a1'; destruct a2'; try reflexivity.
    simpl. destruct (n <=? n0); reflexivity.
  - (* BNot *)
    simpl. remember (fold_constants_bexp b) as b' eqn:Heqb'.
    rewrite IHb.
    destruct b'; reflexivity.
  - (* BAnd *)
    simpl.
    remember (fold_constants_bexp b1) as b1' eqn:Heqb1'.
    remember (fold_constants_bexp b2) as b2' eqn:Heqb2'.
    rewrite IHb1. rewrite IHb2.
    destruct b1'; destruct b2'; reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (fold_constants_com_sound)

    Complete the [while] case of the following proof. *)

Theorem fold_constants_com_sound :
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - (* skip *) apply refl_cequiv.
  - (* := *) apply CAsgn_congruence.
              apply fold_constants_aexp_sound.
  - (* ; *) apply CSeq_congruence; assumption.
  - (* if *)
    assert (bequiv b (fold_constants_bexp b)). {
      apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn:Heqb;
      try (apply CIf_congruence; assumption).
      (* (If the optimization doesn't eliminate the if, then the
          result is easy to prove from the IH and
          [fold_constants_bexp_sound].) *)
    + (* b always true *)
      apply trans_cequiv with c1; try assumption.
      apply if_true. assumption.
    + (* b always false *)
      apply trans_cequiv with c2; try assumption.
      apply if_false. assumption.
  - (* while *)
    assert (bequiv b (fold_constants_bexp b)).
    {apply fold_constants_bexp_sound. }
    destruct (fold_constants_bexp b) eqn: Heqb;
      try (apply CWhile_congruence; assumption).
    + apply while_true. assumption.
    + apply while_false. assumption.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Soundness of (0 + n) Elimination, Redux *)

(** **** Exercise: 4 stars, advanced, optional (optimize_0plus)

    Recall the definition [optimize_0plus] from the [Imp] chapter
    of _Logical Foundations_:

    Fixpoint optimize_0plus (a:aexp) : aexp :=
      match a with
      | ANum n =>
          ANum n
      | <{ 0 + a2 }> =>
          optimize_0plus a2
      | <{ a1 + a2 }> =>
          <{ (optimize_0plus a1) + (optimize_0plus a2) }>
      | <{ a1 - a2 }> =>
          <{ (optimize_0plus a1) - (optimize_0plus a2) }>
      | <{ a1 * a2 }> =>
          <{ (optimize_0plus a1) * (optimize_0plus a2) }>
      end.

   Note that this function is defined over the old [aexp]s,
   without states.

   Write a new version of this function that accounts for variables,
   plus analogous ones for [bexp]s and commands:

     optimize_0plus_aexp
     optimize_0plus_bexp
     optimize_0plus_com

   Prove that these three functions are sound, as we did for
   [fold_constants_*].  Make sure you use the congruence lemmas in
   the proof of [optimize_0plus_com] -- otherwise it will be _long_!

   Then define an optimizer on commands that first folds
   constants (using [fold_constants_com]) and then eliminates [0 + n]
   terms (using [optimize_0plus_com]).

   - Give a meaningful example of this optimizer's output.

   - Prove that the optimizer is sound.  (This part should be _very_
     easy.)  *)

Fixpoint optimize_0plus_aexp (a: aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | <{0 + a2}> => optimize_0plus_aexp a2
  | <{a1 + a2}> => <{optimize_0plus_aexp a1 + optimize_0plus_aexp a2 }>
  | <{a1 - a2}> => <{optimize_0plus_aexp a1 - optimize_0plus_aexp a2 }>
  | <{a1 * a2}> => <{optimize_0plus_aexp a1 * optimize_0plus_aexp a2 }>
  end.

Fixpoint optimize_0plus_bexp (b: bexp) : bexp :=
  match b with
  | <{true}> => <{true}>
  | <{false}> => <{false}>
  | <{a1 = a2}> => <{ optimize_0plus_aexp a1 = optimize_0plus_aexp a2 }>
  | <{a1 <= a2}> => <{ optimize_0plus_aexp a1 <= optimize_0plus_aexp a2 }>
  | <{ ~b1 }> => <{~ optimize_0plus_bexp b1}>
  | <{b1 && b2}> => <{ optimize_0plus_bexp b1 && optimize_0plus_bexp b2 }>
  end.

Fixpoint optimize_0plus_com (c: com) : com :=
  match c with
  | <{ skip }> => <{ skip }>
  | <{ x := a }> => <{ x := optimize_0plus_aexp a }>
  | <{ c1; c2 }> => <{ optimize_0plus_com c1;  optimize_0plus_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      <{ if optimize_0plus_bexp b then optimize_0plus_com c1 else optimize_0plus_com c2 end }>
  | <{ while b do c1 end}> => <{ while optimize_0plus_bexp b do optimize_0plus_com c1 end }>
  end.

Theorem optimize_0plus_aexp_sound : atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. unfold aequiv. intros a st.
  induction a; simpl; subst; try reflexivity;
  try (rewrite IHa1; rewrite IHa2; reflexivity).
  - destruct a1; simpl in *; try rewrite IHa1; rewrite IHa2; try reflexivity.
    destruct n eqn: Hn. reflexivity.
    simpl. reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound : btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. unfold bequiv. intros b st.
  induction b; simpl; try reflexivity;
  try (rewrite <- optimize_0plus_aexp_sound; rewrite <- optimize_0plus_aexp_sound; reflexivity).
  - rewrite <- IHb. reflexivity.
  - rewrite <- IHb1. rewrite <- IHb2. reflexivity.
Qed.

Theorem optimize_0plus_com_sound : ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros c.
  induction c; simpl.
  - apply refl_cequiv.
  - apply CAsgn_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence. auto. auto.
  - apply CIf_congruence. apply optimize_0plus_bexp_sound. auto. auto.
  - apply CWhile_congruence. apply optimize_0plus_bexp_sound. auto.
Qed.

(* ################################################################# *)
(** * Proving Inequivalence *)

(** Suppose that [c1] is a command of the form [X := a1; Y := a2]
    and [c2] is the command [X := a1; Y := a2'], where [a2'] is
    formed by substituting [a1] for all occurrences of [X] in [a2].
    For example, [c1] and [c2] might be:

       c1  =  (X := 42 + 53;
               Y := Y + X)
       c2  =  (X := 42 + 53;
               Y := Y + (42 + 53))

    Clearly, this _particular_ [c1] and [c2] are equivalent.  Is this
    true in general? *)

(** We will see in a moment that it is not, but it is worthwhile
    to pause, now, and see if you can find a counter-example on your
    own. *)

(** More formally, here is the function that substitutes an arithmetic
    expression [u] for each occurrence of a given variable [x] in
    another expression [a]: *)

Fixpoint subst_aexp (x : string) (u : aexp) (a : aexp) : aexp :=
  match a with
  | ANum n       =>
      ANum n
  | AId x'       =>
      if eqb_string x x' then u else AId x'
  | <{ a1 + a2 }>  =>
      <{ (subst_aexp x u a1) + (subst_aexp x u a2) }>
  | <{ a1 - a2 }> =>
      <{ (subst_aexp x u a1) - (subst_aexp x u a2) }>
  | <{ a1 * a2 }>  =>
      <{ (subst_aexp x u a1) * (subst_aexp x u a2) }>
  end.

Example subst_aexp_ex :
  subst_aexp X <{42 + 53}> <{Y + X}>
  = <{ Y + (42 + 53)}>.
Proof. simpl. reflexivity. Qed.

(** And here is the property we are interested in, expressing the
    claim that commands [c1] and [c2] as described above are
    always equivalent.  *)

Definition subst_equiv_property := forall x1 x2 a1 a2,
  cequiv <{ x1 := a1; x2 := a2 }>
         <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.

(** Sadly, the property does _not_ always hold.

    We can show the following counterexample:

       X := X + 1; Y := X

    If we perform the substitution, we get

       X := X + 1; Y := X + 1

    which clearly isn't equivalent to the original program. [] *)

Theorem subst_inequiv :
  ~ subst_equiv_property.
Proof.
  unfold subst_equiv_property.
  intros Contra.

  (* Here is the counterexample: assuming that [subst_equiv_property]
     holds allows us to prove that these two programs are
     equivalent... *)
  remember <{ X := X + 1;
              Y := X }>
      as c1.
  remember <{ X := X + 1;
              Y := X + 1 }>
      as c2.
  assert (cequiv c1 c2) by (subst; apply Contra).
  clear Contra.

  (* ... allows us to show that the command [c2] can terminate
     in two different final states:
        st1 = (Y !-> 1 ; X !-> 1)
        st2 = (Y !-> 2 ; X !-> 1). *)
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
  assert (H2 : empty_st =[ c2 ]=> st2);
  try (subst;
       apply E_Seq with (st' := (X !-> 1));
       apply E_Asgn; reflexivity).
  clear Heqc1 Heqc2.

  apply H in H1.
  clear H.

  (* Finally, we use the fact that evaluation is deterministic
     to obtain a contradiction. *)
  assert (Hcontra : st1 = st2)
    by (apply (ceval_deterministic c2 empty_st); assumption).
  clear H1 H2.

  assert (Hcontra' : st1 Y = st2 Y)
    by (rewrite Hcontra; reflexivity).
  subst. discriminate. Qed.

(** **** Exercise: 4 stars, standard, optional (better_subst_equiv)

    The equivalence we had in mind above was not complete nonsense --
    it was actually almost right.  To make it correct, we just need to
    exclude the case where the variable [X] occurs in the
    right-hand-side of the first assignment statement. *)

Inductive var_not_used_in_aexp (x : string) : aexp -> Prop :=
  | VNUNum : forall n, var_not_used_in_aexp x (ANum n)
  | VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
  | VNUPlus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 + a2 }>)
  | VNUMinus : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 - a2 }>)
  | VNUMult : forall a1 a2,
      var_not_used_in_aexp x a1 ->
      var_not_used_in_aexp x a2 ->
      var_not_used_in_aexp x (<{ a1 * a2 }>).

Lemma aeval_weakening : forall x st a ni,
  var_not_used_in_aexp x a ->
  aeval (x !-> ni ; st) a = aeval st a.
Proof.
  intros. induction H; subst; simpl; try reflexivity;
    try (rewrite IHvar_not_used_in_aexp1; rewrite IHvar_not_used_in_aexp2; reflexivity).
  - unfold t_update. apply false_eqb_string in H. rewrite H. reflexivity.
Qed.

(** Using [var_not_used_in_aexp], formalize and prove a correct version
    of [subst_equiv_property]. *)

Lemma not_used_subst_eq : forall st a1 x1 a2,
    var_not_used_in_aexp x1 a1 ->
    aeval (x1 !-> aeval st a1; st) (subst_aexp x1 a1 a2) = aeval (x1 !-> aeval st a1; st) a2.
Proof.
  intros.
  induction a2; simpl;
    try (rewrite IHa2_1; rewrite IHa2_2; reflexivity).
  - reflexivity.
  - destruct (eqb_string x1 x) eqn: eqxx1.
    + apply eqb_string_true_iff in eqxx1. subst.
      replace ((x !-> aeval st a1; st) x) with (aeval st a1).
      apply aeval_weakening. assumption.
      unfold t_update. rewrite <- eqb_string_refl. reflexivity.
    + simpl. reflexivity.
Qed.

Theorem subst_equiv_property' :
  forall x1 x2 a1 a2,
    var_not_used_in_aexp x1 a1 ->
    cequiv <{ x1 := a1; x2 := a2 }>
    <{ x1 := a1; x2 := subst_aexp x1 a1 a2 }>.
Proof.
  intros.  simpl; unfold cequiv.
  intros. split; intros.
  - intros. inversion H0.
    inversion H3. inversion H6. subst.
    apply E_Seq with (x1 !-> aeval st a1; st).
    + constructor. reflexivity.
    + constructor. assert (H':= H).
      apply aeval_weakening with (ni:= aeval st a1) (st:= x1 !-> aeval st a1; st) in H.
      apply not_used_subst_eq. assumption.
  - intros. inversion H0.
    inversion H3. inversion H6. subst.
    apply E_Seq with (x1 !-> aeval st a1; st).
    + constructor. reflexivity.
    + constructor. apply not_used_subst_eq with (st:= st) (a2:= a2) in H.
      symmetry. assumption.
Qed.

(** **** Exercise: 3 stars, standard (inequiv_exercise)

    Prove that an infinite loop is not equivalent to [skip] *)

Theorem inequiv_exercise:
  ~ cequiv <{ while true do skip end }> <{ skip }>.
Proof.
  intro Contra.
  unfold cequiv in *.
  remember (<{while true do skip end}>) as c1.
  remember (<{skip}>) as c2.
  assert (Hc2: empty_st =[ c2 ]=> empty_st). rewrite Heqc2. constructor.
  apply Contra in Hc2. rewrite Heqc1 in Hc2.
  apply while_true_nonterm in Hc2. assumption.
  apply refl_bequiv.
Qed.
(** [] *)

(* ################################################################# *)
(** * Extended Exercise: Nondeterministic Imp *)

(** As we have seen (in theorem [ceval_deterministic] in the [Imp]
    chapter), Imp's evaluation relation is deterministic.  However,
    _non_-determinism is an important part of the definition of many
    real programming languages. For example, in many imperative
    languages (such as C and its relatives), the order in which
    function arguments are evaluated is unspecified.  The program
    fragment

      x = 0;
      f(++x, x)

    might call [f] with arguments [(1, 0)] or [(1, 1)], depending how
    the compiler chooses to order things.  This can be a little
    confusing for programmers, but it gives the compiler writer useful
    freedom.

    In this exercise, we will extend Imp with a simple
    nondeterministic command and study how this change affects
    program equivalence.  The new command has the syntax [HAVOC X],
    where [X] is an identifier. The effect of executing [HAVOC X] is
    to assign an _arbitrary_ number to the variable [X],
    nondeterministically. For example, after executing the program:

      HAVOC Y;
      Z := Y * 2

    the value of [Y] can be any number, while the value of [Z] is
    twice that of [Y] (so [Z] is always even). Note that we are not
    saying anything about the _probabilities_ of the outcomes -- just
    that there are (infinitely) many different outcomes that can
    possibly happen after executing this nondeterministic code.

    In a sense, a variable on which we do [HAVOC] roughly corresponds
    to an uninitialized variable in a low-level language like C.  After
    the [HAVOC], the variable holds a fixed but arbitrary number.  Most
    sources of nondeterminism in language definitions are there
    precisely because programmers don't care which choice is made (and
    so it is good to leave it open to the compiler to choose whichever
    will run faster).

    We call this new language _Himp_ (``Imp extended with [HAVOC]''). *)

Module Himp.

(** To formalize Himp, we first add a clause to the definition of
    commands. *)

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.                (* <--- NEW *)

Notation "'havoc' l" := (CHavoc l)
                          (in custom com at level 60, l constr at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

(** **** Exercise: 2 stars, standard (himp_ceval)

    Now, we must extend the operational semantics. We have provided
   a template for the [ceval] relation below, specifying the big-step
   semantics. What rule(s) must be added to the definition of [ceval]
   to formalize the behavior of the [HAVOC] command? *)

Reserved Notation "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99, st constr,
          st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''
  | E_Havoc: forall st x (n: nat),
      st =[ havoc x ]=> (x !-> n; st)

  where "st =[ c ]=> st'" := (ceval c st st').

(** As a sanity check, the following claims should be provable for
    your definition: *)

Example havoc_example1 : empty_st =[ havoc X ]=> (X !-> 0).
Proof.
  constructor.
Qed.

Example havoc_example2 :
  empty_st =[ skip; havoc Z ]=> (Z !-> 42).
Proof.
  apply E_Seq with empty_st. constructor. constructor.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_Check_rule_for_HAVOC : option (nat*string) := None.
(** [] *)

(** Finally, we repeat the definition of command equivalence from above: *)

Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
  st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

(** Let's apply this definition to prove some nondeterministic
    programs equivalent / inequivalent. *)

(** **** Exercise: 3 stars, standard (havoc_swap)

    Are the following two programs equivalent? *)

Definition pXY :=
  <{ havoc X ; havoc Y }>.

Definition pYX :=
  <{ havoc Y; havoc X }>.

(** If you think they are equivalent, prove it. If you think they are
    not, prove that. *)

Theorem pXY_cequiv_pYX :
  cequiv pXY pYX \/ ~cequiv pXY pYX.
Proof.
  unfold cequiv. intros. unfold pXY. unfold pYX. left. split.
  - intros. inversion H. inversion H2. inversion H5. subst.
    apply E_Seq with (Y !-> n0; st). constructor.
    assert (Ha: (Y !-> n0; X !-> n; st) = (X !-> n; Y !-> n0; st)).
    { apply functional_extensionality. intros. unfold t_update.
      destruct (eqb_string Y x) eqn: eqYx;
        destruct (eqb_string X x) eqn: eqXx;
        try reflexivity.
      rewrite eqb_string_true_iff in *. subst. discriminate eqXx. }
    rewrite Ha. constructor.
  - intros. inversion H. inversion H2. inversion H5. subst.
    apply E_Seq with (X !-> n0; st). constructor.
        assert (Ha: (Y !-> n; X !-> n0; st) = (X !-> n0; Y !-> n; st)).
    { apply functional_extensionality. intros. unfold t_update.
      destruct (eqb_string Y x) eqn: eqYx;
        destruct (eqb_string X x) eqn: eqXx;
        try reflexivity.
      rewrite eqb_string_true_iff in *. subst. discriminate. }
    rewrite <- Ha. constructor.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard, optional (havoc_copy)

    Are the following two programs equivalent? *)

Definition ptwice :=
  <{ havoc X; havoc Y }>.

Definition pcopy :=
  <{ havoc X; Y := X }>.

(** If you think they are equivalent, then prove it. If you think they
    are not, then prove that.  (Hint: You may find the [assert] tactic
    useful.) *)

Theorem ptwice_cequiv_pcopy :
  cequiv ptwice pcopy \/ ~cequiv ptwice pcopy.
Proof.
  right. unfold cequiv. unfold ptwice. unfold pcopy.
  intros contra.
  assert (H1: empty_st =[ ptwice ]=> (Y !-> 1; X !-> 2)).
  { unfold  ptwice. apply E_Seq with (X !-> 2). constructor. constructor. }
  assert (H2 : empty_st =[ pcopy ]=> (Y !-> 1; X !-> 2)).
  { unfold pcopy. apply contra in H1. assumption. }
  assert (H3 : empty_st =[ pcopy ]=> (Y !-> 1; X !-> 1)).
  { unfold pcopy. apply E_Seq with (X !-> 1). constructor. constructor. reflexivity. }
  inversion H1. inversion H2. subst.
  inversion H4. inversion H7. subst.
  inversion H10. inversion H13. subst.
  assert (Hx: (X !-> n1) X = n1). {reflexivity. }
  simpl in *. rewrite Hx in H14.
  remember (Y !-> n1; X !-> n1) as stn.
  remember (Y !-> 1; X !-> 2) as st.

  (* proving that n1 = 1 *)
  assert (st Y = 1). rewrite Heqst. reflexivity.
  assert (stn Y = n1). rewrite Heqstn. reflexivity.
  rewrite H14 in H5. rewrite H0 in H5.
  (* proving that n1 = 2 *)
  assert (st X = 2). rewrite Heqst. reflexivity.
  assert (stn X = n1). rewrite Heqstn. reflexivity.
  rewrite H14 in H8. rewrite H6 in H8.
  rewrite <- H5 in H8. discriminate H8.
Qed.
(** [] *)

(** The definition of program equivalence we are using here has some
    subtle consequences on programs that may loop forever.  What
    [cequiv] says is that the set of possible _terminating_ outcomes
    of two equivalent programs is the same. However, in a language
    with nondeterminism, like Himp, some programs always terminate,
    some programs always diverge, and some programs can
    nondeterministically terminate in some runs and diverge in
    others. The final part of the following exercise illustrates this
    phenomenon.
*)

(** **** Exercise: 4 stars, advanced (p1_p2_term)

    Consider the following commands: *)

Definition p1 : com :=
  <{ while ~ (X = 0) do
       havoc Y;
       X := X + 1
     end }>.

Definition p2 : com :=
  <{ while ~ (X = 0) do
       skip
     end }>.

(** Intuitively, [p1] and [p2] have the same termination behavior:
    either they loop forever, or they terminate in the same state they
    started in.  We can capture the termination behavior of [p1] and
    [p2] individually with these lemmas: *)

Lemma p1_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p1 ]=> st'.
Proof.
  remember p1.
  unfold p1 in *. intros. unfold not. intros.
  induction H0; try inversion Heqc.
  - rewrite H2 in H0. simpl in H0. Search (negb _ = false).
    apply negb_false_iff in H0. Search (( _ =? _) = true).
    apply beq_nat_true in H0. rewrite H0 in H. destruct H. reflexivity.
  - apply IHceval2. rewrite H2. rewrite H3. reflexivity.
    rewrite H3 in H0_. inversion H0_. inversion H5. inversion H8. subst.
    simpl. unfold t_update at 1. rewrite <- eqb_string_refl.
    unfold t_update. simpl.
    destruct (st X); lia.
Qed.
    
Lemma p2_may_diverge : forall st st', st X <> 0 ->
  ~ st =[ p2 ]=> st'.
Proof.
  remember p2. unfold p2 in *. intros. unfold not. intros.
  induction H0; try inversion Heqc.
  - rewrite H2 in H0. simpl in H0.
    apply negb_false_iff in H0.
    apply beq_nat_true in H0. rewrite H0 in H. destruct H. reflexivity.
  - apply IHceval2. rewrite H2. rewrite H3. reflexivity.
    rewrite H3 in H0_. inversion H0_. subst.
    assumption.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p1_p2_equiv)

    Use these two lemmas to prove that [p1] and [p2] are actually
    equivalent. *)

Theorem p1_p2_equiv : cequiv p1 p2.
Proof.
  unfold cequiv,p1,p2. split; intros.
  - inversion H.
    + constructor. assumption.
    + simpl in H2. apply negb_true_iff in H2. apply beq_nat_false in H2. subst.
      apply p1_may_diverge with (st':=st') in H2. unfold p1, not in H2.
      apply H2 in H. inversion H.
  - inversion H.
    + constructor. assumption.
    + simpl in H2. apply negb_true_iff in H2. apply beq_nat_false in H2. subst.
      apply p2_may_diverge with (st':=st') in H2. unfold p2, not in H2.
      apply H2 in H. inversion H.
Qed.
(** [] *)

(** **** Exercise: 4 stars, advanced (p3_p4_inequiv)

    Prove that the following programs are _not_ equivalent.  (Hint:
    What should the value of [Z] be when [p3] terminates?  What about
    [p4]?) *)

Definition p3 : com :=
  <{ Z := 1;
     while ~(X = 0) do
       havoc X;
       havoc Z
     end }>.

Definition p4 : com :=
  <{ X := 0;
     Z := 1 }>.

Theorem p3_p4_inequiv : ~ cequiv p3 p4.
Proof.
  unfold cequiv, not, p3, p4. intros contra.
  remember (Z !-> 1; X !-> 0; X!-> 1) as st'4.
  assert (Hp4: (X !-> 1) =[ p4 ]=> st'4).
  { unfold p4. apply E_Seq with (X !-> 0; X !-> 1). constructor. reflexivity.
    rewrite Heqst'4. apply E_Asgn. reflexivity. }
  apply contra in Hp4.
  remember (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1) as st'3.
  assert (Hp3: (X !-> 1) =[ p3 ]=> st'3).
  { unfold p3. apply E_Seq with (Z !-> 1; X !-> 1). constructor. reflexivity.
    apply E_WhileTrue with st'3. simpl. reflexivity.
    apply E_Seq with (X !-> 0; Z !-> 1; X !-> 1). apply E_Havoc.
    rewrite Heqst'3. apply E_Havoc.
    apply E_WhileFalse. rewrite Heqst'3. reflexivity. }
  unfold p3 in Hp3.
  apply contra in Hp4.
  apply contra in Hp3.
  inversion Hp3. inversion H1. inversion H4. subst. simpl in *.
  remember (Z !-> 1; X !-> 0; X !-> 1) as st1.
  remember  (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1) as st2.
  assert (st1 Z = st2 Z).
  rewrite H13. reflexivity.
  rewrite Heqst1, Heqst2 in H. discriminate H.
Qed.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (p5_p6_equiv)

    Prove that the following commands are equivalent.  (Hint: As
    mentioned above, our definition of [cequiv] for Himp only takes
    into account the sets of possible terminating configurations: two
    programs are equivalent if and only if the set of possible terminating
    states is the same for both programs when given a same starting state
    [st].  If [p5] terminates, what should the final state be? Conversely,
    is it always possible to make [p5] terminate?) *)

Definition p5 : com :=
  <{ while ~(X = 1) do
       havoc X
     end }>.

Definition p6 : com :=
  <{ X := 1 }>.

Theorem p5_p6_equiv : cequiv p5 p6.
Proof.
  unfold cequiv, p5, p6. remember p5.
  split.
  - intros H. inversion H.
    + (* X = 1 *)
      subst. inversion H4.
      apply negb_false_iff in H1. Search ( _ =? _ = true).
      apply beq_nat_true in H1.
      assert ((X !-> 1; st') = st').
      { apply functional_extensionality. unfold t_update.
        intros. destruct (eqb_string X x) eqn: eqXx.
        apply eqb_string_true_iff in eqXx.
        subst. rewrite H1. reflexivity. reflexivity. }
      rewrite <- H0 at 2. constructor. reflexivity.
    + (* X != 1 *)
      subst. inversion H2. apply negb_true_iff in H1.
      apply beq_nat_false in H1.
      
  
    (* rewrite negb_false_iff in H6. Search ( _ =? _ = true). *)
    (* apply beq_nat_true in H6. *)
    (* assert ((X !-> 1; st') = st'). Search (t_update). *)
    (* { apply functional_extensionality. unfold t_update. *)
    (* intros. destruct (eqb_string X x) eqn: eqXx. *)
    (* rewrite <- H6. apply eqb_string_true_iff in eqXx. rewrite eqXx. reflexivity. *)
    (* reflexivity. } *)
    (* + rewrite <- H5 at 2. constructor. reflexivity. *)
    (* + inversion H2. rewrite negb_true_iff in H8. apply beq_nat_false in H8. *)
    (*   inversion H3. subst. *)
      
    
(* FILL IN HERE *) Admitted.
(** [] *)

End Himp.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars, standard, optional (for_while_equiv)

    This exercise extends the optional [add_for_loop] exercise from
    the [Imp] chapter, where you were asked to extend the language
    of commands with C-style [for] loops.  Prove that the command:

      for (c1; b; c2) {
          c3
      }

    is equivalent to:

       c1;
       while b do
         c3;
         c2
       end
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 3 stars, standard, optional (swap_noninterfering_assignments)

    (Hint: You'll need [functional_extensionality] for this one.) *)


Lemma aeval_noninterfering: forall st l1 a1 a2,
    var_not_used_in_aexp l1 a2 ->
    aeval (l1 !-> aeval st a1; st) a2 = aeval st a2.
Proof.
  intros. induction H; try simpl; try rewrite IHvar_not_used_in_aexp1; try rewrite IHvar_not_used_in_aexp2; try reflexivity.
  - simpl. unfold t_update. apply eqb_string_false_iff in H. rewrite H. reflexivity.
Qed.

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
  l1 <> l2 ->
  var_not_used_in_aexp l1 a2 ->
  var_not_used_in_aexp l2 a1 ->
  cequiv
    <{ l1 := a1; l2 := a2 }>
    <{ l2 := a2; l1 := a1 }>.
Proof.
  intros. unfold cequiv. split; intros.
  inversion H2. inversion H8. inversion H5. subst.
  - apply aeval_noninterfering with st l1 a1 a2 in H0. rewrite H0 in *.
    apply E_Seq with (l2 !-> aeval st a2; st). apply E_Asgn. reflexivity.
    assert ((l2 !-> aeval st a2; l1 !-> aeval st a1; st) = (l1 !-> aeval st a1; l2 !-> aeval st a2; st)).
    { apply functional_extensionality. intros. unfold t_update.
      destruct (eqb_string l2 x) eqn: l2x;
      destruct (eqb_string l1 x) eqn: l1x; try reflexivity.
      apply eqb_string_true_iff in l2x, l1x. subst. destruct H. reflexivity.
    }
    rewrite H3. apply E_Asgn. apply aeval_noninterfering. assumption.
  - inversion H2. inversion H8. inversion H5. subst.
    apply aeval_noninterfering with st l2 a2 a1 in H1.
    apply E_Seq with (l1 !-> aeval st a1; st). constructor. reflexivity.
    rewrite H1.
    assert ((l1 !-> aeval st a1; l2 !-> aeval st a2; st) = (l2 !-> aeval st a2; l1 !-> aeval st a1; st)).
    {apply functional_extensionality. intros. unfold t_update.
     destruct (eqb_string l2 x) eqn: l2x;
     destruct (eqb_string l1 x) eqn: l1x; try reflexivity.
     apply eqb_string_true_iff in l2x, l1x. subst. destruct H. reflexivity. }
    rewrite H3. constructor. apply aeval_noninterfering. assumption.
Qed.    

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (capprox)

    In this exercise we define an asymmetric variant of program
    equivalence we call _program approximation_. We say that a
    program [c1] _approximates_ a program [c2] when, for each of
    the initial states for which [c1] terminates, [c2] also terminates
    and produces the same final state. Formally, program approximation
    is defined as follows: *)

Definition capprox (c1 c2 : com) : Prop := forall (st st' : state),
  st =[ c1 ]=> st' -> st =[ c2 ]=> st'.

(** For example, the program

  c1 = while ~(X = 1) do
         X := X - 1
       end

    approximates [c2 = X := 1], but [c2] does not approximate [c1]
    since [c1] does not terminate when [X = 0] but [c2] does.  If two
    programs approximate each other in both directions, then they are
    equivalent. *)

(** Find two programs [c3] and [c4] such that neither approximates
    the other. *)

Definition c3 : com :=
  <{X := 3}>.

Definition c4 : com :=
  <{X := 4}>.

Theorem c3_c4_different : ~ capprox c3 c4 /\ ~ capprox c4 c3.
Proof.
  unfold not. unfold capprox, c3, c4.
  remember empty_st as st.
  remember ( X!->3; st) as st3. remember ( X !-> 4; st) as st4.
  assert (st =[ X:=3 ]=> st3).
  { rewrite Heqst3, Heqst. constructor. reflexivity. }
  assert (st =[ X:= 4 ]=> st4).
  { rewrite Heqst4, Heqst. constructor. reflexivity. }
  split; intros.
  - apply H1 in H. inversion H. inversion H0.
    assert ((st3 X) = 3).
    { subst. apply t_update_eq. }
    assert ((st4 X) = 4).
    { subst. apply t_update_eq. }
    subst. rewrite H5 in H10. rewrite <- H10 in H13. rewrite t_update_eq in H13.
    inversion H13.
  - apply H1 in H0. inversion H. inversion H0.
    assert ((st3 X) = 3).
    { subst. apply t_update_eq. }
    assert ((st4 X) = 4).
    { subst. apply t_update_eq. }
    subst.
    rewrite  H5 in H10. rewrite H10 in H12. rewrite t_update_eq in H12.
    inversion H12.
Qed.

(** Find a program [cmin] that approximates every other program. *)

Definition cmin : com :=
  <{while true do skip end}>.

Theorem cmin_minimal : forall c, capprox cmin c.
Proof.
  intros. unfold capprox, cmin. intros. apply while_true_nonterm in H.
  destruct H. unfold bequiv. reflexivity.
Qed.

(** Finally, find a non-trivial property which is preserved by
    program approximation (when going from left to right). *)

Definition zprop (c : com) : Prop :=
  exists st st' x v, st =[ c ]=> st' -> st' x = v.

Theorem zprop_preserving : forall c c',
  zprop c -> capprox c' c -> zprop c'.
Proof.
  unfold zprop, capprox. intros.
  destruct H. destruct H. destruct H. destruct H.
  exists x, x0, x1, x2. intros. apply H. apply H0 in H1. assumption.
Qed.

(* 2021-08-11 15:11 *)
