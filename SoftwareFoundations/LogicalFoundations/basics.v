Inductive day: Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
    | sunday => monday
    end.

Compute (next_weekday friday).

Example test_next_weekday :
  (next_weekday friday) = saturday.
Proof.
  simpl.
  reflexivity.
Qed.

Inductive bool: Type :=
  | true
  | false.

Definition negb (b: bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1: bool) (b2: bool) : bool := 
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb2: false || true || false = true.
Proof.
  simpl.
  reflexivity.
Qed.

(* Coq thinks the first element of Inductive type evaluates to true. *)

Definition negb' (b: bool) : bool :=
  if b then false
  else true.
  
Definition andb' (b1: bool) (b2: bool) : bool := 
  if b1 then b2
  else false.


Definition orb' (b1: bool) (b2: bool) : bool := 
  if b1 then true
  else b2.

(* Exercise nandb *)

Definition nandb (b1: bool) (b2: bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

(* Exercise andb3 *)

Definition andb3 (b1: bool) (b2: bool) (b3: bool) : bool := 
  b1 && b2 && b3.

Check true.

Check (negb true).

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Check (primary red).

Definition monochrome (c : color) : bool := 
  match c with
  | black => true
  | white => true
  | primary _ => false
  end.

Definition isred (c : color) : bool := 
  match c with
  | primary red => true
  | _ => false
  end.

(* Namespace *)
Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b.

Check b.

Module TuplePlayground.

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0): nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | _ => false
  end.

Compute (all_zero (bits B0 B0 B0 B0)).

Compute (all_zero (bits B1 B0 B1 B0)).

End TuplePlayground.

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat := 
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n : nat) : nat := 
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S 0 => false
  | S (S n') => even n'
  end.

Module NatPlayground2.

  Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Compute (mult 3 2).

Fixpoint minus (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => minus (pred m) n'
  end.

Compute (minus 11 11).

End NatPlayground2.

(* Exercise: factorial *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => n * factorial n'
  end.

Example test_fact1: (factorial 3) = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_fact2: (factorial 5) = 120.
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
    | O => true
    | S _ => false
    end 
  | S n' => match m with
    | O => false
    | S m' => eqb n' m'
    end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
    | O => false
    | S m' => leb n' m'
    end
  end.
  
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb1: ( 4 <=? 2 ) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n.
  (* refl tries to unfold defined terms, more than simpl *)
  reflexivity.
Qed.

Theorem plus_1_1 : forall n: nat, 1 + n = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_0_1 : forall n: nat, 0 * n = 0.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem plus_id_example: forall n m: nat, n = m -> n + n = m + m.
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.

(* Exercise: plus_id_exercise *)

Theorem plus_id_exercise: forall n m o: nat, n = m -> m =  o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0: forall p q: nat, (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(* Exercise mult_n_1 *)

Theorem mult_n_1: forall p: nat, p * 1 = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem plus_1_neg_0: forall n: nat, (n + 1 ) =? 0 = false.
Proof.
  intros n.
  (* destruct: recover the definition of n *)
  (* as [{lists of list of constructor arguments}] *)
  (* eqn: E: give a name of the destructed var *)
  destruct n as [| n'] eqn: E.
  (* bullets denotes this proof corresponds to subgoal(s) *)
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive: forall b: bool, negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn: E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative: forall b c, andb b c = andb c b.
Proof.
  intros b c.
  destruct b eqn: Eb.
  - destruct c eqn: Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn: Ec.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andb3_exchange: forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d.
  destruct b eqn: Eb.
  - rewrite andb_commutative with (b := c).
  reflexivity.
  - rewrite andb_commutative with (c := d).
  simpl.
  rewrite andb_commutative.
  reflexivity.
Qed.

Theorem andb_true_elim2: forall b c: bool, andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn: E.
  - simpl. intros H. exact H.
  - simpl. intros H. discriminate.
Qed.

(* Exercise *)

Theorem zero_nbeq_plus: forall n: nat, 0 =? (n + 1) = false.
Proof.
  intros [| n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* Exercises *)

Theorem identity_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x: bool), f x = x) -> 
  forall (b: bool), f (f b) = b.
Proof.
  intros f H.
  intros b.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

Theorem andb_eq_orb: 
  forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b eqn: E.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity.
Qed.

Inductive bin: Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m: bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 (n)
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m: bin) : nat :=
  match m with
  | Z => 0
  | B0 n' => 2 * bin_to_nat n'
  | B1 n' => 1 + 2 * bin_to_nat n'
  end.

Example test_bin_incr1: (incr (B1 Z)) = B0 (B1 Z).
Proof.
  reflexivity.
Qed.

Example test_bin_incr2: (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof.
  reflexivity.
Qed.

Example test_bin_incr3: (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  reflexivity.
Qed.

Example test_bin_incr4: bin_to_nat (B0 (B1 Z)) = 2.
Proof.
  reflexivity.
Qed.

Example test_bin_incr5: bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof.
  reflexivity.
Qed.

Example test_bin_incr6: bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof.
  reflexivity.
Qed.
