(* Add LoadPath "/Users/v_chenhongbo04/Code/ComputerScience/SoftwareFoundations/LogicalFoundations". *)
Print LoadPath.

From LF Require Export Basics.

Theorem add_0_r: forall n: nat, n + 0 = n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem minus_n_n: forall n, minus n n = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

(* Exercises *)

Theorem mul_0_r: forall n: nat, n * 0 = 0.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm: forall n m: nat, S (n + m) = n + (S m).
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm: forall n m: nat, n + m = m + n.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. rewrite add_0_r. reflexivity.
    - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem add_assoc: forall n m p: nat, n + (m + p) = (n + m) + p.
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n: nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.

Lemma double_plus: forall n, double n = n + n.
Proof.
    intro n.
    (* destruct doesn't work because the result still contains double! *)
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem even_S: forall n: nat, even (S n) = negb (even n).
Proof.
    intros n.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - rewrite IHn'. simpl. rewrite negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m: nat, (0 + n) * m = n * m.
Proof.
    intros n m.
    assert (0 + n = n) as H. reflexivity.
    rewrite H. reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q: nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
    intros n m p q.
    assert (H: n + m = m + n).
    rewrite add_comm. reflexivity.
    rewrite H. reflexivity.
Qed.

(* Exercises *)

Theorem add_shuffle3: forall n m p: nat, n + (m + p) = m + (n + p).
Proof.
    intros n m p.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite add_comm with (m := S (n' + p)). 
      simpl. rewrite add_comm with (n := (n' + p)).
      rewrite IHn'. reflexivity.
Qed.

Theorem mul_1_r: forall n: nat, n * 1 = n.
Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mul_1k: forall n m: nat, n * S m = n + n * m.
Proof.
    intros n m.
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite IHn'. rewrite add_assoc. rewrite add_assoc. 
    rewrite add_comm with (n := m) (m := n').
    reflexivity.
Qed.


Theorem mul_comm: forall m n: nat, m * n = n * m.
Proof.
    intros m n.
    induction n as [| n' IHn'].
    - simpl. rewrite mul_0_r. reflexivity.
    - simpl. rewrite mul_1k. rewrite IHn'. reflexivity.
Qed.


