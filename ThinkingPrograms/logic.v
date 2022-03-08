(* Coq version of code in Section 2 *)

Require Import Bool.

Require Import Lia.

Require Import Btauto.

Search (if _ then _ else _).

Compute (implb false false).

Lemma formula1: forall a b c: bool, (if a then b else c) = andb (implb a b) (implb (negb a) c).
Proof.
    intros a b c.
    case a.
    simpl.
    (* why coq cannot solve it when only btauto is here? *)
    btauto.
    simpl.
    reflexivity.
Qed.

Lemma formula2: forall a b c: bool, (if a then b else c) = (a && b) || (negb a && c) || (b && c).
Proof.
    intros a b c.
    case a.
    simpl; btauto.
    simpl; btauto.
Qed.

Lemma formula3: forall A B C: Prop, (A \/ B) /\ (A \/ C) /\ (~ (B /\ C)) -> A.
Proof.
    intros. destruct H. destruct H0. unfold not in H1.
    destruct H; destruct H0; try auto.
    assert (H2: B /\ C). split; assumption. 
    apply H1 in H2. destruct H2.
Qed.

Lemma first_order1: forall (T: Type) (f: T -> T) (p q: T-> Prop) (r: (T * T) -> bool) (c: T), forall x: T, (p x) /\ (p x -> q x) -> q x.
Proof.
    intros. destruct H. auto.
Qed.

Lemma first_order2: forall (T: Type) (f: T -> T) (p q: T-> Prop) (r: (T * T) -> bool) (c: T), 
((p c) /\ (forall x: T, (p x -> q (f x))) -> q (f c)).
Proof.
    intros. destruct H. auto.
Qed.

Lemma first_order3: forall (T: Type) (f: T -> T) (p q: T-> Prop) (r: (T * T) -> Prop) (c: T),
forall x: T, p x /\ (p x -> r (x, f x)) -> (exists y: T, r (x, y)).
Proof.
    intros. destruct H. eauto.
Qed.

