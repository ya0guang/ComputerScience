(* Coq in a Hurry *)

(* 1.1 Correct Formulas *)

Check 3.

Check False.

Check (3+4).

Check (3, 4).

Check ((3=5)/\True).

Check nat -> Prop.

Check (3 <= 6).

Check (3, 3=6): nat * Prop.

Check (fun x: nat => x = 3).

Check (forall x: nat, x < 3 \/ (exists y: nat, x = y + 3)).

Check (let f:= fun x => (x * 3, x) in f 3).

(* give out the meaning of the sign? Interpretation and domain? *)
Locate "_ * _".

Check le.

Check (and True False).

(* `Check` not only checks if the expression is well-formed in two aspects: syntax and type *)

(* 1.2 Evaluating *)

Compute let f:= fun x => (x * 3, x) in f 3.

(* 2 Programming in Coq *)

(* 2.1 Defining *)

Definition example1 := fun x : nat => x * x + 2 * x + 1.

(* forget the definition. *)
Reset example1.

Definition example1 (x: nat) := x * x + 2 * x + 1.

Check example1.
(* Check example1'. *)

Compute example1 3.

(* 2.2 Boolean conditional *)

Require Import Bool.

Compute if true then 3 else 5.

(* The command SearchPattern takes a pattern as argument and returns any symbol whose type finishes with that pattern *)
SearchPattern bool.

(* Search takes a list of patterns as arguments and returns any symbol whose type contains all the patterns in the list *)
Search bool.

(* `bool` is returned here rather than `Prop` *)
Check false.

(* 2.3 Computing with Nats *)
Require Import Arith.

(* a nat is either 0 or a successor of a nat (S n) *)
Definition is_zero (n: nat) := 
    match n with
    | 0 => true
    | S _ => false
    end.

Check is_zero.

Compute is_zero 0.

Print pred.

Print Init.Nat.pred.

Print example1.

Fixpoint sum_n n:=
    match n with
    | 0 => 0
    | S p => p + sum_n p
    end.

(* cannot pass check because it's not a structural recursion *)
(* Fixpoint rec_bad n:=
    match n with
    | 0 => 0
    | S p => rec_bad (S p)
    end. *)

Fixpoint sum_n2 n s :=
    match n with
    | 0 => s
    | S p => sum_n2 p (s + p)
    end.

Locate "~ _".

Fixpoint evenb_neg n :=
    match n with
    | 0 => true
    | S p => negb (evenb_neg p)
    end.

Fixpoint evenb n :=
    match n with
    | 0 => true
    | 1 => false
    | S (S p) =>  evenb p
    end.

Compute evenb 10.

(* 2.4 Computing with lists *)

Require Import List.

Check 1::2::3::nil.

Compute map (fun x => x + 3) (1::3::2::nil).

Compute map S (1::22::3::nil).

Compute let l := (1::2::3::nil) in l ++ map (fun x => x + 3) l.

(* Finding more functions *)

SearchPattern (nat -> nat -> bool).

Search Nat.eqb.

Locate "_ =? _".

(* exercise *)
Fixpoint n_list (n: nat) :=
    match n with
    | 0 => nil
    | S p => n::(n_list p)
    end.

Compute (n_list 10).

Definition head_evb l :=
    match l with
    | nil => false
    | a::tl => evenb a
    end.

Fixpoint sum_list l :=
    match l with
    | nil => 0
    | a::tl => a + sum_list tl
    end.

Fixpoint insert n l :=
    match l with
    | nil => n::nil
    | a::tl => if n <=? a then n::l else a::(insert n tl)
    end.

Fixpoint sort l :=
    match l with
    | nil => nil
    | a::tl => insert a (sort tl)
    end.

Compute sort (1::4::3::22::5::16::7::nil).

(* 3 Propositions and proofs *)

(* 3.1 Finding existing proofs *)

Search True.

SearchPattern (_ <= _).

Search (_ <= _) (_ + _).

SearchPattern (_ + _ <= _ + _).

(* it only looks for rewriting theorems, that is, theorems where the proved predicate is an equality *)
SearchRewrite (_ + (_ - _)).

(* 3.2 Constructing new proofs *)

Lemma example2: forall a b: Prop, a/\b -> b/\a.
Proof.
    intros a b H.
    split.
    destruct H as [H1 H2].
    exact H2.
    (* intuition. *)
    destruct H as [H1 H2].
    exact H1.
Qed.

Lemma example3 : forall A B, A\/B -> B\/A.
Proof.
    intros A B H.
    destruct H as [H1 | H1].
    right; assumption.
    left.
    exact H1.
Qed.

Check le_n.

Check le_S.

Lemma example4: 3 <= 5.
Proof.
    apply le_S.
    apply le_S.
    apply le_n.
Qed.

Check le_trans.

Lemma example5: forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
    intros x y.
    intros x10 y10.
    apply le_trans with (m := 10).
    assumption.
    assumption.
Qed.

SearchPattern (_ * (_ * _)).

Lemma example6: forall x y, (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
    intros x y.
    SearchRewrite (_ * (_ + _)).
    rewrite Nat.mul_add_distr_l.
    SearchRewrite ((_ + _) * _).
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.add_assoc.
    SearchRewrite (_ + (_ + _)).
    rewrite <- Nat.add_assoc with (n := x * x).
    SearchPattern (?x * ?y = ?y * ?x).
    rewrite Nat.mul_comm with (n := y) (m := x).
    SearchPattern (S _ * _).
    rewrite <- (Nat.mul_1_l (x * y)) at 1.
    rewrite <- Nat.mul_succ_l.
    SearchRewrite (_ * (_ * _)).
    rewrite Nat.mul_assoc.
    reflexivity.
Qed.

Print Nat.pred.

Lemma pred_S_eq: forall x y, x = S y -> Nat.pred x = y.
Proof.
    intros x y pre.
    unfold Nat.pred.
    (* force pattern matching to chose the write branch *)
    rewrite pre.
    reflexivity.
Qed.

(* 3.4 More advanced tactivs *)

(* automatic theorm proving *)

(* Omega is no longer maintained and it's functionalities are now achieved by `lia` *)
(* Require Import Omega. *)
Require Import Lia.

Lemma omega_example: forall f x y, 0 < x -> 0 < f x -> 3 * f x <= 2 * y -> f x <= y.
Proof.
    intros; lia.
    (* omega. *)
Qed.

(* 4 provng properties of programs on numbers *)

(* 4.1 A proof by induction *)

Lemma sum_n_p: forall n, 2 * sum_n n + n = n * n.
Proof.
    induction n.
    reflexivity.
    assert (SnSn: S n * S n = n * n + 2 * n + 1).
    ring.
    rewrite SnSn.
    rewrite <- IHn.
    simpl.
    ring.
Qed.

(* 4.2 Stronger statements in induction *)
Check negb_involutive.

Lemma evenb_p: forall n, evenb n = true -> exists x, n = 2 * x.
Proof.
    assert (Main: forall n, (evenb n = true -> exists x, n = 2 * x) /\ (evenb (S n) = true -> exists x, S n = 2 * x)).
    induction n.
    split.
    exists 0; ring.
    simpl; intros H; discriminate H.
    split.
    destruct IHn as [_ IHn']; exact IHn'.
    simpl evenb.
    intros H.
    destruct IHn as [IHn' _].
    assert (H': exists x, n = 2 * x).
    apply IHn'; exact H.
    destruct H' as [x q].
    exists (x + 1).
    rewrite q; ring.
    intros n ev.
    destruct (Main n) as [H _].
    apply H.
    exact ev.
Qed.


Lemma evenb_neg_p: forall n, evenb_neg n = true -> exists x, n = 2 * x.
Proof.
    assert (Main: forall n, (evenb_neg n = true -> exists x, n = 2 * x) /\ (evenb_neg (S n) = true -> exists x, S n = 2 * x)).
    induction n.
    split.
    exists 0.
    ring.
    simpl.
    (* Here a contradiction is introduced *)
    intros H; discriminate H.
    split.
    destruct IHn as [_ IHn']; exact IHn'.
    simpl evenb_neg.
    rewrite negb_elim.
    destruct IHn as [IHn' _].
    intros H.
    assert (H': exists x, n = 2 * x).
      apply IHn'; exact H.
    destruct H' as [x q].
    exists (x + 1); rewrite q; ring.
    intros n.
    destruct (Main n) as [H _]; exact H.
Qed.

(* 5. Reasoning on conditional statements *)

Lemma not_is_zero_pred: 
forall x, is_zero x = false -> S (Nat.pred x) = x.
Proof.
    intros x.
    unfold is_zero, Nat.pred.
    Print nat.
    destruct x as [ | p].
    discriminate.
    intros _; reflexivity.
Qed.

(* 6. Proving properties of programs of lists *)

Fixpoint count n l :=
    match l with
    | nil => 0
    | a::tl => let r:= count n tl in if n =? a then 1 + r else r 
    end.

Lemma insert_incr: forall n l, count n (insert n l) =  1 + count n l.
Proof.
  intros n l.
  induction l.
  simpl.
  Search (_ =? _).
  rewrite Nat.eqb_refl.
  reflexivity.
  simpl.
  case (n <=? a).
  simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  simpl.
  rewrite IHl.
  case (n =? a). 
    simpl; reflexivity.
    simpl; reflexivity.
Qed.

(* 7. Defining new datatypes *)

Inductive bin: Type := 
| L: bin
| N: bin -> bin -> bin.

Check N L (N L L ).

Definition example7 (t: bin): bool := 
    match t with
    | N L L => false
    | _ => true
    end.

Check example7.

Fixpoint flatten_aux (t1 t2:bin) : bin :=
    match t1 with
    | L => N L t2
    | N t'1 t'2 => flatten_aux t'1 (flatten_aux t'2 t2)
    end.

Fixpoint size (t: bin) : nat :=
    match t with
    | L => 1
    | N t1 t2 => 1 + size t1 + size t2
    end.

Compute flatten_aux (N L L) L.

(* 7.4 Proof by case *)

