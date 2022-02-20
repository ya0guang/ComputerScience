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

Lemma first_order1: forall T: Type, forall c: T, forall f: T -> T, forall p q: T-> bool, forall r: (T * T) -> bool, forall x: T, p(x) &&  (implb (implb p(x) q(x)) q(x)).
Proof.
    
Qed.
