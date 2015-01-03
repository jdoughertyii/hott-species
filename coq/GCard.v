Require Import HoTT Arith Nat FinSet.
Require Import UnivalenceAxiom.

Axiom (gcard : Type -> nat).
Axiom (gcard_unit : gcard Unit = (S O)).
Axiom (gcard_sum : forall (X Y : Type), gcard (X + Y) = gcard X + gcard Y).

Lemma gcard_equiv (A B : Type) (f : A -> B) : IsEquiv f -> gcard A = gcard B.
Proof.
  intro p. f_ap. apply (path_universe f).
Defined.

Lemma gcard_equiv' (A B : Type) : A <~> B -> gcard A = gcard B.
Proof.
  intro e. f_ap. apply (path_universe e).
Defined.

Lemma gcard_prod (A B : Type) : gcard (A * B) = (gcard A) * (gcard B).
Admitted.

Lemma gcard_empty : gcard Empty = 0.
Proof.
  apply (cancelR_plus 1).
  path_via (gcard Empty + gcard Unit).
  - apply (ap (plus (gcard Empty))).
    symmetry. apply gcard_unit.
  - path_via (gcard (Empty + Unit)).
    + symmetry. apply gcard_sum.
    + path_via (gcard Unit).
      * apply gcard_equiv'. apply empty_sum.
      * apply gcard_unit.
Defined.

                                              

Lemma gcard_fin (n : nat) : gcard (Fin n) = n.
Proof.
  induction n.
  - apply gcard_empty.
  - path_via (gcard (Fin n) + gcard Unit).
    + apply gcard_sum.
    + path_via (gcard (Fin n) + 1).
      * f_ap. apply gcard_unit.
      * refine ((plus_n_Sm _ _) @ _). f_ap.
        refine ((plus_O_r _) @ IHn).
Defined.


Lemma gcard_card (A : FinSet) : gcard A.1 = card A.
Proof.
  destruct A as [A [n p]]. strip_truncations.
  path_via (gcard (Fin n)). f_ap. apply gcard_fin.
Defined.

