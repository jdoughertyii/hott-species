Require Import HoTT Arith FinSet Species.

(** * Defining Trees *)

Definition Graphstr (A : FinSet) 
  := {P : relation A.1 &  ((forall a a', Decidable (P a a'))
                         * (is_mere_relation _ P)
                         * (Symmetric P))%type}.

Definition Graph := {A : FinSet & Graphstr A}.


Definition walk (n : nat) {G : Graph} (v v' : G.1.1)
  := merely {p : nat -> G.1.1 &  ((p O = v) 
                                * (p n = v') 
                                * (forall m, G.2.1 (p m) (p (S m))))%type}.

Definition Connected (G : Graph)
  := forall v v', {n : nat & @walk n G v v'}.

Definition Acyclic (G : Graph)
  := ~ {v : G.1.1 & {n : nat & @walk (S n) G v v}}.

Lemma acyclic_irreflexive (G : Graph) : Acyclic G -> Irreflexive G.2.1.
Proof.
  intro HG. intros v e. apply HG.
  exists v. exists O. unfold walk. apply tr.
  exists (fun _ => v). repeat split.
  apply (fun _ => e).
Defined.

Definition Tree : Species.
Proof.
  exists {G : Graph & ((Connected G) * (Acyclic G))%type}.
  apply (fun G => G.1.1).
Defined.
  


(** * Vertebrates *)

Definition Vertebrate := spec_pointing (spec_pointing Tree).

Lemma gf_verts_tree (n : nat) 
  : gf Vertebrate n = (exp n 2) * (gf Tree n).
Proof.
  refine ((gf_spec_pointing _ _) @ _ @ (mult_assoc _ _ _)^). f_ap.
  refine ((gf_spec_pointing _ _) @ _). f_ap.
  apply (mult_1_r _)^.
Defined.

Definition InhabPerm : Species.
Proof.
  exists {A : FinSet & ((merely A.1) * (A = FSFin (card A)))%type}.
  apply pr1.
Defined.


Definition Arborescence := spec_pointing Tree.


Lemma vert_is_inhab_lord_arb 
  : Vertebrate = (spec_compose InhabPerm Arborescence).
Proof.
Admitted.

Definition end_spec := spec_from_stuff (fun A => A.1 -> A.1).
