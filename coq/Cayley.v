Require Import HoTT Arith FinSet GCard Species.

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

Definition LTree : Species.
Proof.
  exists {G : Graph & ((Connected G) 
                       * (Acyclic G) 
                       * (G.1.1 = Fin (card G.1)))%type}.
  apply (fun G => G.1.1).
Defined.
  


(** * Vertebrates *)

Definition LArborescence := spec_pointing LTree.

Definition Vertebrate := spec_pointing (spec_pointing LTree).

Lemma gf_verts_tree (n : nat) 
  : gf Vertebrate n = (exp n 2) * (gf LTree n).
Proof.
  refine ((gf_spec_pointing _ _) @ _ @ (mult_assoc _ _ _)^). f_ap.
  refine ((gf_spec_pointing _ _) @ _). f_ap.
  apply (mult_1_r _)^.
Defined.

Definition LOrd := spec_from_stuff (fun A => A.1 = Fin (card A)).


Lemma vert_is_inhab_lord_arb 
  : Vertebrate = (spec_compose (spec_inhab LOrd) LArborescence).
Proof.
Admitted.

Definition end_spec := spec_from_stuff (fun A : FinSet => A.1 -> A.1).

Lemma gf_end_spec (n : nat) : gf end_spec n = exp n n.
Proof.
  (* universe inconsistencies again *)
Admitted.
    
Lemma inhab_lord_arb_is_end
  : spec_compose (spec_inhab LOrd) LArborescence = end_spec.
Admitted.
  
  
  
