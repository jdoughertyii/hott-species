Require Import HoTT Arith FinSet GCard.

Definition Species : Type := {X : Type & X -> FinSet}.

Definition spec_from_stuff (P : FinSet -> Type) : Species := (sigT P; pr1).

Lemma functor_sigma_inverse_beta {A B : Type} `{P : A -> Type} `{Q : B -> Type}
      (f : A -> B) (g : forall a, P a -> Q (f a))
      `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
      (u : sigT Q) 
  : (functor_sigma f g)^-1 u = (f^-1 u.1; ((g (f^-1 u.1))^-1 ((eisretr f u.1)^ # u.2))).
Proof.
  induction u as [b q]. simpl.
  apply (ap (functor_sigma f g))^-1.
  refine ((eisretr _ _) @ _).
  unfold functor_sigma. simpl.
  apply path_sigma_uncurried. refine (_; _).
  - simpl. symmetry. apply eisretr.
  - simpl. symmetry. apply eisretr.
Defined.

  
Definition path_stuff_spec (P Q : FinSet -> Type)
  : (forall A, P A <~> Q A) -> (spec_from_stuff P) = (spec_from_stuff Q).
Proof.
  intros Heq. apply path_sigma_uncurried. refine (_; _).
  - apply path_universe_uncurried, equiv_functor_sigma_id.
    intro A. apply Heq.
  - apply path_arrow. intros [A q]. simpl.
    refine ((transport_arrow _ _ _) @ _).
    refine ((transport_const _ _) @ _).
    path_via ((equiv_inverse (equiv_functor_sigma_id (fun B => Heq B))) (A; q)).1.
    f_ap. refine (_ @ (transport_path_universe_uncurried _ _)). f_ap.
    symmetry. apply path_universe_V_uncurried. simpl.
    path_via (A; (Heq A)^-1 (transport _ (eisretr idmap A)^ q)).1.
    f_ap. apply functor_sigma_inverse_beta.
Defined.

    
Definition gen_func (X : Species) (n : nat) : nat.
Proof.
  induction X as [X f].
  apply (gcard (hfiber (card o f) (n))).
Defined.


(** * Generating function simplifications *)

Definition gf (X : Species) (n : nat) := 
  (gcard (BAut (Fin n))) * (gcard (hfiber X.2 (FSFin n))).

Lemma gf_spec_from_stuff (P : FinSet -> Type) (n : nat)
  : gf (spec_from_stuff P) n 
    = 
    (gcard (BAut (Fin n))) * (gcard (P (FSFin n))).
Proof.
  unfold gf. f_ap. simpl. apply gcard_equiv'.
  symmetry. apply hfiber_fibration.
Defined.

Lemma all_spec_from_stuff (X : Species) 
  : {P : FinSet -> Type & X = spec_from_stuff P}.
Proof.
  induction X as [X f]. exists (fun A => hfiber f A).
  apply path_sigma_uncurried. refine (_; _).
  - simpl. apply path_universe_uncurried.
    apply equiv_fibration_replacement.
  - simpl. apply path_arrow. intro w.
    refine ((transport_arrow _ _ _) @ _).
    refine ((transport_const _ _) @ _).
    path_via (f ((equiv_fibration_replacement f)^-1 w)). f_ap.
    path_via (transport idmap 
                        (path_universe_uncurried 
                           (equiv_inverse (equiv_fibration_replacement f)))
                        w).
    f_ap. symmetry. apply path_universe_V_uncurried.
    apply transport_path_universe_uncurried.
    induction w as [A [x p]]. apply p.
Defined.


  
(** * Species Sum/Coproduct *)

Definition spec_sum (X Y : Species) : Species
    := ((X.1 + Y.1)%type; sum_rect _ X.2 Y.2).

Lemma sigma_functor_sum (X : Type) (P Q : X -> Type) :
  ({x : X & P x} + {x : X & Q x}) <~> {x : X & (P x + Q x)%type}.
Proof.
  refine (equiv_adjointify _ _ _ _).
  - intros [[x w] | [x w]]; exists x; [left | right]; apply w.
  - intros [x [w | w]]; [left | right]; apply (x; w).
  - intros [x [w | w]]; reflexivity.
  - intros [[x w] | [x w]]; reflexivity.
Defined.

Definition stuff_spec_sum (P Q : FinSet -> Type) := fun A => (P A + Q A)%type.

Lemma stuff_spec_sum_correct (P Q : FinSet -> Type) : 
  spec_from_stuff (stuff_spec_sum P Q)
  =
  spec_sum (spec_from_stuff P) (spec_from_stuff Q).
Proof.
  apply path_sigma_uncurried. refine (_; _).
  - unfold stuff_spec_sum. simpl. symmetry.
    apply path_universe_uncurried.
    apply sigma_functor_sum.
  - simpl. apply path_arrow. intros x.
    refine ((transport_arrow _ _ _) @ _).
    refine ((transport_const _ _) @ _).
    path_via (transport idmap
                        (path_universe_uncurried (sigma_functor_sum FinSet P Q))
                        x).1.
    f_ap. f_ap. apply inv_V.
    path_via ((sigma_functor_sum FinSet P Q) x).1.
    f_ap. apply transport_path_universe_uncurried.
    destruct x as [[x p] | [x q]]; reflexivity.
Defined.
    
    
Lemma gf_spec_sum (X Y : Species) (n : nat)
  : gf (spec_sum X Y) n = (gf X n) + (gf Y n).
Proof.
  unfold gf. refine (_ @ (nat_dist_l _ _ _)). f_ap. 
  refine (_ @ (gcard_sum _ _)). apply gcard_equiv'.
  induction X as [X f], Y as [Y g].
  refine (equiv_adjointify _ _ _ _).
  - intros [[x | y] p].
    + left. apply (x; p).
    + right. apply (y; p).
  - intros [[x p] | [y p]].
    + exists (inl x). apply p.
    + exists (inr y). apply p.
  - intros [[x p] | [y p]]; reflexivity.
  - intros [[x | y] p]; reflexivity.
Defined.
    


(** * Hadamard product *)

Definition spec_hprod (X Y : Species) : Species.
Proof.
  exists {x : X.1 & {y : Y.1 & X.2 x = Y.2 y}}.
  apply (X.2 o pr1).
Defined.

Definition stuff_spec_hprod (P Q : FinSet -> Type) := fun A => (P A * Q A)%type.

Lemma stuff_spec_hprod_correct (P Q : FinSet -> Type)
  : spec_from_stuff (stuff_spec_hprod P Q)
    =
    spec_hprod (spec_from_stuff P) (spec_from_stuff Q).
Proof.
  refine (_ @ (all_spec_from_stuff _).2^). apply path_stuff_spec. intro A.
  simpl. unfold hfiber, stuff_spec_hprod. symmetry.
  equiv_via {x : {B : FinSet & {p : P B & 
                 {y' : {x : _ & Q x} &
                 B = (let (proj1_sig, _) := y' in proj1_sig)}}} &
                 x.1 = A}.
  refine (equiv_functor_sigma' _ _). simpl. symmetry.
  refine (equiv_sigma_assoc _ _). simpl. 
  intros w. simpl. apply equiv_idmap.
  
  equiv_via {x : {B : FinSet & {_ : P B &
                 {C : FinSet & {_ : Q C & 
                  B = C}}}} 
                   & x.1 = A}. simpl. 
  refine (equiv_functor_sigma' _ _).
  refine (equiv_functor_sigma_id _). intro B.
  refine (equiv_functor_sigma_id _). intro p. symmetry. 
  refine (equiv_sigma_assoc _ _). intros w. simpl.
  apply equiv_idmap.
  

  equiv_via {x : {B : FinSet & {_ : P B & Q B}} & x.1 = A}.
  refine (equiv_functor_sigma' _ _).
  refine (equiv_functor_sigma_id _). intro B.
  refine (equiv_functor_sigma_id _). intro p.
  
  equiv_via {C : FinSet & {_ : B = C & Q C}}.
  refine (equiv_functor_sigma_id _). intro C.
  apply equiv_sigma_symm0.
  equiv_via {w : {C : FinSet & B = C} & Q w.1}.
  refine (equiv_sigma_assoc _ _).
  equiv_via (Q (center {C : FinSet & B = C}).1).
  refine (equiv_contr_sigma _).
  apply equiv_idmap.
  intro a. apply equiv_idmap.

  equiv_via {B : FinSet & {w : {_ : P B & Q B} & B = A}}.
  symmetry. refine (equiv_sigma_assoc _ _). 
  equiv_via {B : FinSet & {_ : B = A & (P B * Q B)%type}}.
  refine (equiv_functor_sigma_id _). intro B.
  equiv_via {_ : B = A & {_ : P B & Q B}}.
  apply equiv_sigma_symm0.
  refine (equiv_functor_sigma_id _). intro p.
  refine (equiv_adjointify _ _ _ _); intro w.
    apply (w.1, w.2).
    apply (fst w; snd w).
    apply eta_prod.
    apply eta_sigma.
  
  equiv_via {w : {B : FinSet & B = A} & (P w.1 * Q w.1)%type}.
  refine (equiv_sigma_assoc _ _).
  equiv_via (P (center {B : FinSet & B = A}).1 * 
             Q (center {B : FinSet & B = A}).1)%type.
  refine (equiv_contr_sigma _). apply equiv_idmap.
Defined.


Lemma gf_spec_hprod (X Y : Species) (n : nat)
  : gf (spec_hprod X Y) n = (fact n) * (gf X n) * (gf Y n).
Proof.
  unfold gf.
  path_via (gcard (BAut (Fin n)) 
             * (gcard (hfiber X.2 (FSFin n))) 
             * gcard (hfiber Y.2 (FSFin n))).
  - refine (_ @ (mult_assoc _ _ _)^). f_ap.
    path_via (gcard ((hfiber X.2 (FSFin n) * (hfiber Y.2 (FSFin n))))).
    + apply gcard_equiv'. 
      induction X as [X f], Y as [Y g].
      refine (equiv_adjointify _ _ _ _).
      * { intros [[x [y p]] q]. split.
          - exists x. apply q.
          - exists y. apply (p^ @ q). }
      * intros [[x p] [y q]]. exists (x; (y; p @ q^)). apply p.
      * { intros [[x p] [y q]]. apply path_prod.
          - reflexivity.
          - apply path_sigma_uncurried. exists 1.
            apply moveR_Vp. symmetry. apply concat_pV_p. }
      * { intros [[x [y p]] q]. apply path_sigma_uncurried.
          refine (_; _). repeat (apply path_sigma_uncurried; exists idpath).
          simpl. apply moveR_pV. symmetry. apply concat_p_Vp.
          simpl pr1. simpl pr2. induction q. 
          admit. }
    + apply gcard_prod.
  - admit.
Defined.
            
        
  
(** * Cauchy product *)


Definition spec_cprod (X Y : Species) : Species.
Proof.
  exists (X.1 * Y.1)%type.
  apply (fun z => (fs_sum (X.2 (fst z)) (Y.2 (snd z)))).
Defined.


Definition stuff_spec_cprod (P Q : FinSet -> Type) 
  := fun A => {U : FinSet & {V : FinSet & (P U * Q V * (fs_sum U V = A))%type}}.


Lemma stuff_spec_cprod_correct (P Q : FinSet -> Type)
  : spec_from_stuff (stuff_spec_cprod P Q)
    =
    spec_cprod (spec_from_stuff P) (spec_from_stuff Q).
Proof.
  refine (_ @ (all_spec_from_stuff _).2^). apply path_stuff_spec. intro A.
  simpl. unfold hfiber, stuff_spec_cprod. symmetry.
  
  equiv_via {x : {w : {x : _ & P x} & {x : _ & Q x}} & fs_sum x.1.1 x.2.1 = A}.
  refine (equiv_functor_sigma' _ _).
  refine (equiv_adjointify _ _ _ _); intro w.
    apply (fst w; snd w).
    apply (w.1, w.2).
    apply eta_sigma.
    apply eta_prod.
  intro w. simpl. apply equiv_idmap.

  equiv_via {p : {x : FinSet & P x} & {q : {x : FinSet & Q x} &
                 fs_sum p.1 q.1 = A}}.
  symmetry. refine (equiv_sigma_assoc _ _).
  
  equiv_via {U : FinSet & {p : P U & {q : {x : FinSet & Q x} &
                 fs_sum U q.1 = A}}}.
  symmetry. refine (equiv_sigma_assoc _ _).
  
  refine (equiv_functor_sigma_id _). intro U.
  equiv_via {q : {x : FinSet & Q x} & {_ : P U & fs_sum U q.1 = A}}.
  refine (equiv_sigma_symm _).
  equiv_via {V : FinSet & {q : Q V  & {_ : P U & fs_sum U V = A}}}.
  symmetry. refine (equiv_sigma_assoc _ _).
  
  refine (equiv_functor_sigma_id _). intro V.
  refine (equiv_adjointify _ _ _ _).
  - intros [q [p r]]. apply (p, q, r).
  - intros [[p q] r]. apply (q; (p; r)).
  - intros w. reflexivity.
  - intros w. reflexivity.
Defined.
  
  

(** * Composition *)

Definition spec_compose (X Y : Species) : Species.
Proof.
  exists {x : X.1 & Fin (card (X.2 x)) -> Y.1}.
  intro w. apply (fin_indexed_sum (card (X.2 w.1)) (Y.2 o w.2)).
Defined.

Definition stuff_spec_compose (P Q : FinSet -> Type)
  := fun A => {C : FinSet & {B : Fin (card C) -> FinSet &
                   ((partition A (card C) B)
                * (P C)
                * (forall k : Fin (card C), Q (B k)))%type}}.

Lemma stuff_spec_compose_correct (P Q : FinSet -> Type)
  : spec_from_stuff (stuff_spec_compose P Q)
    =
    spec_compose (spec_from_stuff P) (spec_from_stuff Q).
Proof.
Admitted.
  
  
  
(** * Derivative *)

Definition spec_derivative (X : Species) : Species
  := spec_from_stuff (fun A => {x : X.1 & X.2 x = fs_sum A (FSFin 1)}).

Definition stuff_spec_derivative (P : FinSet -> Type) 
  := fun A => {B : FinSet & (P B * (B = fs_sum A (FSFin 1)))%type}.

Lemma stuff_spec_derivative_correct (P : FinSet -> Type)
  : spec_from_stuff (stuff_spec_derivative P)
    =
    spec_derivative (spec_from_stuff P).
Proof.
  apply path_stuff_spec. intro A.
  simpl. unfold stuff_spec_derivative.
  
  equiv_via {B : FinSet & {_ : B = fs_sum A (FSFin 1) & P B}}.
  refine (equiv_functor_sigma_id _). intro B.
  refine (equiv_adjointify _ _ _ _); intro w.
    apply (snd w; fst w).
    apply (w.2, w.1).
    apply eta_sigma.
    apply eta_prod.

  equiv_via {w : {B : FinSet & B = fs_sum A (FSFin 1)} & P w.1}.
  refine (equiv_sigma_assoc _ _).

  symmetry.
  equiv_via {B : FinSet & {_ : P B & B = fs_sum A (FSFin 1)}}.
  symmetry. refine (equiv_sigma_assoc _ _).

  equiv_via {B : FinSet & {_ : B = fs_sum A (FSFin 1) & P B}}.
  refine (equiv_functor_sigma_id _). intro B.
  apply equiv_sigma_symm0.
  
  refine (equiv_sigma_assoc _ _).
Defined.
  


Lemma gf_spec_derivative (X : Species) (n : nat)
  : gf (spec_derivative X) n = (S n) * (gf X (S n)).
Proof.
  unfold gf. 
  refine (_ @ (mult_assoc _ _ _)). symmetry.
  path_via (gcard (BAut (Fin (S n))) * S n * gcard (hfiber X.2 (FSFin (S n)))).
  f_ap. apply mult_comm. f_ap.
  (* This requires a real definition of [gcard] *)
  admit.

  symmetry.
  path_via (gcard {x : X.1 & (X.2 x) = (FSFin (S n))}). apply gcard_equiv'.
  induction X as [X f]. simpl.
  equiv_via {x : X & f x = fs_sum (FSFin n) (FSFin 1)}. symmetry.
  refine (hfiber_fibration _ _). refine (equiv_functor_sigma_id _). intro x.
  refine (equiv_transport _ _ _ _). apply path_finset. simpl.
  apply path_universe_uncurried. refine (equiv_functor_sum' _ _).
  apply equiv_idmap. apply empty_sum.
Defined.
  
  


(** * Pointing *)

Definition spec_pointing (X : Species) : Species.
Proof.
  exists {x : X.1 & (X.2 x).1}.
  intro w. apply (X.2 w.1).
Defined.

Definition stuff_spec_pointing (P : FinSet -> Type) 
  := fun A => (P A * A.1)%type.

Lemma stuff_spec_pointing_correct (P : FinSet -> Type)
  : spec_from_stuff (stuff_spec_pointing P)
    =
    spec_pointing (spec_from_stuff P).
Proof.
  refine (_ @ (all_spec_from_stuff _).2^). apply path_stuff_spec. intro A.
  simpl. unfold stuff_spec_pointing. unfold hfiber. symmetry.

  equiv_via {y : {z : _ & P z} & {_ : y.1.1 & y.1 = A}}.
  symmetry. refine (equiv_sigma_assoc _ _). 

  equiv_via {B : FinSet & {_ : P B & {_ : B.1 & B = A}}}.
  symmetry. refine (equiv_sigma_assoc _ _). 

  equiv_via {B : FinSet & {_ : B = A & (P B * B.1)%type}}.
  refine (equiv_functor_sigma_id _). intro B.
  refine (equiv_adjointify _ _ _ _).
    intro w. apply (w.2.2; (w.1, w.2.1)).
    intro w. apply (fst w.2; (snd w.2; w.1)).
    intro w. apply eta_sigma.
    intro w. apply eta_sigma.

  equiv_via {w : {B : FinSet & B = A} & (P w.1 * w.1.1)%type}.
  refine (equiv_sigma_assoc _ _). 
  
  equiv_via (P (center {B : FinSet & B = A}).1
             * (center {B : FinSet & B = A}).1.1)%type.
  refine (equiv_contr_sigma _). apply equiv_idmap. 
Defined.
  
  

Definition gf_spec_pointing (X : Species) (n : nat)
  : gf (spec_pointing X) n  = n * (gf X n).
Proof.
Admitted.

  

(** * Inhabiting *)

Definition spec_inhab (X : Species) : Species.
Proof.
  exists {x : X.1 & merely (X.2 x).1}.
  apply (X.2 o pr1).
Defined.

Definition stuff_spec_inhab (P : FinSet -> Type)
  := fun A => (P A * merely A.1)%type.

Lemma stuff_spec_inhab_correct (P : FinSet -> Type)
  : spec_from_stuff (stuff_spec_inhab P)
    =
    spec_inhab (spec_from_stuff P).
Proof.
  refine (_ @ (all_spec_from_stuff _).2^). apply path_stuff_spec. intro A.
  simpl. unfold stuff_spec_inhab. unfold hfiber. symmetry.

  equiv_via {y : {z : _ & P z} & {_ : merely y.1.1 & y.1 = A}}.
  symmetry. refine (equiv_sigma_assoc _ _). 

  equiv_via {B : FinSet & {_ : P B & {_ : merely B.1 & B = A}}}.
  symmetry. refine (equiv_sigma_assoc _ _). 

  equiv_via {B : FinSet & {_ : B = A & (P B * merely B.1)%type}}.
  refine (equiv_functor_sigma_id _). intro B.
  refine (equiv_adjointify _ _ _ _).
    intro w. apply (w.2.2; (w.1, w.2.1)).
    intro w. apply (fst w.2; (snd w.2; w.1)).
    intro w. apply eta_sigma.
    intro w. apply eta_sigma.

  equiv_via {w : {B : FinSet & B = A} & (P w.1 * merely w.1.1)%type}.
  refine (equiv_sigma_assoc _ _). 
  
  equiv_via (P (center {B : FinSet & B = A}).1
             * merely (center {B : FinSet & B = A}).1.1)%type.
  refine (equiv_contr_sigma _). apply equiv_idmap. 
Defined.
  

(** * Labeling *)

Definition spec_label (X : Species) 
  := spec_hprod X (spec_from_stuff (fun A => A = FSFin (card A))).

Definition stuff_spec_label (P : FinSet -> Type)
  := fun A => (P A * (A = FSFin (card A)))%type.

Lemma stuff_spec_label_correct (P : FinSet -> Type)
  : spec_from_stuff (stuff_spec_label P)
    =
    spec_label (spec_from_stuff P).
Proof.
  refine (_ @ (all_spec_from_stuff _).2^). apply path_stuff_spec. intro A.
  simpl. unfold stuff_spec_label. unfold hfiber. symmetry.

  equiv_via {x : {x : {x : _ & P x} &
     {y : {C : FinSet & C = FSFin (card C)} &
     x.1 = y.1}} & x.1.1 = A}.
Admitted.

