Require Import HoTT Arith FinSet Species.

Definition Zn (n : nat) : Species := (Unit; const (FSFin n)).

Definition spec_lower (X : Species) : Species
  := spec_derivative X.

Definition spec_raise (X : Species) : Species
  := spec_cprod (Zn (S O)) X.

Lemma raise_lower_adjoint (X Y : Species)
  : spec_hprod (spec_raise X) Y
    =
    spec_hprod X (spec_lower Y).
Proof.
  refine ((all_spec_from_stuff _).2 @ _ @ (all_spec_from_stuff _).2^).
  apply path_stuff_spec. intro A. unfold hfiber. simpl.
  
  equiv_via {w
   : {x : X.1 &
     {y : Y.1 & fs_sum (FSFin 1) (X.2 x) = Y.2 y}} &
      fs_sum (const (FSFin 1) tt) (X.2 w.1) = A}.
  refine (equiv_functor_sigma' _ _).
  refine (equiv_functor_sigma' _ _). apply unit_prod.
  intros [z x]. refine (equiv_functor_sigma_id _). intro y.
  apply equiv_path. f_ap.
  intro w. simpl. apply equiv_path. f_ap.

  equiv_via {x : X.1 & 
            {w : {y : Y.1 & fs_sum (const (FSFin 1) tt) (X.2 x) = Y.2 y} &
            fs_sum (const (FSFin 1) tt) (X.2 x) = A}}.
  symmetry. refine (equiv_sigma_assoc _ _).

  equiv_via {x : X.1 &
            {y : Y.1 & 
            {_ : fs_sum (const (FSFin 1) tt) (X.2 x) = Y.2 y &
                 fs_sum (const (FSFin 1) tt) (X.2 x) = A}}}.
  refine (equiv_functor_sigma_id _). intro x.
  symmetry. refine (equiv_sigma_assoc _ _).

  symmetry.
  equiv_via {x : X.1 &
            {w : {z : {B : FinSet & {y : Y.1 & Y.2 y = fs_sum B (FSFin 1)}} &
                 X.2 x = z.1} &
            X.2 x = A}}.
  symmetry. refine (equiv_sigma_assoc _ _).

  refine (equiv_functor_sigma_id _). intro x.
  equiv_via {z : {B : FinSet & {y : Y.1 & Y.2 y = fs_sum B (FSFin 1)}} &
     {_ : X.2 x = z.1 & X.2 x = A}}.
  symmetry. refine (equiv_sigma_assoc _ _).

  equiv_via {B : FinSet & {w : {y : Y.1 & Y.2 y = fs_sum B (FSFin 1)} &
            {_ : X.2 x = B & X.2 x = A}}}.
  symmetry. refine (equiv_sigma_assoc _ _).
  
  equiv_via {B : FinSet &
    {_ : {_ : X.2 x = B & X.2 x = A} & {y : Y.1 & Y.2 y = fs_sum B (FSFin 1)}}}.
  refine (equiv_functor_sigma_id _). intro B.
  apply equiv_sigma_symm0.

  equiv_via {B : FinSet &
   {_ : X.2 x = B & {_ : X.2 x = A & {y : Y.1 & Y.2 y = fs_sum B (FSFin 1)}}}}.
  refine (equiv_functor_sigma_id _). intro B.
  symmetry. refine (equiv_sigma_assoc _ _).

  equiv_via {w : {B : FinSet & X.2 x = B} &
                 {_ : X.2 x = A & {y : Y.1 & Y.2 y = fs_sum w.1 (FSFin 1)}}}.
  refine (equiv_sigma_assoc _ _).

  equiv_via {_ : X.2 x = A & {y : Y.1 & 
             Y.2 y = fs_sum (center {B : FinSet & X.2 x = B}).1 (FSFin 1)}}.
  refine (equiv_contr_sigma _). simpl.

  equiv_via {w : {_ : X.2 x = A & Y.1} & Y.2 w.2 = fs_sum (X.2 x) (FSFin 1)}.
  refine (equiv_sigma_assoc _ _).
  equiv_via {w : {_ : Y.1 & X.2 x = A} & Y.2 w.1 = fs_sum (X.2 x) (FSFin 1)}.
  refine (equiv_functor_sigma' _ _).
  apply equiv_sigma_symm0. intro w. apply equiv_idmap.
  equiv_via {y : Y.1 & {_ : X.2 x = A & Y.2 y = fs_sum (X.2 x) (FSFin 1)}}.
  symmetry. refine (equiv_sigma_assoc _ _).

  refine (equiv_functor_sigma_id _). intro y.
  refine (equiv_adjointify _ _ _ _).
  - intros [p q]. refine (_; _). refine (_ @ q^).
    apply path_finset. apply path_universe_uncurried.
    apply equiv_sum_symm. unfold const. simpl.


  
  

  
                                          
  

  

