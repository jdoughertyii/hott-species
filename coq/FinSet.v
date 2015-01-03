Require Import HoTT Arith Nat.
Require Import UnivalenceAxiom.

Fixpoint Fin (n : nat) :=
  match n with
    | O => Empty
    | S n' => (Fin n' + Unit)%type
  end.

Definition IsFinSet (A : Type) : Type := {n : nat & merely (A = Fin n)}.
Definition FinSet : Type := {A : Type & IsFinSet A}.
Definition FSFin (n : nat) : FinSet := (Fin n; (n; tr 1)).
Definition card (A : FinSet) : nat := A.2.1.

Lemma decpaths_fin {n : nat} : DecidablePaths (Fin n).
Proof.
  induction n.
  - intro r. contradiction.
  - intros x y. induction x, y.
    + destruct (IHn a f) as [p|p].
      * left. f_ap.
      * right. intro q. apply p. apply (path_sum_inl q).
    + right. apply inl_ne_inr.
    + right. intro p. apply (inl_ne_inr _ _ p^).
    + left. f_ap. path_via tt; [symmetry|]; apply eta_unit.
Defined.

Global Instance isset_fin (n : nat) : IsHSet (Fin n).
Proof.
  apply hset_decpaths. apply decpaths_fin.
Defined.


Definition fmax (n : nat) : Fin (S n) := inr tt.

Definition Fin_lift {n : nat} : Fin n -> Fin (S n) := inl.

Definition Fin_lower {n : nat} (z : Fin (S n))
  : (z <> (fmax n)) -> Fin n.
Proof.
  intro p.
  induction z as [z | t].
  - apply z.
  - contradiction p. unfold fmax. f_ap. symmetry. apply eta_unit.
Defined.


Lemma Fin_lift_lower {n : nat} (z : Fin (S n)) (p : z <> (fmax n)) :
  Fin_lift (Fin_lower z p) = z.
Proof.
  induction z as [z | t].
  - reflexivity.
  - contradiction p. unfold fmax. f_ap. apply symmetry, eta_unit.
Defined.

Definition Fin_lift_ne_fmax {n : nat} (z : Fin n) : Fin_lift z <> (fmax n)
  := inl_ne_inr _ _.
  

Lemma cancelR_Fn_U (n m : nat) 
  : Fin (S n) = Fin (S m) -> Fin n = Fin m.
Proof.
  intro f. apply equiv_path in f. apply path_universe_uncurried.
  (* There are two cases: either [f] matches Sn with Sm or not. *)
  destruct (decpaths_fin (f (fmax n)) (fmax m)).
  
  (* if it does, then we just need to restrict f *)
  - refine (equiv_adjointify _ _ _ _).
    + intro z. refine (Fin_lower (f (Fin_lift z)) _).
      intro q. apply (Fin_lift_ne_fmax z). apply (ap f)^-1.
      apply (q @ p^).
    + intro z. refine (Fin_lower (f^-1 (Fin_lift z)) _).
      intro q. apply (Fin_lift_ne_fmax z). apply (ap f^-1)^-1.
      refine (q @ _). apply (ap f)^-1.
      refine (p @ _). apply (eisretr _ _)^.
    + intro z. 
      apply (@path_sum_inl (Fin m) Unit). refine ((Fin_lift_lower _ _) @ _).
      apply (ap f^-1)^-1. refine ((eisretr f^-1 _) @ _).
      refine ((Fin_lift_lower _ _) @ _). f_ap.
    + intro z.
      apply (@path_sum_inl (Fin n) Unit). refine ((Fin_lift_lower _ _) @ _).
      apply (ap f)^-1. refine ((eissect f^-1 _) @ _).
      refine ((Fin_lift_lower _ _) @ _). f_ap.
      
  (* otherwise, we need to "correct" where it leaves [Fin (S m)] *)
  - refine (equiv_adjointify _ _ _ _).
    + intro z. destruct (decpaths_fin (f (Fin_lift z)) (fmax m)).
      * refine (Fin_lower (f (fmax n)) _). apply n0.
      * refine (Fin_lower (f (Fin_lift z)) n1).
    + intro z. destruct (decpaths_fin (Fin_lift z) (f (fmax n))).
      * refine (Fin_lower (f^-1 (fmax m)) _). intro q. apply n0.
        apply (ap f^-1)^-1. refine ((eissect _ _) @ q^).
      * refine (Fin_lower (f^-1 (Fin_lift z)) _).
        intro p. apply n1. apply (ap f^-1)^-1. refine (p @ (eissect _ _)^).
    + intro z. destruct (decpaths_fin (Fin_lift z) (f (fmax n))).
      * simpl. rewrite Fin_lift_lower. rewrite eisretr. simpl.
        apply (@path_sum_inl (Fin m) Unit).
        refine ((Fin_lift_lower _ _) @ p^).
      * simpl. rewrite Fin_lift_lower. rewrite eisretr. reflexivity.
    + intro z. destruct (decpaths_fin (f (Fin_lift z)) (fmax m)).
      * { simpl (let d := inl p in
                 match d with
                   | inl _ => Fin_lower (f (fmax n)) n0
                   | inr n1 => Fin_lower (f (Fin_lift z)) n1
                 end).
          rewrite Fin_lift_lower.
          destruct (decpaths_fin (f (fmax n)) (f (fmax n))).
          - simpl. apply (@path_sum_inl (Fin n) Unit).
            refine ((Fin_lift_lower _ _) @ _).
            apply (ap f)^-1. refine ((eisretr _ _) @ p^).
          - contradiction (n1 1). }
      * { simpl (let d := inr n1 in
                 match d with
                   | inl _ => Fin_lower (f (fmax n)) n0
                   | inr n2 => Fin_lower (f (Fin_lift z)) n2
                 end).
          rewrite Fin_lift_lower.
          destruct (decpaths_fin (f (Fin_lift z)) (f (fmax n))).
          - contradiction (Fin_lift_ne_fmax z). apply (ap f)^-1. apply p.
          - simpl. apply (@path_sum_inl (Fin n) Unit).
            refine ((Fin_lift_lower _ _) @ _).
            refine (eissect _ _). }
Defined.

Lemma Fn_Fm__n_m : forall n m, Fin n = Fin m -> n = m.
Proof.
  induction n, m.
  - intro p. reflexivity.
  - intro p. contradiction ((equiv_path _ _ p)^-1 (inr tt)).
  - intro p. contradiction ((equiv_path _ _ p) (inr tt)).
  - intro p. apply (ap S). apply IHn. apply cancelR_Fn_U. apply p.
Defined.
    

Global Instance hprop_isfinset (A : Type) : IsHProp (IsFinSet A).
Proof.
  apply hprop_allpath.
  intros w w'. induction w as [n p], w' as [m q].
  apply path_sigma_hprop. simpl.
  strip_truncations.
  apply Fn_Fm__n_m.
  apply (p^ @ q).
Defined.

Global Instance isset_isfinset (A : FinSet) : IsHSet A.1.
Proof.
  induction A as [A [n p]]. simpl.
  strip_truncations. apply (trunc_equiv' (Fin n)).
  apply (equiv_inverse (equiv_path _ _ p)).
  apply isset_fin.
Defined.

Definition path_finset (A B : FinSet) : A.1 = B.1 -> A = B 
  := path_sigma_hprop A B.

Definition isequiv_path_finset (A B : FinSet) : IsEquiv (path_finset A B)
  := isequiv_path_sigma_hprop.

Definition equiv_path_finset (A B : FinSet) : A.1 = B.1 <~> A = B
  := equiv_path_sigma_hprop A B.

   
Lemma Finset_equiv_FinSetcard 
  : FinSet <~> {A : Type & {n : nat & @tr 0 Type A = @tr 0 Type (Fin n)}}.
Proof.
  refine (equiv_functor_sigma' (equiv_idmap Type) _). intro A.
  refine (equiv_functor_sigma' (equiv_idmap nat) _). intro n.
  apply equiv_path_Tr.
Defined.


Lemma sum_Fn_Fm : forall n m, (Fin n + Fin m)%type <~> Fin (n + m).
Proof.
  induction n.
  - intro m. apply empty_sum.
  - intro m. equiv_via (Fin n + Fin m + Unit)%type.
    + equiv_via (Fin n + (Unit + Fin m))%type.
      * apply equiv_sum_assoc.
      * {equiv_via (Fin n + (Fin m + Unit))%type.
         - apply equiv_functor_sum'.
           + apply equiv_idmap.
           + apply equiv_sum_symm.
         - apply equiv_inverse, equiv_sum_assoc. }
    + simpl. apply equiv_functor_sum'.
      * apply IHn.
      * apply equiv_idmap.
Defined.

Definition fs_sum (A B : FinSet) : FinSet.
Proof.
  induction A as [A [n p]], B as [B [m q]].
  exists (A + B)%type. exists (n + m).
  strip_truncations. apply tr.
  
  path_via (Fin n + Fin m)%type.
  path_via (A + Fin m)%type. 
  apply (ap (fun s => (A + s)%type) q).
  apply (ap (fun s => (s + Fin m)%type) p).
  apply path_universe_uncurried.
  apply sum_Fn_Fm.
Defined.



Definition path_fs_sum (A B C : FinSet) 
  : (sum A.1 B.1 = C.1) -> (fs_sum A B) = C
  := path_finset (fs_sum A B) C.

Definition isequiv_path_fs_sum (A B C : FinSet) 
  : IsEquiv (path_fs_sum A B C)
  := isequiv_path_finset (fs_sum A B) C.

Definition equiv_path_fs_sum (A B C : FinSet)
  : (sum A.1 B.1 = C.1) <~> (fs_sum A B) = C
  := equiv_path_finset (fs_sum A B) C.


Lemma unit_prod (A : Type) : Unit * A <~> A.
Proof.
  refine (equiv_adjointify snd (fun a => (tt, a)) _ _).
  - intros a. reflexivity.
  - intros [t a]. apply path_prod. apply eta_unit. reflexivity.
Defined.

Lemma sum_prod_dist (A B C : Type) : (A + B) * C <~> (A * C) + (B * C).
Proof.
  refine (equiv_adjointify _ _ _ _).
  - intros [[a | b] c]. apply (inl (a, c)). apply (inr (b, c)).
  - intros [[a c] | [b c]]. apply (inl a, c). apply (inr b, c).
  - intros [[a c] | [b c]]; reflexivity.
  - intros [[a | b] c]; reflexivity.
Defined.

Lemma prod_Fn_Fm (n m : nat) : Fin n * Fin m <~> Fin (n * m).
Proof.
  generalize dependent m.
  induction n.
  - intro m. apply empty_prod.
  - intro m. equiv_via ((Fin n * Fin m) + (Unit * Fin m))%type.
    + apply sum_prod_dist.
    + equiv_via (Fin (n * m) + Fin m)%type.
      * { apply equiv_functor_sum'.
          - apply IHn.
          - apply unit_prod. }
      * { equiv_via (Fin m + Fin (n * m))%type.
          - apply equiv_sum_symm.
          - apply sum_Fn_Fm. }
Defined.

Definition fs_prod (A B : FinSet) : FinSet.
Proof.
  induction A as [A [n p]], B as [B [m q]].
  refine ((A * B)%type; (n * m; _)).
  strip_truncations. apply tr.
  apply path_universe_uncurried.
  equiv_via (Fin n * Fin m)%type.
  - apply equiv_functor_prod'.
    + apply (equiv_path _ _ p).
    + apply (equiv_path _ _ q).
  - apply prod_Fn_Fm.
Defined.
    
Lemma arrow_Fn_Fm (n m : nat) : (Fin n -> Fin m) <~> Fin (exp m n).
Proof.
  induction n, m.
  - refine (equiv_adjointify (fun _ => inr tt) (fun _ => idmap) _ _).
    + intro z. induction z. contradiction a. f_ap. apply eta_unit.
    + intro z. apply path_arrow. intro b. contradiction b.
  - refine (equiv_adjointify (fun _ => inr tt) (fun _ z => Empty_rect _ z) _ _).
    + intro z. destruct z as [z | z].
      * contradiction z.
      * f_ap. apply eta_unit.
    + intro f. apply path_arrow. intro z. contradiction.
  - refine (equiv_adjointify (fun f => f (fmax n)) (fun a => Empty_rect _ a) _ _).
    + intro a. contradiction a.
    + intro f. apply path_arrow. intro w. contradiction (f w).
  - equiv_via (Fin (exp (S m) n) + (Fin m) * Fin (exp (S m) n))%type.
    + refine (equiv_adjointify _ _ _ _).
      * { intro f. destruct (decpaths_fin (f (fmax n)) (fmax m)).
          - left. apply IHn. intro z. apply (f (Fin_lift z)).
          - right. split.
            + apply (Fin_lower (f (fmax n)) n0).
            + apply IHn. intro z. apply (f (Fin_lift z)). }
      * { intros [z | [imax z]].
          - intro w. destruct (decpaths_fin w (fmax n)).
            + apply (fmax m).
            + apply (IHn^-1 z). refine (Fin_lower w n0).
          - intro w. destruct (decpaths_fin w (fmax n)).
            + apply (Fin_lift imax).
            + apply (IHn^-1 z). refine (Fin_lower w n0). }
      * { intros [z | [imax z]]. 
          - simpl. f_ap. apply (ap IHn^-1)^-1. apply eissect.
          - simpl. f_ap. apply path_prod.
            + reflexivity.
            + simpl. apply (ap IHn^-1)^-1. apply eissect. }
      * { intro f. destruct (decpaths_fin (f (fmax n)) (fmax m)).
          - apply path_arrow. intro w. destruct w as [w | w].
            + simpl. refine (ap10 _ w).
              * apply (f o Fin_lift).
              * apply eissect.
            + simpl. refine (p^ @ _). unfold fmax. f_ap. f_ap. apply eta_unit.
          - apply path_arrow. intro w. destruct w as [w | w].
            + simpl. refine (ap10 _ w).
              * apply (f o Fin_lift).
              * apply eissect.
            + simpl. refine ((Fin_lift_lower _ _) @ _).
              unfold fmax. f_ap. f_ap. apply eta_unit. }
    + equiv_via (Fin (exp (S m) n) + Fin (m * exp (S m) n))%type.
      * { apply equiv_functor_sum'.
          - apply equiv_idmap.
          - apply prod_Fn_Fm. }
      * apply sum_Fn_Fm.
Defined.

Definition fs_arrow (A B : FinSet) : FinSet.
Proof.
  induction A as [A [n p]], B as [B [m q]].
  refine ((A -> B); ((exp m n); _)).
  strip_truncations. apply tr.
  apply path_universe_uncurried.
  equiv_via (Fin n -> Fin m).
  + apply equiv_functor_arrow'.
    * apply (equiv_path _ _ p^).
    * apply (equiv_path _ _ q).
  + apply arrow_Fn_Fm.
Defined.


(** * Partitions *)

Definition fin_indexed_sum (n : nat) (P : Fin n -> FinSet) : FinSet.
Proof.
  induction n.
  - apply (FSFin O).
  - refine (fs_sum (IHn (P o Fin_lift)) (P (fmax n))).
Defined.

Definition partition (A : FinSet) (n : nat) (P : Fin n -> FinSet)
  := (A = fin_indexed_sum n P).

