Require Import HoTT Arith FinSet Species GCard.

(** * (-2)-stuff *)

Definition ensembles : Species := (FinSet; idmap).

Lemma gf_ensembles (n : nat) : gf ensembles n = gcard (BAut (Fin n)).
Proof.
  unfold gf. path_via (gcard (BAut (Fin n)) * 1).
  - f_ap. unfold hfiber. simpl. path_via (gcard Unit).
    + apply gcard_equiv'. apply equiv_contr_unit.
    + apply gcard_unit.
  - apply mult_1_r.
Defined.

Lemma contr_stuff_spec (P : FinSet -> Type) (HP : forall A, Contr (P A)) 
  : spec_from_stuff P = ensembles.
Proof.
  path_via (spec_from_stuff (fun _ => Unit)).
  - apply path_stuff_spec. intro A.
    apply equiv_contr_unit.
  - apply path_sigma_uncurried. refine (_; _).
    + apply path_universe_uncurried.
      refine (equiv_adjointify _ _ _ _).
      * apply pr1.
      * apply (fun A => (A; tt)).
      * intro A. reflexivity.
      * intro A. apply path_sigma_hprop. reflexivity.
    + simpl. apply path_arrow. intro A.
      refine ((transport_arrow _ _ _) @ _).
      refine ((transport_const _ _) @ _).
      path_via (transport idmap
      (path_universe_uncurried
         (equiv_inverse
         (equiv_adjointify pr1 (fun A0 : FinSet => (A0; tt))
            (fun A0 : FinSet => 1)
            (fun A0 : {_ : FinSet & Unit} =>
             path_sigma_hprop (let (proj1_sig, _) := A0 in proj1_sig; tt) A0
               1)))) A).1.
      f_ap. f_ap. simpl. symmetry. apply path_universe_V_uncurried. simpl.
      path_via ((equiv_inverse
            (equiv_adjointify pr1 (fun A0 : FinSet => (A0; tt))
               (fun A0 : FinSet => 1)
               (fun A0 : {_ : FinSet & Unit} =>
                path_sigma_hprop (let (proj1_sig, _) := A0 in proj1_sig; tt)
                  A0 1))) A).1.
      f_ap. apply transport_path_universe_uncurried.
Defined.

Lemma gf_contr_stuff_spec (P : FinSet -> Type) (HP : forall A, Contr (P A)) (n : nat)
  : gf (spec_from_stuff P) n = gcard (BAut (Fin n)).
Proof.
  refine (_ @ (gf_ensembles _)). f_ap.
  apply contr_stuff_spec. apply HP.
Defined.


(** ** Decidable (-1)-stuff *)

Definition inhab_delta (A : Type) (HA : Decidable A) : nat :=
  match HA with
    | inl _ => S O
    | inr _ => O
  end.

Definition ddelta (n m : nat) := inhab_delta (n = m) (decpaths_nat n m).

Lemma gf_dec_mere_stuff (P : FinSet -> Type) (HA : forall A, Decidable (P A)) 
      (HA' : forall A, IsHProp (P A)) (n : nat)
  : gf (spec_from_stuff P) n 
    = 
    (gcard (BAut (Fin n))) * (inhab_delta (P (FSFin n)) (HA (FSFin n))).
Proof.
  unfold gf. f_ap.
  simpl. path_via (gcard (P (FSFin n))).
  - apply gcard_equiv'. symmetry. apply hfiber_fibration.
  - destruct (HA (FSFin n)) as [HP | HP]; simpl.
    + path_via (gcard Unit).
      * { apply gcard_equiv'. apply if_hprop_then_equiv_Unit.
          - apply HA'.
          - apply HP. }
      * apply gcard_unit.
    + path_via (gcard Empty).
      * { apply gcard_equiv'. apply if_not_hprop_then_equiv_Empty.
          - apply HA'.
          - intro p. contradiction (HP p). }
      * apply gcard_empty.
Defined.
            
(** ** Empty stuff *)

Definition empty_spec : Species := (Empty; Empty_rec).

Lemma gf_empty_spec (n : nat) : gf empty_spec n = O.
Proof.
  unfold gf. simpl. path_via (gcard (BAut (Fin n)) * O).
  - f_ap. path_via (gcard Empty). 
    + apply gcard_equiv'. unfold hfiber.
      refine (BuildEquiv _ _ _ _). intros [x p]. contradiction.
    + apply gcard_empty.
  - apply mult_O_r.
Defined.


(** *** $n$-element set *)

Definition n_element_spec (n : nat) : Species 
  := spec_from_stuff (fun A => card A = n).

Lemma gf_n_element_spec (n m : nat) 
  : gf (n_element_spec n) m = (gcard (BAut (Fin m))) * (ddelta n m).
Proof.
  unfold n_element_spec.
  (* Universe inconsistencies with [gf_dec_mere_stuff]? *)
Admitted.


(** *** inhabited finite sets *)

Definition inhab_ensembles := spec_inhab ensembles.

Lemma gf_inhab_ensembles (n : nat)
  : gf inhab_ensembles n = (gcard (BAut (Fin n))) * (1 - (ddelta n O)).
Proof. 
  unfold gf. f_ap. unfold ddelta. unfold inhab_delta.
  destruct (decpaths_nat n O).
  - refine (_ @ gcard_empty). apply gcard_equiv'.
    refine (BuildEquiv _ _ _ _).
    intros [[A a] q]. simpl in *. strip_truncations.
    change Empty with (Fin O). apply (transport _ p).
    (* More universe inconsistencies *)
    admit.
  - refine (_ @ gcard_unit). apply gcard_equiv'.
    refine (equiv_adjointify _ _ _ _).
    + intro z. apply tt.
    + intro z. refine ((FSFin n; _); 1). 
      apply tr. apply (transport _ (S_predn n n0)). apply (inr tt).
    + intro z. apply eta_unit.
    + intros [[A a] p]. apply path_sigma_uncurried. refine (_; _).
      * apply path_sigma_hprop. apply p^.
      * simpl in *.
        unfold path_sigma_hprop.
        path_via (transport
                    (fun w  => w = FSFin n)
                    (pr1^-1 p^).1 1).
        f_ap. 
        refine (@transport_pr1_path_sigma_uncurried
                  _
                  (Trunc (-1) o pr1)
                  (FSFin n; tr (transport Fin (S_predn n n0) (inr tt)))
                  (A; a)
                  _
                  (fun w => w = FSFin n)). 
        simpl. induction p. reflexivity.
Defined.

Definition COSH
  := spec_from_stuff (fun A => {n : nat & card A = (2 * n)}).
Definition SINH
  := spec_from_stuff (fun A => {n : nat & card A = S (2 * n)}).

Lemma even_or_odd__ensembles
  : spec_sum COSH SINH = ensembles.
Proof.
    (* Universe problems again *)
Admitted.


(** ** 0-stuff *)

Definition Zn (n : nat) : Species := (Unit; const (FSFin n)).

Lemma gf_Zn (n m : nat) : gf (Zn n) m = ddelta n m.
Proof.
  unfold gf, hfiber, ddelta. simpl.
  destruct (decpaths_nat n m); simpl.
  - path_via (gcard (BAut (Fin m)) * gcard (FSFin n = FSFin m)). 
    + f_ap. apply gcard_equiv'.
      refine (equiv_adjointify _ _ _ _).
      * intros [z q]. apply q.
      * intro q. apply (tt; q).
      * intro q. reflexivity.
      * intros [z q]. induction z. reflexivity.
    + admit. (* need the full [gcard] *)
  - path_via (gcard (BAut (Fin m)) * O).
    + f_ap. refine (_ @ gcard_empty). apply gcard_equiv'.
      refine (BuildEquiv _ _ _ _).
      intros [z p]. contradiction n0.
      apply Fn_Fm__n_m. apply p..1.
    + apply mult_O_r.
Defined.
      