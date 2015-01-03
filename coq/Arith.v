Require Import HoTT Nat.

Fixpoint plus (n m : nat) :=
  match n with
    | O => m
    | S n' => S (n' + m)
  end
    
where "n + m" := (plus n m) : nat_scope.

Definition lt (n m : nat) := {k : nat & n + S k = m}.
Notation "n < m" := (lt n m) (at level 70) : nat_scope.

Theorem O_S : forall n : nat, O <> S n.
Proof.
  intros n H. apply nat_encode in H. contradiction.
Defined.

Lemma plus_n_Sm : forall n m : nat, n + S m = S (n + m).
Proof.
  intro n. induction n. 
  - reflexivity.
  - intro m. apply (ap S). apply IHn.
Defined.
  
Lemma n_lt_O : forall n, ~ (n < O).
Proof.
  intros n w.
  induction w as [m p].
  simpl in p.
  apply (O_S (n + m)).
  path_via (n + S m).
  apply plus_n_Sm.
Defined.

Lemma plus_n_O : forall n, n = n + O.
Proof.
  induction n; simpl.
  - reflexivity.
  - apply (ap S IHn).
Defined.

Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  induction n.
  - intro m. apply plus_n_O.
  - intro m. refine (_ @ (plus_n_Sm _ _)^). apply (ap S). apply IHn.
Defined.

Lemma plus_n_k : forall n k, n + k = O -> n = O.
Proof.
  induction n.
  - reflexivity.
  - intros k p. simpl in p. contradiction (O_S _ p^).
Defined.


Lemma plus_O_r (n : nat) : n + O = n.
Proof.
  induction n.
  - reflexivity.
  - apply (ap S IHn).
Defined.


Lemma cancelL_plus : forall n m k, n + m = n + k -> m = k.
Proof.
  induction n.
  - intros m k p. apply p.
  - intros m k p. apply IHn. apply S_inj. apply p.
Defined.

Lemma cancelR_plus : forall n m k, m + n = k + n -> m = k.
Proof.
  induction n.
  - intros m k p. 
    path_via (m + O). symmetry. apply plus_O_r.
    path_via (k + O). apply plus_O_r.
  - intros m k p. apply IHn.
    apply S_inj. simpl.
    path_via (m + S n). symmetry. apply plus_n_Sm.
    path_via (k + S n). apply plus_n_Sm.
Defined.
  

Global Instance ishprop_lt : forall n m, IsHProp (n < m).
Proof.
  intros n m. apply hprop_allpath. intros x y.
  induction x as [k p], y as [r q].
  apply path_sigma_hprop. simpl.
  apply (S_inj _ _). apply (cancelL_plus n).
  path_via m.
Defined.

Lemma S_predn (n : nat) : n <> O -> S (pred n) = n.
Proof.
  induction n; intro p; [contradiction p |]; reflexivity.
Defined.
    

Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O, _ => n
    | S k, O => n
    | S k, S l => k - l
  end

where "n - m" := (minus n m) : nat_scope.

Lemma minus_O_r (n : nat) : n - O = n.
Proof.
  by induction n.
Defined.

Lemma minus_n_n (n : nat) : n - n = O.
Proof.
  induction n.
  - reflexivity.
  - apply IHn.
Defined.

Lemma not_nltn (n : nat) : ~ (n < n).
Proof.
  intro p. induction p as [k p].
  apply (O_S k). symmetry.
  apply (cancelL_plus n).
  path_via n.
  symmetry. apply plus_O_r.
Defined.
  

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => m + n' * m
  end
    
where "n * m" := (mult n m) : nat_scope.

Lemma cancelL_plus_lt (n m k : nat) : (n + m < n + k) -> (m < k).
Proof.
  induction n.
  - apply idmap.
  - intro p. apply IHn.
    destruct p as [l r]. exists l. apply S_inj. path_via (S n + m + S l). 
Defined.

Lemma plus_assoc : forall n m k, (n + m) + k = n + (m + k).
Proof.
  induction n.
  - reflexivity.
  - intros m k. simpl. apply (ap S (IHn m k)).
Defined.


Lemma mult_1_r (n : nat) : n * 1 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply (ap S IHn).
Defined.

Lemma mult_O_r (n : nat) : n * O = O.
Proof.
  induction n.
  - reflexivity.
  - apply IHn.
Defined.

Lemma nat_dist_l (n m k : nat) : n * (m + k) = (n * m) + (n * k).
Proof.
  induction n.
  - reflexivity.
  - refine ((ap (plus (m + k)) IHn) @ _).
    refine (_ @ (plus_assoc _ _ _)).
    refine ((plus_assoc _ _ _)^ @ _).
    apply (ap (fun s => s + (n * k))). 
    refine ((plus_assoc _ _ _) @ _).
    refine (_ @ (plus_assoc _ _ _)^).
    apply (ap (plus m)).
    apply plus_comm.
Defined.

Lemma nat_dist_r (n m k : nat) : (n + m) * k = (n * k) + (m * k).
Proof.
  induction n.
  - reflexivity.
  - refine (_ @ (plus_assoc _ _ _)^).
    apply (ap (plus k) IHn).
Defined.


Lemma mult_assoc (n m k : nat) : (n * m) * k = n * (m * k).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    refine (_ @ (ap (fun s => (m * k) + s) IHn)).
    apply (nat_dist_r m (n * m) k).
Defined.

Lemma mult_comm (n m : nat) : n * m = m * n.
Proof.
  induction n.
  - symmetry. apply mult_O_r.
  - refine ((ap (plus m) IHn) @ _).
    refine (_ @ (nat_dist_l m 1 n)^).
    f_ap. symmetry. apply mult_1_r.
Defined.
    

(** * Exponential *)

Fixpoint exp (b e : nat) :=
  match e with
    | O => S O
    | S e' => b * (exp b e')
  end.

Lemma exp_sum (b n m : nat) : (exp b (n + m)) = (exp b n) * (exp b m).
Proof.
  induction n.
  - symmetry. apply plus_O_r.
  - refine (_ @ (mult_assoc _ _ _)^). simpl. f_ap.
Defined.

Lemma exp_power (b n m : nat) : (exp (exp b n) m) = (exp b (n * m)).
Proof.
  induction m.
  - apply (ap (exp b) (mult_O_r n))^.
  - refine ((ap (mult (exp b n)) IHm) @ _).
    refine ((exp_sum _ _ _)^ @ _). f_ap.
    refine (_ @ (mult_comm _ _)^).
    simpl. f_ap. apply mult_comm.
Defined.


(** * Factorial *)

Fixpoint fact (n : nat) : nat :=
  match n with
    | O => (S O)
    | S n' => S n' * fact n'
  end.

Lemma fact_ne_O : forall n : nat, fact n <> O.
Proof.
  induction n.
  - intro p. apply (O_S _ p^).
  - simpl. intro p. apply plus_n_k in p. contradiction.
Defined.

Lemma O_lt_Sn (n : nat) : O < S n.
Proof.
  exists n. reflexivity.
Defined.

Definition le (n m : nat) := {k : nat & n + k = m}.
Notation "n <= m" := (le n m) (at level 70) : nat_scope.

Lemma le_partition (n : nat) : forall m, (m <= n) + (n < m).
Proof.
  induction n, m.
  - left. exists O. reflexivity.
  - right. apply O_lt_Sn.
  - left. exists (S n). reflexivity.
  - destruct (IHn m) as [H | H]; [left | right];
      destruct H as [k p]; exists k; simpl; apply (ap S); apply p.
Defined.

(** * Division *)

Fixpoint sgn (n : nat) :=
  match n with
    | O => O
    | S n' => (S O)
  end.

Definition adf (n m : nat) := (n - m) + (m - n).

Lemma dec_nat (n m : nat) : (n = m) + ~ (n = m).
Admitted.

Fixpoint rem (n m : nat) :=
  match n with
    | O => O
    | S n' => match m with
                | O => O
                | S m' => match (dec_nat (rem n' (S m')) m') with
                            | inl _ => O
                            | inr _ => S (rem n' (S m'))
                          end
              end
  end.

Fixpoint quot (n m : nat) :=
  match n with
    | O => O
    | S n' => match m with
                | O => O
                | S m' => match (dec_nat (rem (S n') m') O) with
                            | inl _ => S (quot n' (S m'))
                            | inr _ => quot n' (S m')
                          end
              end
  end.

Definition nPk (n k : nat) := 
  match (le_partition n k) with
    | inl _ => quot (fact n) (fact (n - k))
    | inr _ => O
  end.

Definition nCk (n k : nat) := quot (nPk n k) (fact k).

Lemma quot_n_1 (n : nat) : quot n 1 = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. destruct (dec_nat O O). 
    + apply (ap S IHn).
    + contradiction (n0 1).
Defined.

Lemma quot_n_n (n : nat) : (n <> O) -> (quot n n = 1%nat).
Admitted.

Lemma quot_plus (n m d : nat) : (quot n d) + (quot m d) = quot (n + m) d.
Admitted.

Lemma quot_mult (n1 n2 d1 d2 : nat) 
  : (quot n1 d1) * (quot n2 d2) = quot (n1 * n2) (d1 * d2).
Admitted.

Lemma nCO (n : nat) : nCk n O = (S O).
Proof.
  induction n.
  - unfold nCk. unfold nPk. simpl. destruct (dec_nat O O).
    + simpl. destruct (dec_nat O O).
      * reflexivity.
      * contradiction (n 1).
    + contradiction (n 1).
  - unfold nCk in *. unfold nPk in *. simpl in *.
    refine ((quot_n_1 _) @ _). apply quot_n_n. apply (fact_ne_O (S n)).
Defined.

Lemma nCn (n : nat) : nCk n n = (S O).
Proof.
  induction n.
  - unfold nCk. refine ((quot_n_1 _) @ _).
    unfold nPk. simpl. destruct (dec_nat O O).
    + reflexivity.
    + contradiction (n 1).
  - unfold nCk. simpl. unfold nPk.
    destruct (le_partition (S n) (S n)).
    + rewrite minus_n_n. rewrite quot_n_1. apply quot_n_n.
      apply (fact_ne_O (S n)).
    + destruct l as [m p].
      contradiction (O_S m). symmetry.
      apply (cancelL_plus (S n)). refine (p @ _).
      symmetry. apply plus_O_r.
Defined.

Lemma nPO (n : nat) : nPk n O = (S O).
Proof.
  induction n.
  - unfold nPk. simpl. destruct (dec_nat O O).
    + reflexivity.
    + contradiction (n 1).
  - unfold nPk. simpl. apply quot_n_n.
    apply (fact_ne_O (S n)).
Defined.

Lemma OPO : nPk O O = (S O).
Proof.
  unfold nPk. simpl. destruct (dec_nat O O).
  - reflexivity.
  - contradiction (n 1).
Defined.

Lemma OPn (n : nat) : (n <> O) -> (nPk O n = O).
Proof.
  intro p. unfold nPk. destruct (le_partition O n).
  - contradiction p. destruct l as [m q]. apply (plus_n_k _ _ q).
  - reflexivity.
Defined.

Lemma nPn (n : nat) : nPk n n = fact n.
Proof.
  induction n.
  - unfold nPk. simpl. destruct (dec_nat O O).
    + reflexivity.
    + contradiction (n 1).
  - unfold nPk. simpl. destruct (le_partition n n).
    + path_via (quot (fact (S n)) (S O)).
      * f_ap. path_via (fact O). f_ap. apply minus_n_n.
      * apply quot_n_1.
    + contradiction (not_nltn _ l).
Defined.

Lemma SnPSk (n k : nat) : nPk (S n) (S k) = (S n) * (nPk n k).
Proof.
  unfold nPk. simpl. destruct (le_partition n k).
  - symmetry. 
    path_via (quot (fact n) (fact (n - k)) + quot (n * (fact n)) (fact (n - k))).
    + f_ap. path_via (quot n 1 * quot (fact n) (fact (n - k))).
      * f_ap. symmetry. apply quot_n_1.
      * refine ((quot_mult _ _ _ _) @ _). f_ap. apply plus_O_r.
    + apply quot_plus.
  - simpl. symmetry. apply mult_O_r.
Defined.
  
Lemma nP1 (n : nat) : nPk n 1 = n.
Proof.
  induction n.
  - reflexivity.
  - unfold nPk. destruct (le_partition (S n) 1).
    + refine ((quot_plus _ _ _)^ @ _).
      path_via (1 + quot (n * fact n) (fact ((S n) - 1))).
      * refine (ap (fun s => s + quot (n * fact n) (fact ((S n) - 1))) _).
        simpl. path_via (quot (fact n) (fact n)). f_ap. f_ap. apply minus_O_r.
        apply quot_n_n. apply (fact_ne_O n).
      * apply (ap S). path_via (quot (n * fact n) (1 * fact n)).
        f_ap. simpl. refine (ap fact (minus_O_r n) @ (plus_O_r _)^).
        refine ((quot_mult _ _ _ _)^ @ _).
        refine (_ @ (quot_n_1 n)). refine (_ @ (mult_1_r _)).
        apply (ap (mult (quot n 1))). apply quot_n_n. apply fact_ne_O.
    + destruct l as [m p].
      simpl in p. apply S_inj in p.
      contradiction (O_S (n + m)). refine (p^ @ _).
      apply plus_n_Sm.
Defined.
      
      
      
Lemma foo (n k : nat)
  : quot n.+1 k.+1 = 1 + quot (nPk n k.+1) (fact k.+1).
Proof.
  induction k.
  - refine ((quot_n_1 _) @ _). apply (ap S).
    symmetry. refine ((quot_n_1 _) @ (nP1 _)). 
Admitted.

Lemma SnCSk (n k : nat) : nCk (S n) (S k) = (nCk n k) + (nCk n (S k)).
Proof.
Admitted.
