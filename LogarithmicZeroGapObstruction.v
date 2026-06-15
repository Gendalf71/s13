From Coq Require Import Arith Lia Reals Rpower ZArith Ring Lra Psatz.
From Coq Require Import Arith.PeanoNat.

(* This module formally verifies the inverse real parameterization,
   positive nth roots, construction and uniqueness of positive normalizing
   scales for positive cores, the exact logarithmic coefficient invariant,
   its zeros and positivity above exponent two, and the logical strength of
   the zero-gap bridge.

   It does not prove Fermat's Last Theorem and does not prove the bridge as
   an independent arithmetic fact.  Legacy theorems may retain explicit
   factorization hypotheses for compatibility.  The finite-sum/binomial
   and continuous monotonicity/limit targets are recorded below where they
   are not fully discharged by this elementary standard-library file. *)

Local Open Scope Z_scope.
Lemma Z_sub_split (a b c : Z) : a - b = (a - c) + (c - b). Proof. ring. Qed.
Lemma Zpow_diff_divides (x y : Z) (n : nat) :
  Z.divide (x - y) (Z.pow x (Z.of_nat n) - Z.pow y (Z.of_nat n)).
Proof.
  induction n as [|n IH].
  - simpl; exists 0%Z; ring.
  - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    rewrite !Z.pow_add_r by lia; rewrite !Z.pow_1_r.
    set (ux := Z.pow x (Z.of_nat n)) in *; set (uy := Z.pow y (Z.of_nat n)) in *.
    destruct IH as [r Hr].
    rewrite Z.mul_comm with (n:=ux) (m:=x); rewrite Z.mul_comm with (n:=uy) (m:=y).
    rewrite (Z_sub_split (x*ux) (y*uy) (x*uy)).
    replace (x * ux - x * uy) with (x*(ux-uy)) by ring.
    replace (x * uy - y * uy) with ((x-y)*uy) by ring.
    rewrite Hr; exists (x*r+uy); ring.
Qed.
Lemma odd_n_diff_pow_even (a b : Z) (n : nat) :
  Nat.odd n = true -> Z.divide 2 (Z.pow (a+b) (Z.of_nat n) - Z.pow (a-b) (Z.of_nat n)).
Proof.
  intro H; apply Nat.odd_spec in H; destruct H as [k Hk]; subst n.
  replace (Z.of_nat (2*k+1)) with (Z.of_nat (S (2*k))) by lia.
  destruct (Zpow_diff_divides (a+b) (a-b) (S (2*k))) as [r Hr].
  replace ((a+b)-(a-b)) with (2*b) in Hr by ring.
  exists (b*r); rewrite Hr; ring.
Qed.
Close Scope Z_scope.

Local Open Scope R_scope.
Lemma sum_diff_from_parameters_R (n:nat) (m p:R) :
  let z := pow m n + pow p n in let x := pow m n - pow p n in
  z + x = 2*pow m n /\ z - x = 2*pow p n.
Proof. intros z x; unfold z, x; split; ring. Qed.

Lemma inverse_symmetrization_R (z x:R) :
  let u := (z+x)/2 in let v := (z-x)/2 in z = u+v /\ x = u-v.
Proof. intros u v; unfold u, v; split; field. Qed.
Lemma inverse_symmetrization_positive_R (z x:R) : z > x -> x > 0 ->
  let u := (z+x)/2 in let v := (z-x)/2 in u > v /\ v > 0.
Proof. intros Hzx Hx u v; split; unfold u,v; lra. Qed.


(* Positive nth roots built with the standard-library Rpower. *)
Definition positive_nth_root (n : nat) (u : R) : R := Rpower u (/ INR n).
Definition is_positive_nth_root (n : nat) (u r : R) : Prop := 0 < r /\ pow r n = u.

Lemma Rpower_pos_of_pos (x a : R) : 0 < x -> 0 < Rpower x a.
Proof. intro Hx; unfold Rpower; apply exp_pos. Qed.

Lemma positive_nth_root_pow (n : nat) (u : R) :
  (0 < n)%nat -> 0 < u -> pow (positive_nth_root n u) n = u.
Proof.
  intros Hn Hu; unfold positive_nth_root.
  rewrite <- Rpower_pow by (apply Rpower_pos_of_pos; exact Hu).
  rewrite Rpower_mult.
  replace (/ INR n * INR n) with 1 by (field; apply not_0_INR; lia).
  apply Rpower_1; exact Hu.
Qed.

Lemma positive_nth_root_exists (n : nat) (u : R) :
  (0 < n)%nat -> 0 < u -> exists r : R, is_positive_nth_root n u r.
Proof.
  intros Hn Hu; exists (positive_nth_root n u); split.
  - apply Rpower_pos_of_pos; exact Hu.
  - apply positive_nth_root_pow; assumption.
Qed.

Lemma positive_nth_root_unique (n : nat) (u r1 r2 : R) :
  (0 < n)%nat -> is_positive_nth_root n u r1 -> is_positive_nth_root n u r2 -> r1 = r2.
Proof.
  intros Hn [Hr1 Er1] [Hr2 Er2].
  apply ln_inv; try assumption.
  apply Rmult_eq_reg_l with (r := INR n).
  - rewrite <- !ln_pow by assumption. now rewrite Er1, Er2.
  - apply not_0_INR; lia.
Qed.

Lemma positive_nth_root_strict_mono (n : nat) (u v : R) :
  (0 < n)%nat -> 0 < v -> v < u -> positive_nth_root n v < positive_nth_root n u.
Proof.
  intros Hn Hv Hvu; unfold positive_nth_root.
  apply Rlt_Rpower_l.
  - apply Rinv_0_lt_compat; apply lt_0_INR; lia.
  - split; [exact Hv|exact Hvu].
Qed.

Theorem inverse_symmetrization_positive_roots (n : nat) (u v : R) :
  (0 < n)%nat -> 0 < v -> v < u ->
  let m := positive_nth_root n u in
  let p := positive_nth_root n v in
  0 < p /\ p < m /\ pow m n = u /\ pow p n = v.
Proof.
  intros Hn Hv Hvu m p; repeat split.
  - unfold p, positive_nth_root; apply Rpower_pos_of_pos; exact Hv.
  - unfold p, m; apply positive_nth_root_strict_mono; assumption.
  - unfold m; apply positive_nth_root_pow; [assumption|lra].
  - unfold p; apply positive_nth_root_pow; assumption.
Qed.

Theorem inverse_parameterization_R (n : nat) (z x : R) :
  (0 < n)%nat -> z > x -> x > 0 ->
  let u := (z + x) / 2 in
  let v := (z - x) / 2 in
  let m := positive_nth_root n u in
  let p := positive_nth_root n v in
  0 < p /\ p < m /\
  z = pow m n + pow p n /\ x = pow m n - pow p n.
Proof.
  intros Hn Hzx Hx u v m p.
  assert (Huv : u > v /\ v > 0) by (unfold u, v; lra).
  destruct Huv as [Huv Hvp].
  pose proof (inverse_symmetrization_positive_roots n u v Hn Hvp Huv) as Hroots.
  fold m in Hroots; fold p in Hroots.
  destruct Hroots as [Hp [Hpm [Hm Hpown]]].
  repeat split; try assumption.
  - rewrite Hm, Hpown; unfold u, v; field.
  - rewrite Hm, Hpown; unfold u, v; field.
Qed.

Close Scope R_scope.

Local Open Scope Z_scope.
Lemma sum_diff_from_parameters_Z (n:nat) (m p:Z) :
  let z := m ^ Z.of_nat n + p ^ Z.of_nat n in let x := m ^ Z.of_nat n - p ^ Z.of_nat n in
  z+x = 2*m ^ Z.of_nat n /\ z-x = 2*p ^ Z.of_nat n.
Proof. intros z x; unfold z, x; split; ring. Qed.
Corollary parity_condition_Z (n:nat) (m p:Z) :
  let z := m ^ Z.of_nat n + p ^ Z.of_nat n in let x := m ^ Z.of_nat n - p ^ Z.of_nat n in
  Z.even (z+x)=true /\ Z.even (z-x)=true.
Proof.
  intros; destruct (sum_diff_from_parameters_Z n m p) as [A B]; split;
  [replace (z+x) with (2*m^Z.of_nat n) by exact A|replace (z-x) with (2*p^Z.of_nat n) by exact B];
  rewrite Z.even_mul; reflexivity.
Qed.
Lemma no_parameters_if_parity_violation (n:nat) (z x:Z) :
  Z.even (z+x)=false \/ Z.even (z-x)=false ->
  ~ exists m p:Z, z = m^Z.of_nat n + p^Z.of_nat n /\ x = m^Z.of_nat n - p^Z.of_nat n.
Proof.
  intros H [m [p [Hz Hx]]]; destruct (sum_diff_from_parameters_Z n m p) as [A B]; destruct H as [H|H];
  rewrite Hz,Hx in H; [rewrite A in H|rewrite B in H]; rewrite Z.even_mul in H; discriminate.
Qed.
Lemma no_parameters_if_odd (n:nat) (z x:Z) :
  Z.odd (z+x)=true \/ Z.odd (z-x)=true ->
  ~ exists m p:Z, z = m^Z.of_nat n + p^Z.of_nat n /\ x = m^Z.of_nat n - p^Z.of_nat n.
Proof.
  intros H [m [p [Hz Hx]]]; destruct (sum_diff_from_parameters_Z n m p) as [A B]; destruct H as [H|H];
  rewrite Hz,Hx in H; [rewrite A in H|rewrite B in H]; rewrite Z.odd_mul in H; discriminate.
Qed.
Lemma no_parameters_for_example : ~ exists m p:Z, 2%Z = m^Z.of_nat 3 + p^Z.of_nat 3 /\ 1%Z = m^Z.of_nat 3 - p^Z.of_nat 3.
Proof. apply (no_parameters_if_parity_violation 3 2 1); now left. Qed.
Close Scope Z_scope.

Local Open Scope nat_scope.
Lemma equation_rearrange_nat (n x y z:nat) : x^n + y^n = z^n -> z^n - x^n = y^n.
Proof. intro H; rewrite <- H; lia. Qed.
Lemma parameter_equations_raise_nat (n m p z x:nat) : z = m^n+p^n -> x = m^n-p^n -> z^n=(m^n+p^n)^n /\ x^n=(m^n-p^n)^n.
Proof. intros; subst; split; reflexivity. Qed.
Lemma parameterized_difference_substitution_nat (n m p y:nat) : ((m^n+p^n)^n - (m^n-p^n)^n = y^n) ->
  let z:=m^n+p^n in let x:=m^n-p^n in z^n - x^n = y^n.
Proof. exact (fun H => H). Qed.
Lemma pythagorean_parameter_example : let m:=3 in let p:=2 in let z:=m^2+p^2 in let x:=m^2-p^2 in let y:=2*m*p in z^2=x^2+y^2.
Proof. reflexivity. Qed.

Local Open Scope R_scope.

(* Finite-sum notation for the odd binomial core and the algebraic core. *)
Definition odd_binomial_term (n j : nat) (m p : R) : R :=
  if Nat.odd j then C n j * pow (pow m n) (n - j) * pow (pow p n) j else 0.
Definition odd_binomial_core_sum (n : nat) (m p : R) : R :=
  sum_f_R0 (fun j => odd_binomial_term n j m p) n.
Definition odd_binomial_core (n : nat) (m p : R) : R :=
  (pow (pow m n + pow p n) n - pow (pow m n - pow p n) n) / 2.
Theorem odd_binomial_difference_identity (n : nat) (m p : R) :
  pow (pow m n + pow p n) n - pow (pow m n - pow p n) n = 2 * odd_binomial_core n m p.
Proof. unfold odd_binomial_core; field. Qed.
Lemma pow_lt_nonneg (a b : R) (n : nat) : (0 < n)%nat -> 0 <= a -> a < b -> pow a n < pow b n.
Proof.
  intros Hn Ha Hab.
  destruct (Req_dec a 0) as [Ha0|Han].
  - subst a. rewrite pow_i by exact Hn. apply pow_lt; lra.
  - assert (Ha_pos : 0 < a) by lra.
    assert (Hb_pos : 0 < b) by lra.
    rewrite <- (Rpower_pow n a Ha_pos).
    rewrite <- (Rpower_pow n b Hb_pos).
    apply Rlt_Rpower_l.
    + apply lt_0_INR; exact Hn.
    + split; assumption.
Qed.
Lemma Rabs_sub_lt_sum_pos (a b : R) : 0 < a -> 0 < b -> Rabs (a - b) < a + b.
Proof. intros Ha Hb; destruct (Rcase_abs (a-b)); [rewrite Rabs_left|rewrite Rabs_right]; lra. Qed.
Theorem odd_binomial_core_positive (n : nat) (m p : R) :
  (0 < n)%nat -> 0 < m -> 0 < p -> 0 < odd_binomial_core n m p.
Proof.
  intros Hn Hm Hp; unfold odd_binomial_core.
  set (a := pow m n); set (b := pow p n).
  assert (Ha : 0 < a) by (unfold a; apply pow_lt; exact Hm).
  assert (Hb : 0 < b) by (unfold b; apply pow_lt; exact Hp).
  assert (Habs : Rabs (a-b) < a+b) by (apply Rabs_sub_lt_sum_pos; assumption).
  assert (Hpow : pow (Rabs (a-b)) n < pow (a+b) n) by (apply pow_lt_nonneg; [exact Hn|apply Rabs_pos|exact Habs]).
  assert (Habspow : pow (a-b) n <= pow (Rabs (a-b)) n).
  { replace (pow (Rabs (a - b)) n) with (Rabs (pow (a-b) n)) by (symmetry; apply RPow_abs). apply Rle_abs. }
  apply Rdiv_lt_0_compat; [lra|lra].
Qed.
Theorem parameterized_difference_via_odd_core_R (n : nat) (m p : R) :
  pow (pow m n + pow p n) n - pow (pow m n - pow p n) n = 2 * odd_binomial_core n m p.
Proof. apply odd_binomial_difference_identity. Qed.
Theorem fermat_equation_yields_odd_core_R (n : nat) (m p x y z : R) :
  pow x n + pow y n = pow z n -> z = pow m n + pow p n -> x = pow m n - pow p n ->
  pow y n = 2 * odd_binomial_core n m p.
Proof. intros Hfer Hz Hx; rewrite <- odd_binomial_difference_identity; rewrite <- Hz, <- Hx; lra. Qed.

Definition real_core_factorization (n:nat) (core l:R) : Prop := (0<n)%nat /\ core = INR n * pow l n.
Definition coefficient_mass_factorization (n:nat) (core q:R) : Prop := (0<n)%nat /\ core = INR (2^(n-1)) * pow q n.
Definition residual_scale_equality (n:nat) (l q:R) : Prop := pow l n = pow q n.
Definition coefficient_mass_equality (n:nat) : Prop := n = (2^(n-1))%nat.
Definition logarithmic_gap (l q:R) : R := ln (l/q).
Definition zero_logarithmic_gap (l q:R) : Prop := logarithmic_gap l q = 0.
Definition coefficient_logarithmic_gap (n:nat) : R := (1/INR n) * ln (INR (2^(n-1)) / INR n).

Lemma Rpow_pos_of_pos (a:R) (n:nat) : 0<a -> 0<pow a n.
Proof. intro; induction n; simpl; try lra; apply Rmult_lt_0_compat; assumption. Qed.
Lemma Rdiv_pos_of_pos (a b:R) : 0<a -> 0<b -> 0<a/b.
Proof. intros; unfold Rdiv; apply Rmult_lt_0_compat; [assumption|now apply Rinv_0_lt_compat]. Qed.
Lemma INR_pow2_pos (n:nat) : 0 < INR (2^n).
Proof. apply lt_0_INR; induction n; simpl; lia. Qed.

Lemma real_core_factorization_unique_value (n:nat) (core l1 l2:R) :
  real_core_factorization n core l1 -> real_core_factorization n core l2 -> INR n*pow l1 n = INR n*pow l2 n.
Proof. intros [_ A] [_ B]; rewrite <-A, <-B; reflexivity. Qed.
Lemma real_core_factorization_unique_positive_scale (n:nat) (core l1 l2:R) :
  real_core_factorization n core l1 -> real_core_factorization n core l2 -> 0<l1 -> 0<l2 -> l1=l2.
Proof.
  intros [Hn A] [Hn2 B] Hl1 Hl2. apply ln_inv; try assumption.
  assert (E: pow l1 n = pow l2 n).
  { apply Rmult_eq_reg_l with (r:=INR n); [rewrite <-A, <-B; reflexivity|apply not_0_INR; lia]. }
  assert (INR n * ln l1 = INR n * ln l2).
  { rewrite <- !ln_pow by assumption; now rewrite E. }
  apply Rmult_eq_reg_l with (r:=INR n); [exact H|apply not_0_INR; lia].
Qed.

Lemma real_core_factorization_substitutes_y_power (n:nat) (core l y:R) :
  real_core_factorization n core l -> pow y n = 2*core -> pow y n = 2*INR n*pow l n.
Proof. intros [_ A] B; rewrite B,A; ring. Qed.
Lemma coefficient_mass_factorization_substitutes_difference (n:nat) (core q diff:R) :
  coefficient_mass_factorization n core q -> diff = 2*core -> diff = INR (2^n) * pow q n.
Proof.
  intros [Hn A] B; rewrite B,A. replace (INR (2^n)) with (2*INR (2^(n-1))). ring.
  destruct n; [lia|]. rewrite Nat.pow_succ_r' by lia. replace (S n-1)%nat with n by lia. rewrite mult_INR; simpl; lra.
Qed.
Lemma two_scale_factorizations_relation (n:nat) (core l q:R) :
  real_core_factorization n core l -> coefficient_mass_factorization n core q ->
  pow l n = pow q n * (INR (2^(n-1))/INR n).
Proof.
  intros [Hn A] [_ B]. apply Rmult_eq_reg_l with (r:=INR n); [|apply not_0_INR; lia].
  rewrite A in B. rewrite B. field; apply not_0_INR; lia.
Qed.

Lemma pow_Rdiv (a b:R) (n:nat) : b<>0 -> pow (a/b) n = pow a n / pow b n.
Proof. intro Hb; induction n; simpl; [field|rewrite IHn; field; split; [apply pow_nonzero; exact Hb|exact Hb]]. Qed.
Lemma logarithmic_gap_exact_formula (n:nat) (core l q:R) :
  real_core_factorization n core l -> coefficient_mass_factorization n core q -> 0<l -> 0<q ->
  logarithmic_gap l q = coefficient_logarithmic_gap n.
Proof.
  intros [Hn A] Hcoef Hl Hq. pose proof (two_scale_factorizations_relation n core l q (conj Hn A) Hcoef) as E.
  unfold logarithmic_gap, coefficient_logarithmic_gap.
  assert (Hpq:0<pow q n) by now apply Rpow_pos_of_pos.
  assert (Cpos:0 < INR (2^(n-1)) / INR n) by (apply Rdiv_pos_of_pos; [apply INR_pow2_pos|apply lt_0_INR; lia]).
  assert (Eratio: pow (l/q) n = INR (2^(n-1))/INR n).
  { rewrite pow_Rdiv by lra. rewrite E. field; split; [apply not_0_INR; lia|exact (Rgt_not_eq _ _ Hpq)]. }
  assert (Hratio: 0 < l/q) by (apply Rdiv_pos_of_pos; assumption).
  assert (Hln: INR n * ln (l/q) = ln (INR (2^(n-1))/INR n)).
  { rewrite <- ln_pow by assumption. now rewrite Eratio. }
  apply Rmult_eq_reg_l with (r:=INR n); [|apply not_0_INR; lia].
  rewrite Hln. field; apply not_0_INR; lia.
Qed.
Theorem logarithmic_gap_invariant_under_core (n:nat) (core1 core2 l1 q1 l2 q2:R) :
  real_core_factorization n core1 l1 -> coefficient_mass_factorization n core1 q1 -> 0<l1 -> 0<q1 ->
  real_core_factorization n core2 l2 -> coefficient_mass_factorization n core2 q2 -> 0<l2 -> 0<q2 ->
  logarithmic_gap l1 q1 = logarithmic_gap l2 q2.
Proof. intros; rewrite (logarithmic_gap_exact_formula n core1 l1 q1), (logarithmic_gap_exact_formula n core2 l2 q2); eauto. Qed.
Definition coefficient_gap_on_solution_space (n:nat) (_x _y _z:Z) : R := coefficient_logarithmic_gap n.
Theorem coefficient_gap_constant_on_solution_space : forall n x1 y1 z1 x2 y2 z2,
  coefficient_gap_on_solution_space n x1 y1 z1 = coefficient_gap_on_solution_space n x2 y2 z2.
Proof. reflexivity. Qed.

Lemma pow_eq_pos_base_eq (n:nat) (l q:R) : (0<n)%nat -> 0<l -> 0<q -> pow l n = pow q n -> l=q.
Proof.
  intros Hn Hl Hq E; apply ln_inv; try assumption.
  apply Rmult_eq_reg_l with (r:=INR n); [rewrite <- !ln_pow by assumption; now rewrite E|apply not_0_INR; lia].
Qed.

Lemma real_core_positive_scale_exists_unique (n : nat) (core : R) :
  (0 < n)%nat -> 0 < core ->
  exists! l : R, 0 < l /\ real_core_factorization n core l.
Proof.
  intros Hn Hcore.
  set (l := positive_nth_root n (core / INR n)).
  assert (Hbase : 0 < core / INR n) by (apply Rdiv_pos_of_pos; [exact Hcore|apply lt_0_INR; lia]).
  exists l; split.
  - split.
    + unfold l, positive_nth_root; apply Rpower_pos_of_pos; exact Hbase.
    + split; [exact Hn|]. unfold l. rewrite positive_nth_root_pow by assumption. field; apply not_0_INR; lia.
  - intros l' [Hl' Hfac']. apply real_core_factorization_unique_positive_scale with (n:=n) (core:=core); try assumption.
    + split; [exact Hn|]. unfold l. rewrite positive_nth_root_pow by assumption. field; apply not_0_INR; lia.
    + unfold l, positive_nth_root; apply Rpower_pos_of_pos; exact Hbase.
Qed.

Lemma coefficient_mass_positive_scale_exists_unique (n : nat) (core : R) :
  (0 < n)%nat -> 0 < core ->
  exists! q : R, 0 < q /\ coefficient_mass_factorization n core q.
Proof.
  intros Hn Hcore.
  set (q := positive_nth_root n (core / INR (2^(n-1)))).
  assert (Hcoefpos : 0 < INR (2^(n-1))) by apply INR_pow2_pos.
  assert (Hbase : 0 < core / INR (2^(n-1))) by (apply Rdiv_pos_of_pos; assumption).
  exists q; split.
  - split.
    + unfold q, positive_nth_root; apply Rpower_pos_of_pos; exact Hbase.
    + split; [exact Hn|]. unfold q. rewrite positive_nth_root_pow by assumption. field; lra.
  - intros q' [Hq' [Hn' Hfac']].
    apply (pow_eq_pos_base_eq n q q' Hn).
    + unfold q, positive_nth_root; apply Rpower_pos_of_pos; exact Hbase.
    + exact Hq'.
    + apply Rmult_eq_reg_l with (r:=INR (2^(n-1))).
      * unfold q. rewrite positive_nth_root_pow by assumption. rewrite <- Hfac'. field; lra.
      * lra.
Qed.

Lemma odd_core_normalizing_scales_exist_unique (n : nat) (m p : R) :
  (0 < n)%nat -> 0 < m -> 0 < p ->
  (exists! l : R, 0 < l /\ real_core_factorization n (odd_binomial_core n m p) l) /\
  (exists! q : R, 0 < q /\ coefficient_mass_factorization n (odd_binomial_core n m p) q).
Proof.
  intros Hn Hm Hp.
  assert (Hcore : 0 < odd_binomial_core n m p) by (apply odd_binomial_core_positive; assumption).
  split.
  - apply real_core_positive_scale_exists_unique; assumption.
  - apply coefficient_mass_positive_scale_exists_unique; assumption.
Qed.

Theorem odd_core_logarithmic_gap_exact_formula (n : nat) (m p l q : R) :
  (0 < n)%nat -> 0 < m -> 0 < p ->
  0 < l -> real_core_factorization n (odd_binomial_core n m p) l ->
  0 < q -> coefficient_mass_factorization n (odd_binomial_core n m p) q ->
  logarithmic_gap l q = coefficient_logarithmic_gap n.
Proof.
  intros _ _ _ Hl Hlin Hq Hcoef.
  eapply logarithmic_gap_exact_formula; eauto.
Qed.

Theorem odd_core_logarithmic_gap_depends_only_on_exponent
  (n : nat) (m1 p1 l1 q1 m2 p2 l2 q2 : R) :
  (0 < n)%nat ->
  0 < m1 -> 0 < p1 -> 0 < l1 -> 0 < q1 ->
  real_core_factorization n (odd_binomial_core n m1 p1) l1 ->
  coefficient_mass_factorization n (odd_binomial_core n m1 p1) q1 ->
  0 < m2 -> 0 < p2 -> 0 < l2 -> 0 < q2 ->
  real_core_factorization n (odd_binomial_core n m2 p2) l2 ->
  coefficient_mass_factorization n (odd_binomial_core n m2 p2) q2 ->
  logarithmic_gap l1 q1 = logarithmic_gap l2 q2.
Proof.
  intros; eapply logarithmic_gap_invariant_under_core; eauto.
Qed.

Lemma residual_scale_equality_implies_zero_logarithmic_gap (n:nat) (l q:R) : (0<n)%nat -> 0<l -> 0<q -> residual_scale_equality n l q -> zero_logarithmic_gap l q.
Proof. intros; unfold zero_logarithmic_gap, logarithmic_gap; assert (l=q) by (eapply pow_eq_pos_base_eq; eauto); subst; replace (q/q) with 1 by (field; lra); apply ln_1. Qed.
Lemma zero_logarithmic_gap_implies_residual_scale_equality (n:nat) (l q:R) : (0<n)%nat -> 0<l -> 0<q -> zero_logarithmic_gap l q -> residual_scale_equality n l q.
Proof.
  intros _ Hl Hq Hzero; unfold zero_logarithmic_gap, logarithmic_gap in Hzero; unfold residual_scale_equality.
  assert (l/q=1) by (apply ln_inv; try (apply Rdiv_pos_of_pos; assumption); try lra; now rewrite ln_1).
  assert (l=q) by (replace l with ((l/q)*q) by (field; lra); rewrite H; ring). now subst.
Qed.
Theorem residual_scale_equality_iff_zero_logarithmic_gap (n:nat) (l q:R) : (0<n)%nat -> 0<l -> 0<q -> (residual_scale_equality n l q <-> zero_logarithmic_gap l q).
Proof. split; [apply residual_scale_equality_implies_zero_logarithmic_gap|apply zero_logarithmic_gap_implies_residual_scale_equality]; assumption. Qed.
Lemma residual_scale_equality_forces_coefficient_mass_equality (n:nat) (core l q:R) :
  real_core_factorization n core l -> coefficient_mass_factorization n core q -> residual_scale_equality n l q -> 0<q -> coefficient_mass_equality n.
Proof.
  intros [_ A] [_ B] E Hq; unfold coefficient_mass_equality.
  assert (INR n = INR (2^(n-1))). { apply Rmult_eq_reg_r with (r:=pow q n). - unfold residual_scale_equality in E; rewrite E in A; rewrite <- A; exact B. - pose proof (Rpow_pos_of_pos q n Hq); lra. }
  now apply INR_eq.
Qed.
Lemma coefficient_mass_equality_forces_residual_scale_equality (n:nat) (core l q:R) :
  real_core_factorization n core l -> coefficient_mass_factorization n core q -> coefficient_mass_equality n -> residual_scale_equality n l q.
Proof.
  intros [Hn A] [_ B] H; unfold residual_scale_equality, coefficient_mass_equality in H.
  apply Rmult_eq_reg_l with (r:=INR n); [replace (2^(n-1))%nat with n in B by lia; rewrite <-A, <-B; ring|apply not_0_INR; lia].
Qed.
Theorem coefficient_symmetry_compatibility_iff (n:nat) (core l q:R) :
  real_core_factorization n core l -> coefficient_mass_factorization n core q -> 0<q ->
  (residual_scale_equality n l q <-> coefficient_mass_equality n).
Proof. intros Hlin Hcoef Hq; split; intro H; [eapply residual_scale_equality_forces_coefficient_mass_equality; eauto|eapply coefficient_mass_equality_forces_residual_scale_equality; eauto]. Qed.
Theorem logarithmic_coefficient_symmetry_compatibility_iff (n:nat) (core l q:R) :
  real_core_factorization n core l -> coefficient_mass_factorization n core q -> 0<l -> 0<q ->
  (zero_logarithmic_gap l q <-> coefficient_mass_equality n).
Proof.
  intros Hlin Hcoef Hl Hq; destruct Hlin as [Hn A]; split; intro H.
  - eapply residual_scale_equality_forces_coefficient_mass_equality; eauto. split; eauto. eapply zero_logarithmic_gap_implies_residual_scale_equality; eauto.
  - eapply residual_scale_equality_implies_zero_logarithmic_gap; eauto. eapply coefficient_mass_equality_forces_residual_scale_equality; eauto. split; eauto.
Qed.
Theorem logarithmic_zero_gap_chain (n:nat) (core l q:R) : real_core_factorization n core l -> coefficient_mass_factorization n core q -> 0<l -> 0<q ->
  (residual_scale_equality n l q <-> zero_logarithmic_gap l q) /\ (zero_logarithmic_gap l q <-> coefficient_mass_equality n).
Proof. intros [Hn A] Hcoef Hl Hq; split. - apply residual_scale_equality_iff_zero_logarithmic_gap; assumption. - apply logarithmic_coefficient_symmetry_compatibility_iff with (core:=core); try assumption; split; assumption. Qed.

Record CoefficientSymmetryData := { cs_n:nat; cs_core:R; cs_l:R; cs_q:R; cs_l_pos:0<cs_l; cs_q_pos:0<cs_q; cs_linear_factorization:real_core_factorization cs_n cs_core cs_l; cs_coefficient_factorization:coefficient_mass_factorization cs_n cs_core cs_q; cs_residual_scale_equality:residual_scale_equality cs_n cs_l cs_q }.
Lemma coefficient_symmetry_data_forces_shift (s:CoefficientSymmetryData) : coefficient_mass_equality (cs_n s).
Proof. eapply residual_scale_equality_forces_coefficient_mass_equality; [apply cs_linear_factorization|apply cs_coefficient_factorization|apply cs_residual_scale_equality|apply cs_q_pos]. Qed.
Record LogarithmicCoefficientSymmetryData := { lcs_n:nat; lcs_core:R; lcs_l:R; lcs_q:R; lcs_l_pos:0<lcs_l; lcs_q_pos:0<lcs_q; lcs_linear_factorization:real_core_factorization lcs_n lcs_core lcs_l; lcs_coefficient_factorization:coefficient_mass_factorization lcs_n lcs_core lcs_q; lcs_zero_gap:zero_logarithmic_gap lcs_l lcs_q }.
Lemma logarithmic_data_forces_shift (s:LogarithmicCoefficientSymmetryData) : coefficient_mass_equality (lcs_n s).
Proof. apply logarithmic_coefficient_symmetry_compatibility_iff with (core:=lcs_core s) (l:=lcs_l s) (q:=lcs_q s); [apply lcs_linear_factorization|apply lcs_coefficient_factorization|apply lcs_l_pos|apply lcs_q_pos|apply lcs_zero_gap]. Qed.
Close Scope R_scope.

Section ModularRemark.
Local Open Scope Z_scope.
Definition modular_congruent (modq a b:Z) : Prop := exists t:Z, a = b + modq*t.
Lemma integer_equality_implies_modular_power_congruence (n:nat) (x y z modq:Z) :
  Z.pow x (Z.of_nat n)+Z.pow y (Z.of_nat n)=Z.pow z (Z.of_nat n) -> modular_congruent modq (Z.pow z (Z.of_nat n)) (Z.pow x (Z.of_nat n)+Z.pow y (Z.of_nat n)).
Proof. intro H; exists 0%Z; rewrite <-H; ring. Qed.
Lemma modular_congruence_has_integer_witness (modq lhs rhs:Z) : modular_congruent modq lhs rhs -> exists t:Z, lhs=rhs+modq*t.
Proof. exact (fun H=>H). Qed.
Lemma integer_equality_is_zero_modular_witness (n:nat) (x y z modq:Z) :
 Z.pow x (Z.of_nat n)+Z.pow y (Z.of_nat n)=Z.pow z (Z.of_nat n) -> exists t:Z, t=0%Z /\ Z.pow z (Z.of_nat n)=Z.pow x (Z.of_nat n)+Z.pow y (Z.of_nat n)+modq*t.
Proof. intro H; exists 0%Z; split; [reflexivity|rewrite <-H; ring]. Qed.
Lemma modular_congruence_not_integer_equality : modular_congruent 5 (Z.pow 3 3) (Z.pow 1 3+Z.pow 1 3) /\ Z.pow 1 3+Z.pow 1 3 <> Z.pow 3 3.
Proof. split; [exists 5%Z; reflexivity|discriminate]. Qed.
Record ModularResidues := { mpr_modq:Z; mpr_n:nat; mpr_m:Z; mpr_p:Z; mpr_A:Z; mpr_B:Z; mpr_z:Z; mpr_x:Z; mpr_mn_residue:modular_congruent mpr_modq (Z.pow mpr_m (Z.of_nat mpr_n)) mpr_A; mpr_pn_residue:modular_congruent mpr_modq (Z.pow mpr_p (Z.of_nat mpr_n)) mpr_B; mpr_z_residue:modular_congruent mpr_modq mpr_z (mpr_A+mpr_B); mpr_x_residue:modular_congruent mpr_modq mpr_x (mpr_A-mpr_B)}.
End ModularRemark.

Local Open Scope nat_scope.
Lemma pow2_gt_linear_shift (k:nat) : 2^(k+3) > 2*(k+3).
Proof.
  induction k; simpl; [lia|]. replace (S k+3) with (k+4) by lia.
  replace (2^(S k+3)) with (2*2^(k+3)) by (replace (S k+3) with (S(k+3)) by lia; rewrite Nat.pow_succ_r by lia; lia).
  assert (2*2^(k+3) > 2*(2*(k+3))) by (apply Nat.mul_lt_mono_pos_l; lia).
  lia.
Qed.
Lemma pow2_gt_linear (n:nat) : 3 <= n -> 2^n > 2*n.
Proof. intros H; destruct (Nat.le_exists_sub 3 n H) as [k [E _]]; rewrite E; replace (3+k) with (k+3) by lia; apply pow2_gt_linear_shift. Qed.
Lemma pow2_shift_gt_linear (n:nat) : 2 < n -> 2^(n-1) > n.
Proof.
  intros Hn.
  assert (H3 : 3 <= n) by lia.
  pose proof (pow2_gt_linear n H3) as Hbig.
  destruct n as [|n]; [lia|].
  rewrite Nat.pow_succ_r' in Hbig by lia.
  replace (S n - 1) with n by lia.
  lia.
Qed.
Lemma pow_eq_linear_cases (n:nat) : 2^n = 2*n -> n=0 \/ n=1 \/ n=2.
Proof. destruct n as [|n]; [simpl; lia|]. destruct n as [|n]; [simpl; lia|]. destruct n as [|n]; [simpl; lia|]. intro H; assert (3 <= S(S(S n))) by lia; pose proof (pow2_gt_linear (S(S(S n))) H0) as G; rewrite H in G; lia. Qed.
Lemma pow_eq_linear_positive (n:nat) : 2^n = 2*n -> n=1 \/ n=2.
Proof. intro H; destruct (pow_eq_linear_cases n H) as [A|[A|A]]; subst; try discriminate; auto. Qed.
Lemma two_pow_eq_two_mul_iff_shift (n:nat) : (2^n = 2*n) <-> (n = 2^(n-1)).
Proof.
  destruct n as [|n].
  - simpl; split; intro H; lia.
  - split; intro H.
    + rewrite Nat.pow_succ_r' in H by lia. apply Nat.mul_cancel_l in H; [|lia]. replace (S n-1) with n by lia. symmetry; exact H.
    + rewrite Nat.pow_succ_r' by lia. replace (S n-1) with n in H by lia. rewrite H; reflexivity.
Qed.
Lemma binary_scaling_roots_only_one_two (n:nat) : n = 2^(n-1) -> n=1 \/ n=2.
Proof. intro H; apply two_pow_eq_two_mul_iff_shift in H; now apply pow_eq_linear_positive. Qed.

Local Open Scope R_scope.
Lemma coefficient_logarithmic_gap_zero_iff_coefficient_mass_equality : forall n, (0<n)%nat -> (coefficient_logarithmic_gap n = 0 <-> coefficient_mass_equality n).
Proof.
  intros n Hn; unfold coefficient_logarithmic_gap, coefficient_mass_equality; split; intro H.
  - assert (Hlnzero : ln (INR (2^(n-1))/INR n)=0). { apply Rmult_eq_reg_l with (r:=1/INR n); [rewrite H; lra|assert (0 < 1 / INR n) by (apply Rdiv_pos_of_pos; [lra|apply lt_0_INR; lia]); lra]. }
    assert (Hratio1 : INR (2^(n-1))/INR n = 1). { apply ln_inv. - apply Rdiv_pos_of_pos; [apply INR_pow2_pos|apply lt_0_INR; lia]. - lra. - rewrite ln_1; exact Hlnzero. }
    symmetry; apply INR_eq. replace (INR (2^(n-1))) with ((INR (2^(n-1)) / INR n) * INR n) by (field; apply not_0_INR; lia). rewrite Hratio1. field.
  - replace (INR (2^(n-1))/INR n) with 1 by (rewrite <-H; field; apply not_0_INR; lia). rewrite ln_1; ring.
Qed.
Theorem coefficient_logarithmic_gap_zero_iff_one_or_two : forall n, (0<n)%nat -> (coefficient_logarithmic_gap n = 0 <-> n=1%nat \/ n=2%nat).
Proof.
  intros n Hn; rewrite coefficient_logarithmic_gap_zero_iff_coefficient_mass_equality by exact Hn; split.
  - apply binary_scaling_roots_only_one_two.
  - intros [H|H]; subst n; unfold coefficient_mass_equality; reflexivity.
Qed.
Theorem coefficient_logarithmic_gap_positive_above_two : forall n, (2<n)%nat -> 0 < coefficient_logarithmic_gap n.
Proof.
  intros n Hn; unfold coefficient_logarithmic_gap.
  apply Rmult_lt_0_compat; [apply Rdiv_pos_of_pos; lra + apply lt_0_INR; lia|].
  replace 0 with (ln 1) by apply ln_1. apply ln_increasing; [lra|].
  assert (INR n < INR (2^(n-1))) by (apply lt_INR; now apply pow2_shift_gt_linear).
  unfold Rdiv. replace 1 with (INR n * / INR n) by (field; apply not_0_INR; lia).
  apply Rmult_lt_compat_r; [apply Rinv_0_lt_compat; apply lt_0_INR; lia|exact H].
Qed.

Lemma coefficient_symmetry_data_forces_small_exponent (s:CoefficientSymmetryData) : cs_n s=1%nat \/ cs_n s=2%nat.
Proof. apply binary_scaling_roots_only_one_two, coefficient_symmetry_data_forces_shift. Qed.
Theorem coefficient_symmetry_data_excludes_high_exponent (s:CoefficientSymmetryData) : (2<cs_n s)%nat -> False.
Proof. intro; destruct (coefficient_symmetry_data_forces_small_exponent s); lia. Qed.
Theorem coefficient_symmetry_compatibility_excludes_high_exponent (n:nat) (core l q:R) : real_core_factorization n core l -> coefficient_mass_factorization n core q -> residual_scale_equality n l q -> 0<q -> (2<n)%nat -> False.
Proof. intros; pose proof (residual_scale_equality_forces_coefficient_mass_equality n core l q H H0 H1 H2); destruct (binary_scaling_roots_only_one_two n H4); lia. Qed.
Lemma logarithmic_data_forces_small_exponent (s:LogarithmicCoefficientSymmetryData) : lcs_n s=1%nat \/ lcs_n s=2%nat.
Proof. apply binary_scaling_roots_only_one_two, logarithmic_data_forces_shift. Qed.
Theorem logarithmic_data_excludes_high_exponent (s:LogarithmicCoefficientSymmetryData) : (2<lcs_n s)%nat -> False.
Proof. intro; destruct (logarithmic_data_forces_small_exponent s); lia. Qed.
Theorem logarithmic_zero_gap_excludes_high_exponent (n:nat) (core l q:R) : real_core_factorization n core l -> coefficient_mass_factorization n core q -> zero_logarithmic_gap l q -> 0<l -> 0<q -> (2<n)%nat -> False.
Proof. intros; pose proof (logarithmic_coefficient_symmetry_compatibility_iff n core l q H H0 H2 H3) as [A _]; destruct (binary_scaling_roots_only_one_two n (A H1)); lia. Qed.

Local Open Scope Z_scope.
Definition positive_fermat_solution (n:nat) (x y z:Z) : Prop := (0<x)%Z /\ (0<y)%Z /\ (0<z)%Z /\ Z.pow x (Z.of_nat n) + Z.pow y (Z.of_nat n) = Z.pow z (Z.of_nat n).
Definition no_positive_integer_solution (n:nat) : Prop := forall x y z:Z, ~ positive_fermat_solution n x y z.
Definition zero_gap_bridge (n:nat) : Prop := forall x y z:Z, positive_fermat_solution n x y z -> coefficient_logarithmic_gap n = 0%R.

Record PositiveFermatSolution (n : nat) := {
  pfs_x : Z;
  pfs_y : Z;
  pfs_z : Z;
  pfs_solution : positive_fermat_solution n pfs_x pfs_y pfs_z
}.

Definition gap_on_solution (n : nat) (_s : PositiveFermatSolution n) : R :=
  coefficient_logarithmic_gap n.

(* The arguments of a solution do not enter the coefficient computation: after
   the normalization identity, the formal gap is a function of the exponent. *)
Theorem gap_on_solution_constant :
  forall n (s1 s2 : PositiveFermatSolution n),
    gap_on_solution n s1 = gap_on_solution n s2.
Proof. reflexivity. Qed.

Theorem coefficient_gap_constant_on_positive_fermat_solutions :
  forall n x1 y1 z1 x2 y2 z2,
    positive_fermat_solution n x1 y1 z1 ->
    positive_fermat_solution n x2 y2 z2 ->
    exists s1 s2 : PositiveFermatSolution n,
      gap_on_solution n s1 = gap_on_solution n s2.
Proof.
  intros n x1 y1 z1 x2 y2 z2 H1 H2.
  exists {| pfs_x := x1; pfs_y := y1; pfs_z := z1; pfs_solution := H1 |}.
  exists {| pfs_x := x2; pfs_y := y2; pfs_z := z2; pfs_solution := H2 |}.
  apply gap_on_solution_constant.
Qed.

(* This equivalence does not prove FLT. It shows that, for fixed n > 2,
   the proposed zero-gap bridge has exactly the same logical strength as
   the absence of positive integer solutions. *)
Theorem zero_gap_bridge_iff_no_positive_integer_solution : forall n, (2<n)%nat -> (zero_gap_bridge n <-> no_positive_integer_solution n).
Proof.
  intros n Hn; split.
  - intros Hb x y z Hsol. pose proof (Hb x y z Hsol) as Hzero. pose proof (coefficient_logarithmic_gap_positive_above_two n Hn) as Hpos. lra.
  - intros Hnone x y z Hsol. exfalso; exact (Hnone x y z Hsol).
Qed.
Close Scope Z_scope.


Definition continuous_coefficient_gap (x : R) : R := ln 2 - ln (2 * x) / x.

Definition continuous_coefficient_gap_derivative : Prop :=
  forall x, 0 < x ->
    derivable_pt_lim continuous_coefficient_gap x ((ln (2*x) - 1) / (x^2)).

(* The following two constants record the intended continuous-analysis
   statements as transparent propositions.  They are not used by the arithmetic
   bridge theorem; no axiom is introduced. *)
Definition continuous_coefficient_gap_strictly_increasing : Prop :=
  forall x1 x2, 2 <= x1 -> x1 < x2 ->
    continuous_coefficient_gap x1 < continuous_coefficient_gap x2.

Definition continuous_coefficient_gap_limit : Prop :=
  Un_cv (fun n => continuous_coefficient_gap (INR n)) (ln 2).

Definition coefficient_logarithmic_gap_strictly_increasing : Prop :=
  forall n k, (2 <= n)%nat -> (n < k)%nat ->
    coefficient_logarithmic_gap n < coefficient_logarithmic_gap k.

Definition coefficient_logarithmic_gap_tends_to_ln2 : Prop :=
  Un_cv coefficient_logarithmic_gap (ln 2).

Theorem regression_coefficient_gap_zero_cases : coefficient_logarithmic_gap 1 = 0%R /\ coefficient_logarithmic_gap 2 = 0%R.
Proof. split; apply coefficient_logarithmic_gap_zero_iff_one_or_two; lia. Qed.
Theorem regression_bridge_strength_for_three : zero_gap_bridge 3 <-> no_positive_integer_solution 3.
Proof. apply zero_gap_bridge_iff_no_positive_integer_solution; lia. Qed.

Theorem regression_odd_core_n1 : forall m p : R, odd_binomial_core 1 m p = p.
Proof. intros; unfold odd_binomial_core; simpl; field. Qed.
Theorem regression_odd_core_n2 : forall m p : R, odd_binomial_core 2 m p = 2 * (m^2) * (p^2).
Proof. intros; unfold odd_binomial_core; simpl; field. Qed.
Theorem regression_odd_core_n3 : forall m p : R, odd_binomial_core 3 m p = 3 * (m^3)^2 * (p^3) + (p^3)^3.
Proof. intros; unfold odd_binomial_core; simpl; field. Qed.
Theorem regression_binomial_difference_n3 : forall m p : R,
  pow (pow m 3 + pow p 3) 3 - pow (pow m 3 - pow p 3) 3 = 2 * odd_binomial_core 3 m p.
Proof. apply odd_binomial_difference_identity. Qed.
Theorem regression_gap_monotone_2_3 : coefficient_logarithmic_gap 2 < coefficient_logarithmic_gap 3.
Proof.
  replace (coefficient_logarithmic_gap 2) with 0.
  - apply coefficient_logarithmic_gap_positive_above_two; lia.
  - symmetry; apply coefficient_logarithmic_gap_zero_iff_one_or_two; lia.
Qed.
