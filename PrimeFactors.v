From Stdlib Require Import Znumtheory ZArith Bool List FunInd Recdef Lia.
Import ListNotations.
Open Scope Z.


Definition is_greatest (s : Z -> Prop) (x : Z) :=
  s x /\ (forall y, s y -> y <= x).

Definition is_least (s : Z -> Prop) (x : Z) :=
  s x /\ (forall y, s y -> x <= y).

Lemma prime_divisor_existence (n: Z) (H: 2 <= n):
  exists p, prime p /\ Z.divide p n.
Proof.
  assert (0 <= n) by lia. revert H. pattern n.
  apply Z_lt_induction; auto; intros. clear n H0. destruct (prime_dec x).
  + exists x. split; auto. exists 1. lia.
  + apply not_prime_divide in n; try lia. destruct n as [n [H2 H3]].
    destruct H3. subst. assert (0 <= x0 < x0 * n) by nia.
    assert (2 <= x0) by nia. pose proof (H _ H0 H3).
    destruct H4 as [p [H4 H5]]. exists p. split; auto. destruct H5. subst.
    exists (x * n). ring.
Qed.

Lemma prime_dvd_of_dvd_pow (p a i : Z) (Hp: prime p) (Ha : 1 <= a)
  (Hi : 0 <= i) (H : (p | a ^ i)) : (p | a).
Proof.
  assert (0 <= i) by lia. revert Hi H. pattern i.
  apply Z_lt_induction; auto; intros. clear H0 i.
  assert (x = 0 \/ 0 < x) by lia. destruct H0 as [H0 | H0].
  + subst x. simpl in H1. apply prime_ge_2 in Hp.
    apply Z.divide_1_r_nonneg in H1; lia.
  + replace x with (x - 1 + 1) in H1 by lia.
    rewrite Z.pow_add_r in H1; try lia. apply prime_mult in H1; auto.
    ring_simplify (a ^ 1) in H1. destruct H1 as [H1 | H1].
    - apply H in H1; try lia; auto.
    - auto.
Qed.


(* Main functions *)

Function remove_factor (n f : Z) { measure Z.to_nat n } : Z :=
  if Z_le_dec 1 n
  then if Z_le_dec 2 f
       then if Zdivide_dec f n
            then remove_factor (n / f) f
            else n
       else n
  else n.
Proof. intros. pose proof (Z.div_lt n f). lia. Defined.

Function factor_exponent (n f : Z) { measure Z.to_nat n } : Z :=
  if Z_le_dec 1 n
  then if Z_le_dec 2 f
       then if Zdivide_dec f n
            then factor_exponent (n / f) f + 1
            else 0
       else 0
  else 0.
Proof. intros. pose proof (Z.div_lt n f). lia. Defined.

Function remove_factors_le (n f : Z) { measure Z.to_nat f } : Z :=
  if Z_le_dec 1 n
  then if Z_le_dec 2 f
       then remove_factor (remove_factors_le n (f - 1)) f
       else n
  else n.
Proof. lia. Defined.

Function prime_factors_up_to (n f : Z) { measure Z.to_nat f } : list (Z * Z) :=
  if Z_le_dec 1 n
  then if Z_le_dec 2 f
       then if Zdivide_dec f (remove_factors_le n (f - 1))
            then (f, factor_exponent n f) :: prime_factors_up_to n (f - 1)
            else prime_factors_up_to n (f - 1)
       else []
  else [].
Proof. lia. lia. Defined.


(* Lemmas about the function 'remove_factor' *)

Lemma remove_factor_pos (n f : Z) (Hn : 1 <= n) : 1 <= remove_factor n f.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros. clear H n. rewrite remove_factor_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; auto.
  assert (x / f < x). { apply Z.div_lt; lia. }
  assert (1 <= remove_factor (x / f) f).
  { pose proof Zdivide_Zdiv_lt_pos f x ltac:(lia) ltac:(lia) d. apply H0; lia. }
  simpl in *; lia.
Qed.

Lemma remove_factor_le_self (n f : Z) (Hn : 1 <= n) : remove_factor n f <= n.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros. clear H n. rewrite remove_factor_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; try lia.
  assert (x / f < x). { apply Z.div_lt; lia. }
  assert (remove_factor (x / f) f <= x / f).
  { pose proof Zdivide_Zdiv_lt_pos f x ltac:(lia) ltac:(lia) d.
    apply H0; lia. }
  simpl in *; lia.
Qed.

Lemma factor_exponent_nonneg (n k : Z) : 0 <= factor_exponent n k.
Proof.
  rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
  destruct Zdivide_dec; try lia. assert (0 <= n) by lia. revert l d. pattern n.
  apply Z_lt_induction; auto; intros. clear H n.
  assert (k <= x). { apply Zdivide_le in d; lia. }
  rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
  destruct Zdivide_dec; try lia.
  assert (0 <= factor_exponent (x / k / k) k + 1).
  { apply H0; auto. pose proof (Z.div_pos x k ltac:(lia) ltac:(lia)).
    pose proof (Z.div_lt x k ltac:(lia) ltac:(lia)). lia. }
  lia.
Qed.

Lemma remove_factor_main_lemma (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  n = remove_factor n f * f ^ factor_exponent n f.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros. clear H n. rewrite remove_factor_equation.
  repeat destruct Z_le_dec; try lia. destruct Zdivide_dec.
  + destruct d. rewrite H, Z.div_mul; try lia.
    rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - rewrite Z.div_mul; try lia. rewrite Z.pow_add_r; try lia.
      * rewrite (H0 x0) at 1; try nia.
      * apply factor_exponent_nonneg.
    - exfalso. apply n. exists x0. auto.
  + rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec; try tauto. ring.
Qed.

Lemma remove_factor_not_divided_by_factor (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (f | remove_factor n f) -> False.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros ? ? ?. clear H n.
  rewrite remove_factor_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; auto.
  assert (0 < x / f < x).
  { constructor.
    + apply Zdivide_Zdiv_lt_pos; try lia; auto.
    + apply Z.div_lt; lia. }
  apply H0; lia.
Qed.

Lemma remove_factor_divides_self (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (remove_factor n f | n).
Proof.
  rewrite (remove_factor_main_lemma n f) at 2; try lia. apply Z.divide_factor_l.
Qed.

(* lemmas about `remove_factors_le` *)

Lemma remove_factors_up_to_one (n : Z) (Hn : 1 <= n) : remove_factors_le n 1 = n.
Proof.
  rewrite remove_factors_le_equation. simpl. destruct Z_le_dec; lia.
Qed.

Lemma remove_factors_up_to_two (n : Z) (Hn : 1 <= n) :
  remove_factors_le n 2 = remove_factor n 2.
Proof.
  rewrite remove_factors_le_equation, remove_factors_up_to_one; try lia. simpl.
  destruct Z_le_dec; lia.
Qed.

Lemma remove_factors_le_pos (n f : Z) (Hn : 1 <= n) (Hf : 1 <= f) :
  1 <= remove_factors_le n f.
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 1 \/ 1 < x) by lia. destruct H as [H | H].
  + subst x. rewrite remove_factors_up_to_one; auto.
  + rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    apply remove_factor_pos. apply H0; lia.
Qed.

Lemma remove_factors_le_self (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  remove_factors_le n f <= n.
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 2 \/ 2 < x) by lia. destruct H as [H | H].
  + subst x. rewrite remove_factors_up_to_two; auto.
    apply remove_factor_le_self; auto.
  + rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    assert (remove_factor (remove_factors_le n (x - 1)) x <= remove_factors_le n (x - 1)).
    { apply remove_factor_le_self. apply remove_factors_le_pos; lia. }
    assert (remove_factors_le n (x - 1) <= n). { apply H0; lia. }
    lia.
Qed.

Lemma remove_factors_le_not_dvd_by_bound (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (f | remove_factors_le n f) -> False.
Proof.
  rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
  apply remove_factor_not_divided_by_factor; auto.
  assert (f = 2 \/ 2 < f) by lia. destruct H as [H | H].
  + subst. simpl. rewrite remove_factors_up_to_one; auto.
  + apply remove_factors_le_pos; lia.
Qed.

Lemma remove_factors_le_not_dvd_by_factor (n f x : Z) (Hn : 1 <= n) (Hf : 2 <= f)
  (Hx : f <= x) : (f | remove_factors_le n x) -> False.
Proof.
  assert (0 <= x) by lia. revert Hx. pattern x.
  apply Z_lt_induction; auto; intros. clear H x.
  assert (x0 = f \/ f < x0) by lia. destruct H as [H | H].
  + subst x0. apply remove_factors_le_not_dvd_by_bound in H1; lia.
  + apply H0 with (y := x0 - 1); try lia.
    rewrite remove_factors_le_equation in H1. repeat destruct Z_le_dec; try lia.
    assert (remove_factor (remove_factors_le n (x0 - 1)) x0 | remove_factors_le n (x0 - 1)).
    { apply remove_factor_divides_self; try lia. apply remove_factors_le_pos; try lia. }
    eapply Z.divide_trans; eauto.
Qed.

Lemma remove_factors_le_dvd_self (n f : Z) (Hn : 1 <= n) (Hf : 1 <= f) :
  (remove_factors_le n f | n).
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 1 \/ 1 < x) by lia. destruct H.
  + subst x. rewrite remove_factors_up_to_one; auto. exists 1; ring.
  + rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
    pose proof (remove_factors_le_pos n (x - 1) Hn ltac:(lia)).
    pose proof (remove_factor_divides_self (remove_factors_le n (x - 1)) x H2 l0).
    exact (Z.divide_trans _ _ _ H3 H1).
Qed.

Lemma remove_factors_le_main_lemma_part_1 (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (f | remove_factors_le n (f - 1)) -> prime f /\ (f | n).
Proof.
  intros H. constructor.
  + destruct (prime_dec f); auto. pose proof (prime_divisor_existence f Hf).
    exfalso. destruct H0 as [p [Hp Hp0]]. assert (p <= f).
    { apply Zdivide_le; auto; try lia. pose proof (prime_ge_2 _ Hp). lia. }
    assert (p <> f) by congruence.
    apply (remove_factors_le_not_dvd_by_factor n p (f - 1) Hn (prime_ge_2 _ Hp));
      try lia. eapply Z.divide_trans; eauto.
  + pose proof (remove_factors_le_dvd_self n (f - 1) Hn ltac:(lia)).
    exact (Z.divide_trans _ _ _ H H0).
Qed.

Lemma remove_factors_le_main_lemma_part_2 (n f x : Z) (Hn : 1 <= n) (Hf : 2 <= f)
  (Hx : 1 <= x < f) : prime f -> (f | n) -> (f | remove_factors_le n x).
Proof.
  assert (0 <= x) by lia. revert Hx. pattern x.
  apply Z_lt_induction; auto; intros. clear H x.
  assert (x0 = 1 \/ 1 < x0) by lia. destruct H as [H | H].
  + subst x0. rewrite remove_factors_up_to_one; auto.
  + assert (f | remove_factors_le n (x0 - 1)). { apply H0; try lia; auto. }
    rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    pose proof (remove_factor_main_lemma (remove_factors_le n (x0 - 1)) x0).
    rewrite H4 in H3; try lia.
    - apply prime_mult in H3; auto. destruct H3; auto.
      apply prime_dvd_of_dvd_pow in H3; auto; try lia.
      * apply Zdivide_le in H3; lia.
      * apply factor_exponent_nonneg.
    - apply remove_factors_le_pos; lia.
Qed.

Lemma remove_factors_le_main_lemma (n f1 f2 : Z) (Hn : 1 <= n) (Hi : 2 <= f1)
  (H : f2 = f1 - 1) : (f1 | remove_factors_le n f2) <-> prime f1 /\ (f1 | n).
Proof.
  rewrite H. constructor; intros.
  + apply remove_factors_le_main_lemma_part_1 in H0; auto.
  + destruct H0. apply remove_factors_le_main_lemma_part_2; try lia; auto.
Qed.

Lemma remove_factors_le_ignores_composite (n f1 f2 : Z) (Hn : 1 <= n) (Hf : 2 <= f1)
  (Hf0 : prime f1 -> False) (H : f2 = f1 - 1) :
  remove_factors_le n f1 = remove_factors_le n f2.
Proof.
  rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
  assert ((f1 | remove_factors_le n f2) -> False).
  { rewrite H. rewrite remove_factors_le_main_lemma; try lia; tauto. }
  rewrite remove_factor_equation. pose proof (remove_factors_le_pos n (f1 - 1)).
  repeat destruct Z_le_dec; try lia. rewrite H in H0.
  destruct Zdivide_dec; try tauto. congruence.
Qed.

Lemma remove_factor_le_composite_has_bound (n f : Z) (Hn : 1 <= n) 
  (Hf : 2 <= f) (H : ~ prime (remove_factors_le n f)) (H0 : 1 < remove_factors_le n f) :
  (f + 1) * (f + 1) <= remove_factors_le n f.
Proof.
  intros. apply not_prime_divide in H; auto. destruct H as [m [H H1]].
  assert (remove_factors_le n f = m * (remove_factors_le n f / m)).
  { rewrite <- Zdivide_Zdiv_eq; try lia; auto. }
  pose proof (remove_factors_le_not_dvd_by_factor _ m f Hn ltac:(lia)).
  assert (m <= f \/ f < m) by lia. destruct H4; try tauto.
  assert (remove_factors_le n f / m | remove_factors_le n f). { exists m. auto. }
  destruct (Z_le_dec (remove_factors_le n f / m) f).
  + exfalso. apply remove_factors_le_not_dvd_by_factor in H5; try nia; auto.
  + rewrite H2. apply Z.mul_le_mono_nonneg; try lia.
Qed.

Lemma remove_factors_le_stays_one (n f k : Z) (Hn : 1 <= n) (Hf : 2 <= f)
  (Hk : f <= k) (H : remove_factors_le n f = 1) : remove_factors_le n k = 1.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H0 k.
  assert (f = x \/ f < x) by lia. destruct H0.
  + subst. auto.
  + pose proof (H1 (x - 1) ltac:(lia) ltac:(lia)).
    rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    rewrite H2, remove_factor_equation. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec; auto. apply Z.divide_pos_le in d; try lia.
Qed.

Lemma remove_factors_le_nonincreasing (n a b : Z) (Hn : 1 <= n) (Ha : 1 <= a)
  (Hb : a <= b) : remove_factors_le n b <= remove_factors_le n a.
Proof.
  assert (0 <= b) by lia. revert Hb. pattern b.
  apply Z_lt_induction; auto; intros. clear H b.
  assert (a = x \/ a < x) by lia. destruct H.
  + rewrite H. lia.
  + rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
    pose proof (remove_factors_le_pos n (x - 1) Hn ltac:(lia)).
    pose proof (remove_factor_le_self (remove_factors_le n (x - 1)) x); try lia.
Qed.

(* lemmas about `prime_factors` *)

Lemma prime_factors_up_to_all_prime (n k p : Z) (Hn : 1 <= n) (Hk : 1 <= k)
  (H : In p (map fst (prime_factors_up_to n k))) : prime p.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk H. pattern k.
  apply Z_lt_induction; auto; intros. clear H0 k.
  assert (x = 1 \/ 2 <= x) by lia. destruct H0.
  + subst x. rewrite prime_factors_up_to_equation in H1. simpl in H1.
    destruct Z_le_dec; elim H1.
  + rewrite prime_factors_up_to_equation in H1. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst x. rewrite remove_factors_le_main_lemma in d; try lia; tauto.
      * apply H in H1; try lia; auto.
    - apply H in H1; try lia; auto.
Qed.

Lemma prime_factors_up_to_step (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  prime_factors_up_to n k =
  if prime_dec k
  then if Zdivide_dec k n
       then (k, factor_exponent n k) :: prime_factors_up_to n (k - 1)
       else prime_factors_up_to n (k - 1)
  else prime_factors_up_to n (k - 1).
Proof.
  rewrite prime_factors_up_to_equation. repeat destruct Z_le_dec; try lia.
  destruct Zdivide_dec.
  + rewrite remove_factors_le_main_lemma in d; try lia.
    destruct prime_dec; try destruct Zdivide_dec; try tauto.
  + rewrite remove_factors_le_main_lemma in n0; try lia.
    destruct prime_dec; try destruct Zdivide_dec; try tauto.
Qed.

Lemma head_is_greatest_prime_factor_up_to (n k : Z) (Hn : 1 <= n)
  (Hk : 1 <= k) :
  match prime_factors_up_to n k with
  | nil => True
  | (head, _) :: _ => is_greatest (fun p => p <= k /\ prime p /\ (p | n)) head
  end.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H k.
  assert (x = 1 \/ 1 < x) by lia. destruct H.
  + subst. rewrite prime_factors_up_to_equation. repeat destruct Z_le_dec; try lia.
  + rewrite prime_factors_up_to_step; try lia. destruct prime_dec.
    - destruct Zdivide_dec.
      * constructor; try tauto. constructor; try lia. tauto.
      * pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
        destruct (prime_factors_up_to n (x - 1)); auto. destruct p0.
        unfold is_greatest in *. constructor.
        ++ constructor. lia. tauto.
        ++ intros. apply H1. constructor; try tauto.
           assert (x <> y). { intro. apply n0. rewrite H3. tauto. }
           lia.
    - pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
      destruct (prime_factors_up_to n (x - 1)); auto.
      unfold is_greatest in *. destruct p. constructor.
      ++ constructor. lia. tauto.
      ++ intros. apply H1. constructor; try tauto.
         assert (x <> y). { intro. apply n0. rewrite H3. tauto. }
         lia.
Qed.

Lemma prime_factors_head_is_bound (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  match prime_factors_up_to n k with
  | nil => True
  | (x, _) :: _ => x <= k
  end.
Proof.
  pose proof (head_is_greatest_prime_factor_up_to n k Hn ltac:(lia)).
  destruct (prime_factors_up_to n k); auto. destruct p. destruct H. tauto.
Qed.


(* greatest prime factor *)

Definition greatest_prime_factor_up_to (n k : Z) : Z :=
  match prime_factors_up_to n k with
  | [] => 1
  | (x, _) :: _ => x
  end.

Lemma greatest_prime_factor_up_to_pos (n k : Z) (Hn : 1 <= n) (Hk : 1 <= k) :
  1 <= greatest_prime_factor_up_to n k.
Proof.
  unfold greatest_prime_factor_up_to. pose proof (prime_factors_up_to_all_prime n k).
  remember (prime_factors_up_to n k) as W. destruct W; try lia.
  assert (prime (fst p)).
  { apply H; auto. rewrite HeqW. apply in_map. rewrite <- HeqW. simpl. auto. }
  destruct p; simpl in *. destruct H0. lia.
Qed.

Lemma greatest_prime_factor_up_to_le_self (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  greatest_prime_factor_up_to n k <= n.
Proof.
  unfold greatest_prime_factor_up_to. 
  pose proof (head_is_greatest_prime_factor_up_to n k Hn ltac:(lia)).
  remember (prime_factors_up_to n k) as W. destruct W; try lia.
  destruct p. destruct H. destruct H as [H [H1 H2]].
  apply Z.divide_pos_le in H2; lia.
Qed.

Lemma greatest_prime_factor_up_to_le_bound (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  greatest_prime_factor_up_to n k <= k.
Proof.
  unfold greatest_prime_factor_up_to. pose proof (prime_factors_head_is_bound _ _ Hn Hk).
  destruct (prime_factors_up_to n k); try lia. destruct p; auto.
Qed.

Lemma greatest_prime_factor_skip_composite (n k1 k2 : Z) (Hn : 1 <= n) (Hk : 2 <= k1)
  (Hk0 : ~ prime k1) (H : k2 = k1 - 1) :
  greatest_prime_factor_up_to n k1 = greatest_prime_factor_up_to n k2.
Proof.
  unfold greatest_prime_factor_up_to. rewrite H, prime_factors_up_to_step; try lia.
  destruct prime_dec; try tauto.
Qed.

Lemma greatest_prime_factor_skip_nondivisor (n k1 k2 : Z) (Hn : 1 <= n) (Hk : 2 <= k1)
  (Hk0 : ~ (k1 | n)) (H : k2 = k1 - 1) :
  greatest_prime_factor_up_to n k1 = greatest_prime_factor_up_to n k2.
Proof.
  unfold greatest_prime_factor_up_to. rewrite H, prime_factors_up_to_step; try lia.
  destruct Zdivide_dec; try tauto. destruct prime_dec; auto.
Qed.

Lemma greatest_prime_factor_skip_irrelevant (n k1 k2 : Z) (Hn : 1 <= n)
  (Hk : 2 <= k1) (H : k2 = k1 - 1) (H0 : ~ (prime k1 /\ (k1 | n))) :
  greatest_prime_factor_up_to n k1 = greatest_prime_factor_up_to n k2.
Proof.
  assert (~ prime k1 \/ ~ (k1 | n)). { destruct (prime_dec k1); tauto. } destruct H1.
  + apply greatest_prime_factor_skip_composite; try lia; auto.
  + apply greatest_prime_factor_skip_nondivisor; try lia; auto.
Qed.

Lemma greatest_prime_factor_eq_of_prime_divisor (n k : Z) (Hn : 1 <= n) (Hk : prime k)
  (Hd : (k | n)) : greatest_prime_factor_up_to n k = k.
Proof.
  unfold greatest_prime_factor_up_to. rewrite prime_factors_up_to_step; try lia.
  + destruct prime_dec; try destruct Zdivide_dec; try tauto.
  + apply prime_ge_2; auto.
Qed.

Lemma prime_factors_persist (n k k0 : Z) (Hn : 2 <= n) (Hk : prime k)
  (Hk' : (k | n)) (H : k <= k0) : In k (map fst (prime_factors_up_to n k0)).
Proof.
  assert (2 <= k) by (apply prime_ge_2; auto).
  assert (0 <= k0) by lia. revert H. pattern k0.
  apply Z_lt_induction; auto; intros. clear H1 k0.
  assert (k = x \/ k < x) by lia. destruct H1.
  + subst x. pose proof (greatest_prime_factor_eq_of_prime_divisor n k ltac:(lia) Hk Hk').
    unfold greatest_prime_factor_up_to in H1. destruct (prime_factors_up_to n k); try lia.
    simpl; tauto.
  + rewrite prime_factors_up_to_step; try lia. destruct prime_dec; try tauto.
    - destruct Zdivide_dec; try lia.
      * simpl. right. apply H; try lia.
      * apply H; try lia.
    - apply H; try lia.
Qed.

Lemma greatest_prime_factor_up_to_by_self (n : Z) (Hn : 2 <= n) :
  prime (greatest_prime_factor_up_to n n).
Proof.
  destruct (prime_divisor_existence n Hn) as [p [H H0]].
  assert (In p (map fst (prime_factors_up_to n n))).
  { apply prime_factors_persist; auto; try lia.
    apply Z.divide_pos_le in H0; lia. }
  unfold greatest_prime_factor_up_to. remember (prime_factors_up_to n n) as W.
  destruct W.
  + apply (prime_factors_up_to_all_prime n n); try lia.
    rewrite <- HeqW. simpl. auto.
  + destruct p0. assert (In z (map fst (prime_factors_up_to n n))).
    { rewrite <- HeqW. simpl. auto. }
    apply prime_factors_up_to_all_prime in H2; auto; lia.
Qed.

Lemma greatest_prime_factor_const_of_remove_factors_le_eq_one (n k l : Z) (Hn : 2 <= n)
  (Hk : 2 <= k) (Hl : k <= l) (H : remove_factors_le n k = 1) :
  greatest_prime_factor_up_to n l = greatest_prime_factor_up_to n k.
Proof.
  assert (0 <= l) by lia. revert Hl. pattern l.
  apply Z_lt_induction; auto; intros. clear H0 l.
  assert (k = x \/ k < x) by lia. destruct H0; try congruence.
  destruct (prime_dec x).
  + destruct (Zdivide_dec x n).
    - assert (prime x /\ (x | n)) by tauto.
      rewrite <- remove_factors_le_main_lemma with (f2 := x - 1) in H2; try lia.
      assert (remove_factors_le n (x - 1) = 1).
      { apply remove_factors_le_stays_one with (k := x - 1) in H; try lia. }
      rewrite H3 in H2. apply Z.divide_1_r_nonneg in H2; try lia.
    - rewrite greatest_prime_factor_skip_nondivisor with (k2 := x - 1); try lia; auto.
      apply H1; try lia.
  + rewrite greatest_prime_factor_skip_composite with (k2 := x - 1); try lia; auto.
    apply H1; try lia.
Qed.

Lemma greatest_prime_factor_const_above_n (n k : Z) (Hn : 1 <= n) (Hk : n <= k) :
  greatest_prime_factor_up_to n k = greatest_prime_factor_up_to n n.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H k.
  assert (n = x \/ n < x) by lia. destruct H.
  + congruence.
  + rewrite (greatest_prime_factor_skip_nondivisor n x (x - 1)); try lia.
    - apply H0; lia.
    - intro. apply Z.divide_pos_le in H1; lia.
Qed.


(* Lemmas about factor exponent *)

Lemma factor_exponent_mul_succ (a f : Z) (Ha : 1 <= a) (Hf : prime f) :
  factor_exponent (f * a) f = 1 + factor_exponent a f.
Proof.
  assert (0 <= a) by lia. revert Ha. pattern a.
  apply Z_lt_induction; auto; intros. rewrite factor_exponent_equation.
  assert (2 <= f). { destruct Hf; lia. } assert (1 <= f * x) by nia. 
  repeat destruct Z_le_dec; try lia. destruct Zdivide_dec.
  + rewrite Z.mul_comm, Z.div_mul; try lia.
  + exfalso. apply n. exists x. ring.
Qed.

Lemma factor_exponent_mul_unchanged (a b f : Z)
  (Ha : 1 <= a) (Hb : 1 <= b) (Hf: prime f) (Ha0 : ~ (f | a)) :
  factor_exponent (a * b) f = factor_exponent b f.
Proof.
  rewrite Z.mul_comm. assert (0 <= b) by lia. revert Hb. pattern b.
  apply Z_lt_induction; auto; intros. rewrite factor_exponent_equation.
  assert (2 <= f). { destruct Hf; lia. } assert (1 <= x * a) by nia.
  repeat destruct Z_le_dec; try lia. destruct Zdivide_dec.
  + apply prime_mult in d; auto. destruct d; try tauto. destruct H3.
    subst x. replace (x0 * f * a) with (x0 * a * f) by ring.
    rewrite Z.div_mul; try lia.
    rewrite H0, Z.mul_comm, factor_exponent_mul_succ; try nia; auto.
  + rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec; try tauto. exfalso. apply n. destruct d.
    exists (x0 * a). rewrite H3. ring.
Qed.

Lemma factor_exponent_of_product_as_sum
  (a b f : Z) (Ha : 1 <= a) (Hb : 1 <= b) (Hf : prime f) :
  factor_exponent (a * b) f = factor_exponent a f + factor_exponent b f.
Proof.
  assert (0 <= a) by lia. revert Ha Hb. pattern a.
  apply Z_lt_induction; intros; auto. clear H a. destruct (Zdivide_dec f x).
  + destruct d. subst x. replace (x0 * f * b) with (f * (x0 * b)) by ring.
    rewrite factor_exponent_mul_succ; auto.
    - rewrite (Z.mul_comm x0 f), factor_exponent_mul_succ; try lia; auto.
      * destruct Hf. rewrite H0; nia.
      * destruct Hf. nia.
    - destruct Hf; nia.
  + rewrite factor_exponent_mul_unchanged; auto. rewrite (factor_exponent_equation x f).
    repeat destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto. 
Qed.

Lemma factor_exponent_of_pow (f n i : Z) (Hi : 0 <= i) (Hn : 1 <= n) (Hf : prime f) :
  factor_exponent (n ^ i) f = i * factor_exponent n f.
Proof.
  pose proof Hi. revert Hi. pattern i. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H1.
  + subst x. simpl. rewrite factor_exponent_equation.
    repeat destruct Z_le_dec; try lia. destruct Zdivide_dec; auto.
    exfalso. destruct Hf. apply Z.divide_pos_le in d; try lia.
  + replace x with (x - 1 + 1) at 1 by ring. rewrite Z.pow_add_r; try lia.
    ring_simplify (n ^ 1). rewrite factor_exponent_of_product_as_sum; auto; try lia.
    rewrite H0; try lia.
Qed.

Lemma factor_exponent_pow_coprime (f p i : Z) (Hp : prime p) (Hf : ~ (p | f))
  (Hf0 : 1 <= f) (Hi : 0 <= i) : factor_exponent (f ^ i) p = 0.
Proof.
  pose proof Hi. revert Hi. pattern i. apply Z_lt_induction; auto; intros.
  clear H i. assert (x = 0 \/ 1 <= x) by lia. destruct H.
  + subst x. simpl. rewrite factor_exponent_equation. destruct Z_le_dec; try lia.
    destruct Z_le_dec; auto. destruct Zdivide_dec; auto.
    exfalso. apply Zdivide_le in d; destruct Hp; lia.
  + replace x with (x - 1 + 1) by ring. rewrite Z.pow_add_r; try lia.
    ring_simplify (f ^ 1). rewrite factor_exponent_of_product_as_sum; try lia; auto.
    rewrite H0; try lia. rewrite factor_exponent_equation.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try (destruct Hp; lia).
    destruct Zdivide_dec; try tauto.
Qed.

Lemma factor_exponent_of_another_prime (p q : Z) (Hp : prime p) (Hq : prime q)
  (Hpq : p <> q) : factor_exponent p q = 0.
Proof.
  replace p with (p ^ 1) by ring. apply factor_exponent_pow_coprime; auto; try lia.
  + intro H. apply prime_div_prime in H; auto.
  + destruct Hp; lia.
Qed.

Lemma factor_exponent_remove_factor (n f p : Z) (Hf : 1 <= f < p) (Hp : prime p)
  (Hn : 1 <= n) : factor_exponent (remove_factor n f) p = factor_exponent n p.
Proof.
  assert (f = 1 \/ 2 <= f) by lia. destruct H.
  + subst f. rewrite remove_factor_equation. simpl. destruct Z_le_dec; auto.
  + rewrite (remove_factor_main_lemma n f) at 2; try lia.
    rewrite factor_exponent_of_product_as_sum; auto.
    - rewrite factor_exponent_pow_coprime; auto; try lia.
      * intro. apply Zdivide_le in H0; try lia.
      * apply factor_exponent_nonneg.
    - apply remove_factor_pos; auto.
    - pose proof (Z.pow_pos_nonneg f (factor_exponent n f)).
      pose proof (factor_exponent_nonneg n f). lia.
Qed.

Lemma factor_exponent_remove_factors_le (n f p : Z) (Hn : 1 <= n) (Hp : prime p)
  (Hf : 1 <= f < p) :
  factor_exponent (remove_factors_le n f) p = factor_exponent n p.
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 1 \/ 2 <= x) by lia. destruct H.
  + subst x. rewrite remove_factors_up_to_one; auto.
  + rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    rewrite factor_exponent_remove_factor; auto; try lia.
    - rewrite H0; try lia.
    - apply remove_factors_le_pos; lia.
Qed.

Lemma remove_factors_le_factorization (n f : Z) (Hn : 1 <= n) (Hf : 1 <= f) :
  n = remove_factors_le n f * List.fold_left Z.mul 
      (map (fun p => fst p ^ snd p) (prime_factors_up_to n f)) 1.
Proof.
  assert (0 <= f) by lia. revert Hf n Hn. pattern f.
  apply Z_lt_induction; auto; intros. clear f H.
  assert (x = 1 \/ 2 <= x) by lia. destruct H.
  + subst x. rewrite remove_factors_up_to_one; auto.
    rewrite prime_factors_up_to_equation. simpl. destruct Z_le_dec; simpl; lia.
  + rewrite remove_factors_le_equation. repeat destruct Z_le_dec; try lia.
    rewrite H0 with (y := x - 1) at 1; try lia.
    rewrite (remove_factor_main_lemma (remove_factors_le n (x - 1)) x) at 1; try lia.
    - rewrite <- Z.mul_assoc. f_equal. rewrite (prime_factors_up_to_equation n x).
      repeat destruct Z_le_dec; try lia. destruct Zdivide_dec.
      * assert (forall A (x : A) L (f : A -> Z), fold_left Z.mul (map f (x :: L)) 1 =
          fold_left Z.mul (map f L) (f x)).
        { intros. replace (fold_left _ _ 1) with (fold_left Z.mul (map f L) (1 * f x0))
            by auto. rewrite Z.mul_1_l. auto. } 
        assert (forall L a, fold_left Z.mul L a = a * fold_left Z.mul L 1).
        { induction L; intros; try lia; try (simpl; ring).
          simpl (fold_left _ _ a0). rewrite IHL.
          replace (fold_left _ (a :: L) 1) with (fold_left Z.mul L (1 * a)) by (auto).
          rewrite Z.mul_1_l, (IHL a). ring. }
        rewrite H1, H2, (H2 _ (x ^ _)), Z.mul_1_l. f_equal. f_equal.
        rewrite factor_exponent_remove_factors_le; try lia; auto.
        rewrite remove_factors_le_main_lemma in d; auto. tauto.
      * rewrite <- (Z.mul_1_l (fold_left _ _ 1)) at 2. f_equal.
        replace 1 with (x ^ 0) at 2 by ring. f_equal.
        rewrite factor_exponent_equation. pose proof (remove_factors_le_pos n (x - 1)).
        repeat destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
    - apply remove_factors_le_pos; try lia.
Qed.

Lemma remove_factors_le_self_eq_one (n : Z) (Hn : 1 <= n) :
  remove_factors_le n n = 1.
Proof.
  destruct (Z_le_dec n 1).
  + assert (n = 1) by lia. subst. auto.
  + assert (2 <= n) by lia. clear n0 Hn.
    pose proof (remove_factors_le_pos n n ltac:(lia) ltac:(lia)).
    pose proof (remove_factors_le_dvd_self n n ltac:(lia) ltac:(lia)).
    destruct (Z_le_dec 2 (remove_factors_le n n)); try lia. exfalso.
    destruct (prime_divisor_existence _ l). destruct H2.
    assert (x | n). { exact (Z.divide_trans _ _ _ H3 H1). }
    assert (2 <= x). { destruct H2; lia. }
    apply remove_factors_le_not_dvd_by_factor in H3; try lia.
    apply Zdivide_le in H4; try lia.
Qed.

Lemma factorization (n : Z) (Hn : 1 <= n) :
  n = List.fold_left Z.mul (map (fun p => fst p ^ snd p) (prime_factors_up_to n n)) 1.
Proof.
  rewrite (remove_factors_le_factorization n n Hn Hn) at 1.
  rewrite (remove_factors_le_self_eq_one n Hn). ring.
Qed.

Lemma snd_prime_factors_is_exp (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, In p (prime_factors_up_to n k) -> snd p = factor_exponent n (fst p).
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k.
  apply Z_lt_induction; auto; intros. assert (x = 2 \/ 3 <= x) by lia. destruct H2.
  + subst. rewrite prime_factors_up_to_step in H1; try lia.
    destruct (prime_dec 2); try (pose prime_2; tauto). destruct (Zdivide_dec 2 n).
    - simpl in H1. destruct H1.
      * subst p. simpl. auto.
      * rewrite prime_factors_up_to_equation in H1. repeat destruct Z_le_dec; try lia.
        elim H1.
    - simpl in H1. rewrite prime_factors_up_to_equation in H1.
      repeat destruct Z_le_dec; try lia. elim H1.
  + rewrite prime_factors_up_to_step in H1; try lia. destruct (prime_dec x).
    - destruct Zdivide_dec.
      * simpl in H1. destruct H1.
        ++ subst p. simpl. auto.
        ++ apply H0 in H1; try lia.
      * apply H0 in H1; try lia.
    - apply H0 in H1; try lia.
Qed.


Lemma factor_exponent_le_implies_dvd (a b : Z) (Ha : 1 <= a) (Hb : 1 <= b) :
  (forall p, prime p -> factor_exponent a p <= factor_exponent b p) -> (a | b).
Proof.
  revert b Hb. assert (0 <= a) by lia. revert Ha; pattern a. 
  apply Z_lt_induction; auto; intros. clear H a. destruct (Z_le_dec x 1).
  + assert (x = 1) by lia. subst x. exists b. ring.
  + destruct (prime_divisor_existence x ltac:(lia)) as [p [Hp Hp_dvd]].
    set (e := factor_exponent x p).
    assert (x = p ^ e * (remove_factor x p)).
    { rewrite (remove_factor_main_lemma x p) at 1; try lia. unfold e. ring.
      destruct Hp; lia. } 
    assert (~ (p | remove_factor x p)).
    { intro. apply remove_factor_not_divided_by_factor in H2; try lia.
      destruct Hp; lia. }
    assert ((p ^ e) | b).
    { pose proof (H1 p Hp). assert (b = p ^ factor_exponent b p * remove_factor b p).
      { rewrite (remove_factor_main_lemma b p) at 1; try lia. destruct Hp; lia. }
      exists (p ^ (factor_exponent b p - factor_exponent x p) * remove_factor b p).
      unfold e. assert (forall (a1 a2 a3 : Z), a1 * a2 * a3 = a1 * a3 * a2) by (intros; ring).
      rewrite H5; clear H5. rewrite <- Z.pow_add_r.
      + rewrite Z.sub_add. auto.
      + lia.
      + apply factor_exponent_nonneg. }
    destruct H3 as [b' H3].
    assert (1 <= b').
    { unfold e in H3. pose proof (factor_exponent_nonneg x p).
      pose proof (Z.pow_pos_nonneg p (factor_exponent x p)). destruct Hp; nia. }
    assert (forall q, prime q -> q <> p -> factor_exponent (remove_factor x p) q = factor_exponent x q).
    { intros. rewrite (remove_factor_main_lemma x p) at 2; try (destruct Hp; lia).
      rewrite factor_exponent_of_product_as_sum; auto.
      + rewrite factor_exponent_pow_coprime; auto.
        - rewrite Z.add_0_r. auto.
        - intro. apply prime_div_prime in H7; auto.
        - destruct Hp. lia.
        - apply factor_exponent_nonneg.
      + apply remove_factor_pos. lia.
      + pose proof (factor_exponent_nonneg x p).
        pose proof (Z.pow_pos_nonneg p (factor_exponent x p)). destruct Hp; lia. }
    assert (forall q, prime q -> factor_exponent (remove_factor x p) q <= factor_exponent b' q).
    { intros. destruct (Z.eq_dec p q).
      + subst q. assert (factor_exponent (remove_factor x p) p = 0).
        { rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
          destruct Zdivide_dec; auto. exfalso.
          apply remove_factor_not_divided_by_factor in d; try lia. }
        rewrite H7. apply factor_exponent_nonneg.
      + assert (factor_exponent (remove_factor x p) q = factor_exponent x q).
        { apply H5; auto. }
        rewrite H7.
        assert (factor_exponent x q <= factor_exponent b q).
        { apply H1; auto. }
        rewrite H3 in H8. rewrite factor_exponent_of_product_as_sum in H8; auto.
        - rewrite factor_exponent_pow_coprime in H8; try lia; auto.
          * intro. apply prime_div_prime in H9; auto.
          * destruct Hp; lia.
          * unfold e. apply factor_exponent_nonneg.
        - unfold e. pose proof (factor_exponent_nonneg x p).
          pose proof Z.pow_pos_nonneg p (factor_exponent x p).
          destruct Hp; lia. }
    assert (remove_factor x p | b').
    { apply H0.
      + split.
        - pose proof (remove_factor_pos x p); lia.
        - apply Z.le_lt_trans with (m := x / p).
          * rewrite remove_factor_equation. repeat destruct Z_le_dec; try (destruct Hp; lia).
            destruct Zdivide_dec; try tauto. apply remove_factor_le_self.
            destruct d. subst. rewrite Z.div_mul; try lia.
          * pose proof (Z.div_lt x p). destruct Hp; lia.
      + apply remove_factor_pos. lia.
      + auto.
      + intros. apply H6; auto. }
    rewrite H, H3. destruct H7. rewrite H7. exists x0. ring.
Qed.

Lemma factor_exponent_le_iff_dvd (a b : Z) (Ha : 1 <= a) (Hb : 1 <= b) :
  (forall p, prime p -> factor_exponent a p <= factor_exponent b p) <-> (a | b).
Proof.
  split; intros.
  + apply factor_exponent_le_implies_dvd; auto.
  + destruct H. assert (1 <= x) by nia. rewrite H.
    rewrite factor_exponent_of_product_as_sum; auto.
    pose proof (factor_exponent_nonneg x p). lia.
Qed.

