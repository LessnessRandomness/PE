Require Import VST.floyd.proofauto.
From Stdlib Require Import Znumtheory ZArith.
Open Scope Z.

Function rep_div (n f : Z) { measure Z.to_nat n } : Z :=
  if Z_le_dec 1 n
  then if (Z_le_dec 2 f)
       then if Zdivide_dec f n
            then rep_div (n / f) f
            else n
       else n
  else n.
Proof. intros. assert (n / f < n). { apply Z.div_lt; lia. } lia. Defined.

Function rep_rep_div (n f : Z) { measure Z.to_nat f } : Z :=
  if Z_le_dec 1 n
  then if Z_le_dec 2 f
       then rep_div (rep_rep_div n (f - 1)) f
       else n
  else n.
Proof. lia. Defined.

Function prime_factors (n f : Z) { measure Z.to_nat f } : list Z :=
  if Z_le_dec 1 n
  then if Z_le_dec 2 f
       then 
            if Zdivide_dec f (rep_rep_div n (f - 1))
            then f :: prime_factors n (f - 1)
            else prime_factors n (f - 1)
       else []
  else [].
Proof. lia. lia. Defined.

Definition IsGreatest (s : Z -> Prop) (x : Z) :=
  s x /\ (forall y, s y -> y <= x).

(* Lemmas about the function 'rep_div' *)

Lemma one_le_rep_div (n f : Z) (Hn : 1 <= n) : 1 <= rep_div n f.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros. clear H n. rewrite rep_div_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; auto.
  assert (x / f < x). { apply Z.div_lt; lia. }
  assert (1 <= rep_div (x / f) f).
  { pose proof Zdivide_Zdiv_lt_pos f x ltac:(lia) ltac:(lia) d.
    apply H0; lia. }
  simpl in *; lia.
Qed.

Lemma rep_div_le_self (n f : Z) (Hn : 1 <= n) : rep_div n f <= n.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros. clear H n. rewrite rep_div_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; try lia.
  assert (x / f < x). { apply Z.div_lt; lia. }
  assert (rep_div (x / f) f <= x / f).
  { pose proof Zdivide_Zdiv_lt_pos f x ltac:(lia) ltac:(lia) d.
    apply H0; lia. }
  simpl in *; lia.
Qed.

Lemma rep_div_main_lemma (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  exists (i : Z), 0 <= i /\ n = rep_div n f * f ^ i.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros. clear H n. rewrite rep_div_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; try (exists 0; lia).
  assert (0 < x / f < x).
  { constructor.
    + apply Zdivide_Zdiv_lt_pos; try lia; auto.
    + apply Z.div_lt; lia. }
  destruct (H0 (x / f) ltac:(lia) ltac:(lia)) as [i [Hi0 Hi1]].
  exists (i + 1). constructor; try lia. rewrite Z.pow_add_r; try lia.
  ring_simplify (f ^ 1). destruct d as [d Hd].
  rewrite Z.mul_assoc, <- Hi1, Hd, Z_div_mult; try lia.
Qed.

Lemma rep_div_not_dvd_by_factor (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (f | rep_div n f) -> False.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n.
  apply Z_lt_induction; auto; intros ? ? ?. clear H n.
  rewrite rep_div_equation.
  repeat destruct Z_le_dec; try destruct Zdivide_dec; auto.
  assert (0 < x / f < x).
  { constructor.
    + apply Zdivide_Zdiv_lt_pos; try lia; auto.
    + apply Z.div_lt; lia. }
  apply H0; lia.
Qed.

Lemma rep_div_dvd_self (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
 (rep_div n f | n).
Proof.
  destruct (rep_div_main_lemma n f) as [i [Hi0 Hi1]]; try lia.
  rewrite Hi1 at 2. apply Z.divide_factor_l.
Qed.

(* lemmas about `rep_rep_div` *)

Lemma rep_rep_div_by_one (n : Z) (Hn : 1 <= n) : rep_rep_div n 1 = n.
Proof.
  rewrite rep_rep_div_equation. simpl. destruct Z_le_dec; lia.
Qed.

Lemma rep_rep_div_by_two (n : Z) (Hn : 1 <= n) : rep_rep_div n 2 = rep_div n 2.
Proof.
  rewrite rep_rep_div_equation, rep_rep_div_by_one; try lia. simpl.
  destruct Z_le_dec; lia.
Qed.

Lemma one_le_rep_rep_div (n f : Z) (Hn : 1 <= n) (Hf : 1 <= f) :
  1 <= rep_rep_div n f.
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 1 \/ 1 < x) by lia. destruct H as [H | H].
  + subst x. rewrite rep_rep_div_by_one; auto.
  + rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
    apply one_le_rep_div. apply H0; lia.
Qed.

Lemma rep_rep_div_le_self (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  rep_rep_div n f <= n.
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 2 \/ 2 < x) by lia. destruct H as [H | H].
  + subst x. rewrite rep_rep_div_by_two; auto. apply rep_div_le_self; auto.
  + rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
    assert (rep_div (rep_rep_div n (x - 1)) x <= rep_rep_div n (x - 1)).
    { apply rep_div_le_self. apply one_le_rep_rep_div; lia. }
    assert (rep_rep_div n (x - 1) <= n). { apply H0; lia. }
    lia.
Qed.

Lemma rep_rep_div_not_dvd_by_factor (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (f | rep_rep_div n f) -> False.
Proof.
  rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
  apply rep_div_not_dvd_by_factor; auto.
  assert (f = 2 \/ 2 < f) by lia. destruct H as [H | H].
  + subst. simpl. rewrite rep_rep_div_by_one; auto.
  + apply one_le_rep_rep_div; lia.
Qed.

Lemma rep_rep_div_not_dvd_by_le (n f x : Z) (Hn : 1 <= n) (Hf : 2 <= f)
  (Hx : f <= x) : (f | rep_rep_div n x) -> False.
Proof.
  assert (0 <= x) by lia. revert Hx. pattern x.
  apply Z_lt_induction; auto; intros. clear H x.
  assert (x0 = f \/ f < x0) by lia. destruct H as [H | H].
  + subst x0. apply rep_rep_div_not_dvd_by_factor in H1; lia.
  + apply H0 with (y := x0 - 1); try lia.
    rewrite rep_rep_div_equation in H1. repeat destruct Z_le_dec; try lia.
    assert (rep_div (rep_rep_div n (x0 - 1)) x0 | rep_rep_div n (x0 - 1)).
    { apply rep_div_dvd_self; try lia. apply one_le_rep_rep_div; try lia. }
    eapply Z.divide_trans; eauto.
Qed.

Lemma rep_rep_div_dvd_self (n f : Z) (Hn : 1 <= n) (Hf : 1 <= f) :
  (rep_rep_div n f | n).
Proof.
  assert (0 <= f) by lia. revert Hf. pattern f.
  apply Z_lt_induction; auto; intros. clear H f.
  assert (x = 1 \/ 1 < x) by lia. destruct H.
  + subst x. rewrite rep_rep_div_by_one; auto. exists 1; ring.
  + rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
    pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
    pose proof (one_le_rep_rep_div n (x - 1) Hn ltac:(lia)).
    pose proof (rep_div_dvd_self (rep_rep_div n (x - 1)) x H2 l0).
    exact (Z.divide_trans _ _ _ H3 H1).
Qed.

Theorem prime_divisor_existence (n: Z) (H: 2 <= n):
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

Lemma rep_rep_div_main_lemma_part_1 (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) :
  (f | rep_rep_div n (f - 1)) -> prime f /\ (f | n).
Proof.
  intros H. constructor.
  + destruct (prime_dec f); auto. pose proof (prime_divisor_existence f Hf).
    exfalso. destruct H0 as [p [Hp Hp0]]. assert (p <= f).
    { apply Zdivide_le; auto; try lia. pose proof (prime_ge_2 _ Hp). lia. }
    assert (p <> f) by congruence.
    apply (rep_rep_div_not_dvd_by_le n p (f - 1) Hn (prime_ge_2 _ Hp));
      try lia. eapply Z.divide_trans; eauto.
  + pose proof (rep_rep_div_dvd_self n (f - 1) Hn ltac:(lia)).
    exact (Z.divide_trans _ _ _ H H0).
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

Lemma rep_rep_div_main_lemma_part_2 (n f x : Z) (Hn : 1 <= n) (Hf : 2 <= f)
  (Hx : 1 <= x < f) : prime f -> (f | n) -> (f | rep_rep_div n x).
Proof.
  assert (0 <= x) by lia. revert Hx. pattern x.
  apply Z_lt_induction; auto; intros. clear H x.
  assert (x0 = 1 \/ 1 < x0) by lia. destruct H as [H | H].
  + subst x0. rewrite rep_rep_div_by_one; auto.
  + assert (f | rep_rep_div n (x0 - 1)). { apply H0; try lia; auto. }
    rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
    destruct (rep_div_main_lemma (rep_rep_div n (x0 - 1)) x0) as [w hw]; auto.
    - apply one_le_rep_rep_div; try lia.
    - rewrite (proj2 hw) in H3. apply prime_mult in H3; auto.
      destruct H3 as [H3 | H3]; auto.
      apply prime_dvd_of_dvd_pow in H3; try lia; auto.
      apply Z.divide_pos_le in H3; lia.
Qed.

Lemma rep_rep_div_main_lemma (n f1 f2 : Z) (Hn : 1 <= n) (Hi : 2 <= f1)
  (H : f2 = f1 - 1) : (f1 | rep_rep_div n f2) <-> prime f1 /\ (f1 | n).
Proof.
  rewrite H. constructor; intros.
  + apply rep_rep_div_main_lemma_part_1 in H0; auto.
  + destruct H0. apply rep_rep_div_main_lemma_part_2; try lia; auto.
Qed.

Lemma rep_rep_div_by_not_prime (n f1 f2 : Z) (Hn : 1 <= n) (Hf : 2 <= f1)
  (Hf0 : prime f1 -> False) (H : f2 = f1 - 1) :
  rep_rep_div n f1 = rep_rep_div n f2.
Proof.
  rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
  assert ((f1 | rep_rep_div n f2) -> False).
  { rewrite H. rewrite rep_rep_div_main_lemma; try lia; tauto. }
  rewrite rep_div_equation. pose proof (one_le_rep_rep_div n (f1 - 1)).
  repeat destruct Z_le_dec; try lia. rewrite H in H0.
  destruct Zdivide_dec; try tauto. congruence.
Qed.

Lemma rep_rep_div_lower_bound_of_not_prime (n f : Z) (Hn : 1 <= n) 
  (Hf : 2 <= f) (H : ~ prime (rep_rep_div n f)) (H0 : 1 < rep_rep_div n f) :
  (f + 1) * (f + 1) <= rep_rep_div n f.
Proof.
  intros. apply not_prime_divide in H; auto. destruct H as [m [H H1]].
  assert (rep_rep_div n f = m * (rep_rep_div n f / m)).
  { rewrite <- Zdivide_Zdiv_eq; try lia; auto. }
  pose proof (rep_rep_div_not_dvd_by_le _ m f Hn ltac:(lia)).
  assert (m <= f \/ f < m) by lia. destruct H4; try tauto.
  assert (rep_rep_div n f / m | rep_rep_div n f). { exists m. auto. }
  assert (rep_rep_div n f / m <= f \/ f < rep_rep_div n f / m) by lia.
  destruct H6.
  + exfalso. apply rep_rep_div_not_dvd_by_le in H5; try nia; auto.
  + rewrite H2. apply Z.mul_le_mono_nonneg; try lia.
Qed.

Lemma rep_rep_div_stays_one (n f k : Z) (Hn : 1 <= n) (Hf : 2 <= f)
  (Hk : f <= k) (H : rep_rep_div n f = 1) : rep_rep_div n k = 1.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H0 k.
  assert (f = x \/ f < x) by lia. destruct H0.
  + subst. auto.
  + pose proof (H1 (x - 1) ltac:(lia) ltac:(lia)).
    rewrite rep_rep_div_equation. repeat destruct Z_le_dec; try lia.
    rewrite H2, rep_div_equation. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec; auto. apply Z.divide_pos_le in d; try lia.
Qed.

(* lemmas about `prime_factors` *)

Lemma prime_factors_all_prime (n k p : Z) (Hn : 1 <= n) (Hk : 1 <= k)
  (H : In p (prime_factors n k)) : prime p.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk H. pattern k.
  apply Z_lt_induction; auto; intros. clear H0 k.
  assert (x = 1 \/ 2 <= x) by lia. destruct H0.
  + subst x. rewrite prime_factors_equation in H1. simpl in H1.
    destruct Z_le_dec; tauto.
  + rewrite prime_factors_equation in H1. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst x. rewrite rep_rep_div_main_lemma in d; try lia; tauto.
      * apply H in H1; try lia; auto.
    - apply H in H1; try lia; auto.
Qed.

Lemma prime_factors_eq (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  prime_factors n k =
  if prime_dec k
  then if Zdivide_dec k n
       then k :: prime_factors n (k - 1)
       else prime_factors n (k - 1)
  else prime_factors n (k - 1).
Proof.
  rewrite prime_factors_equation. repeat destruct Z_le_dec; try lia.
  destruct Zdivide_dec.
  + rewrite rep_rep_div_main_lemma in d; try lia.
    destruct prime_dec; try destruct Zdivide_dec; try tauto.
  + rewrite rep_rep_div_main_lemma in n0; try lia.
    destruct prime_dec; try destruct Zdivide_dec; try tauto.
Qed.

Lemma prime_factors_head_greatest_prime_factor (n k : Z) (Hn : 1 <= n)
  (Hk : 1 <= k) :
  match prime_factors n k with
  | nil => True
  | head :: _ => IsGreatest (fun p => p <= k /\ prime p /\ (p | n)) head
  end.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H k.
  assert (x = 1 \/ 1 < x) by lia. destruct H.
  + subst. rewrite prime_factors_equation. repeat destruct Z_le_dec; try lia.
  + rewrite prime_factors_eq; try lia. destruct prime_dec.
    - destruct Zdivide_dec.
      * constructor; try tauto. constructor; try lia. tauto.
      * pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
        destruct (prime_factors n (x - 1)); auto.
        unfold IsGreatest in *. constructor.
        ++ constructor. lia. tauto.
        ++ intros. apply H1. constructor; try tauto.
           assert (x <> y). { intro. apply n0. rewrite H3. tauto. }
           lia.
    - pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
      destruct (prime_factors n (x - 1)); auto.
      unfold IsGreatest in *. constructor.
      ++ constructor. lia. tauto.
      ++ intros. apply H1. constructor; try tauto.
         assert (x <> y). { intro. apply n0. rewrite H3. tauto. }
         lia.
Qed.

Lemma prime_factors_head_le_limit (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  match prime_factors n k with
  | nil => True
  | x :: _ => x <= k
  end.
Proof.
  pose proof (prime_factors_head_greatest_prime_factor n k Hn ltac:(lia)).
  destruct (prime_factors n k); auto. destruct H. tauto.
Qed.

(* greatest [prime] factor *)

Definition greatest_factor (n k : Z) : Z :=
  match prime_factors n k with
  | [] => 1
  | x :: _ => x
  end.

Lemma greatest_factor_le_limit (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  greatest_factor n k <= k.
Proof.
  unfold greatest_factor. pose proof (prime_factors_head_le_limit _ _ Hn Hk).
  destruct (prime_factors n k); lia.
Qed.

Lemma greatest_factor_by_not_prime (n k1 k2 : Z) (Hn : 1 <= n) (Hk : 2 <= k1)
  (Hk0 : ~ prime k1) (H : k2 = k1 - 1) :
  greatest_factor n k1 = greatest_factor n k2.
Proof.
  unfold greatest_factor. rewrite H, prime_factors_eq; try lia.
  destruct prime_dec; try tauto.
Qed.

Lemma greatest_factor_by_not_dvd (n k1 k2 : Z) (Hn : 1 <= n) (Hk : 2 <= k1)
  (Hk0 : ~ (k1 | n)) (H : k2 = k1 - 1) :
  greatest_factor n k1 = greatest_factor n k2.
Proof.
  unfold greatest_factor. rewrite H, prime_factors_eq; try lia.
  destruct Zdivide_dec; try tauto. destruct prime_dec; auto.
Qed.

Lemma greatest_factor_by_not_prime_or_not_dvd (n k1 k2 : Z) (Hn : 1 <= n)
  (Hk : 2 <= k1) (H : k2 = k1 - 1) (H0 : ~ (prime k1 /\ (k1 | n))) :
  greatest_factor n k1 = greatest_factor n k2.
Proof.
  assert (~ prime k1 \/ ~ (k1 | n)) by tauto. destruct H1.
  + apply greatest_factor_by_not_prime; try lia; auto.
  + apply greatest_factor_by_not_dvd; try lia; auto.
Qed.

Lemma greatest_factor_eq (n k : Z) (Hn : 1 <= n) (Hk : prime k)
  (Hd : (k | n)) : greatest_factor n k = k.
Proof.
  unfold greatest_factor. rewrite prime_factors_eq; try lia.
  + destruct prime_dec; try destruct Zdivide_dec; try tauto.
  + apply prime_ge_2; auto.
Qed.

Lemma prime_factors_stay (n k k0 : Z) (Hn : 2 <= n) (Hk : prime k)
  (Hk' : (k | n)) (H : k <= k0) : In k (prime_factors n k0).
Proof.
  assert (2 <= k) by (apply prime_ge_2; auto).
  assert (0 <= k0) by lia. revert H. pattern k0.
  apply Z_lt_induction; auto; intros. clear H1 k0.
  assert (k = x \/ k < x) by lia. destruct H1.
  + subst x. pose proof (greatest_factor_eq n k ltac:(lia) Hk Hk').
    unfold greatest_factor in H1. destruct (prime_factors n k); try lia.
    simpl; tauto.
  + rewrite prime_factors_eq; try lia. destruct prime_dec; try tauto.
    - destruct Zdivide_dec; try lia.
      * simpl. right. apply H; try lia.
      * apply H; try lia.
    - apply H; try lia.
Qed.

Lemma greatest_factor_by_self (n : Z) (Hn : 2 <= n) :
  prime (greatest_factor n n).
Proof.
  destruct (prime_divisor_existence n Hn) as [p [H H0]].
  assert (In p (prime_factors n n)).
  { apply prime_factors_stay; auto; try lia.
    apply Z.divide_pos_le in H0; lia. }
  unfold greatest_factor. remember (prime_factors n n) as W.
  destruct W; try tauto. apply (prime_factors_all_prime n n); try lia.
  rewrite <- HeqW. simpl. auto.
Qed.

Lemma greatest_factor_const_of_rep_rep_div_eq_one (n k l : Z) (Hn : 2 <= n)
  (Hk : 2 <= k) (Hl : k <= l) (H : rep_rep_div n k = 1) :
  greatest_factor n l = greatest_factor n k.
Proof.
  assert (0 <= l) by lia. revert Hl. pattern l.
  apply Z_lt_induction; auto; intros. clear H0 l.
  assert (k = x \/ k < x) by lia. destruct H0; try congruence.
  destruct (prime_dec x).
  + destruct (Zdivide_dec x n).
    - assert (prime x /\ (x | n)) by tauto.
      rewrite <- rep_rep_div_main_lemma with (f2 := x - 1) in H2; try lia.
      assert (rep_rep_div n (x - 1) = 1).
      { apply rep_rep_div_stays_one with (k := x - 1) in H; try lia. }
      rewrite H3 in H2. apply Z.divide_1_r_nonneg in H2; try lia.
    - rewrite greatest_factor_by_not_dvd with (k2 := x - 1); try lia; auto.
      apply H1; try lia.
  + rewrite greatest_factor_by_not_prime with (k2 := x - 1); try lia; auto.
    apply H1; try lia.
Qed.

Lemma greatest_factor_const_after_self (n k : Z) (Hn : 1 <= n) (Hk : n <= k) :
  greatest_factor n k = greatest_factor n n.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H k.
  assert (n = x \/ n < x) by lia. destruct H.
  + congruence.
  + rewrite (greatest_factor_by_not_dvd n x (x - 1)); try lia.
    - apply H0; lia.
    - intro. apply Z.divide_pos_le in H1; lia.
Qed.

Lemma greatest_factor_is_greatest (n : Z) (Hn : 2 <= n) :
  IsGreatest (fun p => prime p /\ (p | n)) (greatest_factor n n).
Proof.
  pose proof (prime_factors_head_greatest_prime_factor n n ltac:(lia)
    ltac:(lia)).
  assert (exists x t, prime_factors n n = x :: t).
  { assert (prime (greatest_factor n n)). 
    { apply greatest_factor_by_self; auto. }
    assert (1 < greatest_factor n n). { apply prime_ge_2 in H0; lia. }
    unfold greatest_factor in *. destruct (prime_factors n n); try lia.
    exists z, l. auto. }
  destruct H0 as [x [t H0]]. unfold greatest_factor. rewrite H0 in *.
  destruct H. constructor; try tauto. intros. apply H1.
  constructor; auto. destruct H2. apply Z.divide_pos_le in H3; lia.
Qed.

(*** Function we want to reason about. ***)

Definition rep_div' (n f highest : Z) : Z * Z :=
  (rep_div n f, if Zdivide_dec f n
                then if Z_lt_dec highest f
                     then f
                     else highest
                else highest).

Lemma div_at_least_one (n f : Z) (Hn : 1 <= n) (Hf : 2 <= f) (H : (f | n)) :
  1 <= n / f.
Proof. destruct H. rewrite H, Z_div_mult; lia. Qed.

Function find (p : Z * Z) (highest : Z) (Hf : 2 <= snd p)
  { measure (fun p => Z.to_nat (Z.sqrt (fst p) + 1 - snd p)) p } : Z * Z :=
  if Z_le_dec (snd p * snd p) (fst p)
  then let temp1 := rep_div' (fst p) (snd p) highest in
       let temp2 := rep_div' (fst temp1) (snd p + 2) (snd temp1) in
       find (fst temp2, snd p + 6) (snd temp2) ltac:(simpl; lia)
  else (fst p, highest).
Proof.
  intros. destruct p as [n f]. simpl in *. assert (1 <= n) by nia.
  pose proof (rep_div_le_self (rep_div n f) (f + 2)
    (one_le_rep_div n f H)).
  pose proof (rep_div_le_self n f H).
  assert (rep_div (rep_div n f) (f + 2) <= n) by lia. clear H0 H1 teq.
  apply Z.sqrt_le_mono in H2. rewrite Z.sqrt_le_square in anonymous; lia.
Qed.

Definition biggestDivisor (n : Z) : Z :=
  let temp1 := @rep_div' n 2 1 in
  let temp2 := @rep_div' (fst temp1) 3 (snd temp1) in
  let (n3, highest3) := @find (fst temp2, 5) (snd temp2) ltac:(simpl; lia) in
  if Z.eq_dec n3 1 then highest3 else n3.

(**  **)

Lemma temp1_lemma (n : Z) (Hn : 1 <= n) :
  rep_div' n 2 1 = (rep_rep_div n 2, greatest_factor n 2).
Proof.
  unfold rep_div'. rewrite rep_rep_div_by_two; auto. simpl. f_equal.
  destruct Zdivide_dec.
  + pose proof prime_2. rewrite greatest_factor_eq; auto.
  + rewrite greatest_factor_by_not_dvd with (k2 := 1); auto; try lia.
    unfold greatest_factor. rewrite prime_factors_equation. simpl.
    destruct Z_le_dec; try lia.
Qed.

Lemma temp2_lemma (n : Z) (Hn : 1 <= n) :
  let temp := rep_div' n 2 1 in
  rep_div' (fst temp) 3 (snd temp) = (rep_rep_div n 3, greatest_factor n 3).
Proof.
  rewrite temp1_lemma; auto. simpl. unfold rep_div'. f_equal.
  + rewrite (rep_rep_div_equation _ 3). simpl. destruct Z_le_dec; try lia.
  + destruct Zdivide_dec; try destruct Z_lt_dec.
    - pose proof prime_3. rewrite greatest_factor_eq; auto.
      destruct (rep_div_main_lemma n 2 Hn ltac:(lia)) as [i [H0 H1]].
      rewrite H1. rewrite rep_rep_div_by_two in d; auto.
      destruct d. rewrite H2. exists (x * 2 ^ i). ring.
    - pose proof (greatest_factor_le_limit n 2 Hn ltac:(lia)). lia.
    - rewrite (greatest_factor_by_not_dvd n 3) with (k2 := 2); try lia.
      intro. apply n0; clear n0. rewrite rep_rep_div_by_two; try lia.
      destruct (rep_div_main_lemma n 2 Hn ltac:(lia)) as [i [H0 H1]].
      rewrite H1 in H. apply (prime_mult 3 prime_3) in H. destruct H; auto.
      apply prime_dvd_of_dvd_pow in H; try lia.
      * exfalso. destruct H. lia.
      * exact prime_3.
Qed.

(*** Helper lemmas ***)

Lemma TTT_aux (n i : Z) (Hn : 2 <= n) (Hi : 0 <= i)
  (H : prime (rep_rep_div n (6 * i + 3)))
  (H0 : (rep_rep_div n (6 * i + 3) | n)) :
  rep_rep_div n (6 * i + 3) = greatest_factor n n.
Proof.
  pose proof (prime_ge_2 _ H). pose proof (greatest_factor_is_greatest n Hn).
  destruct H2 as [[H2 H3] H4].
  assert (rep_rep_div n (6 * i + 3) <= greatest_factor n n).
  { apply H4. tauto. }
  assert (greatest_factor n n | rep_rep_div n (6 * i + 3)).
  { apply (rep_rep_div_main_lemma_part_2 n _ (6 * i + 3)); try lia; auto.
    constructor; try lia.
    destruct (Z.lt_ge_cases (6 * i + 3) (greatest_factor n n)); auto.
    exfalso. eapply (rep_rep_div_not_dvd_by_le n); try lia.
    + exact H1.
    + exact (Z.le_trans _ _ _ H5 H6).
    + exists 1; ring. }
  apply Z.divide_pos_le in H6; lia.
Qed.

Lemma aux (n i : Z) (Hi : 0 <= i) :
  2 <= snd (rep_rep_div n (6 * i + 3), 6 * i + 5).
Proof. simpl. lia. Qed.

Lemma aux0 (i : Z) (HI : 0 <= i) : 0 <= i + 1.
Proof. lia. Qed.

Lemma aux1 (a1 b1 a2 b2 c1 c2 : Z) P1 P2
  (H1 : a1 = a2) (H2 : b1 = b2) (H3 : c1 = c2) :
  find (a1, b1) c1 P1 = find (a2, b2) c2 P2.
Proof.
  subst a1. subst b1. subst c1. f_equal.
  apply Classical_Prop.proof_irrelevance.
Qed.


Lemma not_prime_aux (m1 m2 n: Z) (H1 : n = m1 * m2) (H2 : 1 < m1 < n) :
  ~ prime n.
Proof.
  intro. apply prime_alt in H. destruct H. pose proof (H0 _ H2).
  apply H3. subst n. exists m2. ring.
Qed.

Lemma TTT (n i : Z) (Hn : 2 <= n) (Hi : 0 <= i) (M : nat)
  (HM : Z.to_nat (n - i) = M) :
  let F := find (rep_rep_div n (6 * i + 3), 6 * i + 5)
           (greatest_factor n (6 * i + 3)) (aux n i Hi) in
  let W := greatest_factor n n in
  let W' := greatest_factor (rep_div n W) (rep_div n W) in
  if Z.eq_dec (fst F) 1 then W = snd F else W = fst F.
Proof.
  revert n Hn i Hi HM. pattern M. apply (@well_founded_induction _ lt lt_wf).
  simpl in *. clear M. intros.
  assert (hp0 : ~ prime (6 * i + 9)).
  { apply (not_prime_aux 3 (2 * i + 3)); lia. } 
  assert (hp1 : ~ prime (6 * i + 8)).
  { apply (not_prime_aux 2 (3 * i + 4)); lia. }
  assert (hp2 : ~ prime (6 * i + 6)).
  { apply (not_prime_aux 2 (3 * i + 3)); lia. }
  assert (hp3 : ~ prime (6 * i + 4)).
  { apply (not_prime_aux 2 (3 * i + 2)); lia. }
  assert (ht0 : rep_rep_div n (6 * i + 3) = rep_rep_div n (6 * i + 4)).
  { rewrite rep_rep_div_by_not_prime with (f1 := 6 * i + 4) (f2 := 6 * i + 3);
    try lia. tauto. }
  assert (ht1 : rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5) =
                rep_rep_div n (6 * i + 6)).
  { rewrite rep_rep_div_by_not_prime with (f1 := 6 * i + 6) (f2 := 6 * i + 5);
      try lia; try tauto.
    rewrite ht0, (rep_rep_div_equation n (6 * i + 5)); try lia; try tauto.
    repeat destruct Z_le_dec; try lia. f_equal. f_equal. lia. }
  assert (ht2 : rep_div (rep_rep_div n (6 * i + 6)) (6 * i + 7) =
                rep_rep_div n (6 * i + 7)).
  { rewrite (rep_rep_div_equation n (6 * i + 7)); try lia; try tauto.
    repeat destruct Z_le_dec; try lia. f_equal. f_equal. lia. }
  assert (ht3 : rep_rep_div n (6 * i + 7) = rep_rep_div n (6 * i + 9)).
  { rewrite rep_rep_div_by_not_prime with (f1 := 6 * i + 9) (f2 := 6 * i + 8);
      try lia; try tauto.
    rewrite rep_rep_div_by_not_prime with (f1 := 6 * i + 8) (f2 := 6 * i + 7);
      try lia; try tauto. }
  assert (ht4 : 6 * i + 5 + 2 = 6 * i + 7) by ring.
  assert (ht5 : 6 * i + 5 + 6 = 6 * i + 11) by ring.
  assert (ht6 : 6 * (i + 1) + 3 = 6 * i + 9) by ring.
  assert (ht7 : 6 * (i + 1) + 5 = 6 * i + 11) by ring.
  assert (ht8 : greatest_factor n (6 * i + 9) = greatest_factor n (6 * i + 7)).
  { rewrite greatest_factor_by_not_prime with
      (k1 := 6 * i + 9) (k2 := 6 * i + 8); try lia; try tauto.
    rewrite greatest_factor_by_not_prime with
      (k1 := 6 * i + 8) (k2 := 6 * i + 7); try lia; try tauto. }
  assert (ht9 : greatest_factor n (6 * i + 6) = greatest_factor n (6 * i + 5)).
  { rewrite greatest_factor_by_not_prime with
      (k1 := 6 * i + 6) (k2 := 6 * i + 5); try lia; try tauto. }
  assert (ht10 : greatest_factor n (6 * i + 4) = greatest_factor n (6 * i + 3)).
  { rewrite greatest_factor_by_not_prime with
      (k1 := 6 * i + 4) (k2 := 6 * i + 3); try lia; try tauto. }
  rewrite find_equation. destruct Z_le_dec.
  + remember (Z.to_nat (n - (i + 1))) as y.
    assert (y < x)%nat.
    { rewrite <- HM, Heqy. simpl in *.
      pose proof (rep_rep_div_le_self n (6 * i + 3)). lia. }
    pose proof H y H0 n Hn (i + 1) (aux0 i Hi) ltac:(subst y; auto).
    clear H. simpl in *. 
    assert (forall P Q,
      (6 * i + 5 + 2 | rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5)) ->
      find (rep_div (rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5)) (6 * i + 5 + 2), 6 * i + 5 + 6) (6 * i + 5 + 2) P =
      find (rep_rep_div n (6 * (i + 1) + 3), 6 * (i + 1) + 5) (greatest_factor n (6 * (i + 1) + 3)) Q).
    { intros. apply aux1; try congruence. rewrite ht4, ht6, ht8.
      rewrite ht1, ht4, rep_rep_div_main_lemma in H; try lia.
      rewrite greatest_factor_eq; try lia; tauto. }
    assert (forall P Q,
      ~ (6 * i + 5 + 2 | rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5)) ->
      (6 * i + 5 | rep_rep_div n (6 * i + 3)) ->
      find (rep_div (rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5)) (6 * i + 5 + 2), 6 * i + 5 + 6) (6 * i + 5) P =
      find (rep_rep_div n (6 * (i + 1) + 3), 6 * (i + 1) + 5) (greatest_factor n (6 * (i + 1) + 3)) Q).
    { intros. apply aux1; try congruence. rewrite ht6, ht8.
      rewrite ht1, ht4 in H2. rewrite rep_rep_div_main_lemma in H2; try lia.
      rewrite ht0, rep_rep_div_main_lemma in H3; try lia.
      rewrite greatest_factor_by_not_prime_or_not_dvd with
        (k2 := 6 * i + 6); try lia; auto.
      rewrite ht9, greatest_factor_eq; try lia; tauto. }
    assert (forall P Q,
      ~ (6 * i + 5 + 2 | rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5)) ->
      ~ (6 * i + 5 | rep_rep_div n (6 * i + 3)) ->
      find (rep_div (rep_div (rep_rep_div n (6 * i + 3)) (6 * i + 5)) (6 * i + 5 + 2), 6 * i + 5 + 6) (greatest_factor n (6 * i + 3)) P =
      find (rep_rep_div n (6 * (i + 1) + 3), 6 * (i + 1) + 5) (greatest_factor n (6 * (i + 1) + 3)) Q).
    { intros. apply aux1; try congruence. rewrite ht6, ht8.
      rewrite ht1, ht4 in H3. rewrite rep_rep_div_main_lemma in H3; try lia.
      rewrite ht0, rep_rep_div_main_lemma in H4; try lia.
      rewrite greatest_factor_by_not_prime_or_not_dvd with
        (k1 := 6 * i + 7) (k2 := 6 * i + 6); try lia; auto.
      rewrite ht9, greatest_factor_by_not_prime_or_not_dvd with
        (k1 := 6 * i + 5) (k2 := 6 * i + 4); try lia; auto. }
    assert (greatest_factor n (6 * i + 3) <= 6 * i + 3).
    { apply greatest_factor_le_limit; lia. }
    destruct Z.eq_dec in H1.
    - destruct Zdivide_dec.
      * destruct Z_lt_dec; try lia.
        ++ erewrite H, e; congruence.
        ++ destruct Zdivide_dec; try destruct Z_lt_dec in n0; lia.
      * destruct Zdivide_dec.
        ++ destruct Z_lt_dec.
           -- erewrite H2, e; congruence.
           -- lia.
        ++ erewrite H3, e; congruence.
    - destruct Zdivide_dec.
      * destruct Z_lt_dec; try lia.
        ++ erewrite H; auto. destruct Z.eq_dec; eauto. tauto.
        ++ destruct Zdivide_dec; try destruct Z_lt_dec; lia.
      * destruct Zdivide_dec.
        ++ destruct Z_lt_dec; try lia.
           erewrite H2; auto. destruct Z.eq_dec; eauto. tauto.
        ++ erewrite H3; auto. destruct Z.eq_dec; eauto. tauto.
  + simpl in *. destruct Z.eq_dec.
    - destruct (Z_le_dec (6 * i + 3) n).
      * rewrite greatest_factor_const_of_rep_rep_div_eq_one
          with (k := 6 * i + 3); lia.
      * rewrite <- greatest_factor_const_after_self with (k := 6 * i + 3); lia.
    - destruct (prime_dec (rep_rep_div n (6 * i + 3))).
      * assert (rep_rep_div n (6 * i + 3) | n).
        { apply rep_rep_div_dvd_self; lia. }
        rewrite <- TTT_aux with (i := i); try lia; auto.
      * pose proof (one_le_rep_rep_div n (6 * i + 3) ltac:(lia) ltac:(lia)).
        rewrite ht0 in *.
        pose proof (rep_rep_div_lower_bound_of_not_prime n (6 * i + 4)
          ltac:(lia) ltac:(lia) n2 ltac:(lia)). lia.
Qed.

Lemma main_result (n : Z) (Hn : 2 <= n) :
  IsGreatest (fun d => prime d /\ (d | n)) (biggestDivisor n).
Proof.
  assert (biggestDivisor n = greatest_factor n n).
  { pose proof (TTT n 0 Hn ltac:(lia) (Z.to_nat (n - 0)) ltac:(auto)).
    unfold biggestDivisor. rewrite (temp2_lemma n ltac:(lia)). simpl in *.
    assert (forall P Q, (let (n3, highest3) :=
      find (rep_rep_div n 3, 5) (greatest_factor n 3) P in
      if Z.eq_dec n3 1 then highest3 else n3) =
      let W := find (rep_rep_div n 3, 5) (greatest_factor n 3) Q in
      if Z.eq_dec (fst W) 1 then snd W else fst W).
    { intros. remember (find (rep_rep_div n 3, 5) (greatest_factor n 3) P) as A.
      remember (find (rep_rep_div n 3, 5) (greatest_factor n 3) Q) as B.
      assert (A = B). { rewrite HeqA, HeqB. apply aux1; auto. }
      rewrite H0. destruct B. simpl. auto. }
    destruct Z.eq_dec in H.
    + erewrite H0, H. simpl. destruct Z.eq_dec; tauto.
    + erewrite H0, H. simpl. destruct Z.eq_dec; try tauto. tauto. }
  rewrite H. apply greatest_factor_is_greatest; auto.
Qed.



Require Import EulerProject3.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition new_highest f n h :=
  if Zdivide_dec f n then (if Z_le_dec f h then h else f) else h.

Definition factorize_spec: ident * funspec :=
DECLARE _factorize
  WITH gv: globals, n: Z, f: Z, h: Z
  PRE [ tulong, tulong ]
    PROP (1 <= n <= Int64.max_unsigned; 2 <= f <= Int64.max_unsigned;
          0 <= h <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n); Vlong (Int64.repr f))
    GLOBALS (gv)
    SEP (data_at Ews tulong (Vlong (Int64.repr h)) (gv _highest))
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (rep_div n f)))
    SEP (data_at Ews tulong (Vlong (Int64.repr (new_highest f n h)))
         (gv _highest)).

Definition find_spec: ident * funspec :=
DECLARE _find
  WITH gv: globals, n: Z, h: Z
  PRE [ tulong ]
    PROP (2 <= n <= 1000000000000; 0 <= h <= Int64.max_unsigned)   (* 1000000000000 instead of Int64.max_unsigned *)
    PARAMS (Vlong (Int64.repr n))
    GLOBALS (gv)
    SEP (data_at Ews tulong (Vlong (Int64.repr h)) (gv _highest))
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (biggestDivisor n)))
    SEP ().


Definition Gprog := [find_spec; factorize_spec].

Lemma factorize_proof: semax_body Vprog Gprog f_factorize factorize_spec.
Proof.
  start_function. assert (Int64.unsigned (Int64.repr f) = f).
  { apply Int64.unsigned_repr. lia. }
  assert (Int64.unsigned (Int64.repr n) = n).
  { apply Int64.unsigned_repr. lia. }
  assert (Int64.unsigned (Int64.repr h) = h).
  { apply Int64.unsigned_repr. lia. }
  assert (forall i, 0 <= i ->
    Int64.unsigned (Int64.repr (n / f ^ i)) = n / f ^ i).
  { intros. apply Int64.unsigned_repr. split.
    + apply Z_div_nonneg_nonneg; try lia.
    + destruct (Z.eq_dec i 0).
      - subst. simpl (f ^ 0). rewrite Zdiv_1_r. lia.
      - assert (n / f ^ i < n).
        { apply Z.div_lt; try lia. apply Z.pow_gt_1; try lia. }
        lia. }
  forward_if.
  + deadvars!. forward. entailer!. destruct (Zdivide_dec f n); auto.
    - exfalso. destruct d. subst. assert (x < 1) by nia. lia.
    - f_equal. f_equal. rewrite rep_div_equation.
      repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec; auto. tauto.
    - unfold new_highest. destruct Zdivide_dec.
      * destruct d. subst. assert ((x - 1) * f < 0) by lia.
        assert (x < 1) by nia. lia.
      * auto.
  + destruct (rep_div_main_lemma n f); try lia. destruct H7.
    forward_while (
      EX (i: Z),
        PROP (0 <= i <= x)
        LOCAL (temp _n (Vlong (Int64.repr (n / f ^ i)));
               temp _f (Vlong (Int64.repr f)); gvars gv)
        SEP (data_at Ews tulong (Vlong (Int64.repr
              (if Z.eq_dec i 0 then h else new_highest f n h))) (gv _highest))
    ).
    - Exists 0. entailer!. repeat split; try lia.
      ring_simplify (f ^ 0). rewrite Z.div_1_r. auto.
    - entailer!. apply repr_inj_unsigned64 in H12; try lia.
    - forward.
      * entailer!. apply repr_inj_unsigned64 in H12; try lia.
      * assert (f | n / f ^ i).
        { unfold Int64.modu in HRE. fold (Z.div n (f ^ i)) in HRE.
          rewrite H5, H2 in HRE; try lia.
          apply repr_inj_unsigned64 in HRE; try lia.
          + apply Zmod_divide in HRE; try lia. auto.
          + assert (0 <= (n / f ^ i) mod f < f).
            { apply Z_mod_lt. lia. }
          lia. }
        clear HRE. forward. forward_if.
        ++ apply ltu_inv64 in H11. rewrite H2 in H11. destruct Z.eq_dec.
           -- rewrite H4 in H11. forward. entailer!. Exists 1.
              simpl (f ^ 0) in H10. rewrite Z.div_1_r in H10.
              entailer!.
              ** repeat split; try lia.
                 +++ assert (x = 0 \/ 1 <= x) by lia. destruct H14; try lia.
                     subst x. ring_simplify (rep_div n f * f ^ 0) in H8.
                     rewrite H8 in H10.
                     pose proof (rep_div_not_dvd_by_factor n f); try lia.
                     tauto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia.
                     simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest.
                 repeat if_tac; try lia; auto. tauto.
           -- unfold new_highest in *.
              destruct Zdivide_dec; [destruct Z_le_dec |].
              ** rewrite H4 in H11. lia.
              ** rewrite H2 in H11. lia.
              ** exfalso. apply n1. rewrite H8.
                 exists (rep_div n f * f ^ (x - 1)).
                 rewrite <- Z.mul_assoc. f_equal.
                 replace (f ^ (x - 1) * f) with (f ^ (x - 1) * f ^ 1) by ring.
                 rewrite <- Z.pow_add_r; try lia. f_equal. ring. 
        ++ apply ltu_false_inv64 in H11. rewrite H2 in H11. destruct Z.eq_dec.
           -- rewrite H4 in H11. forward. entailer!. simpl (f ^ 0) in H10.
              rewrite Z.div_1_r in H10. Exists 1. entailer!.
              ** repeat split; try lia.
                 +++ assert (x = 0 \/ 1 <= x) by lia. destruct H14; try lia.
                     subst x. simpl in H8. rewrite H8 in H10.
                     ring_simplify (rep_div n f * 1) in H10.
                     pose proof (rep_div_not_dvd_by_factor n f); try lia.
                     tauto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia.
                     simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest.
                 destruct Zdivide_dec; try tauto.
                 destruct Z_le_dec; try lia. auto.
           -- forward. entailer!. Exists (i + 1). entailer!.
              repeat split; try lia.
              ** rewrite H8, Zdivide_Zdiv_eq_2 in H10; try lia.
                 +++ rewrite <- Z.pow_sub_r in H10; try lia.
                     pose proof (rep_div_not_dvd_by_factor n f
                       ltac:(lia) ltac:(lia)).
                     assert (x - i = 0 \/ 1 <= x - i) by lia. destruct H15.
                     rewrite H15 in H10.
                     ring_simplify (rep_div n f * f ^ 0) in H10. tauto. lia.
                 +++ exists (f ^ (x - i)). rewrite <- Z.pow_add_r; try lia.
                     f_equal. ring.
              ** unfold Int64.divu. do 2 f_equal. rewrite H5; try lia.
                 rewrite H2, Zdiv_Zdiv; try lia. f_equal.
                 rewrite Z.pow_add_r; try lia.
              ** destruct Z.eq_dec; try lia. auto.
    - fold (Z.div n (f ^ i)) in HRE. unfold Int64.modu in HRE.
      rewrite H5 in HRE; try lia. rewrite H2 in HRE.
      assert ((n / f ^ i) mod f <> 0). { intro. apply HRE. congruence. }
      forward. entailer!.
      * do 2 f_equal. assert ((f | n / f ^ i) -> False).
        { intro. apply H10. apply Z.mod_divide; try lia. auto. }
        rewrite H8 at 1. rewrite Zdivide_Zdiv_eq_2; try lia.
        ++ rewrite <- Z.pow_sub_r; try lia. assert (i < x \/ i = x) by lia.
           destruct H14.
           -- exfalso. apply H13.
              rewrite H8, Zdivide_Zdiv_eq_2, <- Z.pow_sub_r; try lia.
              ** exists (rep_div n f * f ^ (x - i - 1)).
                 rewrite <- Z.mul_assoc. f_equal.
                 replace f with (f ^ 1) at 3 by ring.
                 rewrite <- Z.pow_add_r; try lia. f_equal. ring.
              ** exists (f ^ (x - i)). rewrite <- Z.pow_add_r; try lia.
                 f_equal. ring.
           -- subst i. replace (x - x) with 0 by ring. simpl. ring.
        ++ exists (f ^ (x - i)). rewrite <- Z.pow_add_r; try lia. f_equal. ring.
      * assert ((f | n / f ^ i) -> False).
        { intro. apply H10. apply Z.mod_divide; try lia. auto. }
        destruct Z.eq_dec; auto.
        unfold new_highest. destruct Zdivide_dec; [destruct Z_le_dec |]; auto.
        subst. simpl (f ^ 0) in H13. rewrite Z.div_1_r in H13. tauto.
Qed.

Lemma find_proof: semax_body Vprog Gprog f_find find_spec.
Proof.
  assert (Int64.max_unsigned = 18446744073709551615) as HH by auto.
  start_function. assert (1 <= n) by lia. forward. forward_call. forward_call.
  + split.
    - pose proof (one_le_rep_div n 2 H1).
      pose proof (rep_div_le_self n 2 H1). lia.
    - unfold new_highest. destruct Zdivide_dec; [destruct Z_le_dec |]; try lia.
  + autorewrite with norm.
    set (rep_rep_div 3 n) as W.
    admit.
Admitted.
