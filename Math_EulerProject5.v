Require Import VST.floyd.proofauto.
From Stdlib Require Import Znumtheory ZArith Bool List.
Import ListNotations.
Require Import PrimeFactors.

Open Scope Z.

Definition sieve_state := Z -> bool.

Definition init_state (n : Z) : sieve_state :=
  fun i => Z.leb 2 i && Z.leb i n.

Definition mark_multiples (p n : Z) (s : sieve_state) : sieve_state :=
  fun i =>
    if Z.leb (p * p) i && Z.leb i n && (i mod p =? 0)
    then false
    else s i.

(* Argument p is such that fst p is the increasing loop variable,
   but snd p is the limit and is constant. *)
Function sieve_loop (p : Z * Z) (n : Z) (s : sieve_state)
  {measure (fun x => Z.to_nat (snd x - fst x + 1)) p} : sieve_state :=
  if Z.ltb (snd p) (fst p) then s
  else if s (fst p) then sieve_loop (fst p + 1, snd p) n (mark_multiples (fst p) n s)
  else sieve_loop (fst p + 1, snd p) n s.
Proof.
  + intros. destruct p; simpl in *. rewrite Z.ltb_ge in teq. lia.
  + intros. destruct p; simpl in *. rewrite Z.ltb_ge in teq. lia.
Defined.

Definition sieve (n : Z) : sieve_state :=
  let limit := Z.sqrt n in
  sieve_loop (2, limit) n (init_state n).

Definition primes_up_to (n : Z) : list Z :=
  List.filter (sieve n) (map Z.of_nat (List.seq 2 (Z.to_nat (n - 1)))).


(* Every number has a prime divisor *)
Theorem prime_divisor_existence (n: Z) (H: 2 <= n):
  exists p, prime p /\ Z.divide p n.
Proof.
  assert (0 <= n) by lia. revert H. pattern n.
  apply Z_lt_induction; auto; intros. clear n H0. destruct (prime_dec x).
  + exists x. split; auto. exists 1. lia.
  + apply not_prime_divide in n; try lia. destruct n as [d [Hd_bounds Hd_div]].
    destruct Hd_div. assert (0 <= x0 < x0 * d) by nia.
    assert (2 <= x0) by nia. pose proof (H x0 ltac:(lia) H3).
    destruct H4 as [p [Hp Hpd]]. exists p. split; auto. destruct Hpd. subst.
    exists (x1 * d). ring.
Qed.

Lemma composite_has_two_prime_divisors :
  forall n,
    ~ prime n -> 2 <= n ->
    exists p q, prime p /\ prime q /\ (p * q | n).
Proof.
  intros n Hnotprime Hn.
  destruct (not_prime_divide n ltac:(lia) Hnotprime) as [d [Hd_bounds Hd_div]].
  destruct (prime_divisor_existence d ltac:(lia)) as [p [Hp Hpd]].
  destruct Hd_div as [m Hm]. assert (2 <= m) by nia.
  destruct (prime_divisor_existence m H) as [q [Hq Hqd]].
  exists p, q. split; auto. split; auto.
  destruct Hpd as [k1 Hk1]. destruct Hqd as [k2 Hk2].
  rewrite Hk1, Hk2 in Hm. rewrite Hm. exists (k1 * k2). ring.
Qed.

Lemma composite_has_small_prime_factor :
  forall x,
    ~ prime x -> 2 <= x ->
    exists q, prime q /\ q * q <= x /\ x mod q = 0.
Proof.
  intros x Hnotprime Hx.
  destruct (composite_has_two_prime_divisors x Hnotprime Hx) as [p [q [Hp [Hq Hpq_div]]]].
  destruct Hpq_div as [k Hk]. destruct (Z_le_dec p q).
  + exists p. split; auto. split.
    - assert (2 <= p) by (destruct Hp; lia).
      assert (p * p <= p * q) by nia. assert (1 <= k) by nia. nia.
    - apply Z.mod_divide; try lia. exists (q * k). rewrite Hk. ring.
  + exists q. split; auto. split.
    - assert (2 <= q) by (destruct Hq; lia).
      assert (q * q <= p * q) by nia. assert (1 <= k) by nia. nia.
    - apply Z.mod_divide; try lia. exists (p * k). rewrite Hk. ring.
Qed.



Definition sieve_inv (p n : Z) (s : sieve_state) : Prop :=
  forall x, 2 <= x -> x <= n ->
    s x = true <->
    (prime x \/ (forall q, prime q -> q < p -> x mod q <> 0)).

Lemma composite_no_small_factor_ge_p_sq :
  forall x p, 2 <= x -> 2 <= p -> ~ prime x ->
    (forall q, prime q -> q < p -> x mod q <> 0) ->
    p * p <= x.
Proof.
  intros. destruct (composite_has_small_prime_factor x H1 H) as [q [H3 [H4 H5]]].
  assert (q < p \/ p <= q) by lia. destruct H6.
  + exfalso. apply (H2 q H3 H6 H5).
  + nia.
Qed.

Lemma mark_multiples_preserves_inv :
  forall p n s (Hp : 2 <= p),
    sieve_inv p n s ->
    sieve_inv (p + 1) n (mark_multiples p n s).
Proof.
  intros p n s Hp Hinv x Hx0 Hx1. unfold sieve_inv in *. split; intros.
  + destruct (prime_dec x); auto. right. intros.
    unfold mark_multiples in H. remember (_ && _ && _) as B in H.
    destruct B; try congruence. pose proof (proj1 (Hinv x Hx0 Hx1) H).
    destruct H2; try tauto. destruct (Z.eq_dec p q).
    - subst q. apply composite_no_small_factor_ge_p_sq in H2; auto.
      assert (p * p <=? x = true). { rewrite Z.leb_le; auto. }
      assert (x <=? n = true). { rewrite Z.leb_le; auto. }
      rewrite H3, H4 in HeqB. simpl in HeqB. symmetry in HeqB.
      rewrite Z.eqb_neq in HeqB. auto.
    - assert (q < p) by lia. auto.
  + unfold mark_multiples. remember (_ && _ && _) as B. destruct B.
    - exfalso. symmetry in HeqB. do 2 rewrite andb_true_iff in HeqB.
      destruct HeqB as [[H0 H1] H2]. rewrite Z.leb_le in H0, H1.
      rewrite Z.eqb_eq in H2. destruct H.
      * rewrite Z.mod_divide in H2; try lia. destruct H2.
        assert (x0 = 1 \/ 2 <= x0) by nia. destruct H3.
        ++ subst x0. rewrite Z.mul_1_l in H2. subst p. destruct H. nia.
        ++ apply prime_alt in H. destruct H. assert (x0 < x) by nia.
           apply (H4 x0 ltac:(lia)). exists p. rewrite H2. ring.
      * destruct (prime_divisor_existence p Hp) as [q [H3 H4]].
        assert (x mod q = 0).
        { rewrite Z.mod_divide in H2; try lia. rewrite Z.mod_divide.
          + exact (Z.divide_trans _ _ _ H4 H2).
          + destruct H3; lia. }
        refine (H q H3 _ H5). apply Z.divide_pos_le in H4; lia.
    - rewrite Hinv; auto. destruct H; auto. right. intros.
      apply H; auto. lia.
Qed.

Lemma sieve_inv_init :
  forall n, sieve_inv 2 n (init_state n).
Proof.
  intros n x Hx0 Hx1. unfold sieve_inv, init_state.
  remember (_ && _) as B. destruct B.
  + split; intros; auto. right. intros. destruct H0; lia.
  + split; intros; try congruence. symmetry in HeqB.
    rewrite andb_false_iff in HeqB.
    rewrite <- Z.leb_le in Hx0, Hx1. rewrite Hx0, Hx1 in HeqB.
    destruct HeqB; congruence.
Qed.

Lemma sieve_loop_correct :
  forall p limit n s, 2 <= p <= limit -> limit <= n ->
    sieve_inv p n s ->
    sieve_inv (limit + 1) n (sieve_loop (p, limit) n s).
Proof.
  intros p limit n s Hpl Hln Hinv. remember (limit - p) as W.
  assert (0 <= W) by lia. revert s p HeqW Hinv Hpl. pattern W.
  apply Z_lt_induction; auto; intros. clear W H.
  assert (x = 0 \/ 0 < x) by lia. destruct H.
  + assert (limit = p) by lia. subst limit. rewrite sieve_loop_equation.
    simpl. rewrite Z.ltb_irrefl. remember (s p) as S. destruct S.
    - rewrite sieve_loop_equation. simpl. assert (p < p + 1) by lia.
      rewrite (proj2 (Z.ltb_lt _ _) H1). apply mark_multiples_preserves_inv; try lia.
      auto.
    - rewrite sieve_loop_equation. simpl. assert (p < p + 1) by lia.
      rewrite (proj2 (Z.ltb_lt _ _) H1). clear H0. unfold sieve_inv in *.
      intros. destruct (Z.eq_dec p x0).
      * subst x0. rewrite <- HeqS. split; intros; try congruence. exfalso.
        assert ((s p = true) -> False) by congruence. rewrite Hinv in H4; try lia.
        apply H4. destruct H3; auto. right; intros. apply H3; try lia. auto.
      * rewrite Hinv; try lia. split; intros.
        ++ destruct H3; auto. right; intros. apply H3; auto.
           assert (~ prime p).
           { intro. assert (prime p \/ (forall q, prime q -> q < p -> p mod q <> 0)) by tauto.
             rewrite <- Hinv in H7; try lia. congruence. }
           assert (p <> q) by congruence. lia.
        ++ destruct H3; auto. right; intros. apply H3; auto. lia.
  + rewrite sieve_loop_equation. simpl. assert (~ (limit < p)) by lia.
    rewrite <- Z.ltb_lt in H1. assert (limit <? p = false).
    { destruct (limit <? p); congruence. }
    rewrite H2. remember (s p) as S. destruct S.
    - apply (H0 (x - 1)); try lia. apply mark_multiples_preserves_inv; auto; lia.
    - apply (H0 (x - 1)); try lia. clear H0 H1 H2. unfold sieve_inv in *.
      intros. destruct (Z.eq_dec p x0).
      * subst x0. rewrite <- HeqS. split; intros; try congruence. exfalso.
        assert ((s p = true) -> False) by congruence. rewrite Hinv in H3; try lia.
        apply H3. destruct H2; auto. right; intros. apply H2; try lia. auto.
      * rewrite Hinv; try lia. split; intros.
        ++ destruct H2; auto. right; intros. apply H2; auto. assert (~ prime p).
           { intro. assert (prime p \/ (forall q, prime q -> q < p -> p mod q <> 0)) by tauto.
             rewrite <- Hinv in H6; try lia. congruence. }
           assert (p <> q) by congruence. lia.
        ++ destruct H2; auto. right; intros. apply H2; auto. lia.
Qed.

Lemma sieve_final :
  forall n x, 2 <= x <= n ->
    (sieve n x = true <-> prime x).
Proof.
  intros n x [Hx0 Hx1]. unfold sieve. set (limit := Z.sqrt n) in *.
  destruct (Z_le_dec 2 limit).
  + assert (Hln : limit <= n). { unfold limit. apply Z.sqrt_le_lin; lia. }
    assert (Hinv : sieve_inv (limit + 1) n (sieve_loop (2, limit) n (init_state n))).
    { apply sieve_loop_correct; try lia. apply sieve_inv_init. }
    specialize (Hinv x Hx0 Hx1). rewrite Hinv. split; intro H.
    - destruct (prime_dec x); auto. destruct H; auto. exfalso.
      destruct (composite_has_small_prime_factor x n0 Hx0) as [p [H0 [H1 H2]]].
      apply H in H2; try lia; auto. assert (p * p <= n) by lia.
      rewrite Z.sqrt_le_square in H3; try lia. destruct H0; lia.
    - auto.
  + assert (Hn : n < 4).
    { unfold limit in *. rewrite <- Z.sqrt_le_square in n0; try lia. }
    assert (x = 2 \/ x = 3) by lia.
    assert (prime x). { destruct H; subst x. exact prime_2. exact prime_3. }
    split; intros; auto. rewrite sieve_loop_equation. simpl.
    assert (limit < 2) by lia. rewrite <- Z.ltb_lt in H2. rewrite H2.
    unfold init_state. rewrite <- Z.leb_le in Hx0, Hx1. rewrite Hx0, Hx1. auto.
Qed.

(* Finished with the sieve *)


Function get_exp_le_bound (bound a : Z) { measure Z.to_nat bound } : Z :=
  if Z.leb 2 a && Z.leb a bound
  then 1 + get_exp_le_bound (bound / a) a
  else 0.
Proof.
  intros. rewrite andb_true_iff in teq. destruct teq as [H H0].
  rewrite Z.leb_le in H. rewrite Z.leb_le in H0.
  pose proof (Z.div_pos bound a ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt bound a ltac:(lia) ltac:(lia)). lia.
Defined.

Lemma get_exp_le_bound_nonneg (bound a : Z) : 0 <= get_exp_le_bound bound a.
Proof.
  rewrite get_exp_le_bound_equation. remember (_ && _) as B. destruct B.
  + symmetry in HeqB. rewrite andb_true_iff, Z.leb_le, Z.leb_le in HeqB; try lia.
    assert (0 <= bound) by lia. revert HeqB. pattern bound.
    apply Z_lt_induction; auto; intros. rewrite get_exp_le_bound_equation.
    remember (_ && _) as B0. destruct B0; try lia. symmetry in HeqB0.
    rewrite andb_true_iff, Z.leb_le, Z.leb_le in HeqB0.
    assert (0 <= 1 + get_exp_le_bound (x / a / a) a).
    { apply H0; try lia. pose proof (Z_div_nonneg_nonneg x a).
      pose proof (Z.div_lt x a). lia. }
    lia.
  + lia.
Qed.

Lemma get_exp_le_bound_spec (bound a : Z) (Ha : 2 <= a) (Hb : 1 <= bound) :
  is_greatest (fun i => a ^ i <= bound) (get_exp_le_bound bound a).
Proof.
  split.
  + rewrite get_exp_le_bound_equation. remember (_ && _) as B. destruct B.
    - symmetry in HeqB. rewrite andb_true_iff, Z.leb_le, Z.leb_le in HeqB.
      assert (0 <= bound) by lia. revert HeqB Hb. pattern bound.
      apply Z_lt_induction; auto; intros. clear H bound.
      assert (a <= x / a \/ x / a < a) by lia. destruct H.
      * assert (a ^ (1 + get_exp_le_bound (x / a / a) a) <= x / a).
        { apply H0; try lia. pose proof (Z_div_nonneg_nonneg x a).
          pose proof (Z.div_lt x a). lia. }
        rewrite get_exp_le_bound_equation. destruct (_ && _).
        ++ rewrite Z.pow_add_r; try lia.
           -- ring_simplify (a ^ 1). assert (a * (x / a) <= x).
              { apply Z.mul_div_le; try lia. } nia.
           -- pose proof (get_exp_le_bound_nonneg (x / a / a) a). lia.
        ++ ring_simplify (1 + 0). ring_simplify (a ^ 1). lia.
      * rewrite get_exp_le_bound_equation. destruct HeqB.
        rewrite <- Z.leb_le in H1. rewrite H1. rewrite <- Z.leb_gt in H.
        rewrite H. simpl. replace (Z.pow_pos a 1) with a by lia. lia.
    - simpl. auto.
  + intros. assert (0 <= bound) by lia. revert y H Hb. pattern bound.
    apply Z_lt_induction; auto; intros. clear H0 bound.
    rewrite get_exp_le_bound_equation. rewrite (proj2 (Z.leb_le _ _) Ha).
    destruct (Z_le_dec 1 y).
    - assert (a <= a ^ y).
      { replace a with (a ^ 1) at 1 by ring. apply Z.pow_le_mono_r; try lia. }
      pose proof (Z.le_trans _ _ _ H0 H1). rewrite (proj2 (Z.leb_le _ _) H2).
      remember (true && true) as B. simpl in HeqB. destruct B; try congruence.
      assert (0 <= x / a < x).
      { pose proof (Z_div_nonneg_nonneg x a). pose proof (Z.div_lt x a). lia. }
      assert (a ^ (y - 1) <= x / a).
      { rewrite Z.pow_sub_r; try lia. ring_simplify (a ^ 1).
        apply Z_div_le; try lia. }
      assert (1 <= x / a) by lia.
      pose proof (H _ H3 _ H4 H5). lia.
    - assert (y <= 0) by lia. destruct (_ && _); auto. clear H.
      pose proof (get_exp_le_bound_nonneg (x / a) a). lia.
Qed.




Definition LCM_of_range (n : Z) : Z :=
  if Z.leb n 1
  then 1
  else List.fold_left (fun acc p => acc * p ^ get_exp_le_bound n p) (primes_up_to n) 1.

Theorem primes_up_to_In (n p : Z) :
  In p (primes_up_to n) <-> (prime p /\ p <= n).
Proof.
  unfold primes_up_to. split; intros.
  + rewrite filter_In in H. rewrite in_map_iff in H.
    destruct H as [[x [H0 H1]] H2]. rewrite sieve_final in H2.
    - split; try tauto. rewrite in_seq in H1. lia.
    - rewrite in_seq in H1. lia.
  + rewrite filter_In, in_map_iff. rewrite sieve_final.
    - split; try tauto. exists (Z.to_nat p). destruct H as [[H0 H1] H2].
      rewrite in_seq. lia.
    - destruct H  as [[H H0] H1]. lia.
Qed.

Theorem one_le_LCM_of_range (n : Z) : 1 <= LCM_of_range n.
Proof.
  unfold LCM_of_range. remember (n <=? 1) as B. destruct B; try lia.
  symmetry in HeqB. rewrite Z.leb_gt in HeqB. remember (primes_up_to n) as L.
  assert (forall p, In p L -> 1 < p).
  { intros. rewrite HeqL, primes_up_to_In in H. destruct H as [[H0 H1] H2].
    auto. }
  assert (forall x, 1 <= x -> 1 <= fold_left (fun acc p => acc * p ^ get_exp_le_bound n p) L x).
  { intros. clear HeqL. revert x H0. induction L; simpl; try lia. simpl in H.
    intros. apply IHL.
    + intros. apply H; auto.
    + pose proof (get_exp_le_bound_nonneg n a). replace 1 with (a ^ 0) by ring. 
      apply Z.pow_le_mono_r with (a := a) in H1; try nia.
      pose proof (H a ltac:(tauto)). lia. }
  apply H0. lia.
Qed.

Lemma get_exp_le_bound_monotone (k n p : Z) (Hk : 1 <= k <= n) (Hp : prime p) :
  get_exp_le_bound k p <= get_exp_le_bound n p.
Proof.
  pose proof (get_exp_le_bound_spec k p ltac:(destruct Hp; lia) ltac:(lia)).
  pose proof (get_exp_le_bound_spec n p ltac:(destruct Hp; lia) ltac:(lia)).
  destruct H, H0. apply H2. lia.
Qed.

Lemma prime_pow_dvd_k_dvd_LCM (k n p e : Z)
  (Hk : 1 <= k <= n) (Hp : prime p) (He : 0 <= e) (Hd : (p ^ e | k)) :
  e <= get_exp_le_bound n p.
Proof.
  pose proof (get_exp_le_bound_spec n p ltac:(destruct Hp; lia) ltac:(lia)).
  destruct H. apply H0. apply Zdivide_le in Hd; try lia.
  pose proof (Z.pow_pos_nonneg p e). destruct Hp; lia.
Qed.

Lemma factor_exponent_of_product_of_primes_lt (p k : Z) (Hp : prime p)
  (Hk : 1 <= k < p) (f : Z -> Z) (Hf : forall x, 0 <= f x) :
  factor_exponent (fold_left (fun acc p0 => acc * p0 ^ f p0)
    (primes_up_to k) 1) p = 0.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k. apply Z_lt_induction; auto; intros.
  clear H k. assert (x = 1 \/ 2 <= x) by lia. destruct H.
  + rewrite H. simpl. rewrite factor_exponent_equation.
    repeat destruct Z_le_dec; try lia. destruct Zdivide_dec; auto.
    destruct d. assert (0 < x0) by nia. nia.
  + assert (forall a, In a (primes_up_to x) -> 2 <= a < p).
    { intros. unfold primes_up_to in H1. rewrite filter_In in H1.
      destruct H1. rewrite in_map_iff in H1. destruct H1. destruct H1.
      rewrite <- H1. rewrite in_seq in H3. lia. }
    revert H1. generalize (primes_up_to x) as L. intros. induction L.
    - simpl. rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
      destruct Zdivide_dec; auto. destruct d. assert (0 < x0) by nia. nia.
    - Opaque Z.mul. simpl. rewrite <- Z.mul_1_l. assert (2 <= a < p).
      { simpl in H1. apply H1. auto. }
      assert (forall L w, fold_left (fun acc p0 => acc * p0 ^ f p0) L w =
        w * fold_left (fun acc p0 => acc * p0 ^ f p0) L 1).
      { induction L0; intros; simpl; try lia.
        rewrite IHL0, Z.mul_1_l, (IHL0 (a0 ^ f a0)). ring. }
      rewrite H3, Z.mul_1_l. rewrite factor_exponent_of_product_as_sum; auto.
      * rewrite factor_exponent_pow_coprime; auto; try lia; auto.
        ++ rewrite IHL; auto. intros. apply H1. simpl. auto.
        ++ intro. apply Zdivide_le in H4; try lia.
      * pose proof (get_exp_le_bound_nonneg p a). pose proof (Hf a).
        pose proof (Z.pow_pos_nonneg a (f a)). lia.
      * clear IHL. induction L; simpl; try lia. rewrite H3.
        assert (2 <= a0 < p). { apply H1. simpl. auto. }
        assert (0 < a0 ^ f a0).
        { apply (Z.pow_pos_nonneg a0 (f a0)); try lia. apply Hf. }
        assert (forall a1, In a1 (a :: L) -> 2 <= a1 < p).
        { intros. apply H1. simpl in *. tauto. }
        pose proof (IHL H6). lia.
      Transparent Z.mul.
Qed.

Lemma factor_exponent_self (p : Z) (Hp : prime p) : factor_exponent p p = 1.
Proof.
  rewrite factor_exponent_equation.
  destruct (Z_le_dec 1 p); try (destruct Hp; lia).
  destruct (Z_le_dec 2 p); try (destruct Hp; lia).
  destruct Zdivide_dec; try (destruct Hp; lia).
  - destruct d. assert (p / p = 1) by (apply Z.div_same; lia).
    subst. rewrite factor_exponent_equation.
    destruct (Z_le_dec 1 1); try lia.
    destruct (Z_le_dec 2 1); try lia.
    destruct Zdivide_dec; try lia.
    + destruct d. assert (0 < x0) by nia. nia.
    + rewrite H0. simpl. destruct Z_le_dec; try lia.
  - exfalso. apply n. exists 1. ring.
Qed.

(* seq_NoDup *)

Lemma primes_up_to_NoDup (n : Z) : NoDup (primes_up_to n).
Proof.
  unfold primes_up_to. apply NoDup_filter. apply NoDup_map_NoDup_ForallPairs.
  + unfold ForallPairs. intros. lia.
  + apply seq_NoDup.
Qed.

Lemma factor_exponent_fold_left_mul (L : list Z) (p : Z) (Hp : prime p) (f : Z -> Z) :
  (forall q, In q L -> 0 <= f q /\ 1 <= q) ->
  factor_exponent (fold_left (fun acc q => acc * q ^ f q) L 1) p =
  List.fold_left Z.add (map (fun q => factor_exponent (q ^ f q) p) L) 0.
Proof.
  Opaque Z.mul. intros Hf. induction L; simpl.
  - rewrite factor_exponent_equation. repeat destruct Z_le_dec; try lia.
    destruct Zdivide_dec; try lia. exfalso. destruct d. assert (0 < x) by nia. nia.
  - simpl in Hf. assert (forall L' w, fold_left (fun acc q => acc * q ^ f q) L' w =
      w * fold_left (fun acc q => acc * q ^ f q) L' 1).
    { induction L'; simpl; intros; try lia.
      rewrite IHL'. rewrite Z.mul_1_l. rewrite (IHL' (a0 ^ f a0)). ring. }
    rewrite H. rewrite factor_exponent_of_product_as_sum; try lia.
    + rewrite IHL.
      * rewrite Z.mul_1_l. 
        assert (forall L' w, fold_left Z.add (map (fun q => factor_exponent (q ^ f q) p) L') w =
          w + fold_left Z.add (map (fun q => factor_exponent (q ^ f q) p) L') 0).
        { induction L'; simpl; intros; try lia.
          rewrite IHL'. rewrite Z.add_0_l. rewrite (IHL' (factor_exponent (a0 ^ f a0) p)). ring. }
        rewrite (H0 _ (factor_exponent (a ^ f a) p)). auto.
      * intros. apply Hf. auto.
    + rewrite Z.mul_1_l. pose proof (Z.pow_pos_nonneg a (f a)).
      assert (0 <= f a /\ 1 <= a). { apply Hf. auto. } lia.
    + clear IHL. induction L; simpl; try lia.
      rewrite H, Z.mul_1_l. pose proof (Z.pow_pos_nonneg a0 (f a0)).
      assert (0 <= f a0 /\ 1 <= a0). { apply Hf. simpl. auto. }
      assert (forall q, a = q \/ In q L -> 0 <= f q /\ 1 <= q).
      { intros. apply Hf. simpl. tauto. }
      apply IHL in H2. nia.
    + auto.
  Transparent Z.mul.
Qed.

Lemma fold_left_plus_eq (L : list Z) (p : Z) (f : Z -> Z) (v : Z) :
  NoDup L -> In p L ->
  (forall q, In q L -> q <> p -> f q = 0) -> f p = v ->
  List.fold_left Z.add (map f L) 0 = v.
Proof.
  intros Hnodup Hin Hf0 Hfv. induction L; simpl in *; try tauto.
  destruct (Z.eq_dec a p).
  + subst a. rewrite Hfv.
    assert (forall q, In q L -> f q = 0).
    { intros q Hq. apply Hf0; auto. inversion Hnodup. subst. congruence. }
    induction L; simpl; auto. assert (f a = 0).
    { apply Hf0.
      + simpl; auto.
      + inversion Hnodup; subst. inversion H3; subst. simpl in H2. tauto. }
    rewrite H0. rewrite Z.add_0_r. apply IHL0; auto.
    - intros. apply Hf0; auto. simpl; tauto.
    - constructor.
      * inversion Hnodup; subst. simpl in H3. tauto.
      * inversion Hnodup; subst. inversion H4; subst; auto.
    - intros. assert (fold_left Z.add (map f (a :: L)) 0 = v).
      { apply IHL.
        + inversion Hnodup; auto.
        + simpl. auto.
        + intros. eauto. }
      simpl in H1. rewrite H0 in H1. simpl in H1. auto.
    - intros. apply H; simpl; auto.
  + rewrite Hf0; auto. simpl. rewrite IHL; auto.
    - inversion Hnodup; auto.
    - tauto.
Qed.

Lemma factor_exponent_LCM_of_range (n p : Z) (Hp : prime p) :
  factor_exponent (LCM_of_range n) p =
  if Z_le_dec p n then get_exp_le_bound n p else 0.
Proof.
  unfold LCM_of_range. destruct (Z_le_dec n 1).
  + rewrite (proj2 (Z.leb_le _ _) l). rewrite factor_exponent_equation.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try (destruct Hp; lia).
    destruct Zdivide_dec.
    - destruct d. assert (0 < x) by nia. nia.
    - destruct (Z_le_dec p n); lia.
  + rewrite (proj2 (Z.leb_nle _ _) n0). destruct Z_le_dec.
    - assert (In p (primes_up_to n)).
      { rewrite primes_up_to_In. auto. }
      pose proof (primes_up_to_NoDup n).
      assert (fold_left Z.add (map (fun q => factor_exponent (q ^ get_exp_le_bound n q) p)
        (primes_up_to n)) 0 = get_exp_le_bound n p).
      { eapply fold_left_plus_eq; eauto.
        + intros. rewrite factor_exponent_pow_coprime; auto.
          - intro. apply prime_div_prime in H3; auto. rewrite primes_up_to_In in H1.
            tauto.
          - rewrite primes_up_to_In in H1. destruct (proj1 H1). lia.
          - apply get_exp_le_bound_nonneg.
        + rewrite factor_exponent_of_pow.
          - rewrite factor_exponent_self; auto. ring.
          - apply get_exp_le_bound_nonneg.
          - destruct Hp; lia.
          - auto. }
      rewrite factor_exponent_fold_left_mul; auto. intros. split.
      * apply get_exp_le_bound_nonneg.
      * rewrite primes_up_to_In in H2. destruct (proj1 H2). lia.
    - assert (2 <= n < p) by lia.
      apply factor_exponent_of_product_of_primes_lt; auto.
      * lia.
      * apply get_exp_le_bound_nonneg.
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

Theorem prime_pow_le_bound_le_n (n p : Z) (Hp : 2 <= p) (Hpn : p <= n) :
  p ^ get_exp_le_bound n p <= n.
Proof.
  pose proof (get_exp_le_bound_spec n p ltac:(lia) ltac:(lia)).
  destruct H. auto.
Qed.

Lemma coprime_fold_left_mul (a : Z) (L : list Z) :
  (forall x, In x L -> rel_prime a x) -> rel_prime a (fold_left Z.mul L 1).
Proof.
  Opaque Z.mul. induction L; simpl; intros.
  + apply rel_prime_sym. apply rel_prime_1.
  + simpl in *. assert (rel_prime a a0) by (apply H; auto).
    assert (rel_prime a (fold_left Z.mul L 1)) by (apply IHL; auto).
    assert (forall L' w, fold_left Z.mul L' w = w * fold_left Z.mul L' 1).
    { induction L'; simpl; intros; try ring.
      rewrite Z.mul_1_l. rewrite IHL', (IHL' a1). ring. }
    rewrite Z.mul_1_l, H2. apply rel_prime_mult; auto.
  Transparent Z.mul.
Qed.

Lemma rel_prime_mult_dvd (a b y : Z) :
  (a | y) -> (b | y) -> rel_prime a b -> (a * b | y).
Proof.
  intros [k Hk] [m Hm] Huv. apply rel_prime_bezout in Huv.
  destruct Huv as [u v Hbez].
  assert (b | a * k). { rewrite Z.mul_comm, <- Hk. exists m. rewrite Hm. ring. }
  assert (b | a * (k * u)).
  { rewrite Z.mul_assoc. apply Z.divide_mul_l. auto. }
  assert (b | b * (k * v)). { exists (k * v); ring. }
  assert (b | a * (k * u) + b * (k * v)). { apply Z.divide_add_r; auto. }
  replace (a * (k * u) + b * (k * v)) with k in H2.
  + destruct H2 as [m' Hm'].
    exists m'; rewrite Hk, Hm'. ring.
  + replace (a * (k * u) + b * (k * v)) with (k * (u * a + v * b)) by ring.
    rewrite Hbez. ring.
Qed.

Lemma fold_left_mul_dvd (L : list Z) (y : Z) :
  (forall x, In x L -> (x | y)) -> NoDup L ->
  (forall x1 x2, In x1 L -> In x2 L -> x1 <> x2 -> rel_prime x1 x2) ->
  (fold_left Z.mul L 1 | y).
Proof.
  Opaque Z.mul. induction L; simpl; intros.
  + exists y; ring.
  + rewrite Z.mul_1_l. assert (a | y). { apply H; auto. }
    assert (fold_left Z.mul L 1 | y). { apply IHL; auto. inversion H0. auto. }
    assert (forall L' w, fold_left Z.mul L' w = w * fold_left Z.mul L' 1).
    { induction L'; simpl; intros; try ring.
      rewrite Z.mul_1_l. rewrite IHL', (IHL' a0). ring. }
    rewrite H4. assert (rel_prime a (fold_left Z.mul L 1)).
    { apply coprime_fold_left_mul. intros. apply H1; auto. inversion H0.
      congruence. }
    apply rel_prime_mult_dvd; auto.
  Transparent Z.mul.
Qed.

Lemma rel_prime_right_pow (a b i : Z) (H : rel_prime a b)
  (Hi : 0 <= i) : rel_prime a (b ^ i).
Proof.
  pose proof Hi. revert H0. pattern i. apply Z_lt_induction; auto; intros.
  clear Hi i. assert (x = 0 \/ 1 <= x) by lia. destruct H2.
  + subst x. ring_simplify (b ^ 0). apply rel_prime_sym. apply rel_prime_1.
  + replace x with (x - 1 + 1) by ring. rewrite Z.pow_add_r; try lia.
    ring_simplify (a ^ 1). pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)).
    ring_simplify (b ^ 1). apply rel_prime_mult; auto.
Qed.

Lemma rel_prime_pow (a b i j : Z) (H : rel_prime a b)
  (Hi : 0 <= i) (Hj : 0 <= j) : rel_prime (a ^ i) (b ^ j).
Proof.
  apply rel_prime_right_pow; auto. apply rel_prime_sym.
  apply rel_prime_right_pow; auto. apply rel_prime_sym. auto.
Qed.


Theorem LCM_of_range_correct (n : Z) :
  is_least (fun x => 1 <= x /\ (forall k, 1 <= k <= n -> (k | x))) (LCM_of_range n).
Proof.
  Opaque Z.mul. split; [split|].
  + apply one_le_LCM_of_range.
  + intros. unfold LCM_of_range. remember (n <=? 1) as B. destruct B.
    - symmetry in HeqB. rewrite Z.leb_le in HeqB. assert (k = 1) by lia.
      subst k. exists 1. auto.
    - symmetry in HeqB. rewrite Z.leb_gt in HeqB. rewrite (factorization k); try lia.
      assert (forall L w, fold_left Z.mul L w = w * fold_left Z.mul L 1).
      { induction L; simpl; intros; try lia.
        rewrite IHL, Z.mul_1_l, (IHL a). ring. }
      apply factor_exponent_le_implies_dvd.
      * assert (forall x, In x (map (fun p => fst p ^ snd p) (prime_factors_up_to k k)) -> 1 <= x).
        { intros. rewrite in_map_iff in H1. destruct H1 as [[f e] [Hfe Heq]].
          subst x. assert (prime f).
          { apply prime_factors_up_to_all_prime with (n := k) (k := k); try lia.
            rewrite in_map_iff. exists (f, e). auto. }
          assert (2 <= f). { apply prime_ge_2. auto. }
          assert (0 <= e).
          { apply snd_prime_factors_is_exp in Heq; try lia; auto.
            + simpl in Heq. pose proof (factor_exponent_nonneg k f). lia.
            + assert (k = 1 \/ 2 <= k) by lia. destruct H3; auto. subst k.
              rewrite prime_factors_up_to_equation in Heq. simpl in Heq. elim Heq. }
          simpl. pose proof Z.pow_pos_nonneg; lia. }
        revert H1. generalize (map (fun p => fst p ^ snd p) (prime_factors_up_to k k)).
        induction l; simpl; intros; try lia. rewrite Z.mul_1_l, H0.
        assert (1 <= a). { apply H1. auto. }
        assert (1 <= fold_left Z.mul l 1). { apply IHl. intros. apply H1; auto. }
        nia.
      * assert (forall x, In x (primes_up_to n) -> 1 <= x).
        { intros. rewrite primes_up_to_In in H1. destruct (proj1 H1). lia. }
        revert H1. generalize (primes_up_to n). induction l; simpl; intros; try lia.
        rewrite Z.mul_1_l.
        assert (forall L w, fold_left (fun acc p => acc * p ^ get_exp_le_bound n p) L w =
          w * fold_left (fun acc p => acc * p ^ get_exp_le_bound n p) L 1).
        { induction L; simpl; intros; try lia.
          rewrite IHL, Z.mul_1_l, (IHL (a0 ^ get_exp_le_bound n a0)). ring. }
        rewrite H2. pose proof (get_exp_le_bound_nonneg n a).
        pose proof (Z.pow_pos_nonneg a (get_exp_le_bound n a)).
        assert (1 <= a). { apply H1; auto. }
        assert (1 <= a ^ get_exp_le_bound n a) by lia.
        assert (1 <= fold_left (fun acc p => acc * p ^ get_exp_le_bound n p) l 1).
        { apply IHl. intros. apply H1; auto. }
        nia.
      * intros. rewrite <- (factorization k) at 1; try lia.
        pose proof (factor_exponent_LCM_of_range n p H1). unfold LCM_of_range in H2.
        rewrite (proj2 (Z.leb_gt _ _) HeqB) in H2. destruct (Z_le_dec p n).
        ++ rewrite H2. assert (k = 1 \/ 2 <= k <= n) by lia. destruct H3.
           -- simpl. subst k. rewrite factor_exponent_equation. destruct Z_le_dec; try lia.
              destruct Z_le_dec; try (destruct H1; lia). destruct Zdivide_dec.
              ** destruct d. assert (0 < x) by nia. nia.
              ** apply get_exp_le_bound_nonneg.
           -- assert (p ^ factor_exponent k p | k).
              { rewrite (remove_factor_main_lemma k p) at 2.
                + exists (remove_factor k p). auto.
                + lia.
                + destruct H1; lia. }
              apply prime_pow_dvd_k_dvd_LCM with (k := k); auto.
              apply factor_exponent_nonneg.
        ++ rewrite H2. rewrite factor_exponent_equation. destruct Z_le_dec.
           -- destruct Z_le_dec; try (destruct H1; lia).
              destruct Zdivide_dec.
              ** exfalso. apply Zdivide_le in d; try lia.
              ** lia.
           -- lia.
  + intros. apply Zdivide_le; try lia.
    - pose proof (one_le_LCM_of_range n). lia.
    - destruct (Z_le_dec 1 n).
      * set (L := map (fun p => p ^ get_exp_le_bound n p) (primes_up_to n)).
        assert (fold_left Z.mul L 1 | y).
        { apply fold_left_mul_dvd.
          + intros. unfold L in H0. rewrite in_map_iff in H0.
            destruct H0 as [x0 [H0 H1]]. subst x.
            assert (prime x0).
            { rewrite primes_up_to_In in H1. tauto. }
            assert (x0 <= n).
            { rewrite primes_up_to_In in H1. auto. exact (proj2 H1). }
            assert (x0 ^ get_exp_le_bound n x0 <= n).
            { apply prime_pow_le_bound_le_n; auto. destruct H0; lia. }
            assert (1 <= x0 ^ get_exp_le_bound n x0).
            { pose proof Z.pow_pos_nonneg x0 (get_exp_le_bound n x0).
              pose proof (prime_ge_2 x0 H0). pose proof get_exp_le_bound_nonneg n x0.
              lia. }
            apply H; auto.
          + unfold L. apply NoDup_map_NoDup_ForallPairs.
            - unfold ForallPairs. intros. rewrite primes_up_to_In in H0, H1. destruct H0, H1.
              assert (1 <= get_exp_le_bound n a).
              { rewrite get_exp_le_bound_equation. remember ((2 <=? a) && (a <=? n)) as B.
                symmetry in HeqB. destruct B.
                + pose proof (get_exp_le_bound_nonneg (n / a) a). lia.
                + exfalso. rewrite andb_false_iff in HeqB. destruct HeqB.
                  - rewrite Z.leb_gt in H5. destruct H0. lia.
                  - rewrite Z.leb_gt in H5. lia. }
              assert (a | b ^ get_exp_le_bound n b).
              { rewrite <- H2. exists (a ^ (get_exp_le_bound n a - 1)).
                replace a with (a ^ 1) at 5 by ring. rewrite <- Z.pow_add_r; try lia.
                f_equal. ring. }
              apply prime_dvd_of_dvd_pow in H6; auto.
              * apply prime_div_prime in H6; auto.
              * destruct H1; lia.
              * apply get_exp_le_bound_nonneg.
            - apply primes_up_to_NoDup.
          + intros. unfold L in H0, H1. rewrite in_map_iff in H0, H1.
            destruct H0 as [t1 [H0 H3]]. destruct H1 as [t2 [H1 H4]]. subst.
            rewrite primes_up_to_In in H3, H4. apply rel_prime_pow.
            - assert (t1 <> t2) by congruence. apply prime_rel_prime.
              * try tauto.
              * intro. apply prime_div_prime in H1; try tauto.
            - apply get_exp_le_bound_nonneg.
            - apply get_exp_le_bound_nonneg. }
        unfold LCM_of_range. destruct (n <=? 1).
        ++ exists y; ring.
        ++ unfold L in H0.
           assert (forall (L0 : list Z) (f: Z -> Z) w,
             fold_left Z.mul (map f L0) w = fold_left (fun acc p => acc * f p) L0 w).
           { induction L0; simpl; intros; try ring. rewrite IHL0. auto. }
           rewrite H1 in H0. auto.
      * unfold LCM_of_range. destruct (n <=? 1).
        ++ exists y; ring.
        ++ unfold primes_up_to. assert (Z.to_nat (n - 1) = 0%nat) by lia.
           rewrite H0. simpl. exists y; ring.
Qed.
