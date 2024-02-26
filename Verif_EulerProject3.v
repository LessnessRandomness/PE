Require Import VST.floyd.proofauto.
Require Import Znumtheory.
Open Scope Z.

Function repeated_div f n { measure Z.to_nat n }: Z * Z :=
  if Z_le_dec 2 f
  then if Z_le_dec 1 n
       then if Zdivide_dec f n
            then let (i, k) := repeated_div f (n / f) in (i + 1, k)
            else (0, n)
       else (0, n)
  else (0, n).
Proof.
  intros. destruct anonymous1. subst. rewrite Z.div_mul; try lia. nia.
Defined.

Function repeated_repeated_div (i n: Z) { measure Z.to_nat i }: Z :=
  if Z_le_dec 1 n
  then if Z_le_dec i 1
       then n
       else snd (repeated_div i (repeated_repeated_div (i - 1) n))
  else 1.
Proof.
  lia.
Defined.

Function prime_divisor_list (i n: Z) { measure Z.to_nat i}: list (Z * Z) :=
  if Z_le_dec 1 n
  then if Z_le_dec i 1
       then []
       else let W := prime_divisor_list (i - 1) n in
            if Zdivide_dec i (repeated_repeated_div (i - 1) n)
            then cons (i, fst (repeated_div i (repeated_repeated_div (i - 1) n))) W
            else W
  else [].
Proof.
  lia. lia.
Defined.


(* Theorems about the function 'repeated_div' *)

Theorem repeated_div_thm0 f n: 0 <= fst (repeated_div f n).
Proof.
  destruct (Z_le_dec 2 f).
  + destruct (Z_le_dec 1 n).
    - assert (0 <= n) by lia. revert l0. pattern n. apply Z_lt_induction; auto; intros.
      rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
      destruct Zdivide_dec.
      * replace (fst (let (i, k) := repeated_div f (x / f) in (i + 1, k))) with (fst (repeated_div f (x / f)) + 1).
        ++ assert (0 <= x / f < x). { destruct d. subst. rewrite Z.div_mul; try lia. nia. }
           assert (1 <= x / f). { destruct d. subst. rewrite Z.div_mul; try lia. }
           pose proof (H0 _ H1 H2). lia.
        ++ destruct repeated_div. simpl. auto.
      * simpl. lia.
    - rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). simpl. lia.
  + rewrite repeated_div_equation. destruct Z_le_dec; try lia. simpl. lia.
Qed.

Lemma repeated_div_thm1 (f n: Z) (H: 1 <= n): 1 <= snd (repeated_div f n) <= n.
Proof.
  assert (f <= 1 \/ 2 <= f) by lia. destruct H0.
  + rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). simpl. lia.
  + assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction; auto; intros. clear n H1.
    rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec; try (simpl; lia).
    assert (0 <= x / f < x). { destruct d. subst. rewrite Z.div_mul; try lia. nia. }
    assert (1 <= x / f). { destruct d. subst. rewrite Z.div_mul; try lia. }
    pose proof (H _ H1 H3). destruct repeated_div. simpl (snd _) in *. lia.
Qed.

Theorem repeated_div_main_thm f n (Hf: 2 <= f) (Hn: 1 <= n): n = f ^ fst (repeated_div f n) * snd (repeated_div f n).
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n. apply Z_lt_induction; auto; intros. clear H n.
  rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
  + destruct d. subst. assert (0 <= x0 < x0 * f). { split. lia. nia. }
    assert (1 <= x0) by nia. pose proof (H0 _ H H1). rewrite H2 at 1.
    assert (f ^ fst (repeated_div f x0) * snd (repeated_div f x0) * f =
            f ^ (fst (repeated_div f x0) + 1) * snd (repeated_div f x0)).
    { rewrite Zmult_comm. rewrite Zmult_assoc. rewrite (Zmult_comm f).
      replace f with (f ^ 1) at 3 by ring. rewrite <- Z.pow_add_r; try lia. apply repeated_div_thm0; try lia. }
    rewrite Z.div_mul; try lia. destruct repeated_div. simpl. auto.
  + simpl. ring.
Qed.

Theorem repeated_div_thm2 f n (Hf: 2 <= f) (Hn: 1 <= n): (f | snd (repeated_div f n)) -> False.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n. apply Z_lt_induction; auto. clear H n. intros.
  destruct H0. rewrite repeated_div_equation in H0. repeat (destruct Z_le_dec; try lia).
  destruct Zdivide_dec.
  + destruct d. subst. rewrite Z.div_mul in H0; try lia.
    assert (0 <= x1 < x1 * f) by nia. assert (1 <= x1) by nia.
    replace (snd (let (i, k) := repeated_div f x1 in (i + 1, k))) with (snd (repeated_div f x1)) in H0.
    - assert (f | snd (repeated_div f x1)). { exists x0. lia. }
      apply (H _ H1 H2 H3).
    - destruct repeated_div; simpl; auto.
  + simpl in H0. apply n. exists x0. auto.
Qed.

Theorem repeated_div_thm3 f n (Hf: 2 <= f) (Hn: 1 <= n): (snd (repeated_div f n) | n).
Proof.
  exists (f ^ fst (repeated_div f n)). apply repeated_div_main_thm; auto.
Qed.

Theorem different_Gauss a b n (Ha: 0 < a) (Hb: 0 < b): rel_prime a b -> (a | n) -> (b | n) -> (a | n / b).
Proof.
  intros. destruct H1. subst. rewrite Z_div_mult; try lia.
  eapply Gauss. rewrite Zmult_comm in H0. eauto. auto.
Qed.

Theorem repeated_div_thm4 f n (Hf: 2 <= f) (Hn: 1 <= n): (f | n) -> 1 <= fst (repeated_div f n).
Proof.
  intros. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
  destruct Zdivide_dec; try tauto. pose proof (repeated_div_thm0 f (n / f)).
  destruct repeated_div. simpl in *. lia.
Qed.

Theorem repeated_div_thm5 a b n (Ha: 1 <= a) (Hb: 1 <= b) (Hn: 1 <= n):
  rel_prime a b -> (a | n) -> (b | n) -> (a | (snd (repeated_div b n))).
Proof.
  intros. assert (a = 1 \/ 2 <= a) by lia. destruct H2.
  + exists (snd (repeated_div b n)). subst. ring.
  + assert (b = 1 \/ 2 <= b) by lia. destruct H3.
    - subst. simpl. auto.
    - assert (1 <= fst (repeated_div b n)).
      { apply repeated_div_thm4; try lia. auto. }
      assert (rel_prime a (b ^ fst (repeated_div b n))).
      { apply Zpow_facts.rel_prime_Zpower_r. lia. auto. }
      replace (snd (repeated_div b n)) with (n / b ^ fst (repeated_div b n)).
      * apply different_Gauss; try lia; auto. rewrite repeated_div_main_thm with (f:=b) (n:=n) at 2; try lia.
        exists (snd (repeated_div b n)). ring.
      * rewrite repeated_div_main_thm with (f:=b) (n:=n) at 1; try lia. rewrite Zmult_comm. rewrite Z_div_mult; auto.
        assert (0 < b ^ fst (repeated_div b n)). { apply Z.pow_pos_nonneg; try lia. }
        lia.
Qed.

Theorem repeated_div_thm6 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ (i | n)) -> snd (repeated_div i n) = n.
Proof.
  intros. assert (0 <= n) by lia. revert H H1. pattern n. apply Z_lt_induction; auto; intros.
  rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
  + tauto.
  + simpl. auto.
Qed.

Theorem repeated_div_thm7 n (H: 1 <= n) a b (Ha: 1 <= a) (Hb: 1 <= b) (H0: rel_prime a b):
  fst (repeated_div b n) = fst (repeated_div b (n * a)).
Proof.
  assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction; auto; intros.
  rewrite repeated_div_equation. rewrite (repeated_div_equation b (x * a)). repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
  + destruct Zdivide_dec.
    - assert (fst (let (i, k) := repeated_div b (x / b) in (i + 1, k)) = fst (repeated_div b (x / b)) + 1).
      { destruct repeated_div. simpl. auto. }
      rewrite H3; clear H3.
      assert (fst (let (i, k) := repeated_div b (x * a / b) in (i + 1, k)) = fst (repeated_div b (x * a / b)) + 1).
      { destruct repeated_div. simpl. auto. }
      rewrite H3; clear H3. f_equal. destruct d. subst. assert (0 <= x0 < x0 * b) by nia. assert (1 <= x0) by lia.
      pose proof (H _ H3 H4). rewrite Z.div_mul; try lia.
      rewrite <- Z.mul_assoc. rewrite (Z.mul_comm b). rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
    - exfalso. apply n0. destruct d. subst. exists (x0 * a). ring.
  + destruct Zdivide_dec.
    - exfalso. apply n0. rewrite Z.mul_comm in d. apply rel_prime_sym in H0. eapply Gauss; eauto.
    - simpl. auto.
  + auto.
Qed.

Theorem repeated_div_thm8 n (H: 1 <= n) a b (Ha: 1 <= a) (Hb: 1 <= b) (H0: rel_prime a b) i (Hi: 0 <= i):
  fst (repeated_div b n) = fst (repeated_div b (n * a ^ i)).
Proof.
  pose proof Hi. revert H1. pattern i. apply Z_lt_induction; auto; intros. assert (x = 0 \/ 1 <= x) by lia. destruct H3.
  + subst. simpl. do 2 f_equal. ring.
  + replace x with (x - 1 + 1) by ring. rewrite Z.pow_add_r; try lia. replace (a ^ 1) with a by ring.
    rewrite Z.mul_assoc. rewrite <- repeated_div_thm7; try lia; auto. apply H1; try lia.
Qed.

Theorem repeated_div_thm9 n (H: 1 <= n) a b (Ha: 2 <= a) (Hb: 2 <= b) (H0: rel_prime a b):
  fst (repeated_div a (snd (repeated_div b n))) = fst (repeated_div a n).
Proof.
  assert (n = b ^ fst (repeated_div b n) * snd (repeated_div b n)) by (apply repeated_div_main_thm; auto).
  rewrite H1 at 2. rewrite Z.mul_comm. rewrite <- repeated_div_thm8; try lia; auto. apply rel_prime_sym in H0; auto.
  apply repeated_div_thm0; try lia.
Qed.

Theorem repeated_div_thm10 a b (Ha: 2 <= a) (Hb: 1 <= b) (H0: ~ (a | b)) i (Hi: 0 <= i):
  snd (repeated_div a (b * a ^ i)) = b.
Proof.
  pose proof Hi. revert H. pattern i. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H2.
  + subst. simpl. ring_simplify (b * 1). rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
    destruct Zdivide_dec; try tauto.
  + replace x with (x - 1 + 1) by ring. rewrite Z.pow_add_r; try lia. ring_simplify (a ^ 1).
    rewrite repeated_div_equation in *. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
    - assert (snd (let (i0, k) := repeated_div a (b * (a ^ (x - 1) * a) / a) in (i0 + 1, k)) =
              snd (repeated_div a (b * (a ^ (x - 1) * a) / a))).
      { destruct repeated_div; simpl; tauto. }
      rewrite H3; clear H3. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
      apply H; try lia.
    - exfalso. apply n. exists (b * a ^ (x - 1)). ring.
Qed.

Theorem aux0 a b (H1: rel_prime a b) i (H2: 0 <= i) W: (b | W * a ^ i) -> (b | W).
Proof.
  pose proof H2. revert H. pattern i. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H4.
  + subst. replace (W * a ^ 0) with W in H3 by ring. auto.
  + replace x with (x - 1 + 1) in H3 by ring. rewrite Z.pow_add_r in H3; try lia.
    ring_simplify (a ^ 1) in H3. rewrite Z.mul_assoc in H3. assert (b | W * a ^ (x - 1)).
    { apply Gauss with (b := a).
      + replace (a * (W * a ^ (x - 1))) with (W * a ^ (x - 1) * a) by ring. auto.
      + apply rel_prime_sym. auto. }
    apply H in H5; try lia. auto.
Qed.

Theorem aux1 n a b (H1: rel_prime a b) (H2: (a | n)) (H3: (b | n)): 0 < a -> 0 < b -> (a * b | n).
Proof.
  intros. assert (b | n / a). { apply different_Gauss; auto. apply rel_prime_sym. auto. }
  destruct H4. exists x. replace (x * (a * b)) with (x * b * a) by ring. rewrite <- H4.
  destruct H2. subst. rewrite Z.div_mul; auto. lia.
Qed.

Theorem aux2 n (Hn: 1 <= n) a b (H1: rel_prime a b) (H2: (a | n)) (H3: (b | n)): 0 < a -> 0 < b -> n / a / b = n / b / a.
Proof.
  intros. assert (0 <= n) by lia. revert Hn H2 H3. pattern n. apply Z_lt_induction; auto; intros.
  assert (a * b | x). { apply aux1; auto. }
  destruct H6. subst. rewrite (Z.mul_comm a b) at 1. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
  rewrite Z.div_mul; try lia. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia. rewrite Z.div_mul; try lia.
Qed.

Theorem aux3 n (Hn: 1 <= n) a b (Hb: 1 <= b) (H: (b | n)): n / b * a = n * a / b.
Proof.
  destruct H. subst. rewrite Z.div_mul; try lia. rewrite <- Z.mul_assoc. rewrite (Z.mul_comm b a).
  rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
Qed.

Theorem aux4 n (Hn: 1 <= n) a b (H: 2 <= a) (H0: 2 <= b) (H1: rel_prime a b) i (H2: 0 <= i) j (H3: 0 <= j):
  (a ^ i | n) -> (b ^ j | n) -> (b | n / a ^ i / b ^ j) -> (b | n / b ^ j).
Proof.
  intros. pose proof H2. revert H7 H4 H6. pattern i. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H9.
  + subst. simpl (a ^ 0) in H8. rewrite Z.div_1_r in H8. auto.
  + destruct H6. subst. rewrite Z.div_mul in H8; try lia.
    rewrite <- aux3; try lia.
    - destruct H8. exists (x1 * a ^ x). rewrite H6. ring.
    - apply aux0 in H5; try lia; auto. apply Zpow_facts.rel_prime_Zpower_r; auto.
Qed.

Theorem aux5 a b c: c <> 0 -> a * c = b * c -> a = b.
Proof. nia. Qed.

Theorem aux6 a b c d (H1: 1 <= a) (H2: 1 <= b) (H3: 1 <= c) (H4: 1 <= d) (H5: (b | a)) (H6: (d | c)):
  a * d = b * c -> a / b = c / d.
Proof.
  intros. apply aux5 with (c := b * d). nia.
  rewrite Z.mul_assoc. rewrite aux3; auto. rewrite Z.div_mul; try lia.
  rewrite (Z.mul_comm b). rewrite Z.mul_assoc. rewrite aux3; try lia; auto. rewrite Z.div_mul; try lia; auto.
Qed.

Theorem repeated_div_thm11 n (H: 1 <= n) a b (Ha: 2 <= a) (Hb: 2 <= b) (H0: rel_prime a b):
  (a ^ fst (repeated_div a n) | snd (repeated_div b n)).
Proof.
  assert (a ^ fst (repeated_div a n) | snd (repeated_div b n) * b ^ fst (repeated_div b n)).
  { rewrite Z.mul_comm. rewrite <- repeated_div_main_thm; auto. exists (snd (repeated_div a n)).
    rewrite Z.mul_comm. rewrite <- repeated_div_main_thm; auto. }
  apply aux0 in H1; auto.
  + apply Zpow_facts.rel_prime_Zpower_r.
    - apply repeated_div_thm0; auto.
    - apply rel_prime_sym; auto.
  + apply repeated_div_thm0; auto.
Qed.

Theorem repeated_div_thm12 n (H: 1 <= n) a b (Ha: 2 <= a) (Hb: 2 <= b) (H0: rel_prime a b):
  snd (repeated_div a (snd (repeated_div b n))) = snd (repeated_div b (snd (repeated_div a n))).
Proof.
  pose proof repeated_div_main_thm.
  assert (forall N a, 2 <= a -> 1 <= N -> snd (repeated_div a N) = N / a ^ fst (repeated_div a N)).
  { intros. rewrite (H1 a0 N H2 H3) at 2. rewrite Z.mul_comm, Z.div_mul; auto.
    apply Z.pow_nonzero; try lia. apply repeated_div_thm0; auto. }
  pose proof repeated_div_thm1.
  pose proof (H2 (snd (repeated_div b n)) a Ha (proj1 (H3 b n H))).
  pose proof (H2 (snd (repeated_div a n)) b Hb (proj1 (H3 a n H))).
  rewrite H4. rewrite H5. pose proof (rel_prime_sym a b H0).
  rewrite repeated_div_thm9; auto. rewrite repeated_div_thm9; auto.
  apply aux6; auto.
  + apply repeated_div_thm1; auto.
  + assert (0 < a ^ fst (repeated_div a n)). { apply Z.pow_pos_nonneg; try lia. apply repeated_div_thm0; auto. } lia.
  + apply repeated_div_thm1; auto.
  + assert (0 < b ^ fst (repeated_div b n)). { apply Z.pow_pos_nonneg; try lia. apply repeated_div_thm0; auto. } lia.
  + apply repeated_div_thm11; auto; try lia.
  + apply repeated_div_thm11; auto; try lia.
  + rewrite <- H1; auto. rewrite Z.mul_comm. rewrite <- H1; auto.
Qed.

Theorem repeated_div_thm13 (n k: Z) (H: 1 <= n): 0 <= k -> snd (repeated_div n (n ^ k)) = 1.
Proof.
  intros. pose proof H0. revert H0. pattern k. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H3.
  + subst. simpl. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
    - destruct Zdivide_dec.
      * exfalso. destruct d. assert (0 < x) by lia. nia.
      * simpl. auto.
    - simpl. auto.
  + simpl. replace x with ((x - 1) + 1) by ring. rewrite Z.pow_add_r; try lia.
    ring_simplify (n ^ 1). rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
    - destruct Zdivide_dec.
      * assert (0 < n ^ (x - 1)). { apply Z.pow_pos_nonneg; try lia. }
        assert (1 <= n ^ (x - 1)) by lia.
        assert (n ^ (x - 1) * n / n = n ^ (x - 1)). { rewrite Z.div_mul; try lia. }
        rewrite H6.
        assert (forall (p: Z * Z), snd (let (i, k) := p in (i + 1, k)) = snd p).
        { intros [p1 p2]. simpl. auto. }
        rewrite H7. apply H0; try lia.
      * exfalso. apply n0. exists (n ^ (x - 1)). ring.
    - simpl. assert (n = 1) by lia. subst. rewrite Z.pow_1_l; try lia.
Qed.



(* Theorems about the function 'repeated_repeated_div' *)

Theorem repeated_repeated_div_thm0 (i n: Z) (H: 1 <= n): 1 <= repeated_repeated_div i n.
Proof.
  destruct (Z_le_dec i 1).
  + rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
  + assert (0 <= i) by lia. pattern i. apply Z_lt_induction; auto; intros. clear n0.
    rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    apply repeated_div_thm1; auto; try lia. apply H1. lia.
Qed.

Theorem repeated_repeated_div_thm1 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (i | repeated_repeated_div i n) -> False.
Proof.
  intros. rewrite repeated_repeated_div_equation in H1. repeat (destruct Z_le_dec in H1; try lia).
  apply repeated_div_thm2 in H1; auto. apply repeated_repeated_div_thm0. auto.
Qed.

Theorem repeated_repeated_div_thm2 (i n w: Z) (H: 1 <= n) (H0: 1 <= i) (H1: 0 <= w):
  forall i, 2 <= i <= i + w -> (i | repeated_repeated_div (i + w) n) -> False.
Proof.
  pattern w. apply Z_lt_induction; auto; intros. clear H1 w.
  assert (x = 0 \/ 1 <= x) by lia. destruct H1.
  + subst. ring_simplify (i0 + 0) in H4. apply repeated_repeated_div_thm1 in H4; lia.
  + rewrite repeated_repeated_div_equation in H4. destruct Z_le_dec in H4; try lia. destruct Z_le_dec in H4; try lia.
    assert (0 <= x - 1 < x) by lia. assert (2 <= i0 <= i0 + (x - 1)) by lia.
    pose proof (H2 _ H5 _ H6). ring_simplify (i0 + (x - 1)) in H7.
    assert (1 <= i0 + x) by lia.
    assert (1 <= repeated_repeated_div (i0 + x - 1) n) by (apply repeated_repeated_div_thm0; try lia).
    apply (H2 _ H5 _ H6).
    assert (snd (repeated_div (i0 + x) (repeated_repeated_div (i0 + x - 1) n)) | (repeated_repeated_div (i0 + x - 1) n)).
    { apply repeated_div_thm3; try lia. }
    ring_simplify (i0 + (x - 1)). eapply Z.divide_trans; eauto.
Qed.

Theorem repeated_repeated_div_thm3 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  forall x, 2 <= x <= i -> (x | repeated_repeated_div i n) -> False.
Proof.
  intros. replace i with (x + (i - x)) in H2 by lia.
  eapply repeated_repeated_div_thm2 in H2; eauto. lia. lia.
Qed.

Theorem repeated_repeated_div_thm4 (i n x: Z) (H: 1 <= n) (H0: 1 <= i) (H1: 2 <= x):
  ( x | repeated_repeated_div i n) -> (x | n).
Proof.
  assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H2 i.
  rewrite repeated_repeated_div_equation in H4. destruct Z_le_dec in H4; try lia. destruct Z_le_dec in H4; auto.
  assert (x | repeated_repeated_div (x0 - 1) n).
  { destruct H4. exists (x1 * x0 ^ fst (repeated_div x0 (repeated_repeated_div (x0 - 1) n))).
    rewrite Zmult_comm. rewrite Zmult_assoc. rewrite (Zmult_comm x). rewrite <- H2.
    rewrite Zmult_comm. rewrite <- repeated_div_main_thm; try lia.
    apply repeated_repeated_div_thm0. auto. }
  assert (x0 = 1 \/ 1 <= x0 - 1) by lia. destruct H5.
  + subst. simpl in *. rewrite repeated_repeated_div_equation in H2.
    destruct Z_le_dec in H2; try lia.
  + apply H0 in H2; auto. lia.
Qed.

Theorem repeated_repeated_div_thm5 (i n: Z) (H: 1 <= n) (H0: 1 <= i):
  (i + 1 | repeated_repeated_div i n) -> prime (i + 1) /\ (i + 1 | n).
Proof.
  intros. split.
  + destruct (prime_dec (i + 1)); auto. exfalso. apply not_prime_divide in n0; try lia.
    destruct n0 as [k [H2 H3]]. destruct H3. assert (Z.divide k (repeated_repeated_div i n)).
    { destruct H1. exists (x0 * x). lia. }
    apply repeated_repeated_div_thm3 in H4; auto. lia. lia.
  + eapply repeated_repeated_div_thm4; eauto. lia.
Qed.

Theorem repeated_repeated_div_thm6 (i n: Z) (H: 1 <= n) (H0: 1 <= i):
  prime (i + 1) -> (i + 1 | n) -> (i + 1 | repeated_repeated_div i n).
Proof.
  intros. destruct H1. remember (i + 1) as W. assert (0 <= i) by lia. assert (i < W) by lia.
  revert H5. pattern i. apply Z_lt_induction; auto; intros.
  assert (2 <= x \/ x <= 1) by lia. destruct H7.
  + rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
    assert (W | repeated_repeated_div (x - 1) n).
    { apply H5. lia. lia. }
    destruct H8. remember (repeated_repeated_div (x - 1) n) as X.
    eapply Gauss.
    - exists x0. rewrite <- H8. rewrite repeated_div_main_thm with (f := x); eauto; try lia.
      subst. apply repeated_repeated_div_thm0. auto.
    - apply Zpow_facts.rel_prime_Zpower_r.
      * apply repeated_div_thm0.
      * apply rel_prime_sym. apply H3. lia.
  + rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia). auto.
Qed.

Theorem repeated_repeated_div_main_thm (i n: Z) (H: 1 <= n) (H0: 1 <= i):
  (i + 1 | repeated_repeated_div i n) <-> prime (i + 1) /\ (i + 1 | n).
Proof.
  split.
  + apply repeated_repeated_div_thm5; auto.
  + intros [H1 H2]. apply repeated_repeated_div_thm6; auto.
Qed.

Theorem repeated_repeated_div_thm7 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ prime i) -> ~ (i | repeated_repeated_div (i - 1) n).
Proof.
  intros. intro. apply H1. replace i with ((i - 1) + 1) in H2 at 1 by ring. replace i with ((i - 1) + 1) by ring.
  assert (i = 2 \/ 2 <= i - 1) by lia. destruct H3.
  + subst. pose prime_2. tauto.
  + apply repeated_repeated_div_main_thm in H2. tauto. lia. lia.
Qed.

Theorem repeated_repeated_div_thm8 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ prime i) -> repeated_repeated_div i n = repeated_repeated_div (i - 1) n.
Proof.
  intros. eapply repeated_repeated_div_thm7 with (n:=n) in H1; eauto.
  rewrite repeated_repeated_div_equation at 1. repeat (destruct Z_le_dec; try lia).
  rewrite repeated_div_thm6; try lia; auto.
  apply repeated_repeated_div_thm0. auto.
Qed.

Theorem repeated_repeated_div_thm9 (i n: Z) (H: 1 <= n): repeated_repeated_div i n <= n.
Proof.
  assert (i <= 1 \/ 2 <= i) by lia. destruct H0.
  + rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
  + assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros.
    assert (x = 2 \/ 2 <= x - 1) by lia. destruct H3.
    - subst. rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
      simpl. rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
      apply repeated_div_thm1; lia.
    - rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
      assert (snd (repeated_div x (repeated_repeated_div (x - 1) n)) <= repeated_repeated_div (x - 1) n).
      { apply repeated_div_thm1; try lia. apply repeated_repeated_div_thm0. auto. }
      assert (repeated_repeated_div (x - 1) n <= n).
      { apply H0; try lia. }
      lia.
Qed.

Theorem repeated_repeated_div_thm10 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  forall k, 1 < k -> Z.divide k (repeated_repeated_div i n) -> k > i.
Proof.
  intros. assert (1 < k <= i \/ k > i) by lia. destruct H3; auto.
  apply repeated_repeated_div_thm3 in H2; try lia.
Qed.

Theorem repeated_repeated_div_thm11 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ prime (repeated_repeated_div i n)) -> 1 < repeated_repeated_div i n -> (i + 1) * (i + 1) <= repeated_repeated_div i n.
Proof.
  intros. apply not_prime_divide in H1; try lia.
  destruct H1 as [k [H1 H3]]. destruct H3. assert (Z.divide k (repeated_repeated_div i n)).
    { exists x; lia. }
    assert (Z.divide x (repeated_repeated_div i n)).
    { exists k; lia. }
    apply (repeated_repeated_div_thm10 i n H H0) in H4; try lia.
    apply (repeated_repeated_div_thm10 i n H H0) in H5; try nia.
Qed.

Theorem repeated_repeated_div_thm12 i n (H: 1 <= n) (H0: 2 <= i):
  1 < repeated_repeated_div i n -> i < repeated_repeated_div i n.
Proof.
  intros. pose proof (repeated_repeated_div_thm10 i n H H0 _ H1 ltac:(exists 1; ring)). lia.
Qed.

Theorem repeated_repeated_div_thm13 n f (H: 1 <= n) (H0: 2 <= f): (~ Z.divide f n) -> repeated_repeated_div f n = repeated_repeated_div (f - 1) n.
Proof.
  intros. rewrite (repeated_repeated_div_equation f). destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
  destruct (Zdivide_dec f (repeated_repeated_div (f - 1) n)).
  + apply repeated_repeated_div_thm4 in d; try lia. tauto.
  + rewrite repeated_div_thm6; auto. apply repeated_repeated_div_thm0. auto.
Qed.

Theorem repeated_repeated_div_thm14 n f (H: 1 <= n) (H0: 2 <= f) g (H1: f <= g):
  repeated_repeated_div f (repeated_repeated_div g n) = repeated_repeated_div g n.
Proof.
  assert (0 <= f) by lia. revert H1 H0. pattern f. apply Z_lt_induction; auto; intros.
  assert (x = 2 \/ 3 <= x) by lia. destruct H4.
  + subst. rewrite (repeated_repeated_div_equation 2). simpl. rewrite (repeated_repeated_div_equation 1).
    simpl. destruct Z_le_dec.
    - destruct (Zdivide_dec 2 (snd (repeated_div 2 n))).
      * exfalso. apply repeated_div_thm2 in d; lia.
      * apply repeated_div_thm6; auto. unfold not. apply repeated_repeated_div_thm3; try lia.
    - pose proof (repeated_repeated_div_thm0 g n H). tauto.
  + rewrite (repeated_repeated_div_equation x). repeat (destruct Z_le_dec; try lia).
    - rewrite H0; try lia. apply repeated_div_thm6; try lia. unfold not. apply repeated_repeated_div_thm3; try lia.
    - pose proof (repeated_repeated_div_thm0 g n H). tauto.
Qed.

Theorem repeated_repeated_div_thm15 (n f x: Z) (H: 1 <= n) (H0: 2 <= f) (H1: 0 <= x):
  repeated_repeated_div f n = 1 -> repeated_repeated_div (f + x) n = 1.
Proof.
  pose proof H1. revert H2. pattern x. apply Z_lt_induction; auto; intros.
  assert (x0 = 0 \/ 1 <= x0) by lia. destruct H5.
  + subst. ring_simplify (f + 0). auto.
  + assert (0 <= x0 - 1 < x0) by lia. assert (0 <= x0 - 1) by lia. pose proof (H2 _ H6 H7 H4).
    ring_simplify (f + (x0 - 1)) in H8. rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
    rewrite H8. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
    - destruct d. assert (0 < x1) by lia. nia.
    - simpl. reflexivity.
Qed.

Theorem repeated_repeated_div_thm17 (n i j: Z):
  1 <= n -> 2 <= i <= j -> repeated_repeated_div i n = 1 -> repeated_repeated_div j n = 1.
Proof.
  intros. replace j with (i + (j - i)) by ring. apply repeated_repeated_div_thm15; try lia.
Qed.

Theorem repeated_repeated_div_thm18 (n i w: Z):
  1 <= n -> 2 <= i <= i + w -> repeated_repeated_div (i + w) n <= repeated_repeated_div i n.
Proof.
  intros. assert (0 <= w) by lia. pose proof H1. destruct H0. clear H3.
  revert H1 n H. pattern w. apply Z_lt_induction; auto; intros. clear H2 w.
  assert (x = 0 \/ 1 <= x) by lia. destruct H2.
  + subst. ring_simplify (i + 0). lia.
  + assert (0 <= x - 1 < x) by lia. assert (0 <= x - 1) by lia.
    rewrite (repeated_repeated_div_equation (i + x)).
    repeat (destruct Z_le_dec; try lia). rewrite (repeated_div_equation).
    repeat (destruct Z_le_dec; try lia).
    - destruct Zdivide_dec.
      * assert (forall (p: Z * Z), snd (let (i, k) := p in (i + 1, k)) = snd p).
        { intros. destruct p. simpl. auto. }
        rewrite H6. pose proof (H _ H4 H5 _ H3). ring_simplify (i + (x - 1)) in H7.
        destruct d. rewrite H8. rewrite Z.div_mul; try lia.
        assert (snd (repeated_div (i + x) x0) <= x0). { apply repeated_div_thm1. nia. }
        assert (x0 <= repeated_repeated_div (i + x - 1) n). { nia. }
        lia.
      * simpl. replace (i + x - 1) with (i + (x - 1)) by ring. apply H; auto.
    - simpl. replace (i + x - 1) with (i + (x - 1)) by ring. apply H; auto.
Qed.

Theorem repeated_repeated_div_thm19 (n i j: Z): 1 <= n -> 2 <= i <= j -> repeated_repeated_div j n <= repeated_repeated_div i n.
Proof.
  intros. replace j with (i + (j - i)) by ring. apply repeated_repeated_div_thm18; try lia.
Qed.

Theorem repeated_repeated_div_thm20 (n i: Z) (Hn: 1 <= n) (Hi: 2 <= i):
  (repeated_repeated_div i n | n).
Proof.
  assert (0 <= i) by lia. revert Hi. pattern i. apply Z_lt_induction; auto; intros. clear H i.
  assert (x = 2 \/ 2 < x) by lia. destruct H.
  + subst. clear Hi. clear H0. rewrite repeated_repeated_div_equation.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
    rewrite repeated_repeated_div_equation. simpl. destruct Z_le_dec; try lia.
    apply repeated_div_thm3; try lia.
  + assert (0 <= x - 1 < x) by lia. assert (2 <= x - 1) by lia.
    pose proof (H0 _ H1 H2). rewrite repeated_repeated_div_equation.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    pose proof (repeated_div_thm3 x (repeated_repeated_div (x - 1) n) Hi).
    assert (1 <= repeated_repeated_div (x - 1) n). { apply repeated_repeated_div_thm0; try lia. }
    pose proof (H4 H5). destruct H3, H6. exists (x0 * x1). lia.
Qed.


(* Definition of (brute_force n) etc. *)

Function Zseq (n: Z) { measure Z.to_nat n }: list Z :=
  if Z_le_dec n 0 then [] else Zseq (n - 1) ++ n :: nil.
Proof. abstract lia. Defined.

Theorem Zseq_thm (n: Z): forall x, In x (Zseq n) <-> 1 <= x <= n.
Proof.
  destruct (Z_le_dec n 0).
  + intro. rewrite Zseq_equation. destruct Z_le_dec; try lia. intuition.
  + intro. assert (1 <= n) by lia. clear n0. assert (0 <= n) by lia.
    revert H x. pattern n. apply Z_lt_induction; auto; clear H0; intros. split; intros.
    - rewrite Zseq_equation in H1. destruct Z_le_dec.
      * elim H1.
      * clear n0. apply in_app in H1. destruct H1.
        ++ assert (x = 0 \/ x = 1 \/ 2 <= x) by lia. destruct H2; try lia. destruct H2; try lia.
           -- subst. simpl in H1. elim H1.
           -- apply H in H1; try lia.
        ++ simpl in H1. destruct H1; try lia.
    - rewrite Zseq_equation. destruct Z_le_dec; try lia. apply in_app.
      assert (1 <= x0 <= x - 1 \/ x0 = x) by lia. destruct H2.
      * left. apply H; try lia.
      * subst. right. simpl. auto.
Qed.

Definition max_of_list (default: Z) (L: list Z): Z := fold_right Z.max default L.

(* prime_dec does not compute :( *)
Definition all_prime_divisors (n: Z) := filter prime_dec (filter (fun x => Zdivide_dec x n) (Zseq n)).

Definition brute_force (n: Z) := max_of_list 1 (all_prime_divisors n).

Definition biggest_prime_divisor (n m: Z) :=
  let P x := prime x /\ Z.divide x n in P m /\ forall k, P k -> m <> k -> k < m.

Theorem In_max_thm (L: list Z) x (H: In x L): x <= max_of_list 1 L.
Proof.
  induction L.
  + elim H.
  + simpl. destruct H; try lia. pose (IHL H). lia.
Qed.

Theorem max_In_thm (L: list Z) x (H: max_of_list 1 L = x) (H0: L <> []) (H1: forall w, In w L -> 2 <= w):
  In x L.
Proof.
  revert x H H0. induction L; intros.
  + elim H0; auto.
  + simpl in *. clear H0. assert (forall w, In w L -> 2 <= w). { intros. apply H1. auto. }
    rewrite Zmax_spec in H. destruct zlt in H; auto. subst. pose proof (IHL H0). destruct L.
    - simpl in *. clear H H0. assert (a = a \/ False) by auto. apply H1 in H. lia.
    - simpl in *. clear IHL. pose proof (H _ (eq_refl (Z.max z (max_of_list 1 L)))).
      assert (z :: L <> []) by congruence. apply H2 in H3. destruct H3.
      * rewrite <- H3. auto.
      * auto.
Qed.

Theorem max_In_thm0 (L: list Z) x (H: 1 < x) (H0: forall w, In w L -> w < x): max_of_list 1 (L ++ [x]) = x.
Proof.
  induction L.
  + simpl. lia.
  + simpl. rewrite IHL.
    - assert (In a (a :: L)) by (simpl; auto). apply H0 in H1. lia.
    - intros. simpl in H0. assert (a = w \/ In w L) by auto. apply H0 in H2. auto.
Qed.


(* Theorems about brute_force *)

Theorem brute_force_thm0 (n: Z) (H: 2 <= n):
  forall w, In w (filter prime_dec (filter (fun x => Zdivide_dec x n) (Zseq n))) <->
  (Z.divide w n /\ 1 <= w <= n /\ prime w).
Proof.
  intros. split; intros.
  + apply filter_In in H0. destruct H0. destruct prime_dec in H1; simpl in *; try congruence.
    apply filter_In in H0. destruct H0. destruct Zdivide_dec in H2; simpl in *; try congruence.
    apply Zseq_thm in H0. auto.
  + destruct H0. destruct H1. apply filter_In. destruct prime_dec.
    - simpl. split; auto. apply filter_In. destruct Zdivide_dec; simpl.
      * split; auto. apply Zseq_thm. auto.
      * elim (n0 H0).
    - elim (n0 H2).
Qed.

Theorem prime_divisor_existence (n: Z) (H: 2 <= n):
  exists p, prime p /\ Z.divide p n.
Proof.
  assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction; auto. clear n H0. intros.
  destruct (prime_dec x).
  + exists x. split; auto. exists 1. lia.
  + apply not_prime_divide in n; try lia. destruct n as [n [H1 H2]]. destruct H2.
    subst. assert (0 <= x0 < x0 * n) by nia. assert (2 <= x0) by nia. pose proof (H _ H2 H3).
    destruct H4 as [p [H4 H5]]. exists p. split; auto. destruct H5. subst. exists (x * n). lia.
Qed.

Theorem brute_force_main_thm n (H: 2 <= n): biggest_prime_divisor n (brute_force n).
Proof.
  unfold biggest_prime_divisor. unfold brute_force.
  assert (forall x, prime x -> (x | n) -> In x (all_prime_divisors n)).
  { intros. apply filter_In. split.
    + apply filter_In. split.
      - apply Zseq_thm. split.
        * destruct H0. lia.
        * destruct H1. destruct H0. assert (0 < x0) by lia. nia.
      - destruct Zdivide_dec; simpl; auto.
    + destruct prime_dec; simpl; auto. }
  pose proof (prime_divisor_existence _ H). destruct H1. destruct H1. pose proof (H0 _ H1 H2). 
  assert (all_prime_divisors n <> []).
  { intro. rewrite H4 in H3. elim H3. }
  assert (prime (max_of_list 1 (all_prime_divisors n))).
  { pose proof (max_In_thm (all_prime_divisors n)).
    eapply H5 in H4; eauto.
    + apply filter_In in H4. destruct H4. destruct prime_dec in H6; simpl in *; try congruence.
    + intros. apply filter_In in H6. destruct H6. destruct prime_dec in H7; simpl in *; try congruence.
      destruct p. lia. }
  repeat split.
  + destruct H5. auto.
  + exists n0; lia.
  + exists (max_of_list 1 (all_prime_divisors n)). lia.
  + intros. apply prime_alt in H5. destruct H5. assert (x0 = 1 \/ x0 = -1 \/ x0 = 0 \/ 1 < x0 \/ x0 < - 1) by lia.
    destruct H10 as [H10 | [H11 | [H12 | [H13 | H14]]]].
    - subst. exists 1. auto.
    - subst. exists (-1). auto.
    - subst. destruct H7. lia.
    - exfalso. apply (H9 x0); auto. split; auto. destruct H7. assert (0 < x1) by lia. nia.
    - exfalso. apply (H9 (-x0)); auto.
      * split; try lia. destruct H7. assert (0 < -x1) by lia. nia.
      * destruct H8. rewrite H8. exists (-x1). ring.
  + pose proof (max_In_thm (all_prime_divisors n)).
    pose proof (eq_refl (max_of_list 1 (all_prime_divisors n))).
    apply H6 in H7. clear H6.
    - apply filter_In in H7. destruct H7. apply filter_In in H6. destruct H6.
      destruct Zdivide_dec in H8; simpl in *; try congruence.
    - auto.
    - intros. apply filter_In in H8. destruct H8. destruct prime_dec in H9; simpl in *; try congruence.
      destruct p. lia.
  + intros. destruct H6. pose (H0 _ H6 H8). apply In_max_thm in i. lia.
Qed.

Theorem brute_force_thm1 (n: Z) (H: prime n): brute_force n = n.
Proof.
  assert (2 <= n). { destruct H. lia. }
  pose proof (brute_force_main_thm n H0). destruct H1. destruct H1.
  assert (brute_force n <= n).
  { apply Z.divide_pos_le in H3; try lia. }
  assert (n | n). { exists 1. ring. }
  pose proof (H2 n (conj H H5)). lia.
Qed.


(* How to calculate brute_force *)

Definition value_of_highest i n :=
  match Z_le_dec 1 n with
  | left _ => match prime_divisor_list i n with
             | nil => 1
             | (x, p) :: _ => x
             end
  | _ => 1
  end.

Theorem value_of_highest_thm0 i n (H: 1 <= n) (H0: 1 <= i): 1 <= value_of_highest i n.
Proof.
  assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros.
  assert (x = 1 \/ 1 <= x - 1) by lia. destruct H3.
  + subst. unfold value_of_highest. rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. simpl. lia.
  + unfold value_of_highest in *. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
    destruct Zdivide_dec; try lia. apply H0; try lia.
Qed.

Theorem value_of_highest_thm1 i n (H: 1 <= n) (H0: 1 <= i): value_of_highest i n <= i.
Proof.
  assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros.
  assert (x = 1 \/ 1 <= x - 1) by lia. destruct H3.
  + subst. unfold value_of_highest. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
  + unfold value_of_highest in *. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
    destruct Zdivide_dec; try lia. pose proof (H0 (x - 1) ltac:(lia) ltac:(lia)). lia.
Qed.

Theorem value_of_highest_thm2 i n (H: 1 <= n) (H0: 1 <= i):
  max_of_list 1 (filter prime_dec (filter (fun x => Zdivide_dec x n) (Zseq i))) = value_of_highest i n.
Proof.
  unfold value_of_highest. assert (0 <= i) by lia. destruct Z_le_dec; try lia. revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H1 i.
  assert (x = 1 \/ 1 <= x - 1) by lia. destruct H1.
  + subst. simpl. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
    - simpl. auto.
    - simpl. auto.
  + assert (0 <= x - 1 < x) by lia. pose proof (H0 _ H3 H1). rewrite Zseq_equation. repeat (destruct Z_le_dec; try lia).
    rewrite filter_app. rewrite filter_app. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
    simpl. destruct (Zdivide_dec x n).
    - simpl. destruct prime_dec.
      * simpl. destruct Zdivide_dec.
        ++ apply max_In_thm0; try lia. intros. apply filter_In in H5. destruct H5. apply filter_In in H5.
           destruct H5. apply Zseq_thm in H5. lia.
        ++ exfalso. apply n2; clear n2. replace x with ((x - 1) + 1) at 1 by ring.
           rewrite repeated_repeated_div_main_thm; try lia. ring_simplify (x - 1 + 1). auto.
      * simpl. destruct Zdivide_dec.
        ++ exfalso. apply n2; clear n2. replace x with (x - 1 + 1) in d0 at 1 by ring.
           rewrite repeated_repeated_div_main_thm in d0; try lia. ring_simplify (x - 1 + 1) in d0. tauto.
        ++ rewrite app_nil_r. auto.
    - simpl. rewrite app_nil_r. rewrite H4. destruct Zdivide_dec.
      * replace x with (x - 1 + 1) in d at 1 by ring. apply repeated_repeated_div_main_thm in d; try lia.
        ring_simplify (x - 1 + 1) in d. tauto.
      * auto.
Qed.

Theorem value_of_highest_thm3 (n f: Z) (H: 1 <= n) (H0: 2 <= f): (~ prime f) -> value_of_highest f n = value_of_highest (f - 1) n.
Proof.
  intros. unfold value_of_highest. destruct Z_le_dec; try lia. rewrite (prime_divisor_list_equation f).
  destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. destruct Zdivide_dec.
  + exfalso. apply repeated_repeated_div_thm7 in d; try lia; auto.
  + auto.
Qed.

Theorem brute_force_replacement n (H: 1 <= n):
  brute_force n = value_of_highest n n.
Proof.
  apply value_of_highest_thm2; auto.
Qed.

Theorem brute_force_thm2 n (H: 1 <= n): 1 <= brute_force n <= n.
Proof.
  rewrite brute_force_replacement; try lia. split.
  + apply value_of_highest_thm0; try lia.
  + apply value_of_highest_thm1; try lia.
Qed.

Theorem brute_force_thm3 f n (H: 2 <= n) (H0: 2 <= f): 1 < brute_force (repeated_repeated_div f n) -> f + 1 <= brute_force (repeated_repeated_div f n).
Proof.
  assert (forall x, 1 <= x -> Z.divide (brute_force x) x).
  { intros. assert (x = 1 \/ 2 <= x) by lia. destruct H2.
    + subst. assert (brute_force 1 = 1).
      { rewrite brute_force_replacement; try lia. reflexivity. }
      exists 1. lia.
    + pose proof (brute_force_main_thm x H2). destruct H3. tauto. }
  intros. pose proof (repeated_repeated_div_thm0 f n ltac:(lia)). pose proof (H1 _ H3).
  apply repeated_repeated_div_thm10 in H4; try lia.
Qed.

Theorem brute_force_thm4 n: 2 <= n -> 1 < brute_force n.
Proof.
  intros. pose proof (brute_force_main_thm n H). destruct H0. destruct H0. destruct H0. auto.
Qed.

Theorem brute_force_thm5 (n: Z) (H: 2 <= n): prime (brute_force n).
Proof.
  pose proof (brute_force_main_thm _ H). destruct H0. tauto.
Qed.

Theorem brute_force_thm6 (n: Z) (H: 2 <= n): (brute_force n | n).
Proof.
  pose proof (brute_force_main_thm _ H). destruct H0. tauto.
Qed.

Theorem brute_force_thm7 (n: Z) (H: 2 <= n): brute_force (snd (repeated_div (brute_force n) n)) < brute_force n.
Proof.
  pose proof (brute_force_main_thm n H). pose proof (brute_force_thm0 n ltac:(lia)). 
  pose proof (repeated_div_thm1 (brute_force n) n ltac:(lia)). destruct H0.
  assert (snd (repeated_div (brute_force n) n) = 1 \/ 2 <= snd (repeated_div (brute_force n) n)) by lia.
  destruct H4.
  + rewrite H4. assert (brute_force 1 = 1). { compute. auto. } rewrite H5. apply brute_force_thm4; auto.
  + apply H3.
    - split.
      * apply brute_force_thm5. auto.
      * pose proof (brute_force_thm6 _ H4). destruct H0. destruct H0.
        pose proof (repeated_div_thm3 (brute_force n) n ltac:(lia) ltac:(lia)).
        exact (Z.divide_trans _ _ _ H5 H8).
    - intro. pose proof (brute_force_thm6 _ H4). rewrite <- H5 in H6. apply repeated_div_thm2 in H6; try lia.
      pose proof (brute_force_thm4 _ H). lia.
Qed.

Theorem aux7 (n m: Z) (H: n < m): prime n -> prime m -> rel_prime n m.
Proof.
  intros. apply prime_alt in H0, H1. destruct H0, H1. split.
  + exists n. ring.
  + exists m. ring.
  + intros. assert (x < -1 \/ x = - 1 \/ x = 0 \/ x = 1 \/ 1 < x) by lia.
    destruct H6 as [H6|[H6|[H6|[H6|H6]]]].
    - assert ((-x) | n). { destruct H4. exists (-x0). rewrite H4. ring. }
      assert ((-x) | m). { destruct H5. exists (-x0). rewrite H5. ring. }
      assert (0 < n) by lia. pose proof (Z.divide_pos_le _ _ H9 H7).
      assert (1 < -x < m) by lia. apply H3 in H11. tauto.
    - subst. exists (-1). ring.
    - subst. destruct H5. lia.
    - subst. exists 1. ring.
    - assert (0 < n) by lia. pose proof (Z.divide_pos_le _ _ H7 H4).
      assert (1 < x < m) by lia. apply H3 in H9. tauto.
Qed.

Theorem aux8 (n m: Z) (H: n <> m): prime n -> prime m -> rel_prime n m.
Proof.
  intros. assert (n < m \/ m < n) by lia. destruct H2.
  + apply aux7; auto.
  + apply rel_prime_sym. apply aux7; auto.
Qed.

Definition two_highest_prime_divisors (n p q: Z) :=
  let P x := prime x /\ Z.divide x n in
  (P p /\ P q /\ p < q /\ forall k, P k -> p <> k -> q <> k -> k < p).

Theorem two_highest_prime_divisors_thm (n m: Z) (H: 2 <= n) (H0: 2 <= snd (repeated_div (brute_force n) n)):
  two_highest_prime_divisors n (brute_force (snd (repeated_div (brute_force n) n))) (brute_force n).
Proof.
  unfold two_highest_prime_divisors. split; [split | split; [split | split]]; intros.
  + apply brute_force_thm5. auto.
  + pose proof (brute_force_thm6 _ H0).
    assert (1 <= brute_force n). { apply brute_force_thm2. lia. }
    assert (brute_force n = 1 \/ 2 <= brute_force n) by lia. destruct H3.
    - rewrite H3. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia). simpl.
      rewrite H3. exists n. ring.
    - pose proof (repeated_div_thm3 (brute_force n) n H3 ltac:(lia)).
      exact (Z.divide_trans _ _ _ H1 H4).
  + apply brute_force_thm5. auto.
  + apply brute_force_thm6. auto.
  + apply brute_force_thm7. auto.
  + pose proof (brute_force_main_thm _ H0). pose proof (brute_force_main_thm _ H).
    destruct H5. destruct H5. destruct H4. destruct H4.
    apply H8; auto. split; try tauto. destruct H1. pose proof (aux8 _ _ H3 H5 H1).
    apply repeated_div_thm5; try lia; auto.
    - destruct H1. lia.
    - destruct H5. lia.
    - apply rel_prime_sym. auto.
Qed.

Theorem aux9 (n m: Z) (Hn: 2 <= n) (Hm: 2 <= m): rel_prime n m -> ~ (n | m).
Proof.
  intros. intro. destruct H0. assert (0 < x) by lia. unfold rel_prime in H. subst.
  apply Zis_gcd_gcd in H; try lia. rewrite Z.mul_comm, Z.gcd_mul_diag_l in H; lia.
Qed.

Theorem brute_force_thm8 (p: Z) (Hp: prime p): brute_force p = p.
Proof.
  pose proof (brute_force_main_thm p ltac:(destruct Hp; lia)).
  destruct H. destruct H. apply prime_div_prime in H1; auto.
Qed.

Theorem brute_force_thm9 (n i: Z) (Hn: prime n) (Hi: 1 <= i): brute_force (n ^ i) = n.
Proof.
  assert (2 <= n ^ i).
  { destruct Hn. clear H0. pose proof (Zpow_facts.Zpower_gt_1 n i H). lia. }
  pose proof (brute_force_main_thm (n ^ i) H).
  unfold biggest_prime_divisor in H0. destruct H0. destruct H0. clear H1.
  apply Zpow_facts.prime_power_prime in H2; try lia; auto.
Qed.

Theorem brute_force_thm10 (p q: Z) (Hp: prime p) (Hq: prime q): brute_force (p * q) = Z.max p q.
Proof.
  intros. assert (2 <= p * q). { destruct Hp, Hq. lia. }
  pose proof (brute_force_main_thm _ H). destruct H0, H0.
  apply prime_mult in H2; auto. destruct H2.
  + apply prime_div_prime in H2; auto. rewrite H2 in H1.
    pose proof (H1 q (conj Hq ltac:(apply Z.divide_factor_r))). lia.
  + apply prime_div_prime in H2; auto. rewrite H2 in H1.
    pose proof (H1 p (conj Hp ltac:(apply Z.divide_factor_l))). lia.
Qed.


Theorem value_of_highest_thm4 i n m (Hn: 1 <= n) (Hm: 1 <= m) (H0: 1 <= i):
  max_of_list 1 (filter prime_dec (filter (fun x => Zdivide_dec x (m * n)) (Zseq i))) =
  Z.max (value_of_highest i n) (value_of_highest i m).
Proof.
  unfold value_of_highest. assert (0 <= i) by lia. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
  revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H i.
  assert (x = 1 \/ 1 <= x - 1) by lia. destruct H.
  + subst. clear H0. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
    rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
    simpl. destruct Zdivide_dec.
    - simpl. auto.
    - elim n0. exists (m * n). lia.
  + assert (0 <= x - 1 < x) by lia. pose proof (H0 _ H2 H). clear H0. rewrite Zseq_equation. destruct Z_le_dec; try lia.
    rewrite filter_app, filter_app. rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
    rewrite (prime_divisor_list_equation x m). repeat (destruct Z_le_dec; try lia).
    repeat destruct Zdivide_dec.
    - simpl. destruct Zdivide_dec.
      * simpl. destruct prime_dec.
        ++ simpl. rewrite max_In_thm0; try lia. intros. apply filter_In in H0. destruct H0.
           apply filter_In in H0. destruct H0. apply Zseq_thm in H0. lia.
        ++ simpl. rewrite app_nil_r. apply (repeated_repeated_div_thm7) with (n:=n) in n3; try lia. tauto.
      * simpl. rewrite app_nil_r. exfalso. apply repeated_repeated_div_thm4 in d; try lia.
        apply n3. apply Z.divide_mul_r; auto.
    - simpl. destruct Zdivide_dec.
      * simpl. destruct prime_dec.
        ++ simpl. rewrite max_In_thm0; try lia.
           -- assert (value_of_highest (x - 1) m <= x - 1).
              { apply value_of_highest_thm1; try lia. }
              unfold value_of_highest in H0. destruct Z_le_dec; try lia.
           -- intros. apply filter_In in H0. destruct H0. apply filter_In in H0. destruct H0. apply Zseq_thm in H0. lia.
        ++ exfalso. apply n4. replace x with ((x - 1) + 1) in d at 1 by ring.
           apply repeated_repeated_div_main_thm in d; try lia. ring_simplify (x - 1 + 1) in d. tauto.
      * exfalso. apply n4. apply Z.divide_mul_r. eapply repeated_repeated_div_thm4; try lia. exact H. auto.
    - simpl. destruct Zdivide_dec.
      * simpl. destruct prime_dec.
        ++ simpl. rewrite max_In_thm0; try lia.
           -- assert (value_of_highest (x - 1) n <= x - 1).
              { apply value_of_highest_thm1; try lia. }
              unfold value_of_highest in H0. destruct Z_le_dec; try lia.
           -- intros. apply filter_In in H0. destruct H0. apply filter_In in H0. destruct H0. apply Zseq_thm in H0. lia.
        ++ exfalso. apply n4. replace x with (x - 1 + 1) in d at 1 by ring.
           apply repeated_repeated_div_main_thm in d; try lia. ring_simplify (x - 1 + 1) in d. tauto.
      * exfalso. apply n4. apply Z.divide_mul_l. eapply repeated_repeated_div_thm4; try lia. exact H. auto.
    - simpl. destruct Zdivide_dec.
      * simpl. destruct prime_dec.
        ++ simpl. rewrite max_In_thm0; try lia.
           -- apply prime_mult in d; auto. destruct d.
              ** exfalso. replace x with (x - 1 + 1) in p by ring. replace x with (x - 1 + 1) in H0 by ring.
                 pose proof (conj p H0). apply repeated_repeated_div_main_thm in H4; try lia.
                 ring_simplify (x - 1 + 1) in H4. tauto.
              ** exfalso. replace x with (x - 1 + 1) in p by ring. replace x with (x - 1 + 1) in H0 by ring.
                 pose proof (conj p H0). apply repeated_repeated_div_main_thm in H4; try lia.
                 ring_simplify (x - 1 + 1) in H4. tauto.
           -- intros. apply filter_In in H0. destruct H0. apply filter_In in H0. destruct H0. apply Zseq_thm in H0. lia.
        ++ simpl. rewrite app_nil_r. auto.
      * simpl. rewrite app_nil_r. auto.
Qed.

Theorem repeated_repeated_div_thm21 n (H: 1 <= n): repeated_repeated_div n 1 = 1.
Proof.
  assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction; auto; intros. clear n H0.
  rewrite repeated_repeated_div_equation. repeat (destruct Z_le_dec; try lia).
  rewrite H; try lia. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
  destruct Zdivide_dec.
  + destruct d. assert (1 <= x0) by nia. nia.
  + simpl. auto.
Qed.

Theorem prime_divisor_list_thm0 k n (Hk: 0 <= k) (Hn: 0 <= n): prime_divisor_list (n + k) n = prime_divisor_list n n.
Proof.
  assert (0 <= k) by lia. revert H n Hn. pattern k. apply Z_lt_induction; auto; intros. clear k Hk.
  assert (x = 0 \/ 1 <= x) by lia. destruct H1.
  + subst. f_equal. lia.
  + assert (0 <= x - 1 < x) by lia. assert (0 <= x - 1) by lia. pose proof (H _ H2 H3). clear H H2 H3 H0.
    replace (n + x) with (n + (x - 1) + 1) by lia. rewrite prime_divisor_list_equation.
    repeat (destruct Z_le_dec; try lia).
    - destruct Zdivide_dec.
      * ring_simplify (n + (x - 1) + 1) in d. ring_simplify (n + (x - 1) + 1).
        exfalso. assert (repeated_repeated_div (n + x - 1) n | n).
        { assert (n = 1 \/ 2 <= n) by lia. destruct H.
          + subst. ring_simplify (1 + x - 1). rewrite repeated_repeated_div_thm21; try lia. exists 1. ring.
          + apply repeated_repeated_div_thm20; try lia. }
        assert (n + x | n). { eapply Z.divide_trans; eauto. }
        destruct H0. assert (1 <= x0) by nia. nia.
      * ring_simplify (n + (x - 1) + 1 - 1). rewrite <- H4; try lia. f_equal. ring.
    - assert (n = 0) by lia. subst. compute. auto.
Qed.

Theorem brute_force_thm11 (n m: Z) (Hn: 1 <= n) (Hm: 1 <= m):
  brute_force (n * m) = Z.max (brute_force n) (brute_force m).
Proof.
  rewrite (brute_force_replacement n); try nia. rewrite (brute_force_replacement m); try nia.
  unfold brute_force. unfold all_prime_divisors. rewrite value_of_highest_thm4; try nia.
  repeat unfold value_of_highest. repeat (destruct Z_le_dec; try nia).
  assert (prime_divisor_list n n = prime_divisor_list (n * m) n).
  { replace (n * m) with (n + (n * m - n)) by ring. rewrite prime_divisor_list_thm0; try nia. auto. }
  assert (prime_divisor_list m m = prime_divisor_list (n * m) m).
  { replace (n * m) with (m + (n * m - m)) by ring. rewrite prime_divisor_list_thm0; try nia. auto. }
  rewrite H, H0. lia.
Qed.

Theorem brute_force_thm12 (n i: Z) (Hn: 1 <= n) (Hi: 2 <= i):
  2 <= brute_force (repeated_repeated_div i n) -> brute_force (repeated_repeated_div i n) = brute_force n.
Proof.
Admitted.


(* Finding out possible loop invariants *)

Inductive state N (H: 2 <= N): Z -> Z -> nat -> Prop :=
 | Start: state N H (value_of_highest 3 N) (repeated_repeated_div 3 N) 0
 | Loop: forall h n i, (6 * Z.of_nat i + 5) * (6 * Z.of_nat i + 5) <= n ->
         state N H h n i ->
         state N H (value_of_highest (6 * Z.of_nat i + 9) N) (snd (repeated_div (6 * Z.of_nat i + 7) (snd (repeated_div (6 * Z.of_nat i + 5) n)))) (i + 1).

Definition is_loop_invariant (T: Z -> Z -> Prop) :=
  forall N H n i h (s: state N H h n i), T n (Z.of_nat i).

Definition loop_invariant_candidate n i :=
  if Z.eq_dec n 1
  then True
  else if Z_le_dec ((6 * i + 5) * (6 * i + 5)) n
       then True
       else n = repeated_repeated_div (6 * i + 4) n /\
         let W := brute_force n in
         ~ Z.divide (W * W) n /\ (~ prime (W - 2) \/ ~ Z.divide (W - 2) n).

Theorem state_thm0 N H h n i: state N H h n i -> n = repeated_repeated_div (6 * Z.of_nat i + 4) N.
Proof.
  intros. induction H0.
  + simpl. rewrite (repeated_repeated_div_thm8 4 N); try lia.
    - reflexivity.
    - intro. apply prime_alt in H0. destruct H0. pose proof (H1 2 ltac:(lia)). apply H2. exists 2. ring.
  + rewrite Nat2Z.inj_add. simpl. remember (Z.of_nat i) as X. ring_simplify (6 * (X + 1) + 4).
    rewrite IHstate. rewrite (repeated_repeated_div_thm8 (6 * X + 10) N); try lia.
    - ring_simplify (6 * X + 10 - 1). rewrite (repeated_repeated_div_thm8 (6 * X + 9)); try lia.
      ++ ring_simplify (6 * X + 9 - 1). rewrite (repeated_repeated_div_thm8 (6 * X + 8)); try lia.
         -- ring_simplify (6 * X + 8 - 1). rewrite (repeated_repeated_div_equation (6 * X + 7)).
            destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. do 2 f_equal. ring_simplify (6 * X + 7 - 1).
            rewrite (repeated_repeated_div_thm8 (6 * X + 6)); try lia.
            ** ring_simplify (6 * X + 6 - 1). rewrite (repeated_repeated_div_equation (6 * X + 5)).
               destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. do 2 f_equal.
               ring_simplify (6 * X + 5 - 1). auto.
            ** intro. apply prime_alt in H2. destruct H2. pose proof (H3 2 ltac:(lia)). apply H4. exists (3 * X + 3). ring.
         -- intro. apply prime_alt in H2. destruct H2. pose proof (H3 2 ltac:(lia)). apply H4. exists (3 * X + 4). ring.
      ++ intro. apply prime_alt in H2. destruct H2. pose proof (H3 3 ltac:(lia)). apply H4. exists (2 * X + 3). ring.
    - intro. apply prime_alt in H2. destruct H2. pose proof (H3 2 ltac:(lia)). apply H4. exists (3 * X + 5). ring.
Qed.

Theorem state_thm1 N H h n i: state N H h n i -> h = value_of_highest (6 * Z.of_nat i + 3) N.
Proof.
  intro. induction H0.
  + simpl. auto.
  + rewrite Nat2Z.inj_add. simpl. ring_simplify (6 * (Z.of_nat i + 1) + 3). auto.
Qed.

Theorem correct_loop_invariant: is_loop_invariant loop_invariant_candidate.
Proof.
  unfold is_loop_invariant, loop_invariant_candidate. intros.
  induction s.
  + destruct Z.eq_dec; auto. destruct Z_le_dec; auto. simpl in *.
    assert (repeated_repeated_div 3 N < 25) by lia. clear n0. assert (1 <= N) as H' by lia.
    pose proof (repeated_repeated_div_thm0 3 N H').
    remember (repeated_repeated_div 3 N) as W.
    assert (In W [2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24]).
    { simpl. lia. }
    split.
    - subst. rewrite (repeated_repeated_div_thm8 4); try lia.
      * simpl. symmetry. apply repeated_repeated_div_thm14; try lia.
      * intro. apply prime_alt in H3. destruct H3. pose proof (H4 2 ltac:(lia)). apply H5. exists 2. ring.
    - destruct H2 as [H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|H2]]]]]]]]]]]]]]]]]]]]]]].
      * rewrite <- H2. assert (brute_force 2 = 2).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ left. apply not_prime_0.
      * rewrite <- H2 in *. assert (brute_force 3 = 3).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ left. apply not_prime_1.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 2. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 5 = 5).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 3. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 7 = 7).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 4. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * exfalso. assert (Z.divide 3 (repeated_repeated_div 3 N)).
        { exists 3. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 5. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 11 = 11).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 6. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 13 = 13).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 7. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * exfalso. assert (Z.divide 3 (repeated_repeated_div 3 N)).
        { exists 5. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 8. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 17 = 17).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 9. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 19 = 19).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 10. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * exfalso. assert (Z.divide 3 (repeated_repeated_div 3 N)).
        { exists 7. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 11. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * rewrite <- H2 in *. assert (brute_force 23 = 23).
        { rewrite brute_force_replacement. compute. auto. lia. }
        rewrite H3. simpl. split.
        ++ intro. destruct H4. lia.
        ++ right. intro. destruct H4. lia.
      * exfalso. assert (Z.divide 2 (repeated_repeated_div 3 N)).
        { exists 12. lia. }
        apply repeated_repeated_div_thm3 in H3; auto; try lia.
      * elim H2.
  + rewrite Nat2Z.inj_add. simpl. remember (Z.of_nat i) as X. destruct Z.eq_dec.
    - lia.
    - destruct Z_le_dec; try tauto. clear l IHs. destruct Z.eq_dec; auto. destruct Z_le_dec; auto. repeat split.
      * remember (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) n)))) as W.
        ring_simplify (6 * (X + 1) + 4). pose proof (state_thm0 _ _ _ _ _ s). rewrite H1 in HeqW.
        rewrite <- HeqX in HeqW. assert (W = repeated_repeated_div (6 * X + 7) n).
        { rewrite HeqW. rewrite (repeated_repeated_div_equation (6 * X + 7)). repeat (destruct Z_le_dec; try lia).
          do 2 f_equal. ring_simplify (6 * X + 7 - 1). rewrite (repeated_repeated_div_thm8 (6 * X + 6)); try lia.
          + ring_simplify (6 * X + 6 - 1). rewrite (repeated_repeated_div_equation (6 * X + 5)).
            repeat (destruct Z_le_dec; try lia). ring_simplify (6 * X + 5 - 1). do 2 f_equal.
            rewrite H1. rewrite repeated_repeated_div_thm14; try lia. congruence.
          + intro. apply prime_alt in H2. destruct H2. pose proof (H3 2 ltac:(lia)). apply H4.
            exists (3 * X + 3). ring. }
        rewrite H2. assert (1 <= n) by lia. rewrite (repeated_repeated_div_thm8 (6 * X + 10)); try lia.
        ++ ring_simplify (6 * X + 10 - 1). rewrite (repeated_repeated_div_thm8 (6 * X + 9)); try lia.
           -- ring_simplify (6 * X + 9 - 1). rewrite (repeated_repeated_div_thm8 (6 * X + 8)); try lia.
              ** ring_simplify (6 * X + 8 - 1). symmetry. apply repeated_repeated_div_thm14; try lia.
              ** apply repeated_repeated_div_thm0. auto.
              ** intro. apply prime_alt in H4. destruct H4. pose proof (H5 2 ltac:(lia)). apply H6.
                 exists (3 * X + 4). ring.
           -- apply repeated_repeated_div_thm0; auto.
           -- intro. apply prime_alt in H4. destruct H4. pose proof (H5 3 ltac:(lia)). apply H6.
              exists (2 * X + 3). ring.
        ++ apply repeated_repeated_div_thm0; auto.
        ++ intro. apply prime_alt in H4. destruct H4. pose proof (H5 2 ltac:(lia)). apply H6. exists (3 * X + 5). ring.
      * pose proof (state_thm0 _ _ _ _ _ s). rewrite <- HeqX in H1.
        intro. remember (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) n)))) as W.
        assert (W < (6 * X + 11) * (6 * X + 11)) by lia. clear n2. assert (1 <= n) by lia.
        assert (W = repeated_repeated_div (6 * X + 10) n).
        { rewrite repeated_repeated_div_thm8; try lia.
          + ring_simplify (6 * X + 10 - 1). rewrite repeated_repeated_div_thm8; try lia.
            - ring_simplify (6 * X + 9 - 1). rewrite repeated_repeated_div_thm8; try lia.
              * ring_simplify (6 * X + 8 - 1). rewrite repeated_repeated_div_equation.
                repeat (destruct Z_le_dec; try lia). rewrite HeqW. do 2 f_equal. ring_simplify (6 * X + 7 - 1).
                rewrite repeated_repeated_div_thm8; try lia.
                ++ ring_simplify (6 * X + 6 - 1). rewrite repeated_repeated_div_equation.
                   repeat (destruct Z_le_dec; try lia). ring_simplify (6 * X + 5 - 1).
                   rewrite H1. rewrite repeated_repeated_div_thm14; try lia.
                ++ intro. apply prime_alt in H5. destruct H5. pose proof (H6 2 ltac:(lia)). apply H7. exists (3 * X + 3). ring.
              * intro. apply prime_alt in H5. destruct H5. pose proof (H6 2 ltac:(lia)). apply H7. exists (3 * X + 4). ring.
            - intro. apply prime_alt in H5. destruct H5. pose proof (H6 3 ltac:(lia)). apply H7. exists (2 * X + 3). ring.
          + intro. apply prime_alt in H5. destruct H5. pose proof (H6 2 ltac:(lia)). apply H7. exists (3 * X + 5). ring. } 
        assert (6 * X + 11 <= brute_force W).
        { rewrite H5. replace (6 * X + 11) with (6 * X + 10 + 1) by ring. apply brute_force_thm3; try lia.
          apply brute_force_thm4. pose proof (repeated_repeated_div_thm0 (6 * X + 10) n H4). lia. }
        apply Z.divide_pos_le in H2.
        ++ nia.
        ++ pose proof (proj1 (repeated_div_thm1 (6 * X + 5) n H4)).
           pose proof (proj1 (repeated_div_thm1 (6 * X + 7) _ H7)). lia.
      * remember (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) n)))) as W.
        assert (W < (6 * (X + 1) + 5) * (6 * (X + 1) + 5)) by lia. clear n2.
        pose proof (state_thm0 _ _ _ _ _ s). ring_simplify (6 * (X + 1) + 5) in H1. rewrite <- HeqX in H2.
        assert (W = repeated_repeated_div (6 * X + 10) n).
        { rewrite repeated_repeated_div_thm8; try lia.
          + ring_simplify (6 * X + 10 - 1). rewrite repeated_repeated_div_thm8; try lia.
            - ring_simplify (6 * X + 9 - 1). rewrite repeated_repeated_div_thm8; try lia.
              * ring_simplify (6 * X + 8 - 1). rewrite repeated_repeated_div_equation.
                repeat (destruct Z_le_dec; try lia). rewrite HeqW. do 2 f_equal. ring_simplify (6 * X + 7 - 1).
                rewrite repeated_repeated_div_thm8; try lia.
                ++ ring_simplify (6 * X + 6 - 1). rewrite repeated_repeated_div_equation.
                   repeat (destruct Z_le_dec; try lia). ring_simplify (6 * X + 5 - 1).
                   rewrite H2. rewrite repeated_repeated_div_thm14; try lia.
                ++ intro. apply prime_alt in H3. destruct H3. pose proof (H4 2 ltac:(lia)). apply H5. exists (3 * X + 3). ring.
              * intro. apply prime_alt in H3. destruct H3. pose proof (H4 2 ltac:(lia)). apply H5. exists (3 * X + 4). ring.
            - intro. apply prime_alt in H3. destruct H3. pose proof (H4 3 ltac:(lia)). apply H5. exists (2 * X + 3). ring.
          + intro. apply prime_alt in H3. destruct H3. pose proof (H4 2 ltac:(lia)). apply H5. exists (3 * X + 5). ring. }
        assert (6 * X + 11 <= brute_force W).
        { rewrite H3. replace (6 * X + 11) with (6 * X + 10 + 1) by ring. apply brute_force_thm3; try lia. apply brute_force_thm4.
          pose proof (repeated_repeated_div_thm0 (6 * X + 10) n ltac:(lia)). lia. }
        destruct (prime_dec (brute_force W - 2)); try tauto.
        destruct (Zdivide_dec (brute_force W - 2) W); try tauto.
        exfalso. assert (2 <= W).
        { rewrite H3. pose proof (repeated_repeated_div_thm0 (6 * X + 10) n). lia. }
        assert (prime (brute_force W)).
        { pose proof (brute_force_main_thm _ H5). destruct H6. destruct H6. auto. }
        assert (brute_force W = 6 * X + 11 \/ brute_force W = 6 * X + 12 \/ 6 * X + 13 <= brute_force W) by lia.
        destruct H7 as [H7 |[H7 | H7]].
        ++ rewrite H7 in p. ring_simplify (6 * X + 11 - 2) in p. apply prime_alt in p. destruct p.
           pose proof (H9 3 ltac:(lia)). apply H10. exists (2 * X + 3). ring.
        ++ rewrite H7 in H6. apply prime_alt in H6. destruct H6. pose proof (H8 2 ltac:(lia)).
           apply H9. exists (3 * X + 6). ring.
        ++ assert (rel_prime (brute_force W) (brute_force W - 2)).
           { replace (brute_force W - 2) with (brute_force W * 1 + (-2)) by ring.
             apply Zis_gcd_for_euclid2. apply Zis_gcd_minus. simpl. split.
             + exists (brute_force W). ring.
             + exists 2. ring.
             + intros. apply prime_alt in H6. destruct H6. pose proof (prime_divisors 2 prime_2 x H9).
               destruct H11 as [H11 |[H11 |[H11 | H11]]].
               - subst. exists (-1). ring.
               - subst. exists 1. ring.
               - exfalso. pose proof (H10 x ltac:(lia)). tauto.
               - exfalso. pose proof (H10 (-x) ltac:(lia)). apply H12. destruct H8. exists (-x0). rewrite H8. ring. }
           assert (Z.divide (brute_force W) W).
           { pose proof (brute_force_main_thm _ H5). destruct H9. destruct H9. auto. }
           pose proof (aux1 W _ _ H8 H9 d ltac:(lia) ltac:(lia)). apply Z.divide_pos_le in H10; try lia.
           nia.
Qed.


Theorem repeated_repeated_div_thm22 (n i: Z) (Hn: 1 <= n) (Hi: 2 <= i):
  repeated_repeated_div i n = 1 -> brute_force n <= i.
Proof.
  intros.
Admitted.

Theorem repeated_repeated_div_thm23 (n i: Z) (Hn: 1 <= n) (Hi: 2 <= i):
  2 <= repeated_repeated_div i n -> i + 1 <= brute_force n.
Proof.
  intros.
Admitted.


Definition type1 (N: Z): Prop :=
  let W := repeated_repeated_div 3 N in
  W = 1 \/ Z.divide (brute_force W * brute_force W) W \/ (prime (brute_force W - 2) /\ Z.divide (brute_force W - 2) W).

Theorem TTT N H h n i (H': 2 <= N):
  forall (s: state N H h n i), n < (6 * Z.of_nat i + 5) * (6 * Z.of_nat i + 5) ->
  (type1 N <-> h = brute_force N /\ n = 1) /\
  (~ type1 N <-> h = brute_force (snd (repeated_div (brute_force N) N)) /\ n = brute_force N).
Proof.
  intros. unfold type1. pose proof (state_thm0 _ _ _ _ _ s). induction s.
  + remember (repeated_repeated_div 3 N) as W. simpl in *. assert (1 <= W).
    { rewrite HeqW. apply repeated_repeated_div_thm0; lia. }
    destruct (prime_dec W).
    - pose proof (brute_force_thm1 _ p). rewrite H3. repeat split; intros.
      * destruct H4 as [H4|[H4|[H4 H5]]].
        ++ rewrite H4 in p. pose proof not_prime_1. tauto.
        ++ destruct H4. destruct p. assert (0 < x) by lia. nia.
        ++ assert (4 <= W). { destruct H4. lia. }
           assert (W = 4 \/ 5 <= W) by lia.
           destruct H7.
           -- apply prime_alt in p. destruct p. pose proof (H9 2 ltac:(lia)). exfalso. apply H10. exists 2. lia.
           -- destruct H5. assert (0 < x) by nia. nia.
      * destruct H4 as [H4|[H4|[H4 H5]]]; try lia.
        ++ assert (2 <= W). { destruct p. lia. } destruct H4. assert (0 < x) by lia. nia.
        ++ assert (4 <= W). { destruct H4. lia. }
           assert (W = 4 \/ 5 <= W) by lia.
           destruct H7 as [H7|H7].
           -- apply prime_alt in p. destruct p. pose proof (H9 2 ltac:(lia)). elim H10. exists 2. lia.
           -- destruct H5. assert (0 < x) by nia. nia.
      * lia.
      * assert (W <> 1 /\ ~ Z.divide (W * W) W /\ (~ prime (W - 2) \/ ~ Z.divide (W - 2) W)) by tauto. clear H4.
        destruct H5 as [H5 [H6 H7]].
        assert (N = W * 3 ^ (fst (repeated_div 3 N)) * 2 ^ (fst (repeated_div 2 N))).
        { clear H5 H6 H3 H2 H1. rewrite HeqW. rewrite repeated_repeated_div_equation.
          destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
          rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
          simpl. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
          assert (fst (repeated_div 3 N) = fst (repeated_div 3 (snd (repeated_div 2 N)))).
          { rewrite repeated_div_thm9; try lia. unfold rel_prime. pose proof (Zgcd_is_gcd 3 2). compute in H1. auto. }
          rewrite H1. rewrite (Z.mul_comm (snd _)). rewrite <- repeated_div_main_thm; try lia.
          + rewrite Z.mul_comm. rewrite <- repeated_div_main_thm; try lia.
          + apply repeated_div_thm1; try lia. }
        clear H5 H6 H7 H3 H2 H1. assert (W > 3).
        { apply repeated_repeated_div_thm10 with (n := N); try lia.
          + destruct p. auto.
          + exists 1. lia. }
        pose proof (repeated_div_thm0 3 N). pose proof (repeated_div_thm0 2 N).
        assert (fst (repeated_div 2 N) = 0 \/ 1 <= fst (repeated_div 2 N)) by lia. destruct H5.
        ++ rewrite H5 in *. simpl in H4. ring_simplify (W * 3 ^ fst (repeated_div 3 N) * 1) in H4.
           assert (fst (repeated_div 3 N) = 0 \/ 1 <= fst (repeated_div 3 N)) by lia. destruct H6.
           -- rewrite H6 in *. ring_simplify (W * 3 ^ 0) in H4. rewrite H4.
              rewrite (brute_force_thm1 W); auto. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
              rewrite Z_div_same; try lia. destruct Zdivide_dec.
              ** rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
                 destruct Zdivide_dec.
                 +++ destruct d0. assert (0 < x) by lia. nia.
                 +++ simpl. assert (brute_force 1 = 1). { compute. auto. } rewrite H7.
                     rewrite <- value_of_highest_thm2; try lia. simpl.
                     destruct (Zdivide_dec 2); simpl.
                     --- rewrite HeqW in d0. apply repeated_repeated_div_thm3 in d0; try lia.
                     --- destruct (Zdivide_dec 3); simpl.
                         *** rewrite HeqW in d0. apply repeated_repeated_div_thm3 in d0; try lia.
                         *** destruct Zdivide_dec; simpl; auto.
              ** elim n. exists 1. ring.
           -- unfold value_of_highest. destruct Z_le_dec; try lia.
              rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
              destruct Zdivide_dec.
              ** assert (brute_force N = W).
                 { pose proof (brute_force_main_thm N H). destruct H7. destruct H7.
                   assert (forall k, prime k /\ (k | N) <-> (k = 3 \/ k = W)).
                   { split; intros.
                     + destruct H10. rewrite H4 in H11. apply prime_mult in H11; auto. destruct H11.
                       - apply prime_div_prime in H11; auto.
                       - pose proof prime_3. apply Zpow_facts.prime_power_prime in H11; auto.
                     + destruct H10.
                       - rewrite H10. split. apply prime_3. rewrite H4. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                       - rewrite H10. split; auto. rewrite H4. apply Z.divide_factor_l. }
                   pose proof (conj H7 H9). apply H10 in H11. destruct H11; auto.
                   setoid_rewrite H10 in H8. rewrite H11 in H8. pose proof (H8 W). lia. }
                 rewrite H7. rewrite repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 destruct Zdivide_dec.
                 +++ replace (snd (let (i, k) := repeated_div W (N / W) in (i + 1, k))) with (snd (repeated_div W (N / W))).
                     --- rewrite H4. rewrite Z.mul_comm. rewrite Z.div_mul; try lia.
                         rewrite repeated_div_equation at 1. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                         destruct Zdivide_dec.
                         *** apply Zpow_facts.prime_power_prime in d1; try lia; auto. apply prime_3.
                         *** simpl. rewrite brute_force_thm9; auto. apply prime_3.
                     --- destruct (repeated_div W (N / W)). simpl. auto.
                 +++ exfalso. apply n0. rewrite H4. apply Z.divide_factor_l.
              ** exfalso. elim n0. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
                 rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 pose proof (repeated_div_main_thm 2 N ltac:(lia) l). rewrite H5 in H7. simpl in *. ring_simplify in H7.
                 rewrite <- H7. rewrite H4. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
        ++ assert (fst (repeated_div 3 N) = 0 \/ 1 <= fst (repeated_div 3 N)) by lia. destruct H6.
           -- rewrite H6 in *. ring_simplify in H4. unfold value_of_highest. destruct Z_le_dec; try lia.
              rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
              destruct Zdivide_dec.
              ** exfalso. rewrite repeated_repeated_div_equation in d.
                 destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl in d.
                 rewrite repeated_repeated_div_equation in d.
                 destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 pose proof (repeated_div_main_thm 2 N ltac:(lia) l).
                 assert (W = snd (repeated_div 2 N)) by nia.
                 apply prime_alt in p. destruct p. assert (1 < 3 < W) by lia. rewrite <- H8 in d.
                 exact (H10 3 H11 d).
              ** rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 simpl. destruct Zdivide_dec.
                 +++ clear d. assert (brute_force N = W).
                     { pose proof (brute_force_main_thm N H). destruct H7. destruct H7.
                       assert (forall k, prime k /\ (k | N) <-> (k = 2 \/ k = W)).
                       { split; intros.
                         + destruct H10. rewrite H4 in H11. apply prime_mult in H11; auto. destruct H11.
                           - apply prime_div_prime in H11; auto.
                           - pose proof prime_2. apply Zpow_facts.prime_power_prime in H11; auto.
                         + destruct H10.
                           - rewrite H10 in *. split. apply prime_2. rewrite H4. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                           - rewrite H10. split; auto. rewrite H4. apply Z.divide_factor_l. }
                     pose proof (conj H7 H9). apply H10 in H11. destruct H11; auto.
                     setoid_rewrite H10 in H8. rewrite H11 in H8. pose proof (H8 W). lia. }
                     rewrite H7. rewrite repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                     destruct Zdivide_dec.
                     --- replace (snd (let (i, k) := repeated_div W (N / W) in (i + 1, k))) with (snd (repeated_div W (N / W))).
                         *** rewrite H4. rewrite Z.mul_comm. rewrite Z.div_mul; try lia. rewrite repeated_div_equation.
                             destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. destruct Zdivide_dec.
                             ++++ apply Zpow_facts.prime_power_prime in d0; try lia; auto. apply prime_2.
                             ++++ simpl. rewrite brute_force_thm9; auto. apply prime_2.
                         *** destruct (repeated_div W (N / W)). simpl. auto.
                     --- exfalso. apply n2. rewrite H4. apply Z.divide_factor_l.
                 +++ elim n2. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                     rewrite H4. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
           -- assert (brute_force N = W).
              { pose proof (brute_force_main_thm N H). destruct H7. destruct H7.
                assert (forall k, prime k /\ (k | N) <-> (k = 2 \/ k = 3 \/ k = W)).
                { split; intros.
                  + destruct H10. rewrite H4 in H11. apply prime_mult in H11; auto. destruct H11.
                    - apply prime_mult in H11; auto. destruct H11.
                      * apply prime_div_prime in H11; auto.
                      * pose proof prime_3. apply Zpow_facts.prime_power_prime in H11; auto.
                    - pose proof prime_2. apply Zpow_facts.prime_power_prime in H11; auto.
                  + destruct H10 as [H10 |[H10 | H10]].
                    - rewrite H10. split. apply prime_2. rewrite H4. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                    - rewrite H10. split. apply prime_3. rewrite H4. apply Z.divide_mul_l. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                    - rewrite H10. split; auto. rewrite H4. apply Z.divide_mul_l. apply Z.divide_factor_l. }
                pose proof (conj H7 H9). apply H10 in H11. assert (W | N).
                { rewrite H4. apply Z.divide_mul_l. apply Z.divide_factor_l. }
                pose proof (H8 W (conj p H12)). lia. }
              rewrite H7. rewrite repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
              destruct Zdivide_dec.
              ** replace (snd (let (i, k) := repeated_div W (N / W) in (i + 1, k))) with (snd (repeated_div W (N / W))).
                 +++ rewrite H4 at 2. replace (W * 3 ^ fst (repeated_div 3 N) * 2 ^ fst (repeated_div 2 N)) with
                       (3 ^ fst (repeated_div 3 N) * 2 ^ fst (repeated_div 2 N) * W) by lia.
                     rewrite Z.div_mul; try lia. rewrite repeated_div_equation. destruct Z_le_dec; try lia.
                     destruct Z_le_dec; try lia. destruct Zdivide_dec.
                     --- exfalso. apply prime_mult in d0; auto. destruct d0.
                         *** pose proof prime_3. apply Zpow_facts.prime_power_prime in H8; auto. lia.
                         *** pose proof prime_2. apply Zpow_facts.prime_power_prime in H8; auto. lia.
                     --- simpl. remember (3 ^ fst (repeated_div 3 N) * 2 ^ fst (repeated_div 2 N)) as X.
                         assert (2 <= X).
                         { replace (fst (repeated_div 2 N)) with (fst (repeated_div 2 N) - 1 + 1) in HeqX by lia.
                           rewrite Z.pow_add_r in HeqX; lia. }
                         pose proof (brute_force_main_thm _ H8). destruct H9. destruct H9.
                         assert (forall k, prime k /\ (k | X) <-> (k = 2 \/ k = 3)).
                         { split; intros.
                           + destruct H12. rewrite HeqX in H13. apply prime_mult in H13; auto. destruct H13.
                             - pose proof prime_3. apply Zpow_facts.prime_power_prime in H13; auto.
                             - pose proof prime_2. apply Zpow_facts.prime_power_prime in H13; auto.
                           + destruct H12.
                             - rewrite H12. split. apply prime_2. rewrite HeqX. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                             - rewrite H12. split. apply prime_3. rewrite HeqX. apply Z.divide_mul_l. apply Zpow_facts.Zpower_divide. lia. }
                         pose proof (conj H9 H11). rewrite H12 in H13. destruct H13.
                         *** exfalso. pose proof prime_3. assert (3 | X).
                             { rewrite HeqX. apply Z.divide_mul_l. apply Zpow_facts.Zpower_divide. lia. }
                             pose proof (conj H14 H15). apply H10 in H16; lia.
                         *** rewrite H13. unfold value_of_highest. destruct Z_le_dec; try lia.
                             rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                             simpl. destruct Zdivide_dec; auto. exfalso. apply n1.
                             assert (repeated_repeated_div 2 N = W * 3 ^ fst (repeated_div 3 N)).
                             { rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                               simpl. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
                               destruct Z_le_dec; try lia. rewrite H4 at 1. rewrite repeated_div_thm10; try lia.
                               intro. pose proof prime_2. apply prime_mult in H14; auto. destruct H14.
                               + apply prime_alt in p. destruct p. apply (H17 2); try lia. auto.
                               + apply Zpow_facts.prime_power_prime in H14; try lia; auto. apply prime_3. }
                             rewrite H14. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                 +++ destruct (repeated_div W (N / W)). simpl. auto.
              ** exfalso. apply n. rewrite H4. apply Z.divide_mul_l. apply Z.divide_factor_l.
      * assert (N = W * 3 ^ (fst (repeated_div 3 N)) * 2 ^ (fst (repeated_div 2 N))).
        { rewrite HeqW. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
          rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
          rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
          assert (fst (repeated_div 3 N) = fst (repeated_div 3 (snd (repeated_div 2 N)))).
          { rewrite repeated_div_thm9; try lia. unfold rel_prime. pose proof (Zgcd_is_gcd 3 2). compute in H5. auto. }
          rewrite H5. rewrite (Z.mul_comm (snd _)). rewrite <- repeated_div_main_thm; try lia.
          + rewrite Z.mul_comm. rewrite <- repeated_div_main_thm; try lia.
          + apply repeated_div_thm1; try lia. }
        assert (W > 3).
        { apply repeated_repeated_div_thm10 with (n := N); try lia. exists 1. lia. }
        pose proof (brute_force_main_thm N H). destruct H7. destruct H7.
        pose proof (repeated_div_thm0 2 N). pose proof (repeated_div_thm0 3 N).
        assert (fst (repeated_div 2 N) = 0 \/ 1 <= fst (repeated_div 2 N)) by lia.
        assert (fst (repeated_div 3 N) = 0 \/ 1 <= fst (repeated_div 3 N)) by lia.
        destruct H12, H13.
        ++ rewrite H12, H13 in H5. simpl in H5. ring_simplify in H5. rewrite H5. rewrite brute_force_thm1; auto.
        ++ rewrite H12 in H5. simpl in H5. ring_simplify in H5.
           pose proof (brute_force_main_thm N H). destruct H14, H14.
           assert (forall k, prime k /\ (k | N) <-> (k = 3 \/ k = W)).
           { split; intros.
             + destruct H17. rewrite H5 in H18. apply prime_mult in H18; auto. destruct H18.
               - apply prime_div_prime in H18; auto.
               - pose proof prime_3. apply Zpow_facts.prime_power_prime in H18; auto.
             + destruct H17.
               - rewrite H17. split. apply prime_3. rewrite H5. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
               - rewrite H17. split; auto. rewrite H5. apply Z.divide_factor_l. }
           pose proof (conj H14 H16). apply H17 in H18. destruct H18; auto. rewrite H18 in H15.
           assert (W | N). { rewrite H5. apply Z.divide_factor_l. }
           pose proof (conj p H19). apply H15 in H20; lia.
        ++ rewrite H13 in H5. simpl in H5. ring_simplify in H5.
           pose proof (brute_force_main_thm N H). destruct H14, H14.
           assert (forall k, prime k /\ (k | N) <-> (k = 2 \/ k = W)).
           { split; intros.
             + destruct H17. rewrite H5 in H18. apply prime_mult in H18; auto. destruct H18.
               - apply prime_div_prime in H18; auto.
               - pose proof prime_2. apply Zpow_facts.prime_power_prime in H18; auto.
             + destruct H17.
               - rewrite H17. split. apply prime_2. rewrite H5. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
               - rewrite H17. split; auto. rewrite H5. apply Z.divide_factor_l. }
           pose proof (conj H14 H16). apply H17 in H18. destruct H18; auto. rewrite H18 in H15.
           assert (W | N). { rewrite H5. apply Z.divide_factor_l. }
           pose proof (conj p H19). apply H15 in H20; lia.
        ++ pose proof (brute_force_main_thm N H). destruct H14, H14.
           assert (forall k, prime k /\ (k | N) <-> (k = 2 \/ k = 3 \/ k = W)).
           { split; intros.
             + destruct H17. rewrite H5 in H18. apply prime_mult in H18; auto. destruct H18.
               - apply prime_mult in H18; auto. destruct H18.
                 * apply prime_div_prime in H18; auto.
                 * pose proof prime_3. apply Zpow_facts.prime_power_prime in H18; auto.
               - pose proof prime_2. apply Zpow_facts.prime_power_prime in H18; auto.
             + destruct H17 as [H17 |[H17 | H17]].
               - rewrite H17. split. apply prime_2. rewrite H5. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
               - rewrite H17. split. apply prime_3. rewrite H5. apply Z.divide_mul_l. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
               - rewrite H17. split; auto. rewrite H5. apply Z.divide_mul_l. apply Z.divide_factor_l. }
           pose proof (conj H14 H16). apply H17 in H18. assert (W | N).
           { rewrite H5. apply Z.divide_mul_l. apply Z.divide_factor_l. }
           destruct H18 as [H18 |[H18 | H18]]; auto.
           -- pose proof (H15 _ (conj p H19)). lia.
           -- pose proof (H15 _ (conj p H19)). lia.
      * intro. destruct H5 as [H5 |[H5 |[H5 H6]]].
        ++ destruct p. lia.
        ++ destruct p. destruct H5. assert (0 < x) by lia. nia.
        ++ destruct H5. destruct H6. assert (W = 4 \/ 5 <= W) by lia. destruct H8.
           -- apply prime_alt in p. destruct p. pose proof (H10 2 ltac:(lia)). apply H11. exists 2. lia.
           -- assert (0 < x) by nia. nia.
    - assert (W = 1 \/ (2 | W) \/ (3 | W)).
      { assert (W = 1 \/ 2 <= W) by lia. destruct H3; auto. right.
        pose proof (repeated_repeated_div_thm12 4 N ltac:(lia) ltac:(lia) ltac:(lia)).
        assert (In W [5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24]). { simpl. lia. }
        destruct H5 as [H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|[H5|H5]]]]]]]]]]]]]]]]]]]].
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (n0 = 2 \/ n0 = 3 \/ n0 = 4) by lia. destruct H7. lia.
        + left. exists 3. lia.
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (In n0 [2;3;4;5;6]) by (simpl; lia). simpl in H8. destruct H7. lia.
        + left. exists 4. lia.
        + right. exists 3. lia.
        + left. exists 5. lia.
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (In n0 [2;3;4;5;6;7;8;9;10]) by (simpl; lia). simpl in H8. destruct H7. lia.
        + left. exists 6. lia.
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (In n0 [2;3;4;5;6;7;8;9;10;11;12]) by (simpl; lia). simpl in H8. destruct H7. lia.
        + left. exists 7. lia.
        + right. exists 5. lia.
        + left. exists 8. lia.
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (In n0 [2;3;4;5;6;7;8;9;10;11;12;13;14;15;16]) by (simpl; lia). simpl in H8. destruct H7. lia.
        + left. exists 9. lia.
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (In n0 [2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18]) by (simpl; lia). simpl in H8. destruct H7. lia.
        + left. exists 10. lia.
        + right. exists 7. lia.
        + left. exists 11. lia.
        + exfalso. apply n. rewrite <- H5. apply prime_alt. split; try lia. intros. intro.
          assert (In n0 [2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22]) by (simpl; lia). simpl in H8. destruct H7. lia.
        + left. exists 12. lia.
        + elim H5. }
      destruct H3 as [H3 |[H3 | H3]].
      * rewrite H3. split; split.
        ++ intros. split; auto. clear H4. rewrite H3 in *. clear H3 n H2 H0 H' H1.
           rewrite repeated_repeated_div_equation in HeqW. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl in *.
           rewrite repeated_repeated_div_equation in HeqW. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl in *.
           rewrite repeated_repeated_div_equation in HeqW. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
           pose proof (repeated_div_main_thm 3 (snd (repeated_div 2 N)) ltac:(lia) (proj1 (repeated_div_thm1 _ _ l))).
           pose proof (repeated_div_main_thm 2 N ltac:(lia) l). rewrite H0 in H1. rewrite <- HeqW in H1. ring_simplify in H1.
           rewrite repeated_div_thm9 in H1; try lia.
           -- clear HeqW H0. pose proof (repeated_div_thm0 2 N). pose proof (repeated_div_thm0 3 N).
              assert (fst (repeated_div 2 N) = 0 \/ 1 <= fst (repeated_div 2 N)) by lia.
              assert (fst (repeated_div 3 N) = 0 \/ 1 <= fst (repeated_div 3 N)) by lia.
              destruct H3, H4.
              ** rewrite H3, H4 in *. simpl in H1. rewrite H1. compute. auto.
              ** rewrite H3 in H1. simpl in H1. ring_simplify in H1. rewrite H1. pose proof prime_3. rewrite brute_force_thm9; try lia; auto.
                 unfold value_of_highest. destruct Z_le_dec; try lia. rewrite prime_divisor_list_equation.
                 destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. destruct Zdivide_dec; auto. simpl in *.
                 exfalso. apply n2. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 simpl. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 rewrite repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. destruct Zdivide_dec.
                 +++ exfalso. pose proof prime_2. pose proof prime_3. apply Zpow_facts.prime_power_prime in d; auto. lia.
                 +++ simpl. apply Zpow_facts.Zpower_divide. lia.
              ** rewrite H4 in H1. simpl in H1. ring_simplify in H1. rewrite H1. pose proof prime_2. rewrite brute_force_thm9; try lia; auto.
                 unfold value_of_highest. destruct Z_le_dec; try lia. rewrite prime_divisor_list_equation.
                 destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. destruct Zdivide_dec; simpl in *.
                 +++ exfalso. rewrite repeated_repeated_div_equation in d. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl in d.
                     rewrite repeated_repeated_div_equation in d. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                     rewrite repeated_div_thm13 in d; try lia. destruct d. lia.
                 +++ rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec; auto.
                     rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                     exfalso. apply n4. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                     apply Zpow_facts.Zpower_divide. lia.
              ** assert (brute_force N = 3).
                 { pose proof (brute_force_main_thm N ltac:(lia)). destruct H5. assert (forall k, prime k /\ (k | N) <-> (k = 2 \/ k = 3)).
                   { split; intros.
                     + destruct H7. rewrite H1 in H8. apply prime_mult in H8; auto. destruct H8.
                       - apply Zpow_facts.prime_power_prime in H8; try lia; auto. apply prime_2.
                       - apply Zpow_facts.prime_power_prime in H8; try lia; auto. apply prime_3.
                     + destruct H7.
                       - rewrite H7. split. apply prime_2. rewrite H1. apply Z.divide_mul_l. apply Zpow_facts.Zpower_divide. lia.
                       - rewrite H7. split. apply prime_3. rewrite H1. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia. }
                   apply H7 in H5. destruct H5; auto. pose proof prime_3. assert (3 | N).
                   { rewrite H1. apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia. }
                   pose proof (H6 _ (conj H8 H9)). lia. }
                 rewrite H5. rewrite H1. unfold value_of_highest. destruct Z_le_dec; try lia.
                 rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 destruct Zdivide_dec; auto. simpl in n2. exfalso. apply n2.
                 rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. simpl.
                 rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                 apply repeated_div_thm5; try lia.
                 +++ unfold rel_prime. pose proof (Zgcd_is_gcd 3 2). compute in H6. auto.
                 +++ apply Z.divide_mul_r. apply Zpow_facts.Zpower_divide. lia.
                 +++ apply Z.divide_mul_l. apply Zpow_facts.Zpower_divide. lia.
           -- unfold rel_prime. pose proof (Zgcd_is_gcd 3 2). compute in H2. auto.
        ++ intros. destruct H4. auto.
        ++ intros. exfalso. apply H4; auto.
        ++ intros. destruct H4. intro. apply brute_force_thm4 in H. lia.
      * rewrite HeqW in H3. apply repeated_repeated_div_thm3 in H3; try lia.
      * rewrite HeqW in H3. apply repeated_repeated_div_thm3 in H3; try lia.
  + simpl in *. pose proof (state_thm0 _ _ _ _ _ s). rewrite Nat2Z.inj_add in *. remember (Z.of_nat i) as X.
    simpl in *. ring_simplify (6 * (X + 1) + 5) in H0. clear IHs.
    pose proof (correct_loop_invariant _ _ _ _ _ s). unfold loop_invariant_candidate in H4. rewrite <- HeqX in *.
    ring_simplify (6 * (X + 1) + 4) in H1. rewrite H1 in H0. clear H1.
    destruct Z.eq_dec.
    - rewrite e in *. lia.
    - destruct Z_le_dec.
      * clear H4 l. rewrite H3 in n0, H2. clear n0. repeat split; intros. destruct H1.
        ++ assert (repeated_repeated_div (6 * X + 4) N = 1).
           { apply (repeated_repeated_div_thm17 N 3 (6 * X + 4)); try lia; auto. }
           lia.
        ++ destruct H1.
           -- assert (1 <= brute_force (repeated_repeated_div 3 N)).
              { apply brute_force_thm2. apply repeated_repeated_div_thm0; try lia. }
              assert (brute_force (repeated_repeated_div 3 N) = 1 \/ 2 <= brute_force (repeated_repeated_div 3 N)) by lia.
              destruct H5.
              ** pose proof (brute_force_thm4 (repeated_repeated_div 3 N)).
                 assert (repeated_repeated_div (6 * X + 4) N <= repeated_repeated_div 3 N).
                 { apply repeated_repeated_div_thm19; try lia. }
                 lia.
              ** assert (brute_force (repeated_repeated_div 3 N) = brute_force N).
                 { apply brute_force_thm12; try lia. }
                 assert (repeated_repeated_div 3 N | N).
                 { apply repeated_repeated_div_thm20; try lia. }
                 assert (brute_force N * brute_force N | N).
                 { rewrite H6 in H1. apply (Z.divide_trans _ _ _ H1 H7). }
                 clear H3 H1 H4 H5 H6 H7.
                 assert (repeated_repeated_div (6 * X + 10) N = 1 \/ 6 * X + 11 <= repeated_repeated_div (6 * X + 10) N).
                 { pose proof (repeated_repeated_div_thm0 (6 * X + 10) N ltac:(lia)).
                   assert (repeated_repeated_div (6 * X + 10) N = 1 \/ 1 < repeated_repeated_div (6 * X + 10) N) by lia.
                   destruct H3; try tauto. apply repeated_repeated_div_thm12 in H3; try lia. }
                 destruct H1.
                 +++ assert (~ prime (6 * X + 10)).
                     { intro. apply prime_alt in H3. destruct H3. pose proof (H4 2 ltac:(lia)). apply H5.
                       exists (3 * X + 5). lia. }
                     assert (~ prime (6 * X + 9)).
                     { intro. apply prime_alt in H4. destruct H4. pose proof (H5 3 ltac:(lia)). apply H6.
                       exists (2 * X + 3). lia. }
                     assert (~ prime (6 * X + 8)).
                     { intro. apply prime_alt in H5. destruct H5. pose proof (H6 2 ltac:(lia)). apply H7.
                       exists (3 * X + 4). lia. }
                     assert (~ prime (6 * X + 6)).
                     { intro. apply prime_alt in H6. destruct H6. pose proof (H7 2 ltac:(lia)). apply H9.
                       exists (3 * X + 3). lia. }
                     assert (~ prime (6 * X + 4)).
                     { intro. apply prime_alt in H7. destruct H7. pose proof (H9 2 ltac:(lia)). apply H10.
                       exists (3 * X + 2). lia. }
                     clear H0. rewrite repeated_repeated_div_thm8 in H1; auto; try lia. ring_simplify (6 * X + 10 - 1) in H1.
                     rewrite repeated_repeated_div_thm8 in H1; auto; try lia. ring_simplify (6 * X + 9 - 1) in H1.
                     rewrite repeated_repeated_div_thm8 in H1; auto; try lia. ring_simplify (6 * X + 8 - 1) in H1.
                     rewrite value_of_highest_thm3; auto; try lia. ring_simplify (6 * X + 9 - 1).
                     rewrite value_of_highest_thm3; auto; try lia. ring_simplify (6 * X + 8 - 1).
                     rewrite repeated_repeated_div_thm8 in H2; auto; try lia. ring_simplify (6 * X + 4 - 1) in H2.
                     apply repeated_repeated_div_thm22 in H1; try lia.
                     pose proof (brute_force_thm5 N ltac:(lia)).
                     unfold value_of_highest. destruct Z_le_dec; try lia.
                     assert (6 * X + 4 <= brute_force N).
                     { assert (2 <= repeated_repeated_div (6 * X + 3) N) by lia.
                       apply repeated_repeated_div_thm23 in H9; try lia. }
                     assert (brute_force N <> 6 * X + 4) by congruence.
                     assert (brute_force N <> 6 * X + 6) by congruence.
                     rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia).
                     destruct Zdivide_dec.
                     --- replace (6 * X + 7) with (6 * X + 7 - 1 + 1) in d at 1 by ring.
                         rewrite repeated_repeated_div_main_thm in d; try lia. ring_simplify (6 * X + 7 - 1 + 1) in d.
                         pose proof (brute_force_main_thm N H). destruct H12, H12, d.
                         pose proof (H13 _ (conj H15 H16)). lia.
                     --- ring_simplify (6 * X + 7 - 1). assert (brute_force N <> 6 * X + 7).
                         { intro. apply n1. replace (6 * X + 7) with (6 * X + 7 - 1 + 1) at 1 by ring.
                           rewrite repeated_repeated_div_main_thm; try lia. ring_simplify (6 * X + 7 - 1 + 1).
                           pose proof (brute_force_main_thm N H). destruct H13, H13. split; congruence. }
                         assert (brute_force N = 6 * X + 5) by lia. rewrite H13.
                         rewrite prime_divisor_list_equation. repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec.
                         *** exfalso. replace (6 * X + 6) with (6 * X + 6 - 1 + 1) in d at 1 by ring.
                             rewrite repeated_repeated_div_main_thm in d; try lia. ring_simplify (6 * X + 6 - 1 + 1) in d.
                             tauto.
                         *** ring_simplify (6 * X + 6 - 1). rewrite prime_divisor_list_equation.
                             repeat (destruct Z_le_dec; try lia). destruct Zdivide_dec; auto.
                             replace (6 * X + 5) with (6 * X + 5 - 1 + 1) in n5 at 1 by ring.
                             rewrite repeated_repeated_div_main_thm in n5; try lia. ring_simplify (6 * X + 5 - 1 + 1) in n5.
                             pose proof (brute_force_main_thm N H). destruct H14, H14. rewrite H13 in *. tauto.
                 +++ exfalso. assert (2 <= repeated_repeated_div (6 * X + 10) N) by lia.
                     apply repeated_repeated_div_thm23 in H3; try lia. ring_simplify (6 * X + 10 + 1) in H3.
                     destruct H8. assert ((6 * X + 11) * (6 * X + 11) <= repeated_repeated_div (6 * X + 10) N).
                     { assert (brute_force N | repeated_repeated_div (6 * X + 10) N).
                       { pose proof (brute_force_main_thm N H). destruct H5, H5.
                         destruct (Zdivide_dec (brute_force N) (repeated_repeated_div (6 * X + 10) N)); auto.
                         exfalso. assert (brute_force N <= 6 * X + 10) by admit. lia.
                       }
                     assert (brute_force N * brute_force N | repeated_repeated_div (6 * X + 10) N) by admit.
                     destruct H6. assert (1 <= x0) by nia. nia.
                     }
                     lia.
           -- assert (brute_force (repeated_repeated_div 3 N) = 1 \/ 2 <= brute_force (repeated_repeated_div 3 N)) by admit.
              destruct H4.
              ** pose proof (brute_force_thm4 (repeated_repeated_div 3 N)).
                 assert (2 <= repeated_repeated_div 3 N) by admit. lia.
              ** assert (brute_force N = brute_force (repeated_repeated_div 3 N)) by admit.
                 assert (brute_force N | N) by admit.
                 assert (brute_force N - 2 | N) by admit.
                 assert (brute_force N = 6 * X + 7) by admit.
                 admit.
        ++ rewrite H3. destruct H1.
           -- admit.
           -- destruct H1.
              ** assert (brute_force (repeated_repeated_div 3 N) = 1 \/ 2 <= brute_force (repeated_repeated_div 3 N)) by admit.
                 destruct H4.
                 +++ pose proof (brute_force_thm4 (repeated_repeated_div 3 N)).
                     assert (2 <= repeated_repeated_div 3 N) by admit. lia.
                 +++ assert (brute_force N = brute_force (repeated_repeated_div 3 N)) by admit.
                     assert (brute_force N * brute_force N | N) by admit.
                     assert (6 * X + 5 <= brute_force N <= 6 * X + 7) by admit.
                     assert (brute_force N = 6 * X + 5 \/ brute_force N = 6 * X + 7) by admit.
                     admit.
              ** assert (brute_force (repeated_repeated_div 3 N) = 1 \/ 2 <= brute_force (repeated_repeated_div 3 N)) by admit.
                 destruct H4.
                 +++ pose proof (brute_force_thm4 (repeated_repeated_div 3 N)). assert (2 <= repeated_repeated_div 3 N) by admit. lia.
                 +++ assert (brute_force N = brute_force (repeated_repeated_div 3 N)) by admit.
                     assert (brute_force N | N) by admit.
                     assert (brute_force N - 2 | N) by admit.
                     assert (brute_force N = 6 * X + 7) by admit.
                     admit.
        ++ destruct H1. rewrite H3 in H4. assert (repeated_repeated_div 3 N = 1 \/ 2 <= repeated_repeated_div 3 N) by admit.
           destruct H5; auto. right. assert (6 * X + 5 <= brute_force N <= 6 * X + 7) by admit.
           assert (brute_force N = 6 * X + 5 \/ brute_force N = 6 * X + 7) by admit.
           assert (2 <= brute_force (repeated_repeated_div 3 N)) by admit.
           assert (brute_force N = brute_force (repeated_repeated_div 3 N)) by admit.
           rewrite <- H9. destruct H7.
           -- left. assert (repeated_repeated_div (6 * X + 4) N = (6 * X + 5) * (6 * X + 5)) by admit.
              assert ((6 * X + 5) * (6 * X + 5) | repeated_repeated_div (6 * X + 4) N). { exists 1. lia. }
              rewrite H7. admit.
           -- right. assert (prime (6 * X + 5)) by admit.
              assert (repeated_repeated_div (6 * X + 4) N = (6 * X + 5) * (6 * X + 7)) by admit.
              rewrite H7. ring_simplify (6 * X + 7 - 2).
              assert ((6 * X + 5) * (6 * X + 7) | repeated_repeated_div (6 * X + 4) N). { exists 1. lia. }
              assert ((6 * X + 5) * (6 * X + 7) | repeated_repeated_div 3 N) by admit.
              split; auto. destruct H13. exists (x * (6 * X + 7)). lia.
        ++ assert (repeated_repeated_div 3 N <> 1 /\
                   ~ (brute_force (repeated_repeated_div 3 N) * brute_force (repeated_repeated_div 3 N) | repeated_repeated_div 3 N) /\
                   (~ prime (brute_force (repeated_repeated_div 3 N) - 2) \/
                    ~ (brute_force (repeated_repeated_div 3 N) - 2 | repeated_repeated_div 3 N))) by tauto.
           clear H1. destruct H4. destruct H4. destruct H5.
           -- clear H3. assert (brute_force (repeated_repeated_div 3 N) = brute_force N) by admit.
              rewrite H3 in *. assert (~ (brute_force N * brute_force N | N)) by admit.
              clear H1.
              (* Goal means that brute_force (snd (repeated_div (brute_force N) N) <= 6 * X + 7 *)
              (* and repeated_repeated_div (6 * X + 10) N = brute_force N, therefore brute_force N >= 6 * X + 11 ??? *)
              admit. (* ? *)
           -- clear H3. assert (brute_force (repeated_repeated_div 3 N) = brute_force N) by admit.
              rewrite H3 in *. clear H1. assert (~ (brute_force N * brute_force N | N)) by admit.
              admit. (* ?? *)
        ++ assert (repeated_repeated_div 3 N <> 1 /\
                   ~ (brute_force (repeated_repeated_div 3 N) * brute_force (repeated_repeated_div 3 N) | repeated_repeated_div 3 N) /\
                   (~ prime (brute_force (repeated_repeated_div 3 N) - 2) \/
                    ~ (brute_force (repeated_repeated_div 3 N) - 2 | repeated_repeated_div 3 N))) by tauto.
           clear H1. destruct H4. destruct H4. destruct H5.
           -- rewrite H3. assert (brute_force (repeated_repeated_div 3 N) = brute_force N) by admit.
              rewrite H6 in *. assert (~ (brute_force N * brute_force N | N)) by admit.
              (* Goal is equivalent to brute_force N >= 6 * X + 11. *)
              admit. (* ? *)
           -- rewrite H3. assert (brute_force (repeated_repeated_div 3 N) = brute_force N) by admit.
              rewrite H6 in *.
              assert (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) (repeated_repeated_div (6 * X + 4) N)))) =
                      repeated_repeated_div (6 * X + 7) N) by admit.
              rewrite H7. clear H7 H3. admit. (* ?? *)
        ++ intro. destruct H1. destruct H4.
           -- rewrite H3 in H5. clear H3. assert (repeated_repeated_div (6 * X + 4) N = 1) by admit. lia.
           -- destruct H4.
              ** rewrite H3 in H5. clear H3.
                 assert (repeated_repeated_div 3 N = 1 \/ 2 <= repeated_repeated_div 3 N) by admit.
                 destruct H3.
                 +++ assert (repeated_repeated_div (6 * X + 4) N = 1) by admit. lia.
                 +++ assert (brute_force (repeated_repeated_div 3 N) = brute_force N) by admit.
                     rewrite H6 in *. assert (brute_force N * brute_force N | N) by admit.
                     clear H4 H3 H6.
                     assert (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) (repeated_repeated_div (6 * X + 4) N)))) =
                             repeated_repeated_div (6 * X + 7) N) by admit.
                     rewrite H3 in H5. clear H3.
                     assert (repeated_repeated_div (6 * X + 10) N = repeated_repeated_div (6 * X + 7) N) by admit.
                     rewrite H3 in H0. clear H3. assert (value_of_highest (6 * X + 9) N = brute_force N) by admit.
                     pose proof (brute_force_thm7 _ H). lia.
              ** destruct H4. rewrite H3 in H5.
                 assert (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) (repeated_repeated_div (6 * X + 4) N)))) =
                         repeated_repeated_div (6 * X + 7) N) by admit.
                 rewrite H7 in *. clear H7. clear H3.
                 assert (value_of_highest (6 * X + 9) N = brute_force N) by admit.
                 pose proof (brute_force_thm7 _ H). lia.
      * lia.
Admitted.







Require Import EulerProject3.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition new_highest f n h :=
  if Zdivide_dec f n then (if Z_le_dec f h then h else f) else h.

Definition factorize_spec: ident * funspec :=
DECLARE _factorize
  WITH gv: globals, n: Z, f: Z, h: Z
  PRE [ tulong, tulong ]
    PROP (1 <= n <= Int64.max_unsigned; 2 <= f <= Int64.max_unsigned; 0 <= h <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n); Vlong (Int64.repr f))
    GLOBALS (gv)
    SEP (data_at Ews tulong (Vlong (Int64.repr h)) (gv _highest))
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (snd (repeated_div f n))))
    SEP (data_at Ews tulong (Vlong (Int64.repr (new_highest f n h))) (gv _highest)).

Definition find_spec: ident * funspec :=
DECLARE _find
  WITH gv: globals, n: Z, h: Z
  PRE [ tulong ]
    PROP (2 <= n <= 1000000000000 (* instead of Int64.max_unsigned *); 0 <= h <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n))
    GLOBALS (gv)
    SEP (data_at Ews tulong (Vlong (Int64.repr h)) (gv _highest))
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (brute_force n)))
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
  assert (forall i, 0 <= i -> Int64.unsigned (Int64.repr (n / f ^ i)) = n / f ^ i).
  { intros. apply Int64.unsigned_repr. split.
    + apply Z_div_nonneg_nonneg; try lia.
    + destruct (Z.eq_dec i 0).
      - subst. simpl (f ^ 0). rewrite Zdiv_1_r. lia.
      - assert (n / f ^ i < n). { apply Z.div_lt; try lia. apply Z.pow_gt_1; try lia. }
        lia. }
  forward_if.
  + deadvars!. forward. entailer!. destruct (Zdivide_dec f n); auto.
    - exfalso. destruct d. subst. assert (x < 1) by nia. lia.
    - f_equal. f_equal. rewrite repeated_div_equation. repeat (destruct Z_le_dec; try lia).
      destruct Zdivide_dec; auto. tauto.
    - unfold new_highest. destruct Zdivide_dec.
      * destruct d. subst. assert ((x - 1) * f < 0) by lia. assert (x < 1) by nia. lia.
      * auto.
  + forward_while (
      EX (i: Z),
        PROP (0 <= i <= fst (repeated_div f n))
        LOCAL (temp _n (Vlong (Int64.repr (n / f ^ i))); temp _f (Vlong (Int64.repr f)); gvars gv)
        SEP (data_at Ews tulong (Vlong (Int64.repr (if Z.eq_dec i 0 then h else new_highest f n h))) (gv _highest))
    ).
    - Exists 0. entailer!. repeat split; try lia.
      * apply repeated_div_thm0.
      * simpl (f ^ 0). rewrite Z.div_1_r. auto.
    - entailer!. apply repr_inj_unsigned64 in H10; try lia.
    - forward.
      * entailer!. apply repr_inj_unsigned64 in H10; try lia.
      * assert (f | n / f ^ i).
        { unfold Int64.modu in HRE. fold (Z.div n (f ^ i)) in HRE. rewrite H5, H2 in HRE; try lia.
          apply repr_inj_unsigned64 in HRE; try lia.
          + apply Zmod_divide in HRE; try lia. auto.
          + assert (0 <= (n / f ^ i) mod f < f). { apply Z_mod_lt. lia. } lia. }
        clear HRE. forward. forward_if.
        ++ apply ltu_inv64 in H9. rewrite H2 in H9. destruct Z.eq_dec.
           -- rewrite H4 in H9. forward. entailer!. Exists 1. simpl (f ^ 0) in H8. rewrite Z.div_1_r in H8.
              entailer!.
              ** repeat split; try lia.
                 +++ apply repeated_div_thm4; try lia. auto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia. simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest. repeat if_tac; try lia; auto. tauto.
           -- unfold new_highest in *. destruct Zdivide_dec; [destruct Z_le_dec |].
              ** rewrite H4 in H9. lia.
              ** rewrite H2 in H9. lia.
              ** elim n1. clear n1. assert (f ^ i | n).
                 { rewrite repeated_div_main_thm with (f := f) (n := n); try lia.
                   exists (f ^ (fst (repeated_div f n) - i) * snd (repeated_div f n)).
                   rewrite <- Z.mul_assoc. rewrite (Z.mul_comm _ (f ^ i)). rewrite Z.mul_assoc.
                   rewrite <- Z.pow_add_r; try lia. ring_simplify (fst (repeated_div f n) - i + i). auto. }
                 destruct H8. exists (x * f ^ i). replace (x * f ^ i * f) with (x * f * f ^ i) by ring.
                 rewrite <- H8. rewrite Z.mul_comm. rewrite <- Zdivide_Zdiv_eq; auto; try lia.
        ++ apply ltu_false_inv64 in H9. rewrite H2 in H9. destruct Z.eq_dec.
           -- rewrite H4 in H9. forward. entailer!. simpl (f ^ 0) in H8. rewrite Z.div_1_r in H8.
              Exists 1. entailer!.
              ** repeat split; try lia.
                 +++ apply repeated_div_thm4; try lia; auto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia. simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest. destruct Zdivide_dec; try tauto.
                 destruct Z_le_dec; try lia. auto.
           -- forward. entailer!. Exists (i + 1). entailer!. repeat split; try lia.
              ** rewrite (repeated_div_main_thm f n) in H8; try lia. rewrite Z.mul_comm in H8.
                 rewrite Zdivide_Zdiv_eq_2 in H8; try lia.
                 +++ rewrite <- Z.pow_sub_r in H8; try lia.
                     assert ((f | snd (repeated_div f n)) -> False). { apply repeated_div_thm2; try lia. }
                     assert (f | f ^ (fst (repeated_div f n) - i)).
                     { exists (f ^ (fst (repeated_div f n) - i - 1)). replace f with (f ^ 1) at 5 by lia.
                       rewrite <- Z.pow_add_r; try lia. f_equal. ring.
                       destruct (Z_le_lt_dec 0 (fst (repeated_div f n) - i - 1)); auto.
                       exfalso. assert (i = fst (repeated_div f n)) by lia. subst.
                       ring_simplify (fst (repeated_div f n) - fst (repeated_div f n)) in H8.
                       simpl (f ^ 0) in H8. ring_simplify (snd (repeated_div f n) * 1) in H8. auto. }
                     remember (fst (repeated_div f n) - i) as W. assert (0 < W).
                     { assert (W = 0 \/ 0 < W) by lia. destruct H14; auto. rewrite H14 in H13. simpl (f ^ 0) in H13.
                       apply Z.divide_1_r_nonneg in H13; lia. }
                     lia.
                 +++ exists (f ^ (fst (repeated_div f n) - i)). rewrite <- Z.pow_add_r; try lia. f_equal. ring.
              ** clear H9. unfold Int64.divu. do 2 f_equal. rewrite H5; try lia. rewrite H2.
                 rewrite Zdiv_Zdiv; try lia. f_equal. rewrite Z.pow_add_r; try lia.
              ** clear H9. destruct Z.eq_dec; try lia. auto.
    - fold (Z.div n (f ^ i)) in HRE. unfold Int64.modu in HRE. rewrite H5 in HRE; try lia. rewrite H2 in HRE.
      assert ((n / f ^ i) mod f <> 0). { intro. apply HRE. congruence. } clear HRE.
      forward. entailer!.
      * do 2 f_equal. assert ((f | n / f ^ i) -> False).
        { intro. apply H8. apply Z.mod_divide; try lia. auto. }
        clear H8. assert (n = f ^ fst (repeated_div f n) * snd (repeated_div f n)) by (apply repeated_div_main_thm; try lia).
        rewrite H8 at 1. rewrite Z.mul_comm. rewrite Zdivide_Zdiv_eq_2; try lia.
        ++ rewrite <- Z.pow_sub_r; try lia. assert (i < fst (repeated_div f n) \/ i = fst (repeated_div f n)) by lia.
           destruct H12.
           -- exfalso. apply H11. rewrite H8. rewrite Z.mul_comm. rewrite Zdivide_Zdiv_eq_2; try lia.
              rewrite <- Z.pow_sub_r; try lia. destruct (Zdivide_dec f (snd (repeated_div f n))).
              ** destruct d. rewrite H13. exists (x * f ^ (fst (repeated_div f n) - i)). ring.
              ** exists (snd (repeated_div f n) * f ^ (fst (repeated_div f n) - i - 1)).
                 rewrite <- Z.mul_assoc. f_equal. replace f with (f ^ 1) at 5 by ring.
                 rewrite <- Z.pow_add_r; try lia. f_equal. ring.
              ** exists (f ^ (fst (repeated_div f n) - i)). rewrite <- Z.pow_add_r; try lia. f_equal. ring.
           -- subst. ring_simplify (fst (repeated_div f n) - fst (repeated_div f n)). simpl (f ^ 0). ring.
         ++ exists (f ^ (fst (repeated_div f n) - i)). rewrite <- Z.pow_add_r; try lia. f_equal. ring.
      * assert ((f | n / f ^ i) -> False).
        { intro. apply H8. apply Z.mod_divide; try lia. auto. }
        clear H8. destruct Z.eq_dec; auto.
        unfold new_highest. destruct Zdivide_dec; [destruct Z_le_dec |]; auto.
        subst. simpl (f ^ 0) in H11. rewrite Z.div_1_r in H11. tauto.
Qed.


(*
Lemma find_proof: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function. assert (Int64.max_unsigned = 18446744073709551615) as HH by auto.
  assert (1 <= n) by lia. forward. forward_call. forward_call.
  + split.
    - assert (1 <= 2) by lia. pose proof (repeated_div_thm1 _ H1 _ H2). lia.
    - unfold new_highest. destruct Zdivide_dec; [destruct Z_le_dec |]; try lia.
  + autorewrite with norm.
    set (repeated_repeated_div 3 n H1) as W.
    set (W = 1 \/ (Z.divide ((brute_force W) ^ 2) W) \/ (prime (brute_force W - 2) /\ Z.divide (brute_force W - 2) W)) as P.
    assert ({P} + {~ P}).
    { unfold P. destruct (Z.eq_dec W 1).
      + left. auto.
      + destruct (Zdivide_dec (brute_force W ^ 2) W).
        - left. auto.
        - destruct (prime_dec (brute_force W - 2)).
          * destruct (Zdivide_dec (brute_force W - 2) W).
            ++ left. auto.
            ++ right. tauto.
          * tauto. }
    - forward_if (
      if H2
      then PROP ()
           LOCAL (temp _n (Vlong (Int64.repr 1)); gvars gv)
           SEP (data_at Ews tulong (Vlong (Int64.repr (brute_force W))) (gv _highest))
      else PROP ()
           LOCAL (temp _n (Vlong (Int64.repr (brute_force W))); gvars gv)
           SEP (data_at Ews tulong (Vlong (Int64.repr (brute_force (snd (repeated_div n (brute_force W)))))) (gv _highest))
      ).
      * admit.
      * admit.
      * destruct H2.
        ++ admit.
        ++ admit.
Admitted.
*)