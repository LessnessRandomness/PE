Require Import VST.floyd.proofauto.
From Stdlib Require Import Znumtheory.
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

Function factorization (i n: Z) { measure Z.to_nat i}: list (Z * Z) :=
  if Z_le_dec 1 n
  then if Z_le_dec i 1
       then []
       else let W := factorization (i - 1) n in
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
  (x | repeated_repeated_div i n) -> (x | n).
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

Theorem repeated_repeated_div_thm13 n f (H: 1 <= n) (H0: 2 <= f):
  (~ Z.divide f n) -> repeated_repeated_div f n = repeated_repeated_div (f - 1) n.
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

Theorem repeated_repeated_div_thm19 (n i j: Z):
  1 <= n -> 2 <= i <= j -> repeated_repeated_div j n <= repeated_repeated_div i n.
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

Theorem repeated_repeated_div_of_one (i : Z) (Hi : 1 <= i):
  repeated_repeated_div i 1 = 1.
Proof.
  assert (0 <= i) by lia. revert Hi. pattern i. apply Z_lt_induction; auto; intros. clear H i.
  assert (x = 1 \/ 2 <= x) by lia. destruct H.
  + subst. compute. reflexivity.
  + rewrite repeated_repeated_div_equation. simpl. destruct Z_le_dec; try lia.
    rewrite H0; try lia. rewrite repeated_div_equation. destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - destruct d. assert (0 < x0) by nia. nia.
    - reflexivity.
Qed.


(* Theorems about factorization *)

Definition prod_of_list (L: list Z): Z := fold_right Z.mul 1 L.

Definition factorization_thm0 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  n = repeated_repeated_div k n *
  prod_of_list (List.map (fun (p : Z * Z) => fst p ^ snd p) (factorization k n)).
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear H k.
  assert (x = 2 \/ 3 <= x) by lia. destruct H.
  + subst. rewrite factorization_equation.
    rewrite repeated_repeated_div_equation. simpl.
    rewrite repeated_repeated_div_equation. simpl.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - simpl. rewrite factorization_equation. simpl. destruct Z_le_dec; try lia.
      simpl. ring_simplify. rewrite Z.mul_comm, <- (repeated_div_main_thm 2 n); try lia.
    - rewrite factorization_equation. simpl. destruct Z_le_dec; try lia.
      simpl. rewrite repeated_div_equation. simpl. destruct Z_le_dec; try lia.
      destruct Zdivide_dec; try tauto. simpl. ring.
  + rewrite factorization_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl. pose proof (repeated_div_main_thm x (repeated_repeated_div (x - 1) n) Hk).
      pose proof (H1 (repeated_repeated_div_thm0 (x - 1) n Hn)). clear H1.
      rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia.
      assert (forall (z1 z2 z3: Z), z1 * (z2 * z3) = z2 * z1 * z3) by (intros; ring).
      rewrite H1. rewrite <- H2. rewrite <- H0; try lia.
    - rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia. rewrite repeated_div_equation.
      destruct Z_le_dec; try lia.
      pose proof (repeated_repeated_div_thm0 (x - 1) n Hn).
      destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
      simpl. rewrite <- H0; try lia.
Qed.

Definition factorization_thm1 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, In p (factorization k n) -> fst p <= k.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear H k.
  assert (x = 2 \/ 3 <= x) by lia. destruct H.
  + subst. rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * rewrite <- H; simpl; lia.
      * rewrite factorization_equation in H. simpl in H. destruct Z_le_dec; try lia.
        elim H.
    - rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
      elim H1.
  + rewrite factorization_equation in H1. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst. simpl. lia.
      * apply H0 in H1; try lia.
    - apply H0 in H1; try lia.
Qed.

Definition factorization_thm2 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, In p (factorization k n) -> 1 <= snd p.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear k H.
  assert (x = 2 \/ 3 <= x) by lia. destruct H.
  + subst. rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst. simpl. apply repeated_div_thm4; try lia; auto.
        apply repeated_repeated_div_thm0; try lia.
      * rewrite factorization_equation in H. simpl in H. destruct Z_le_dec; try lia.
        elim H.
    - rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
      elim H1.
  + rewrite factorization_equation in H1. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst. simpl. apply repeated_div_thm4; try lia; auto.
        apply repeated_repeated_div_thm0; try lia.
      * apply H0 in H1; try lia.
    - apply H0 in H1; try lia.
Qed.

Theorem factorization_thm3 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, In p (factorization k n) -> prime (fst p).
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear k H.
  assert (x = 2 \/ 3 <= x) by lia. destruct H.
  + subst. rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst. simpl. exact prime_2.
      * rewrite factorization_equation in H. simpl in H. destruct Z_le_dec; try lia. elim H.
    - rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia. elim H1.
  + rewrite factorization_equation in H1. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst. simpl. assert (x = x - 1 + 1) by ring. rewrite H1 in d at 1.
        apply repeated_repeated_div_main_thm in d; try lia. destruct d. congruence.
      * apply H0 in H1; try lia. exact H1.
    - apply H0 in H1; try lia. exact H1.
Qed.

Theorem factorization_thm4_aux0 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, prime p -> k < p -> snd (repeated_div k (n * p)) = snd (repeated_div k n) * p.
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n. apply Z_lt_induction; try lia; intros. clear n H.
  destruct (Zdivide_dec k x).
  + rewrite repeated_div_equation. rewrite (repeated_div_equation k x).
    destruct Z_le_dec. destruct Z_le_dec; try nia. destruct Z_le_dec; try lia.
    - assert (k | x * p). { destruct d. subst x. exists (x0 * p). ring. }
      destruct Zdivide_dec; try tauto. destruct Zdivide_dec; try tauto.
      destruct d. subst x. rewrite Z.div_mul; try lia.
      replace (x0 * k * p) with (x0 * p * k) by ring. rewrite Z.div_mul; try lia.
      assert (forall (W : Z * Z), snd (let (i, k) := W in (i + 1, k)) = snd W).
      { destruct W. simpl. auto. }
      rewrite H3, H3. rewrite H0; try nia; auto.
    - auto.
  + assert (~ (k | x * p)).
    { intro. apply n. clear n. rewrite Z.mul_comm in H. apply Gauss in H; auto.
      apply rel_prime_le_prime; auto; lia. }
    rewrite (repeated_div_equation k (x * p)). rewrite (repeated_div_equation k x).
    destruct Z_le_dec; try lia. destruct Z_le_dec; try nia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec; try tauto. destruct Zdivide_dec; try tauto.
Qed.

Theorem factorization_thm4_aux0' (n k i : Z) (Hn : 1 <= n) (Hk : 2 <= k) (Hi : 0 <= i) :
  forall p, prime p -> k < p -> snd (repeated_div k (n * p ^ i)) = snd (repeated_div k n) * p ^ i.
Proof.
  assert (0 <= i) by lia. revert Hi. pattern i. apply Z_lt_induction; try lia; intros. clear i H.
  assert (x = 0 \/ 1 <= x) by lia. destruct H.
  + subst. simpl. ring_simplify (n * 1). ring.
  + replace x with (x - 1 + 1) at 1 by ring. rewrite Z.pow_add_r; try lia.
    replace (n * (p ^ (x - 1) * p ^ 1)) with (n * p ^ (x - 1) * p) by ring.
    rewrite factorization_thm4_aux0; try lia; auto.
    rewrite H0; try lia; auto. rewrite <- Z.mul_assoc. f_equal.
    replace (p ^ (x - 1) * p) with (p ^ (x - 1) * p ^ 1) by ring.
    rewrite <- Z.pow_add_r; try lia. f_equal. ring.
Qed.

Theorem factorization_thm4_aux1 (n k : Z) (Hn : 1 <= n) (Hk : 1 <= k) :
  forall p, prime p -> k < p ->
  repeated_repeated_div k (n * p) = repeated_repeated_div k n * p.
Proof.
  assert (0 <= k) by lia. revert Hk n Hn. pattern k.
  apply Z_lt_induction; auto; intros. clear k H.
  assert (x = 1 \/ 2 <= x) by lia. destruct H.
  + subst. rewrite repeated_repeated_div_equation. rewrite (repeated_repeated_div_equation 1).
    simpl. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
  + do 2 rewrite (repeated_repeated_div_equation x).
    destruct Z_le_dec; try nia. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    rewrite H0; try lia; auto. rewrite factorization_thm4_aux0; auto; try lia.
    apply repeated_repeated_div_thm0; try lia.
Qed.

Theorem factorization_thm4_aux2 (n : Z) (Hn : 1 <= n) :
  forall p, prime p ->
  fst (repeated_div p (repeated_repeated_div (p - 1) n)) = fst (repeated_div p n).
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n. apply Z_lt_induction; auto; intros. clear n H.
  destruct (Zdivide_dec p x).
  + assert (p = 2 \/ 3 <= p). { destruct H1; lia. } destruct H.
    - subst. simpl. rewrite repeated_repeated_div_equation. simpl.
      destruct Z_le_dec; try lia.
    - pose proof (repeated_repeated_div_thm6 (p - 1) x Hn ltac:(lia)).
      ring_simplify (p - 1 + 1) in H2. pose proof (H2 H1 d).
      rewrite repeated_div_equation. destruct Z_le_dec; try lia.
      assert (1 <= repeated_repeated_div (p - 1) x). { apply repeated_repeated_div_thm0. auto. }
      destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
      rewrite (repeated_div_equation p x). destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
      assert (forall (W : Z * Z), fst (let (i, k) := W in (i + 1, k)) = fst W + 1).
      { destruct W. simpl. auto. }
      rewrite H5, H5. f_equal. rewrite <- (H0 (x / p)); try lia; auto.
      * f_equal. f_equal. destruct d1. subst x.
        rewrite factorization_thm4_aux1; try lia; auto. rewrite Z.div_mul; try lia.
        rewrite Z.div_mul; try lia.
      * destruct d1. subst. rewrite Z.div_mul; nia.
      * destruct d. subst. rewrite Z.div_mul; nia.
  + rewrite repeated_div_equation. destruct Z_le_dec; try lia.
    assert (1 <= repeated_repeated_div (p - 1) x). { apply repeated_repeated_div_thm0. auto. }
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - exfalso. apply n. apply repeated_repeated_div_thm4 in d; try lia. auto.
    - simpl. rewrite repeated_div_equation. destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
    - simpl. destruct H1; lia.
Qed.

Theorem factorization_thm4 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  if prime_dec k
  then if Zdivide_dec k n
       then factorization k n = (k, fst (repeated_div k n)) :: factorization (k - 1) n
       else factorization k n = factorization (k - 1) n
  else factorization k n = factorization (k - 1) n.
Proof.
  destruct prime_dec.
  + destruct Zdivide_dec.
    - rewrite (factorization_equation k). destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
      f_equal. f_equal. rewrite factorization_thm4_aux2; auto.
      exfalso. apply n1. replace k with (k - 1 + 1) at 1 by ring.
      rewrite repeated_repeated_div_main_thm; try lia; auto.
      ring_simplify (k - 1 + 1). auto.
    - rewrite (factorization_equation k). destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia. destruct Zdivide_dec.
      * exfalso. apply n0. apply repeated_repeated_div_thm4 in d; try lia; auto.
      * auto.
  + rewrite (factorization_equation k). destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - exfalso. apply n0; clear n0.
      replace k with (k - 1 + 1) in d at 1 by ring.
      rewrite repeated_repeated_div_main_thm in d; try lia.
      ring_simplify (k - 1 + 1) in d. tauto.
    - auto.
Qed.

Theorem factorization_thm5 (n k : Z) (Hn : 2 <= n) (Hk : n < k) :
  factorization k n = factorization n n.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear k H.
  assert (x = n + 1 \/ n + 1 < x) by lia. destruct H.
  + subst. rewrite factorization_equation.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try lia. ring_simplify (n + 1 - 1).
    destruct Zdivide_dec.
    - exfalso. pose proof (repeated_repeated_div_thm9 n n l).
      pose proof (repeated_repeated_div_thm0 n n l).
      destruct d. assert (1 <= x) by nia. nia.
    - reflexivity.
  + rewrite factorization_equation. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - exfalso. pose proof (repeated_repeated_div_thm9 (x - 1) n l).
      pose proof (repeated_repeated_div_thm0 (x - 1) n l).
      destruct d. assert (1 <= x0) by nia. nia.
    - rewrite H0; try lia. reflexivity.
Qed.

Theorem factorization_thm6 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, In p (factorization k n) -> (fst p ^ snd p | n).
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear k H.
  assert (x = 2 \/ 2 < x) by lia. destruct H.
  + subst. rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
    rewrite repeated_repeated_div_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
    rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1; try tauto. subst. simpl. rewrite (repeated_div_main_thm 2 n) at 2; try lia.
      exists (snd (repeated_div 2 n)). ring.
    - elim H1.
  + rewrite factorization_equation in H1. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - simpl in H1. destruct H1.
      * subst. simpl.
        pose proof (repeated_div_main_thm x (repeated_repeated_div (x - 1) n) Hk
          (repeated_repeated_div_thm0 (x - 1) n l)).
        assert (x ^ fst (repeated_div x (repeated_repeated_div (x - 1) n)) |
          repeated_repeated_div (x - 1) n).
        { rewrite H1 at 2. exists (snd (repeated_div x (repeated_repeated_div (x - 1) n))). ring. }
        assert (repeated_repeated_div (x - 1) n | n).
        { apply repeated_repeated_div_thm20; try lia. }
        apply (Z.divide_trans _ _ _ H2 H3).
      * apply H0 in H1; try lia. exact H1.
    - apply H0 in H1; try lia. exact H1.
Qed.

Theorem factorization_of_one (k : Z) (Hk : 1 <= k) : factorization k 1 = [].
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k. apply Z_lt_induction; auto; intros. clear k H.
  assert (x = 1 \/ 2 <= x) by lia. destruct H.
  + subst. reflexivity.
  + rewrite factorization_equation. simpl. destruct Z_le_dec; try lia.
    rewrite repeated_repeated_div_of_one; try lia. destruct Zdivide_dec.
    - destruct d. assert (0 < x0) by nia. nia.
    - rewrite H0; try lia. auto.
Qed.

Theorem factorization_thm7 (n k : Z) (Hn : 1 <= n) (Hk : 2 <= k) :
  forall p, In p (factorization k n) -> (fst p ^ (snd p + 1) | n) -> False.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k. apply Z_lt_induction; try lia; intros. clear k H.
  assert (x = 2 \/ 3 <= x) by lia. destruct H.
  + subst. clear H0. assert (fst p ^ snd p | n). { apply factorization_thm6 in H1; try lia. auto. }
    rewrite factorization_equation in H1. destruct Z_le_dec; try lia. simpl in H1.
    destruct Zdivide_dec.
    - rewrite (repeated_repeated_div_equation 1 n) in *. simpl in *.
      destruct Z_le_dec; try lia. destruct H1.
      * subst p. simpl in *.
        pose proof (repeated_div_main_thm 2 n ltac:(lia) ltac:(lia)).
        rewrite H0 in H2 at 2. destruct H2.
        rewrite Z.pow_add_r in H1; try lia.
        ++ assert (0 < x) by lia.
           assert (snd (repeated_div 2 n) = 2 * x) by nia.
           assert (2 | snd (repeated_div 2 n)). { exists x. lia. }
           apply repeated_div_thm2 in H4; try lia.
        ++ apply repeated_div_thm0.
      * rewrite factorization_equation in H0. simpl in H0. destruct Z_le_dec; try lia. elim H0.
    - rewrite factorization_equation in H1. simpl in H1. destruct Z_le_dec; try lia. elim H1.
  + assert (fst p <= x). { apply factorization_thm1 in H1; auto; lia. }
    assert (x = fst p \/ fst p < x) by lia. destruct H4.
    - subst x. assert (prime (fst p)). { apply factorization_thm3 in H1; try lia; auto. }
      pose proof (factorization_thm4 n (fst p) ltac:(lia) ltac:(lia)).
      destruct prime_dec; try tauto.
      assert (fst p | n). { rewrite Z.pow_add_r in H2; try lia. ring_simplify (fst p ^ 1) in H2.
        destruct H2. subst n. exists (x * fst p ^ snd p). ring.
        apply factorization_thm2 in H1; try lia. }
      destruct Zdivide_dec; try tauto.
      rewrite H5 in H1. simpl in H1. destruct H1.
      * destruct p; simpl in *. inversion H1. subst z0.
        destruct H2. rewrite (repeated_div_main_thm z n) in H2 at 1; try lia.
        rewrite Z.pow_add_r in H2; try lia.
        ++ ring_simplify (z ^ 1) in H2. assert (snd (repeated_div z n) = x * z).
           { assert (0 < z ^ fst (repeated_div z n)).
             { apply Z.pow_pos_nonneg; try lia. apply repeated_div_thm0. }
             nia. }
           assert (z | snd (repeated_div z n)).
           { rewrite H7. exists x; ring. }
           apply (repeated_div_thm2) in H8; try lia.
        ++ apply repeated_div_thm0.
      * apply H0 in H1; try lia. auto.
    - rewrite factorization_equation in H1. destruct Z_le_dec; try lia.
      destruct Z_le_dec; try lia. destruct Zdivide_dec.
      * simpl in H1. destruct H1.
        ++ subst p. simpl in *. lia.
        ++ apply H0 in H1; auto; try lia.
      * apply H0 in H1; auto; try lia.
Qed.

(**


Theorem factorization_thm5'_aux1 (p q i j : Z)
  (Hp: prime p) (Hi : 0 <= i) (Hj : 0 <= j) (Hq : ~ (p | q)) :
  (p ^ i | p ^ j * q) -> i <= j.
Proof.
  intros. assert (rel_prime p q).
  { unfold rel_prime. constructor.
    + exists p; ring.
    + exists q; ring.
    + intros. apply prime_divisors in H0; auto. destruct H0 as [H0|[H0|[H0|H0]]].
      - exists (-1). lia.
      - exists 1. lia.
      - exfalso. apply Hq. congruence.
      - exfalso. destruct H1. rewrite H0 in H1. apply Hq. exists (- x0). lia. }
  assert (rel_prime (p ^ i) (q ^ 1)).
  { apply Zpow_facts.rel_prime_Zpower; try lia; auto. }
  replace q with (q ^ 1) in H by ring. apply aux0 in H; try lia; auto.
  + apply factorization_thm5'_aux0 in H; try lia. destruct Hp; lia.
  + apply rel_prime_sym. ring_simplify (q ^ 1) in H1. auto.
Qed.
**)


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

Theorem factorization_thm8 (n k : Z) (Hn : 2 <= n) (Hk : prime k) (Hk0 : (k | n)) :
  factorization k n = [] -> False.
Proof.
  assert (2 <= k). { destruct Hk. lia. }
  destruct Hk0. subst. intros. rewrite factorization_equation in H0.
  destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
  destruct Zdivide_dec.
  + congruence.
  + apply n0. assert (k = k - 1 + 1) by ring. rewrite H1 at 1.
    rewrite repeated_repeated_div_main_thm; try lia. rewrite <- H1. constructor.
    - exact Hk.
    - exists x. ring.
Qed.

Theorem factorization_thm9 (n k p : Z) (Hn : 2 <= n) (Hp : prime p) (Hp0 : (p | n)) (Hk : p <= k) :
  factorization k n = [] -> False.
Proof.
  assert (0 <= k). { destruct Hp; lia. }
  revert Hk n Hn Hp0. pattern k. apply Z_lt_induction; auto; intros. clear k H.
  assert (x = p \/ p < x) by lia. destruct H.
  + subst. apply factorization_thm8 in H1; try lia; auto.
  + assert (1 < p). { destruct Hp; auto. }
    rewrite factorization_equation in H1. destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - congruence.
    - apply H0 in H1; try lia. exact Hp0.
Qed.

Theorem factorization_thm10 (n : Z) (Hn : 2 <= n) : factorization n n = [] -> False.
Proof.
  destruct (prime_divisor_existence n Hn). destruct H.
  apply (factorization_thm9) with (p := x); try lia; auto.
  destruct H0. assert (1 < x). { destruct H; auto. }
  assert (1 <= x0) by nia. nia.
Qed.

Definition biggest_prime_divisor_le (max n: Z) : Z -> Prop :=
  fun m => let P x := prime x /\ Z.divide x n /\ x <= max in
           P m /\ forall k, P k -> k <= m.

Definition biggest_prime_divisor (n : Z) : Z -> Prop :=
  fun m => let P x := prime x /\ Z.divide x n in
           P m /\ forall k, P k -> k <= m.

Definition factorization_max (k n : Z) (Hn : 2 <= n) (Hk : 2 <= k) : option (Z * Z) :=
  match (factorization k n) with
  | nil => None
  | p :: _ => Some p
  end.

Theorem factorization_thm11 (k n : Z) (Hn : 2 <= n) (Hk : 2 <= k) :
  match factorization k n with
  | [] => True
  | p :: _ => biggest_prime_divisor_le k n (fst p)
  end.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k.
  apply Z_lt_induction; auto; intros.
  assert (x = 2 \/ 3 <= x) by lia. destruct H1.
  + subst. clear H0. rewrite factorization_equation. simpl.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - simpl. rewrite repeated_repeated_div_equation in d. simpl in d.
      destruct Z_le_dec; try lia. unfold biggest_prime_divisor_le.
      constructor. refine (conj prime_2 (conj d _)). lia.
      intros. tauto.
    - rewrite repeated_repeated_div_equation in n0. destruct Z_le_dec; try lia. simpl in n0.
      rewrite factorization_equation. simpl. destruct Z_le_dec; try lia.
  + rewrite factorization_equation. destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - assert (x = x - 1 + 1) by ring. rewrite H2 in d at 1.
      rewrite repeated_repeated_div_main_thm in d; try lia. rewrite <- H2 in d.
      unfold biggest_prime_divisor_le. simpl. constructor. destruct d.
      refine (conj H3 (conj H4 _)). lia.
      lia.
    - assert (0 <= x - 1 < x). { abstract lia. }
      assert (2 <= x - 1). { abstract lia. }
      pose proof (H0 _ H2 _ Hn H3).
      remember (factorization (x - 1) n) as W.
      destruct W; auto. unfold biggest_prime_divisor_le in *.
      destruct H4 as [[H4 [H5 H6]] H7]. constructor.
      * refine (conj H4 (conj H5 _)). lia.
      * intros. assert (x = x - 1 + 1) by ring.
        assert (~ prime x \/ ~ (x | n)).
        { rewrite H9 in n1 at 1. rewrite repeated_repeated_div_main_thm in n1; try lia.
          rewrite <- H9 in n1. tauto. }
        destruct H10.
        ++ destruct H8 as [H8 [H12 H13]]. assert (x <> k0). { congruence. }
           apply H7; auto. refine (conj H8 (conj H12 _)). lia.
        ++ destruct H8 as [H8 [H12 H13]]. assert (x <> k0). { congruence. }
           apply H7; auto. refine (conj H8 (conj H12 _)). lia.
Qed.

Theorem factorization_thm12 (n : Z) (Hn : 2 <= n) :
  match factorization n n with
  | [] => False
  | p :: _ => biggest_prime_divisor n (fst p)
  end.
Proof.
  remember (factorization n n) as L. destruct L.
  - symmetry in HeqL. apply factorization_thm10 in HeqL; try lia.
  - pose proof (factorization_thm11 n n Hn Hn). unfold factorization_max in H.
    rewrite <- HeqL in H. unfold biggest_prime_divisor_le, biggest_prime_divisor in *.
    intuition. apply H1; try lia. refine (conj H4 (conj H5 _)).
    destruct H5. destruct H4. assert (1 <= x) by nia. nia.
Qed.


Theorem factorization_thm13 (n k p : Z) (Hn : 1 <= n) (Hk : 2 <= k)
  (Hp : prime p) (Hp0 : k < p) :
  factorization k (p * n) = factorization k n.
Proof.
  assert (0 <= k) by lia. revert Hk Hp0 n Hn. pattern k. apply Z_lt_induction; auto; intros. clear H k.
  assert (x = 2 \/ 3 <= x) by lia. destruct H.
  + subst. rewrite factorization_equation. simpl.
    rewrite (factorization_equation 2). simpl.
    rewrite repeated_repeated_div_equation. simpl.
    rewrite repeated_repeated_div_equation. simpl.
    rewrite factorization_equation. simpl.
    rewrite factorization_equation. simpl.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    repeat destruct Zdivide_dec.
    - rewrite Z.mul_comm. rewrite <- repeated_div_thm7 with (a := p); try lia; auto.
      apply rel_prime_sym. apply rel_prime_le_prime; try lia; auto.
    - apply prime_mult in d; try (apply prime_2). destruct d; try tauto.
      apply prime_alt in Hp. destruct Hp. exfalso. revert H. apply H2. lia.
    - exfalso. apply n0; clear n0. destruct d. subst n. exists (p * x). ring.
    - auto.
  + pose proof (factorization_thm4 n x ltac:(lia) ltac:(lia)).
    pose proof (factorization_thm4 (p * n) x ltac:(nia) ltac:(lia)).
    destruct prime_dec.
    - destruct Zdivide_dec.
      * assert (x | p * n). { destruct d. subst n. exists (p * x0); ring. }
        destruct Zdivide_dec; try tauto.
        rewrite H1, H2. rewrite H0; try lia. f_equal. f_equal.
        rewrite Z.mul_comm. rewrite <- repeated_div_thm7 with (a := p); try lia.
        apply rel_prime_sym. apply rel_prime_le_prime; auto; try lia.
      * assert (~ (x | p * n)).
        { intro. apply n0. apply prime_mult in H3; auto. destruct H3; auto.
          apply prime_alt in Hp. destruct Hp. exfalso. revert H3. apply H5. lia. }
        destruct Zdivide_dec; try tauto. rewrite H1, H2. rewrite H0; try lia. auto.
    - rewrite H2, H1. rewrite H0; try lia. auto.
Qed.

Theorem factorization_thm13' (n k p i : Z) (Hn : 1 <= n) (Hk : 2 <= k) (Hi : 0 <= i)
  (Hp : prime p) (Hp0 : k < p) : factorization k (n * p ^ i) = factorization k n.
Proof.
  assert (0 <= i) by auto. revert Hi. pattern i. apply Z_lt_induction; auto; intros. clear i H.
  assert (x = 0 \/ 1 <= x) by lia. destruct H.
  + subst. simpl. f_equal. ring.
  + replace x with (x - 1 + 1) by ring. rewrite Z.pow_add_r; try lia.
    replace (n * (p ^ (x - 1) * p ^ 1)) with (p * (n * p ^ (x - 1))) by ring.
    rewrite factorization_thm13; try lia; auto.
    apply H0; try lia.
Qed.

Theorem factorization_thm14_aux (x n w : Z) (Hn : 2 <= n) (Hx : 2 <= x) (Hx0 : prime x) (Hw : 0 <= w) :
  factorization (x - 1) (x ^ w * snd (repeated_div x n)) =
  factorization (x - 1) (snd (repeated_div x n)).
Proof.
  assert (0 <= w) by auto. revert Hw. pattern w. apply Z_lt_induction; auto; intros. clear w H.
  assert (x0 = 0 \/ 1 <= x0) by lia. destruct H.
  + subst. simpl. f_equal. ring.
  + replace x0 with (x0 - 1 + 1) by ring. rewrite Z.pow_add_r; try lia.
    replace (x ^ (x0 - 1) * x ^ 1 * snd (repeated_div x n)) with
          (x * (x ^ (x0 - 1) * snd (repeated_div x n))) by ring.
    assert (x = 2 \/ 3 <= x) by lia. destruct H1.
    - subst. simpl in *. rewrite (factorization_equation 1). simpl.
      rewrite (factorization_equation). simpl. repeat destruct Z_le_dec; auto.
    - rewrite factorization_thm13; try lia; auto.
      * apply H0; lia.
      * assert (1 <= snd (repeated_div x n)). { apply repeated_div_thm1. lia. }
        nia.
Qed.

Theorem factorization_thm14 (k n : Z) (Hn : 2 <= n) (Hk : 2 <= k) :
  match factorization k n with
  | [] => True
  | p :: t => t = factorization (fst p - 1) (snd (repeated_div (fst p) n))
  end.
Proof.
  assert (0 <= k) by lia. revert n Hn Hk. pattern k.
  apply Z_lt_induction; auto; intros. clear H k.
  pose proof (factorization_thm4 n x ltac:(lia) ltac:(lia)).
  destruct prime_dec.
  + destruct Zdivide_dec.
    - rewrite H; simpl. pose proof (repeated_div_main_thm x n ltac:(lia) ltac:(lia)).
      rewrite H1 at 1. assert (0 <= fst (repeated_div x n)). { apply repeated_div_thm0. }
      apply factorization_thm14_aux; try lia; auto.
    - rewrite H. assert (x = 2 \/ 2 < x) by lia. destruct H1.
      * subst. simpl. rewrite (factorization_equation 1). simpl. destruct Z_le_dec; auto.
      * apply H0; try lia.
  + rewrite H. assert (x = 2 \/ 2 < x) by lia. destruct H1.
    - subst. simpl. rewrite (factorization_equation 1). simpl. destruct Z_le_dec; auto.
    - apply H0; try lia.
Qed.

Theorem factorization_max_thm0 (n k : Z) (Hn0 : 2 <= n) (Hn : prime n) (Hk : 2 <= k) (Hk0 : k < n) :
  factorization_max k n Hn0 Hk = None.
Proof.
  assert (0 <= k) by lia. revert Hk Hk0. pattern k. apply Z_lt_induction; auto; intros. clear k H.
  assert (x = 2 \/ 2 < x) by lia. destruct H.
  + subst. clear H0. unfold factorization_max. rewrite factorization_equation.
    destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec.
    - rewrite repeated_repeated_div_equation in d. simpl in d.
      destruct Z_le_dec; try lia. exfalso. destruct d. subst.
      destruct Hn. pose proof (H0 2 ltac:(lia)).
      unfold rel_prime in H1. inversion H1.
      assert (2 | 1). { apply H4. exists 1. ring. exists x; ring. }
      destruct H5. lia.
    - rewrite factorization_equation. simpl. destruct Z_le_dec; try lia. auto.
  + unfold factorization_max. rewrite factorization_equation. destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - exfalso. assert (x | n).
      { apply repeated_repeated_div_thm4 in d; try lia. exact d. }
      destruct H1. subst. destruct Hn. pose proof (H2 x0 ltac:(nia)).
      inversion H3. assert (1 < x0) by nia.
      assert (x0 | 1). { apply H6. exists 1; ring. exists x; ring. }
      destruct H8. assert (1 <= x1) by nia. nia.
    - pose proof (H0 (x - 1)).
      assert (0 <= x - 1 < x) by lia. assert (2 <= x - 1) by lia.
      assert (x - 1 < n) by lia. pose proof (H1 H2 H3 H4).
      unfold factorization_max in H5. auto.
Qed.

Theorem factorization_max_thm1 (n : Z) (Hn : 2 <= n) (Hn0 : prime n) :
  factorization_max _ _ Hn Hn = Some (n, 1).
Proof.
  pose proof (factorization_thm4 n n ltac:(lia) ltac:(lia)).
  destruct prime_dec; try tauto. destruct Zdivide_dec.
  + unfold factorization_max. rewrite H. simpl. f_equal. f_equal.
    rewrite repeated_div_equation. destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
    rewrite Z_div_same; try lia. rewrite repeated_div_equation.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Zdivide_dec.
    - destruct d1. assert (0 < x) by nia. nia.
    - auto.
  + exfalso. apply n0. exists 1. ring.
Qed.

Definition max_divisor (n : Z) : Z * Z :=
  if (Z_le_dec 2 n)
  then match (factorization n n) with
       | nil => (1, 0)
       | p :: t => p
       end
  else (1, 0).

Theorem max_divisor_div (n : Z) : (fst (max_divisor n) | n).
Proof.
  unfold max_divisor. destruct Z_le_dec.
  + remember (factorization n n) as W. destruct W.
    - simpl. exists n. ring.
    - pose proof (factorization_thm12 n l). rewrite <- HeqW in H.
      destruct H. tauto.
  + simpl. exists n. ring.
Qed.

Theorem one_le_max_divisor (n : Z): 1 <= fst (max_divisor n).
Proof.
  unfold max_divisor. destruct Z_le_dec.
  + remember (factorization n n) as W. destruct W.
    - simpl. lia.
    - pose proof (factorization_thm12 n l). rewrite <- HeqW in H.
      destruct H. destruct H. destruct H. lia.
  + simpl. lia.
Qed.

Theorem max_divisor_prime (n : Z) (Hn : 2 <= n) : prime (fst (max_divisor n)).
Proof.
  unfold max_divisor. destruct Z_le_dec; try lia.
  remember (factorization n n) as W. destruct W.
  + pose proof (factorization_thm12 n l). rewrite <- HeqW in H. elim H.
  + assert (In p (factorization n n)). { rewrite <- HeqW. simpl. auto. }
    apply (factorization_thm3 n n); try lia. auto.
Qed.
  
  
Definition max_divisor_le (k n : Z) : Z * Z :=
  if (Z_le_dec 2 n)
  then if (Z_le_dec 2 k)
       then match (factorization k n) with
            | nil => (1, 0)
            | p :: t => p
            end
       else (1, 0)
  else (1, 0).


(* loop invariant tinkering *)

Inductive state N (H: 2 <= N): Z -> Z -> nat -> Prop :=
 | Start: state N H (fst (max_divisor_le 3 N)) (repeated_repeated_div 3 N) 0
 | Loop: forall h n i, (6 * Z.of_nat i + 5) * (6 * Z.of_nat i + 5) <= n ->
         state N H h n i ->
         state N H (fst (max_divisor_le (6 * Z.of_nat i + 9) N))
           (snd (repeated_div (6 * Z.of_nat i + 7) (snd (repeated_div (6 * Z.of_nat i + 5) n))))
           (i + 1).

Definition is_loop_invariant (loop_inv: Z -> Z -> Prop) :=
  forall N H n i h (s: state N H h n i), loop_inv n (Z.of_nat i).

Definition loop_invariant n i :=
  (n = 1) \/ ((6 * i + 5) * (6 * i + 5) <= n) \/
  let m := repeated_repeated_div (6 * i + 4) n in
  let W := fst (max_divisor m) in
  (~ Z.divide (W * W) m /\ (~ prime (W - 2) \/ ~ Z.divide (W - 2) m)).

Theorem state_thm0 N H h n i:
  state N H h n i -> n = repeated_repeated_div (6 * Z.of_nat i + 4) N.
Proof.
  intros. induction H0.
  + simpl. rewrite (repeated_repeated_div_thm8 4 N); try lia.
    - reflexivity.
    - intro. apply prime_alt in H0. destruct H0.
      pose proof (H1 2 ltac:(lia)). apply H2. exists 2. ring.
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

Theorem state_thm1 N H h n i: state N H h n i -> h = fst (max_divisor_le (6 * Z.of_nat i + 3) N).
Proof.
  intro. induction H0.
  + simpl. auto.
  + rewrite Nat2Z.inj_add. simpl. ring_simplify (6 * (Z.of_nat i + 1) + 3). auto.
Qed.

Theorem correct_loop_invariant: is_loop_invariant loop_invariant.
Proof.
  unfold is_loop_invariant, loop_invariant. intros.
  induction s.
  + destruct (Z.eq_dec (repeated_repeated_div 3 N) 1); try tauto.
    right. simpl. destruct (Z_le_dec 25 (repeated_repeated_div 3 N)); try tauto.
    right. assert (repeated_repeated_div 3 N < 25) by lia. clear n0.
    assert (1 <= N) by lia.
    pose proof (repeated_repeated_div_thm0 3 N H1).
    remember (repeated_repeated_div 3 N) as W.
    assert (In W [2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24]).
    { simpl. lia. }
    simpl in H3.
    split.
    - rewrite repeated_repeated_div_thm8; try lia. simpl.
      * destruct H3 as [H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|H3]]]]]]]]]]]]]]]]]]]]]]].
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { rewrite <- H3. exists 1. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (3 | repeated_repeated_div 3 N). { rewrite <- H3. exists 1. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { rewrite <- H3. exists 2. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 5) with 5 by reflexivity.
           replace (fst (max_divisor 5)) with 5 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { rewrite <- H3. exists 3. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 7) with 7 by reflexivity.
           replace (fst (max_divisor 7)) with 7 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { rewrite <- H3. exists 4. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (3 | repeated_repeated_div 3 N). { rewrite <- H3. exists 3. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 10) with 5 by reflexivity.
           replace (fst (max_divisor 5)) with 5 by reflexivity. intro. destruct H4. lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 11) with 11 by reflexivity.
           replace (fst (max_divisor 11)) with 11 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { rewrite <- H3. exists 6. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 13) with 13 by reflexivity.
           replace (fst (max_divisor 13)) with 13 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { rewrite <- H3. exists 7. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (3 | repeated_repeated_div 3 N). { rewrite <- H3. exists 5. lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { exists 8; lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 17) with 17 by reflexivity.
           replace (fst (max_divisor 17)) with 17 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { exists 9; lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 19) with 19 by reflexivity.
           replace (fst (max_divisor 19)) with 19 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { exists 10; lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (3 | repeated_repeated_div 3 N). { exists 7; lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { exists 11; lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ rewrite <- H3. replace (repeated_repeated_div 3 23) with 23 by reflexivity.
           replace (fst (max_divisor 23)) with 23 by reflexivity. intro. destruct H4. lia.
        ++ exfalso. subst.
           assert (2 | repeated_repeated_div 3 N). { exists 12; lia. }
           apply repeated_repeated_div_thm3 in H4; try lia.
        ++ elim H3.
      * intro. apply prime_alt in H4. destruct H4. pose proof (H5 2).
        apply H6. lia. exists 2. auto.
    - assert (~ prime 4).
      { intro. apply prime_alt in H4. destruct H4. pose proof (H5 2).
        apply H6; try lia. exists 2; auto. }
      rewrite repeated_repeated_div_thm8; try lia; auto. simpl.
      destruct H3 as [H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|H3]]]]]]]]]]]]]]]]]]]]]]].
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * right. rewrite <- H3. simpl. intro. apply repeated_repeated_div_thm1 in H5; lia.
      * rewrite <- H3. simpl. left. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 7) with 7 by reflexivity.
        replace (fst (max_divisor 7)) with 7 by reflexivity. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 10) with 5 by reflexivity.
        replace (fst (max_divisor 5)) with 5 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 11) with 11 by reflexivity.
        replace (fst (max_divisor 11)) with 11 by reflexivity. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 13) with 13 by reflexivity.
        replace (fst (max_divisor 13)) with 13 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 14) with 7 by reflexivity.
        replace (fst (max_divisor 7)) with 7 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 15) with 5 by reflexivity.
        replace (fst (max_divisor 5)) with 5 by reflexivity. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 17) with 17 by reflexivity.
        replace (fst (max_divisor 17)) with 17 by reflexivity. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 19) with 19 by reflexivity.
        replace (fst (max_divisor 19)) with 19 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 20) with 5 by reflexivity.
        replace (fst (max_divisor 5)) with 5 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 21) with 7 by reflexivity.
        replace (fst (max_divisor 7)) with 7 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 22) with 11 by reflexivity.
        replace (fst (max_divisor 11)) with 11 by reflexivity. intro. destruct H5. lia.
      * right. rewrite <- H3. replace (repeated_repeated_div 3 23) with 23 by reflexivity.
        replace (fst (max_divisor 23)) with 23 by reflexivity. intro. destruct H5. lia.
      * left. rewrite <- H3. simpl. intro. destruct H5. lia.
      * elim H3.
  + rewrite Nat2Z.inj_add. simpl. remember (Z.of_nat i) as X.
    pose proof (state_thm0 _ _ _ _ _ s). pose proof (state_thm1 _ _ _ _ _ s).
    clear IHs. rewrite <- HeqX in H1. rewrite <- HeqX in H2. subst n h. clear s.
    assert (snd (repeated_div (6 * X + 7) (snd (repeated_div (6 * X + 5) (repeated_repeated_div (6 * X + 4) N)))) =
      repeated_repeated_div (6 * X + 10) N).
    { assert (~ prime (6 * X + 10)).
      { intro. apply prime_alt in H1. destruct H1. pose proof (H2 2 ltac:(lia)).
        apply H3. exists (3 * X + 5); ring. }
      rewrite (repeated_repeated_div_thm8 (6 * X + 10)); try lia; auto.
      ring_simplify (6 * X + 10 - 1).
      assert (~ prime (6 * X + 9)).
      { intro. apply prime_alt in H2. destruct H2. pose proof (H3 3 ltac:(lia)).
        apply H4. exists (2 * X + 3); ring. }
      rewrite (repeated_repeated_div_thm8 (6 * X + 9)); try lia; auto.
      ring_simplify (6 * X + 9 - 1).
      assert (~ prime (6 * X + 8)).
      { intro. apply prime_alt in H3. destruct H3. pose proof (H4 2 ltac:(lia)).
        apply H5. exists (3 * X + 4); ring. }
      rewrite (repeated_repeated_div_thm8 (6 * X + 8)); try lia; auto.
      ring_simplify (6 * X + 8 - 1).
      rewrite (repeated_repeated_div_equation (6 * X + 7) N).
      destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
      f_equal. f_equal. ring_simplify (6 * X + 7 - 1).
      assert (~ prime (6 * X + 6)).
      { intro. apply prime_alt in H4. destruct H4. pose proof (H5 2 ltac:(lia)).
        apply H6. exists (3 * X + 3); ring. }
      rewrite (repeated_repeated_div_thm8 (6 * X + 6)); try lia; auto.
      ring_simplify (6 * X + 6 - 1).
      rewrite (repeated_repeated_div_equation (6 * X + 5) N).
      destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
      ring_simplify (6 * X + 5 - 1). reflexivity. }
    rewrite H1. clear H1. ring_simplify (6 * (X + 1) + 5). ring_simplify (6 * (X + 1) + 4).
    assert (repeated_repeated_div (6 * X + 10) (repeated_repeated_div (6 * X + 10) N) =
            repeated_repeated_div (6 * X + 10) N).
    { rewrite repeated_repeated_div_thm14; try lia. }
    rewrite H1. clear H1.
    destruct (Z.eq_dec (repeated_repeated_div (6  * X + 10) N) 1); try tauto. right.
    assert (1 < repeated_repeated_div (6 * X + 10) N).
    { pose proof (repeated_repeated_div_thm0 (6 * X + 10) N). lia. }
    apply repeated_repeated_div_thm12 in H1; try lia. clear n.
    destruct (Z_le_dec ((6 * X + 11) * (6 * X + 11)) (repeated_repeated_div (6 * X + 10) N)); try tauto.
    right. assert (repeated_repeated_div (6 * X + 10) N < (6 * X + 11) * (6 * X + 11)) by lia.
    clear n. remember (repeated_repeated_div (6 * X + 10) N) as W.
    destruct (Zdivide_dec (fst (max_divisor W) * fst (max_divisor W)) W).
    - destruct (Z_le_dec (6 * X + 11) (fst (max_divisor W))).
      * destruct d. assert (1 <= x) by nia. nia.
      * assert (fst (max_divisor W) <= 6 * X + 10) by lia. clear n.
        pose proof (max_divisor_div W).
        rewrite HeqW in H4 at 2. apply repeated_repeated_div_thm10 in H4; try lia.
        unfold max_divisor. destruct Z_le_dec; try lia.
        remember (factorization W W) as L. destruct L.
        -- pose proof (factorization_thm12 W l). rewrite <- HeqL in H5. elim H5.
        -- pose proof (factorization_thm12 W l). rewrite <- HeqL in H5.
           destruct H5. destruct H5. destruct H5. auto.
    - constructor; try tauto.
      destruct (prime_dec (fst (max_divisor W) - 2)); try tauto.
      right. intro. pose proof (max_divisor_div W).
      destruct (Z_le_dec (6 * X + 11) (fst (max_divisor W) - 2)).
      * assert (6 * X + 13 <= fst (max_divisor W)) by lia.
        assert ((fst (max_divisor W) - 2) * fst (max_divisor W) | W).
        { apply aux1; try lia; auto.
          unfold rel_prime. constructor.
          + exists (fst (max_divisor W) - 2). ring.
          + exists (fst (max_divisor W)). ring.
          + intros. apply prime_divisors in H6; auto.
            destruct H6 as [H6 | [H6 | [H6 | H6]]]; subst x.
            * exists (-1). ring.
            * exists 1. ring.
            * exfalso. destruct H7.
              assert (2 = (x - 1) * fst (max_divisor W)) by nia.
              nia.
            * exfalso. destruct H7.
              assert (2 = (-x - 1) * fst (max_divisor W)) by nia.
              nia. }
        destruct H6. assert (1 <= 6 * X + 11) by lia.
        assert (1 <= 6 * X + 13) by lia. assert (1 <= W) by lia.
        assert (1 < fst (max_divisor W) - 2). { destruct p; auto. }
        assert (1 <= x) by nia.
        assert ((6 * X + 11) * (6 * X + 13) <= (fst (max_divisor W) - 2) * fst (max_divisor W))
          by nia. nia. 
      * assert (fst (max_divisor W) < 6 * X + 13) by lia. clear n0.
        assert (fst (max_divisor W) = 6 * X + 11).
        { assert (prime (fst (max_divisor W))). { apply max_divisor_prime;  auto. lia. }
          assert (fst (max_divisor W) <> 6 * X + 12).
          { intro. pose proof (max_divisor_prime W ltac:(lia)).
            rewrite H7 in H8. apply prime_alt in H8. destruct H8.
            pose proof (H9 2 ltac:(lia)). apply H10. exists (3 * X + 6). ring. }
          assert (6 * X + 10 < fst (max_divisor W)).
          { rewrite HeqW in H4 at 2. apply repeated_repeated_div_thm10 in H4; try lia.
            destruct H6; auto. }
          lia. }
        rewrite H6 in H3. ring_simplify (6 * X + 11 - 2) in H3.
        rewrite HeqW in H3. apply repeated_repeated_div_thm10 in H3; try lia.
Qed.



Definition type1 (N : Z) : Prop :=
  let W := repeated_repeated_div 3 N in
  W = 1 \/ (fst (max_divisor W) * fst (max_divisor W) | W) \/
  (prime (fst (max_divisor W) - 2) /\ ((fst (max_divisor W) - 2) | W)).

Theorem TTT_aux00 (N i k : Z) (HN : 1 <= N) (Hi : 2 <= i) (Hk : i <= k) : 
  repeated_repeated_div i N = 1 -> factorization k N = factorization i N.
Proof.
  assert (0 <= k) by lia. revert Hk. pattern k. apply Z_lt_induction; auto; intros. clear H k.
  assert (forall k, i <= k -> repeated_repeated_div k N = 1).
  { intros. apply repeated_repeated_div_thm17 with (i := i); try lia. }
  assert (x = i \/ i < x) by lia. destruct H2.
  + congruence.
  + rewrite (factorization_equation). destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia. destruct Zdivide_dec.
    - rewrite H in d; try lia. destruct d. assert (1 <= x0) by nia. nia.
    - rewrite H0; try lia. reflexivity.
Qed.

Theorem TTT_aux01 (N k : Z) (Hk : 2 <= k <= N) :
  repeated_repeated_div k N = 1 -> max_divisor N = max_divisor_le k N.
Proof.
  intros. unfold max_divisor, max_divisor_le. destruct Z_le_dec; try lia.
  destruct Z_le_dec; try lia. rewrite TTT_aux00 with (i := k); try lia; auto.
Qed.

(*
Fixpoint decreasing (L : list Z) : Prop :=
  match L with
  | x :: (y :: t as L') => x > y /\ decreasing L'
  | _ => True
  end.

Theorem TTT_aux02 (N k : Z) (HN : 1 <= N) (Hk : 2 <= k) :
  decreasing (List.map fst (factorization k N)).
Proof. Admitted.
*)

Theorem TTT_aux02 (N k : Z) (HN : 1 <= N) (Hk : prime k) :
  max_divisor_le (k - 1) N = max_divisor_le (k - 1) (snd (repeated_div k N)).
Proof.
  pose proof (repeated_div_main_thm k N ltac:(destruct Hk; lia) HN).
  rewrite H at 1. unfold max_divisor_le. destruct Z_le_dec.
  + destruct Z_le_dec.
    - destruct Z_le_dec.
      * rewrite (factorization_thm14_aux); try lia; auto. apply repeated_div_thm0.
      * rewrite (factorization_thm14_aux); try lia; auto.
        ++ assert (1 <= snd (repeated_div k N)). { apply repeated_div_thm1; lia. }
           assert (snd (repeated_div k N) = 1) by lia. rewrite H1.
           rewrite (factorization_of_one); try lia. auto.
        ++ apply repeated_div_thm0.
    - destruct Z_le_dec; auto.
  + destruct Z_le_dec.
    - rewrite <- H in n. assert (N = 1) by lia. exfalso. rewrite H0 in l.
      rewrite repeated_div_equation in l. destruct Z_le_dec.
      * destruct Z_le_dec; try lia. destruct Zdivide_dec.
        ++ destruct d. assert (0 < x) by nia. nia.
        ++ simpl in l. lia.
      * simpl in l. lia.
    - auto.
Qed.

Theorem TTT_aux03 (N k : Z) (HN : 1 <= N) (Hk : 2 <= k) (Hk0 : ~ prime k) :
  max_divisor_le k N = max_divisor_le (k - 1) N.
Proof.
  unfold max_divisor_le. destruct Z_le_dec.
  + destruct Z_le_dec; try lia.
    destruct Z_le_dec.
    - pose proof (factorization_thm4 N k ltac:(lia) ltac:(lia)).
      destruct prime_dec; try tauto. rewrite H. auto.
    - assert (k = 2) by lia. subst. elim Hk0. exact prime_2.
 + auto.
Qed.

Theorem TTT_aux04 (N k : Z) (HN : 1 <= N) (Hk : 2 <= k) (Hk0: ~ (k | N)) :
  max_divisor_le k N = max_divisor_le (k - 1) N.
Proof.
  unfold max_divisor_le. destruct Z_le_dec.
  + destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    - pose proof (factorization_thm4 N k ltac:(lia) ltac:(lia)).
      destruct Zdivide_dec; try tauto. destruct prime_dec; rewrite H; auto.
    - assert (k = 2) by lia. subst. rewrite factorization_equation. simpl.
      destruct Z_le_dec; try lia. rewrite repeated_repeated_div_equation.
      simpl. destruct Z_le_dec; try lia. destruct Zdivide_dec; try tauto.
      rewrite factorization_equation. simpl. destruct Z_le_dec; try auto.
  + auto.
Qed.

Theorem TTT_aux05 (N k p i : Z) (HN : 1 <= N) (Hk : 2 <= k) (Hp : prime p) (Hpk : k < p)
  (hi : 0 <= i) : max_divisor_le k (N * p ^ i) = max_divisor_le k N.
Proof.
  unfold max_divisor_le. rewrite factorization_thm13'; try lia; auto.
  destruct Z_le_dec.
  + destruct Z_le_dec; try lia. destruct Z_le_dec.
    - auto.
    - assert (N = 1) by lia. subst N. rewrite factorization_of_one; try lia. auto.
  + destruct Z_le_dec; try lia. auto.
Qed.

Theorem TTT_aux06 (N k x : Z) (HN : 1 <= N) (Hk : 2 <= k) (Hx : k <= x) :
  (forall w, k < w <= x -> prime w -> (w | N) -> False) ->
  max_divisor_le x N = max_divisor_le k N.
Proof.
  intro. assert (0 <= x) by lia. revert H Hx. pattern x.
  apply Z_lt_induction; auto; intros. clear x H0.
  assert (x0 = k \/ k < x0) by lia. destruct H0.
  + subst x0. auto.
  + assert (forall w : Z, k < w <= x0 - 1 -> prime w -> (w | N) -> False).
    { intros. apply H1 with (w := w); auto. lia. }
    pose proof (H (x0 - 1) ltac:(lia) H2 ltac:(lia)). clear H.
    unfold max_divisor_le in *. destruct Z_le_dec; auto.
    destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
    destruct Z_le_dec; try lia.
    pose proof (factorization_thm4 N x0 ltac:(lia) ltac:(lia)).
    destruct (prime_dec x0).
    - destruct Zdivide_dec.
      * exfalso. revert d. apply H1; auto. lia.
      * rewrite H. auto.
    - rewrite H. auto.
Qed.

Theorem TTT N H h n i (H': 2 <= N):
  let W := fst (max_divisor N) in
  let W' := fst (max_divisor (snd (repeated_div W N))) in
  forall (s: state N H h n i), n < (6 * Z.of_nat i + 5) * (6 * Z.of_nat i + 5) ->
  (type1 N <-> (h, n) = (W, 1)) /\ (~ type1 N <-> (h, n) = (W', W)).
Proof.
  pose proof correct_loop_invariant as HL. unfold is_loop_invariant, loop_invariant in HL.
  intros. unfold type1. pose proof (state_thm0 _ _ _ _ _ s) as P0.
  pose proof (state_thm1 _ _ _ _ _ s) as P1. revert H0 P0 P1. induction s.
  + clear HL. intros P1 _ _. simpl in *. pose proof (repeated_repeated_div_thm0 3 N ltac:(lia)).
    remember (repeated_repeated_div 3 N) as M.
    assert (In M [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24]).
    { simpl. lia. }
    simpl in H1.
    destruct H1 as [H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|[H3|H3]]]]]]]]]]]]]]]]]]]]]]]].
    - rewrite <- H3 in *. simpl.
      assert ((1 = 1 \/ (1 | 1) \/ prime (-1) /\ (-1 | 1)) <-> True) by tauto.
      rewrite H1. constructor.
      * constructor; auto. intro. f_equal. unfold W. assert (N = 2 \/ 3 <= N) by lia. destruct H4.
        ++ rewrite H4; reflexivity.
        ++ rewrite TTT_aux01 with (k := 3); try lia.
      * constructor; try tauto. intros. intros _. clear H1.
        unfold W', W in H2. assert (N = 2 \/ 3 <= N) by lia. destruct H1.
        ++ rewrite H1 in H2. simpl in H2. congruence.
        ++ pose proof (TTT_aux01 N 3 ltac:(lia) ltac:(lia)).
           inversion H2; clear H2. pose proof (max_divisor_prime N H).
           destruct H2. lia.
    - exfalso. assert (3 < repeated_repeated_div 3 N).
      { apply repeated_repeated_div_thm12; try lia. }
      lia.
    - exfalso. assert (3 < repeated_repeated_div 3 N).
      { apply repeated_repeated_div_thm12; try lia. }
      lia.
    - exfalso. assert (2 | repeated_repeated_div 3 N).
      { exists 2. lia. }
      apply repeated_repeated_div_thm10 in H1; try lia.
    - rewrite <- H3. simpl.
      assert ((5 = 1 \/ (25 | 5) \/ prime 3 /\ (3 | 5)) <-> False).
      { intuition.
        + destruct H1; try lia.
        + destruct H4; try lia. }
      rewrite H1. intuition.
      * inversion H6.
      * clear H4 H1 H2 H5 H6. rewrite <- H3 in HeqM.
        assert (N = 2 \/ N = 3 \/ N = 4 \/ 5 <= N) by lia. destruct H1 as [H1|[H1|[H1|H1]]].
        ++ rewrite H1 in HeqM. inversion HeqM.
        ++ rewrite H1 in HeqM. inversion HeqM.
        ++ rewrite H1 in HeqM. inversion HeqM.
        ++ assert (W = 5).
           { unfold W. rewrite TTT_aux01 with (k := 5); try lia.
             + unfold max_divisor. unfold max_divisor_le. destruct Z_le_dec; try lia. simpl.
               rewrite factorization_equation. destruct Z_le_dec; try lia; simpl.
               destruct Zdivide_dec.
               - simpl. reflexivity.
               - exfalso. apply n; clear n. rewrite repeated_repeated_div_thm8; try lia.
                 * simpl. exists 1. lia.
                 * intro. apply prime_alt in H2. destruct H2. pose proof (H4 2 ltac:(lia)).
                   apply H5. exists 2. reflexivity.
             + rewrite repeated_repeated_div_equation. simpl. destruct Z_le_dec; try lia.
               rewrite repeated_repeated_div_thm8; try lia.
               - simpl. rewrite <- HeqM. simpl. reflexivity.
               - intro. apply prime_alt in H2. destruct H2. pose proof (H4 2 ltac:(lia)).
                 apply H5. exists 2. auto. }
           rewrite H2 in *. f_equal. unfold W'. rewrite H2. f_equal.
           pose proof (repeated_div_main_thm 5 N ltac:(lia) ltac:(lia)).
           rewrite H4 at 1. rewrite Z.mul_comm.
           rewrite TTT_aux05; try lia.
           -- clear M P1 H0 H3 W' W H2.
              assert (forall x, max_divisor x = max_divisor_le x x).
              { intros. unfold max_divisor, max_divisor_le. destruct Z_le_dec; auto. }
              rewrite H0; clear H0.
              assert (1 <= snd (repeated_div 5 N)). { apply repeated_div_thm1; lia. }
              remember (snd (repeated_div 5 N)) as W.
              assert (W = 1 \/ W = 2 \/ W = 3 \/ 3 < W) by lia. destruct H2 as [H2|[H2|[H2|H2]]].
              ** rewrite H2. reflexivity.
              ** rewrite H2. reflexivity.
              ** rewrite H2. reflexivity.
              ** assert (prime 5). { apply prime_alt. constructor. lia.
                   intros. intro. destruct H5. assert (n = 2 \/ n = 3 \/ n = 4) by lia. lia. }
                 symmetry. rewrite TTT_aux06 with (k := 3); auto; try lia.
                 intros. rewrite H4 in HeqM.
                 assert (repeated_repeated_div 3 (5 ^ fst (repeated_div 5 N) * W) =
                         5 ^ fst (repeated_div 5 N) * repeated_repeated_div 3 W).
                 { rewrite repeated_repeated_div_equation. simpl.
                   rewrite repeated_repeated_div_equation. simpl.
                   rewrite repeated_repeated_div_equation. simpl.
                   rewrite repeated_repeated_div_equation. simpl.
                   rewrite repeated_repeated_div_equation. simpl.
                   rewrite repeated_repeated_div_equation. simpl.
                   destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
                   rewrite Z.mul_comm, factorization_thm4_aux0'; try lia; auto.
                   + rewrite factorization_thm4_aux0'; try lia; auto.
                     - apply repeated_div_thm1; auto.
                     - apply repeated_div_thm0.
                   + apply repeated_div_thm0. }
                 rewrite H8 in HeqM; clear H8.
                 assert (~ (5 | repeated_repeated_div 3 W)).
                 { intro. assert (5 | W).
                   { apply repeated_repeated_div_thm4 in H8; try lia; auto. }
                   rewrite HeqW in H9. apply repeated_div_thm2 in H9; try lia. }
                 assert (5 ^ fst (repeated_div 5 N) | 5).
                 { rewrite HeqM at 3. exists (repeated_repeated_div 3 W). ring. }
                 assert (0 < 5 ^ fst (repeated_div 5 N)).
                 { apply Z.pow_pos_nonneg; try lia. apply repeated_div_thm0. }
                 apply prime_divisors in H9; try lia; auto.
                 destruct H9 as [H9|[H9|[H9|H9]]]; try lia.
                 +++ rewrite H9 in HeqM. apply H8. rewrite HeqM. exists 1. ring.
                 +++ rewrite H9 in HeqM. assert (repeated_repeated_div 3 W = 1) by lia.
                     assert (forall n, 3 < n -> prime n -> (n | W) -> False).
                     { intros. pose proof (repeated_repeated_div_main_thm (n - 1) W
                       ltac:(lia) ltac:(lia)). ring_simplify (n - 1 + 1) in H15.
                       assert (n | repeated_repeated_div (n - 1) W) by tauto.
                       assert (repeated_repeated_div (n - 1) W = 1).
                       { apply repeated_repeated_div_thm17 with (i := 3); try lia. }
                       rewrite H17 in H16. destruct H16. assert (0 < x) by nia. nia. }
                     apply H12 with (n := w); auto. lia.
           -- apply prime_alt. constructor; try lia. intros. intro.
              assert (n = 2 \/ n = 3 \/ n = 4) by lia. destruct H6. lia.
           -- apply repeated_div_thm0.
    - exfalso. assert (2 | repeated_repeated_div 3 N).
      { exists 3. lia. }
      apply repeated_repeated_div_thm10 in H1; try lia.
    - rewrite <- H3. simpl.
      assert ((7 = 1 \/ (49 | 7) \/ prime 5 /\ (5 | 7)) <-> False).
      { intuition.
        + destruct H1. lia.
        + destruct H4. lia. }
      rewrite H1. intuition.
      * inversion H6.
      * clear H4 H1 H2 H5 H6. unfold W, W'.
      
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
    RETURN (Vlong (Int64.repr (fst (max_divisor n))))
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

Definition loop_invariant_candidate n i :=
  (n = 1) \/ ((6 * i + 5) * (6 * i + 5) <= n) \/
  let m := repeated_repeated_div (6 * i + 4) n in
  let W := fst (max_divisor m) in
  (~ Z.divide (W * W) m /\ (~ prime (W - 2) \/ ~ Z.divide (W - 2) m)).

Lemma find_proof: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function. assert (Int64.max_unsigned = 18446744073709551615) as HH by auto.
  assert (1 <= n) by lia. forward. forward_call. forward_call.
  + split.
    - assert (1 <= 2) by lia. 
      pose proof (repeated_div_thm1 2 n H1). lia.
    - unfold new_highest. destruct Zdivide_dec; [destruct Z_le_dec |]; try lia.
  + autorewrite with norm.
    set (repeated_repeated_div 3 n) as W.
    set (W = 1 \/ (Z.divide (fst (max_divisor W) ^ 2) W \/
         prime (fst (max_divisor W) - 2) /\ Z.divide (fst (max_divisor W) - 2) W)) as P.
    assert ({P} + {~ P}).
    { unfold P. destruct (Z.eq_dec W 1).
      + left. auto.
      + destruct (Zdivide_dec (fst (max_divisor W) ^ 2) W).
        - left. auto.
        - destruct (prime_dec (fst (max_divisor W) - 2)).
          * destruct (Zdivide_dec (fst (max_divisor W) - 2) W).
            ++ left. auto.
            ++ right. tauto.
          * tauto. }
    - forward_if (
      if H2
      then PROP ()
           LOCAL (temp _n (Vlong (Int64.repr 1)); gvars gv)
           SEP (data_at Ews tulong (Vlong (Int64.repr (fst (max_divisor W)))) (gv _highest))
      else PROP ()
           LOCAL (temp _n (Vlong (Int64.repr (fst (max_divisor W)))); gvars gv)
           SEP (data_at Ews tulong (Vlong (Int64.repr (fst (max_divisor (snd (repeated_div n (fst (max_divisor W)))))))) (gv _highest))
      ).
      * 
        admit.
      * admit.
      * destruct H2.
        ++ admit.
        ++ admit.
Admitted.
