Require Import Znumtheory ZArith Lia Recdef.
Open Scope Z.

Theorem aux f (Hf: 2 <= f) n (Hn: 1 <= n): Z.divide f n -> 1 <= n / f.
Proof.
  intros [x Hx]. subst. replace (x * f / f) with x. nia.
  symmetry. apply Z_div_mult. lia.
Qed.

Function repeated_div' f (Hf: 2 <= f) n (Hn: 1 <= n) { measure Z.to_nat n }: Z * Z :=
  match Zdivide_dec f n with
  | left H => let (i, k) := repeated_div' f Hf (n / f) (aux f Hf n Hn H) in (i + 1, k)
  | right _ => (0, n)
  end.
Proof.
  intros. destruct H. subst. rewrite Z_div_mult; try nia.
Defined.

Definition repeated_div f n :=
  match Z_le_dec 2 f with
  | left H1 => match Z_le_dec 1 n with
               | left H2 => repeated_div' f H1 n H2
               | _ => (0, n)
               end
  | _ => (0, n)
  end.

Function repeated_repeated_div (i n: Z) (H: 1 <= n) { measure Z.to_nat i }: Z :=
  if Z_le_dec i 1
  then n
  else snd (repeated_div i (repeated_repeated_div (i - 1) _ H)).
Proof. lia. Defined.

Theorem repeated_div'_aux f n1 n2 (Hf1 Hf2: 2 <= f) (Hn1: 1 <= n1) (Hn2: 1 <= n2) (H: n1 = n2):
  repeated_div' f Hf1 n1 Hn1 = repeated_div' f Hf2 n2 Hn2.
Proof.
  subst. assert (0 <= n2) by lia. revert Hn1 Hn2. pattern n2. apply Z_lt_induction; auto. clear H. intros.
  rewrite repeated_div'_equation at 1. rewrite repeated_div'_equation at 1.
  destruct Zdivide_dec; auto. destruct d; subst.
  assert (0 <= x0 < x0 * f). { split; try lia. nia. }
  pose (H _ H0). remember (repeated_div' f Hf1 (x0 * f / f) _) as W1.
  remember (repeated_div' f Hf2 (x0 * f / f) _) as W2. destruct W1, W2.
  assert (repeated_div' f Hf1 (x0 * f / f) (aux f Hf1 (x0 * f) Hn1 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl)) =
          repeated_div' f Hf2 (x0 * f / f) (aux f Hf2 (x0 * f) Hn2 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl))).
  { apply H. rewrite Z_div_mult; try lia. }
  congruence.
Qed.

Theorem Zle_0_repeated_div' f n (Hf: 2 <= f) (Hn: 1 <= n): 0 <= fst (repeated_div' f Hf n Hn).
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n. apply Z_lt_induction; auto. clear H.
  intros. rewrite repeated_div'_equation. destruct Zdivide_dec; try (simpl; lia).
  remember (repeated_div' f Hf (x / f) (aux f Hf x Hn d)) as W. destruct W. simpl.
  assert (0 <= x / f < x). { split. apply Z_div_nonneg_nonneg; lia. apply Z.div_lt; lia. }
  assert (1 <= x / f). { destruct d. subst. rewrite Z_div_mult; nia. }
  assert (repeated_div' f Hf (x / f) (aux f Hf x Hn d) = repeated_div' f Hf (x / f) H1).
  { apply repeated_div'_aux; auto. }
  pose proof (H _ H0 H1). do 2 destruct repeated_div'. inversion HeqW; inversion H2; subst. simpl in *. lia.
Qed.

Theorem repeated_div_thm f n (H: 2 <= f) (H': 1 <= n): n = f ^ fst (repeated_div f n) * snd (repeated_div f n).
Proof.
  unfold repeated_div. repeat destruct Z_le_dec. clear H H'. assert (0 <= n) by lia. revert l0.
  pattern n. apply Z_lt_induction; auto. clear H. intros.
  rewrite repeated_div'_equation. destruct Zdivide_dec.
  + destruct d. subst. assert (0 <= x0 < x0 * f). { split. lia. nia. }
    assert (1 <= x0) by nia. pose proof (H _ H0 H1). rewrite H2 at 1.
    assert (f ^ fst (repeated_div' f l x0 H1) * snd (repeated_div' f l x0 H1) * f =
            f ^ (fst (repeated_div' f l x0 H1) + 1) * snd (repeated_div' f l x0 H1)).
    { rewrite Zmult_comm. rewrite Zmult_assoc. rewrite (Zmult_comm f).
      assert (f ^ fst (repeated_div' f l x0 H1) * f = f ^ fst (repeated_div' f l x0 H1) * f ^ 1).
      { f_equal. lia. }
      rewrite H3. rewrite <- Z.pow_add_r; try lia. apply Zle_0_repeated_div'. }
    rewrite H3. clear H3.
    assert (repeated_div' f l (x0 * f / f) (aux f l (x0 * f) l0 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl)) =
            repeated_div' f l x0 H1).
    { apply repeated_div'_aux. rewrite Z_div_mult; lia. }
    rewrite H3. clear H3. destruct (repeated_div' f l x0 H1). simpl. auto.
  + simpl (fst (0, x)). simpl (snd (0, x)). lia.
  + simpl (fst (0, n)). simpl (snd (0, n)). lia.
  + simpl (fst (0, n)). simpl (snd (0, n)). lia.
Qed.

Lemma repeated_div_snd_thm (n: Z) (H: 1 <= n) f (H0: 2 <= f): 1 <= snd (repeated_div f n) <= n.
Proof.
  split.
  + unfold repeated_div. repeat destruct Z_le_dec; try lia. assert (0 <= n) by lia. revert l0. 
    pattern n. apply Z_lt_induction; auto. clear H H1. intros.
    rewrite repeated_div'_equation. destruct Zdivide_dec.
    - assert (snd (let (i, k) := repeated_div' f l (x / f) (aux f l x l0 d) in (i + 1, k)) =
              snd (repeated_div' f l (x / f) (aux f l x l0 d))).
      { destruct repeated_div'. simpl. auto. }
      rewrite H1; clear H1. destruct d. apply H. subst.
      rewrite Z_div_mult; try lia. nia.
    - simpl. auto.
  + unfold repeated_div. repeat destruct Z_le_dec; try lia. assert (0 <= n) by lia. revert l0.
    pattern n. apply Z_lt_induction; auto. clear H H1. intros.
    rewrite repeated_div'_equation. destruct Zdivide_dec.
    - assert (snd (let (i, k) := repeated_div' f l (x / f) (aux f l x l0 d) in (i + 1, k)) =
              snd (repeated_div' f l (x / f) (aux f l x l0 d))).
      { destruct repeated_div'. simpl. auto. }
      rewrite H1; clear H1. destruct d. subst.
      assert (0 <= x0 < x0 * f) by nia. assert (1 <= x0) by lia. pose (H _ H1 H2).
      assert (repeated_div' f l x0 H2 =
              repeated_div' f l (x0 * f / f) (aux f l (x0 * f) l0 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl))).
      { apply repeated_div'_aux. rewrite Z_div_mult; try lia. }
      rewrite <- H3. nia.
    - simpl. lia.
Qed.

Theorem repeated_div_aux_thm0 (i n: Z) (H: 1 <= n): 1 <= repeated_repeated_div i n H.
Proof.
  destruct (Z_le_dec i 1).
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
  + assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H1.
    rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
    assert (x = 2 \/ 2 <= x - 1) by lia. destruct H1.
    - subst. apply repeated_div_snd_thm; auto. lia.
    - apply repeated_div_snd_thm; auto. apply H0. lia. lia. lia.
    - lia.
Qed.

Theorem repeated_div_thm2 f n (H: 2 <= f) (H': 1 <= n): Z.divide f (snd (repeated_div f n)) -> False.
Proof.
  intros. unfold repeated_div in *. repeat destruct Z_le_dec; try lia. clear H H'.
  assert (0 <= n) by lia. revert l0 H0. pattern n. apply Z_lt_induction; auto. clear H. intros.
  destruct H0. rewrite repeated_div'_equation in H0. destruct Zdivide_dec in *.
  + destruct d. subst. assert (0 <= x1 * f / f < x1 * f). { rewrite Z_div_mult; nia. }
    assert (1 <= x1 * f / f). { rewrite Z_div_mult; nia. }
    pose (H _ H1 H2). apply f0. clear f0. exists x0. remember (repeated_div' _ l _ _) as W in H0.
    destruct W. simpl in H0. subst.
    assert (repeated_div' f l (x1 * f / f) (aux f l (x1 * f) l0 (ex_intro (fun z : Z => x1 * f = z * f) x1 eq_refl)) =
            repeated_div' f l (x1 * f / f) H2) by (apply repeated_div'_aux; lia).
    rewrite <- HeqW in H0. rewrite <- H0. auto.
  + simpl in H0. apply n0. subst. exists x0. auto.
Qed.

Theorem repeated_div_aux_thm1 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide i (repeated_repeated_div i n H) -> False.
Proof.
  intros. rewrite repeated_repeated_div_equation in H1. destruct Z_le_dec in H1; try lia.
  apply repeated_div_thm2 in H1; auto. apply repeated_div_aux_thm0.
Qed.

Theorem repeated_div_thm3 f n (H: 2 <= f) (H0: 1 <= n):
  Z.divide (snd (repeated_div f n)) n.
Proof.
  exists (f ^ fst (repeated_div f n)). apply repeated_div_thm; auto.
Qed.

Theorem repeated_div_aux_thm2 (i n w: Z) (H: 1 <= n) (H0: 2 <= i) (H1: 0 <= w):
  forall i, 2 <= i <= i + w -> (i | repeated_repeated_div (i + w) n H) -> False.
Proof.
  pattern w. apply Z_lt_induction; auto; intros. clear H1 w.
  assert (x = 0 \/ 1 <= x) by lia. destruct H1.
  + subst. ring_simplify (i0 + 0) in H4. apply repeated_div_aux_thm1 in H4; lia.
  + rewrite repeated_repeated_div_equation in H4. destruct Z_le_dec in H4; try lia.
    assert (0 <= x - 1 < x) by lia. assert (2 <= i0 <= i0 + (x - 1)) by lia.
    pose proof (H2 _ H5 _ H6). ring_simplify (i0 + (x - 1)) in H7.
    assert (2 <= i0 + x) by lia.
    assert (1 <= repeated_repeated_div (i0 + x - 1) n H) by apply (repeated_div_aux_thm0).
    pose proof (repeated_div_thm3 _ _ H8 H9). apply H7.
    eapply Z.divide_trans; eauto.
Qed.

Theorem repeated_div_aux_thm3 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  forall x, 2 <= x <= i -> (x | repeated_repeated_div i n H) -> False.
Proof.
  intros. replace i with (x + (i - x)) in H2 by lia.
  eapply repeated_div_aux_thm2 in H2; eauto. lia. lia.
Qed.

Theorem repeated_div_aux_thm4 (i n x: Z) (H: 1 <= n) (H0: 2 <= i) (H1: 2 <= x):
  Z.divide x (repeated_repeated_div i n H) -> Z.divide x n.
Proof.
  assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H2 i.
  rewrite repeated_repeated_div_equation in H4. destruct Z_le_dec in H4; auto.
  assert (x | repeated_repeated_div (x0 - 1) n H).
  { destruct H4. exists (x1 * x0 ^ fst (repeated_div x0 (repeated_repeated_div (x0 - 1) n H))).
    rewrite Zmult_comm. rewrite Zmult_assoc. rewrite (Zmult_comm x). rewrite <- H2.
    rewrite Zmult_comm. rewrite <- repeated_div_thm; try lia.
    apply repeated_div_aux_thm0. }
  assert (x0 = 2 \/ 2 <= x0 - 1) by lia. destruct H5.
  + subst. simpl in *. rewrite repeated_repeated_div_equation in H2.
    destruct Z_le_dec in H2; try lia. auto.
  + apply H0 in H2; auto. lia.
Qed.

Theorem repeated_div_aux_thm5 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide (i + 1) (repeated_repeated_div i n H) -> prime (i + 1) /\ Z.divide (i + 1) n.
Proof.
  intros. split.
  + destruct (prime_dec (i + 1)); auto. exfalso. apply not_prime_divide in n0; try lia.
    destruct n0 as [k [H2 H3]]. destruct H3. assert (Z.divide k (repeated_repeated_div i n H)).
    { destruct H1. exists (x0 * x). lia. }
    apply repeated_div_aux_thm3 in H4; auto. lia.
  + eapply repeated_div_aux_thm4; eauto. lia.
Qed.

Theorem aux_thm0 a b n (Ha: 0 < a) (Hb: 0 < b): rel_prime a b -> Z.divide a n -> Z.divide b n -> Z.divide a (n / b).
Proof.
  intros. destruct H1. subst. rewrite Z_div_mult; try lia.
  eapply Gauss. rewrite Zmult_comm in H0. eauto. auto.
Qed.

Theorem Zle_1_repeated_div' f n (Hf: 2 <= f) (Hn: 1 <= n) (H: Z.divide f n): 1 <= fst (repeated_div' f Hf n Hn).
Proof.
  rewrite repeated_div'_equation. destruct Zdivide_dec; try tauto.
  pose proof (Zle_0_repeated_div' f (n / f)).
  assert (1 <= n / f). { destruct H. subst. rewrite Z_div_mult; nia. }
  assert (repeated_div' f Hf (n / f) H1 = repeated_div' f Hf (n / f) (aux f Hf n Hn d)).
  { apply repeated_div'_aux; auto. }
  rewrite <- H2. pose proof (Zle_0_repeated_div' f (n / f) Hf H1). destruct repeated_div'. simpl in *. lia.
Qed.

Theorem aux_thm1 a b n (H: 1 <= n) (Ha: 2 <= a) (Hb: 2 <= b):
  rel_prime a b -> Z.divide a n -> Z.divide b n -> Z.divide a (snd (repeated_div b n)).
Proof.
  intros. assert (1 <= fst (repeated_div b n)).
  { unfold repeated_div. repeat destruct Z_le_dec; try lia. apply Zle_1_repeated_div'; auto. }
  assert (rel_prime a (b ^ fst (repeated_div b n))).
  { remember (fst (repeated_div b n)) as W. assert (0 <= W) by lia. revert H3.
    pattern W. apply Z_lt_induction; auto; intros.
    assert (x = 1 \/ 1 <= x - 1) by lia. destruct H6.
    + subst. replace (b ^ 1) with b by lia. auto.
    + replace x with ((x - 1) + 1) by ring. rewrite Z.pow_add_r; try lia. replace (b ^ 1) with b by lia.
      apply rel_prime_mult.
      - apply H3. lia. auto.
      - auto. }
  replace (snd (repeated_div b n)) with (n / b ^ fst (repeated_div b n)).
  + apply aux_thm0; try lia. auto. auto. rewrite repeated_div_thm with (f:=b) (n:=n) at 2; auto.
    exists (snd (repeated_div b n)). ring.
  + rewrite repeated_div_thm with (f:=b) (n:=n) at 1; auto. rewrite Zmult_comm. rewrite Z_div_mult; auto.
    assert (0 < b ^ fst (repeated_div b n)). { apply Z.pow_pos_nonneg; try lia. }
    lia.
Qed.

Theorem rel_prime_aux a b n (H: 0 <= n): rel_prime a b -> rel_prime a (b ^ n).
Proof.
  intro. pose proof H. revert H1. pattern n. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H3.
  + subst. simpl. apply rel_prime_sym. apply rel_prime_1.
  + replace (b ^ x) with (b ^ (x - 1) * b).
    - apply rel_prime_mult; auto. apply H1; try lia.
    - replace b with (b ^ 1) at 2 by lia. rewrite <- Z.pow_add_r; try lia.
      replace (x - 1 + 1) with x by ring. auto.
Qed.

Theorem repeated_div_aux_thm6 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  prime (i + 1) -> Z.divide (i + 1) n -> Z.divide (i + 1) (repeated_repeated_div i n H).
Proof.
  intros. destruct H1. remember (i + 1) as W. assert (0 <= i) by lia. assert (i < W) by lia.
  revert H5. pattern i. apply Z_lt_induction; auto; intros.
  assert (2 <= x \/ x <= 1) by lia. destruct H7.
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
    assert (W | repeated_repeated_div (x - 1) n H).
    { apply H5. lia. lia. }
    destruct H8. remember (repeated_repeated_div (x - 1) n H) as X.
    eapply Gauss. exists x0. rewrite <- H8. rewrite repeated_div_thm with (f := x); eauto.
    - rewrite HeqX. apply repeated_div_aux_thm0.
    - apply rel_prime_aux.
      * unfold repeated_div. repeat destruct Z_le_dec; try lia.
        ++ apply Zle_0_repeated_div'.
        ++ simpl. lia.
      * apply rel_prime_sym. apply H3. lia.
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. auto.
Qed.

Theorem repeated_div_aux_thm7 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide (i + 1) (repeated_repeated_div i n H) <-> prime (i + 1) /\ Z.divide (i + 1) n.
Proof.
  split.
  + apply repeated_div_aux_thm5; auto.
  + intros [H1 H2]. apply repeated_div_aux_thm6; auto.
Qed.
