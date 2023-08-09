Require Import VST.floyd.proofauto.
Require Import Znumtheory.
Open Scope Z.

Theorem repeated_div'_aux f (Hf: 2 <= f) n (Hn: 1 <= n): Z.divide f n -> 1 <= n / f.
Proof.
  intros [x Hx]. subst. replace (x * f / f) with x. nia.
  symmetry. apply Z_div_mult. lia.
Qed.

Function repeated_div' f (Hf: 2 <= f) n (Hn: 1 <= n) { measure Z.to_nat n }: Z * Z :=
  match Zdivide_dec f n with
  | left H => let (i, k) := repeated_div' f Hf (n / f) (repeated_div'_aux f Hf n Hn H) in (i + 1, k)
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

Function prime_divisor_list (i n: Z) (H: 1 <= n) { measure Z.to_nat i}: list Z :=
  let W := prime_divisor_list (i - 1) n H in
  if Z_le_dec i 1
  then []
  else if Zdivide_dec i (repeated_repeated_div (i - 1) n H)
       then cons i W
       else W.
Proof.
  lia. lia.
Defined.


Theorem repeated_div'_thm0 f n1 n2 (Hf1 Hf2: 2 <= f) (Hn1: 1 <= n1) (Hn2: 1 <= n2) (H: n1 = n2):
  repeated_div' f Hf1 n1 Hn1 = repeated_div' f Hf2 n2 Hn2.
Proof.
  subst. assert (0 <= n2) by lia. revert Hn1 Hn2. pattern n2. apply Z_lt_induction; auto. clear H. intros.
  rewrite repeated_div'_equation at 1. rewrite repeated_div'_equation at 1.
  destruct Zdivide_dec; auto. destruct d; subst.
  assert (0 <= x0 < x0 * f). { split; try lia. nia. }
  pose (H _ H0). remember (repeated_div' f Hf1 (x0 * f / f) _) as W1.
  remember (repeated_div' f Hf2 (x0 * f / f) _) as W2. destruct W1, W2.
  assert (repeated_div' f Hf1 (x0 * f / f) (repeated_div'_aux f Hf1 (x0 * f) Hn1 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl)) =
          repeated_div' f Hf2 (x0 * f / f) (repeated_div'_aux f Hf2 (x0 * f) Hn2 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl))).
  { apply H. rewrite Z_div_mult; try lia. }
  congruence.
Qed.

Theorem repeated_div'_thm1 f n (Hf: 2 <= f) (Hn: 1 <= n): 0 <= fst (repeated_div' f Hf n Hn).
Proof.
  assert (0 <= n) by lia. revert Hn. pattern n. apply Z_lt_induction; auto. clear H.
  intros. rewrite repeated_div'_equation. destruct Zdivide_dec; try (simpl; lia).
  remember (repeated_div' f Hf (x / f) (repeated_div'_aux f Hf x Hn d)) as W. destruct W. simpl.
  assert (0 <= x / f < x). { split. apply Z_div_nonneg_nonneg; lia. apply Z.div_lt; lia. }
  assert (1 <= x / f). { destruct d. subst. rewrite Z_div_mult; nia. }
  assert (repeated_div' f Hf (x / f) (repeated_div'_aux f Hf x Hn d) = repeated_div' f Hf (x / f) H1).
  { apply repeated_div'_thm0; auto. }
  pose proof (H _ H0 H1). do 2 destruct repeated_div'. inversion HeqW; inversion H2; subst. simpl in *. lia.
Qed.

Theorem repeated_div_thm0 f n (H: 2 <= f) (H': 1 <= n): n = f ^ fst (repeated_div f n) * snd (repeated_div f n).
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
      rewrite H3. rewrite <- Z.pow_add_r; try lia. apply repeated_div'_thm1. }
    rewrite H3. clear H3.
    assert (repeated_div' f l (x0 * f / f) (repeated_div'_aux f l (x0 * f) l0 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl)) =
            repeated_div' f l x0 H1).
    { apply repeated_div'_thm0. rewrite Z_div_mult; lia. }
    rewrite H3. clear H3. destruct (repeated_div' f l x0 H1). simpl. auto.
  + simpl (fst (0, x)). simpl (snd (0, x)). lia.
  + simpl (fst (0, n)). simpl (snd (0, n)). lia.
  + simpl (fst (0, n)). simpl (snd (0, n)). lia.
Qed.

Lemma repeated_div_thm1 (n: Z) (H: 1 <= n) f (H0: 2 <= f): 1 <= snd (repeated_div f n) <= n.
Proof.
  split.
  + unfold repeated_div. repeat destruct Z_le_dec; try lia. assert (0 <= n) by lia. revert l0. 
    pattern n. apply Z_lt_induction; auto. clear H H1. intros.
    rewrite repeated_div'_equation. destruct Zdivide_dec.
    - assert (snd (let (i, k) := repeated_div' f l (x / f) (repeated_div'_aux f l x l0 d) in (i + 1, k)) =
              snd (repeated_div' f l (x / f) (repeated_div'_aux f l x l0 d))).
      { destruct repeated_div'. simpl. auto. }
      rewrite H1; clear H1. destruct d. apply H. subst.
      rewrite Z_div_mult; try lia. nia.
    - simpl. auto.
  + unfold repeated_div. repeat destruct Z_le_dec; try lia. assert (0 <= n) by lia. revert l0.
    pattern n. apply Z_lt_induction; auto. clear H H1. intros.
    rewrite repeated_div'_equation. destruct Zdivide_dec.
    - assert (snd (let (i, k) := repeated_div' f l (x / f) (repeated_div'_aux f l x l0 d) in (i + 1, k)) =
              snd (repeated_div' f l (x / f) (repeated_div'_aux f l x l0 d))).
      { destruct repeated_div'. simpl. auto. }
      rewrite H1; clear H1. destruct d. subst.
      assert (0 <= x0 < x0 * f) by nia. assert (1 <= x0) by lia. pose (H _ H1 H2).
      assert (repeated_div' f l x0 H2 =
              repeated_div' f l (x0 * f / f) (repeated_div'_aux f l (x0 * f) l0 (ex_intro (fun z : Z => x0 * f = z * f) x0 eq_refl))).
      { apply repeated_div'_thm0. rewrite Z_div_mult; try lia. }
      rewrite <- H3. nia.
    - simpl. lia.
Qed.

Theorem repeated_repeated_div_thm0 (i n: Z) (H: 1 <= n): 1 <= repeated_repeated_div i n H.
Proof.
  destruct (Z_le_dec i 1).
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
  + assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H1.
    rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
    assert (x = 2 \/ 2 <= x - 1) by lia. destruct H1.
    - subst. apply repeated_div_thm1; auto. lia.
    - apply repeated_div_thm1; auto. apply H0. lia. lia. lia.
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
    assert (repeated_div' f l (x1 * f / f) (repeated_div'_aux f l (x1 * f) l0 (ex_intro (fun z : Z => x1 * f = z * f) x1 eq_refl)) =
            repeated_div' f l (x1 * f / f) H2) by (apply repeated_div'_thm0; lia).
    rewrite <- HeqW in H0. rewrite <- H0. auto.
  + simpl in H0. apply n0. subst. exists x0. auto.
Qed.

Theorem repeated_repeated_div_thm1 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide i (repeated_repeated_div i n H) -> False.
Proof.
  intros. rewrite repeated_repeated_div_equation in H1. destruct Z_le_dec in H1; try lia.
  apply repeated_div_thm2 in H1; auto. apply repeated_repeated_div_thm0.
Qed.

Theorem repeated_div_thm3 f n (H: 2 <= f) (H0: 1 <= n): Z.divide (snd (repeated_div f n)) n.
Proof.
  exists (f ^ fst (repeated_div f n)). apply repeated_div_thm0; auto.
Qed.

Theorem repeated_repeated_div_thm2 (i n w: Z) (H: 1 <= n) (H0: 2 <= i) (H1: 0 <= w):
  forall i, 2 <= i <= i + w -> (i | repeated_repeated_div (i + w) n H) -> False.
Proof.
  pattern w. apply Z_lt_induction; auto; intros. clear H1 w.
  assert (x = 0 \/ 1 <= x) by lia. destruct H1.
  + subst. ring_simplify (i0 + 0) in H4. apply repeated_repeated_div_thm1 in H4; lia.
  + rewrite repeated_repeated_div_equation in H4. destruct Z_le_dec in H4; try lia.
    assert (0 <= x - 1 < x) by lia. assert (2 <= i0 <= i0 + (x - 1)) by lia.
    pose proof (H2 _ H5 _ H6). ring_simplify (i0 + (x - 1)) in H7.
    assert (2 <= i0 + x) by lia.
    assert (1 <= repeated_repeated_div (i0 + x - 1) n H) by apply (repeated_repeated_div_thm0).
    pose proof (repeated_div_thm3 _ _ H8 H9). apply H7.
    eapply Z.divide_trans; eauto.
Qed.

Theorem repeated_repeated_div_thm3 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  forall x, 2 <= x <= i -> (x | repeated_repeated_div i n H) -> False.
Proof.
  intros. replace i with (x + (i - x)) in H2 by lia.
  eapply repeated_repeated_div_thm2 in H2; eauto. lia. lia.
Qed.

Theorem repeated_repeated_div_thm4 (i n x: Z) (H: 1 <= n) (H0: 2 <= i) (H1: 2 <= x):
  Z.divide x (repeated_repeated_div i n H) -> Z.divide x n.
Proof.
  assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros. clear H2 i.
  rewrite repeated_repeated_div_equation in H4. destruct Z_le_dec in H4; auto.
  assert (x | repeated_repeated_div (x0 - 1) n H).
  { destruct H4. exists (x1 * x0 ^ fst (repeated_div x0 (repeated_repeated_div (x0 - 1) n H))).
    rewrite Zmult_comm. rewrite Zmult_assoc. rewrite (Zmult_comm x). rewrite <- H2.
    rewrite Zmult_comm. rewrite <- repeated_div_thm0; try lia.
    apply repeated_repeated_div_thm0. }
  assert (x0 = 2 \/ 2 <= x0 - 1) by lia. destruct H5.
  + subst. simpl in *. rewrite repeated_repeated_div_equation in H2.
    destruct Z_le_dec in H2; try lia. auto.
  + apply H0 in H2; auto. lia.
Qed.

Theorem repeated_repeated_div_thm5 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide (i + 1) (repeated_repeated_div i n H) -> prime (i + 1) /\ Z.divide (i + 1) n.
Proof.
  intros. split.
  + destruct (prime_dec (i + 1)); auto. exfalso. apply not_prime_divide in n0; try lia.
    destruct n0 as [k [H2 H3]]. destruct H3. assert (Z.divide k (repeated_repeated_div i n H)).
    { destruct H1. exists (x0 * x). lia. }
    apply repeated_repeated_div_thm3 in H4; auto. lia.
  + eapply repeated_repeated_div_thm4; eauto. lia.
Qed.

Theorem different_Gauss a b n (Ha: 0 < a) (Hb: 0 < b): rel_prime a b -> Z.divide a n -> Z.divide b n -> Z.divide a (n / b).
Proof.
  intros. destruct H1. subst. rewrite Z_div_mult; try lia.
  eapply Gauss. rewrite Zmult_comm in H0. eauto. auto.
Qed.

Theorem repeated_div'_thm2 f n (Hf: 2 <= f) (Hn: 1 <= n) (H: Z.divide f n): 1 <= fst (repeated_div' f Hf n Hn).
Proof.
  rewrite repeated_div'_equation. destruct Zdivide_dec; try tauto.
  pose proof (repeated_div'_thm0 f (n / f)).
  assert (1 <= n / f). { destruct H. subst. rewrite Z_div_mult; nia. }
  assert (repeated_div' f Hf (n / f) H1 = repeated_div' f Hf (n / f) (repeated_div'_aux f Hf n Hn d)).
  { apply repeated_div'_thm0; auto. }
  rewrite <- H2. pose proof (repeated_div'_thm1 f (n / f) Hf H1). destruct repeated_div'. simpl in *. lia.
Qed.

Theorem repeated_div_thm4 a b n (H: 1 <= n) (Ha: 2 <= a) (Hb: 2 <= b):
  rel_prime a b -> Z.divide a n -> Z.divide b n -> Z.divide a (snd (repeated_div b n)).
Proof.
  intros. assert (1 <= fst (repeated_div b n)).
  { unfold repeated_div. repeat destruct Z_le_dec; try lia. apply repeated_div'_thm2; auto. }
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
  + apply different_Gauss; try lia. auto. auto. rewrite repeated_div_thm0 with (f:=b) (n:=n) at 2; auto.
    exists (snd (repeated_div b n)). ring.
  + rewrite repeated_div_thm0 with (f:=b) (n:=n) at 1; auto. rewrite Zmult_comm. rewrite Z_div_mult; auto.
    assert (0 < b ^ fst (repeated_div b n)). { apply Z.pow_pos_nonneg; try lia. }
    lia.
Qed.

Theorem rel_prime_thm0 a b n (H: 0 <= n): rel_prime a b -> rel_prime a (b ^ n).
Proof.
  intro. pose proof H. revert H1. pattern n. apply Z_lt_induction; auto; intros.
  assert (x = 0 \/ 1 <= x) by lia. destruct H3.
  + subst. simpl. apply rel_prime_sym. apply rel_prime_1.
  + replace (b ^ x) with (b ^ (x - 1) * b).
    - apply rel_prime_mult; auto. apply H1; try lia.
    - replace b with (b ^ 1) at 2 by lia. rewrite <- Z.pow_add_r; try lia.
      replace (x - 1 + 1) with x by ring. auto.
Qed.

Theorem repeated_repeated_div_thm6 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  prime (i + 1) -> Z.divide (i + 1) n -> Z.divide (i + 1) (repeated_repeated_div i n H).
Proof.
  intros. destruct H1. remember (i + 1) as W. assert (0 <= i) by lia. assert (i < W) by lia.
  revert H5. pattern i. apply Z_lt_induction; auto; intros.
  assert (2 <= x \/ x <= 1) by lia. destruct H7.
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
    assert (W | repeated_repeated_div (x - 1) n H).
    { apply H5. lia. lia. }
    destruct H8. remember (repeated_repeated_div (x - 1) n H) as X.
    eapply Gauss. exists x0. rewrite <- H8. rewrite repeated_div_thm0 with (f := x); eauto.
    - rewrite HeqX. apply repeated_repeated_div_thm0.
    - apply rel_prime_thm0.
      * unfold repeated_div. repeat destruct Z_le_dec; try lia.
        ++ apply repeated_div'_thm1.
        ++ simpl. lia.
      * apply rel_prime_sym. apply H3. lia.
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia. auto.
Qed.

Theorem repeated_repeated_div_main_thm (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide (i + 1) (repeated_repeated_div i n H) <-> prime (i + 1) /\ Z.divide (i + 1) n.
Proof.
  split.
  + apply repeated_repeated_div_thm5; auto.
  + intros [H1 H2]. apply repeated_repeated_div_thm6; auto.
Qed.

Theorem repeated_repeated_div_thm7 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ prime i) -> (~ Z.divide i (repeated_repeated_div (i - 1) n H)).
Proof.
  intros. intro. apply H1. replace i with ((i - 1) + 1) in H2 at 1 by ring. replace i with ((i - 1) + 1) by ring.
  assert (i = 2 \/ 2 <= i - 1) by lia. destruct H3.
  + subst. exfalso. apply H1. apply prime_2.
  + apply repeated_repeated_div_main_thm in H2. tauto. lia.
Qed.

Theorem repeated_div'_thm3 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ Z.divide i n) -> snd (repeated_div' i H0 n H) = n.
Proof.
  intros. assert (0 <= n) by lia. revert H H1. pattern n. apply Z_lt_induction; auto; intros.
  rewrite repeated_div'_equation. destruct Zdivide_dec.
  + tauto.
  + simpl. auto.
Qed.

Theorem repeated_repeated_div_thm8 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  (~ prime i) -> repeated_repeated_div i n H = repeated_repeated_div (i - 1) n H.
Proof.
  intros. eapply repeated_repeated_div_thm7 with (n:=n) (H:=H) in H1; eauto.
  rewrite repeated_repeated_div_equation at 1. destruct Z_le_dec; try lia.
  unfold repeated_div. repeat destruct Z_le_dec; try lia.
  + rewrite repeated_div'_thm3; auto.
  + simpl. auto.
Qed.


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


Definition max_of_list (L: list Z): Z := fold_right Z.max 0 L.

(* prime_dec does not compute :( *)
Definition all_prime_divisors (n: Z) := filter prime_dec (filter (fun x => Zdivide_dec x n) (Zseq n)).

Definition factorization (n: Z) (H: 1 <= n): list Z :=
  flat_map (fun x => repeat x (Z.to_nat (fst (repeated_div x n)))) (all_prime_divisors n).

Definition brute_force (n: Z) := max_of_list (all_prime_divisors n).

Definition biggest_prime_divisor (n m: Z) :=
  let P x := prime x /\ Z.divide x n in P m /\ forall k, P k -> k <= m.

Theorem In_max_thm (L: list Z) x (H: In x L): x <= max_of_list L.
Proof.
  induction L.
  + elim H.
  + simpl. destruct H; try lia. pose (IHL H). lia.
Qed.

Theorem max_In_thm (L: list Z) x (H: max_of_list L = x) (H0: L <> []) (H1: forall w, In w L -> 1 <= w):
  In x L.
Proof.
  revert x H H0. induction L; intros.
  + elim H0; auto.
  + simpl in *. clear H0. assert (forall w, In w L -> 1 <= w). { intros. apply H1. auto. }
    rewrite Zmax_spec in H. destruct zlt in H; auto. subst. pose proof (IHL H0). destruct L.
    - simpl in *. clear H H0. assert (a = a \/ False) by auto. apply H1 in H. lia.
    - simpl in *. clear IHL. pose proof (H _ (eq_refl (Z.max z (max_of_list L)))).
      assert (z :: L <> []) by congruence. apply H2 in H3. destruct H3.
      * rewrite <- H3. auto.
      * auto.
Qed.

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
  assert (prime (max_of_list (all_prime_divisors n))).
  { pose proof (max_In_thm (all_prime_divisors n)).
    eapply H5 in H4; eauto.
    + apply filter_In in H4. destruct H4. destruct prime_dec in H6; simpl in *; try congruence.
    + intros. apply filter_In in H6. destruct H6. destruct prime_dec in H7; simpl in *; try congruence.
      destruct p. lia. }
  repeat split.
  + destruct H5. auto.
  + exists n0; lia.
  + exists (max_of_list (all_prime_divisors n)). lia.
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
    pose proof (eq_refl (max_of_list (all_prime_divisors n))).
    apply H6 in H7. clear H6.
    - apply filter_In in H7. destruct H7. apply filter_In in H6. destruct H6.
      destruct Zdivide_dec in H8; simpl in *; try congruence.
    - auto.
    - intros. apply filter_In in H8. destruct H8. destruct prime_dec in H9; simpl in *; try congruence.
      destruct p. lia.
  + intros. destruct H6. pose (H0 _ H6 H7). apply In_max_thm. auto.
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
    PROP (2 <= n <= Int64.max_unsigned; 0 <= h <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n))
    GLOBALS (gv)
    SEP (data_at Ews tulong (Vlong (Int64.repr h)) (gv _highest))
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (brute_force n)))
    SEP (TT).


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
    - f_equal. f_equal. unfold repeated_div. destruct Z_le_dec; try lia. destruct Z_le_dec; try lia.
      rewrite repeated_div'_equation. destruct Zdivide_dec; auto. tauto.
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
      * unfold repeated_div. repeat destruct Z_le_dec; try lia. apply repeated_div'_thm1.
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
                 +++ unfold repeated_div. repeat destruct Z_le_dec; try lia. apply repeated_div'_thm2. auto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia. simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest. repeat if_tac; try lia; auto. tauto.
           -- unfold new_highest in *. destruct Zdivide_dec; [destruct Z_le_dec |].
              ** rewrite H4 in H9. lia.
              ** rewrite H2 in H9. lia.
              ** elim n1. clear n1. destruct H8. exists (x * f ^ i). rewrite (repeated_div_thm0 f n) in H8; try lia.
                 rewrite (repeated_div_thm0 f n); try lia. rewrite Z.mul_comm in H8.
                 rewrite Z.divide_div_mul_exact in H8; try lia.
                 +++ rewrite <- Z.pow_sub_r in H8; try lia. replace (x * f ^ i * f) with (x * f * f ^ i) by ring.
                     rewrite <- H8. rewrite <- Z.mul_assoc. rewrite <- Z.pow_add_r; try lia.
                     ring_simplify (fst (repeated_div f n) - i + i). ring.
                 +++ exists (f ^ (fst (repeated_div f n) - i)). rewrite <- Z.pow_add_r; try lia.
                     ring_simplify (fst (repeated_div f n) - i + i). auto.
        ++ apply ltu_false_inv64 in H9. rewrite H2 in H9. destruct Z.eq_dec.
           -- rewrite H4 in H9. forward. entailer!. simpl (f ^ 0) in H8. rewrite Z.div_1_r in H8.
              Exists 1. entailer!.
              ** repeat split; try lia.
                 +++ unfold repeated_div. repeat destruct Z_le_dec; try lia. apply repeated_div'_thm2. auto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia. simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest. destruct Zdivide_dec; try tauto.
                 destruct Z_le_dec; try lia. auto.
           -- forward. entailer!. Exists (i + 1). entailer!. repeat split; try lia.
              ** rewrite (repeated_div_thm0 f n) in H8; try lia. rewrite Z.mul_comm in H8.
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
        clear H8. assert (n = f ^ fst (repeated_div f n) * snd (repeated_div f n)) by (apply repeated_div_thm0; try lia).
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


Theorem repeated_repeated_div_thm9 (i n: Z) (H: 1 <= n): repeated_repeated_div i n H <= n.
Proof.
  assert (i <= 1 \/ 2 <= i) by lia. destruct H0.
  + rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
  + assert (0 <= i) by lia. revert H0. pattern i. apply Z_lt_induction; auto; intros.
    assert (x = 2 \/ 2 <= x - 1) by lia. destruct H3.
    - subst. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
      simpl. rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
      apply repeated_div_thm1; lia.
    - rewrite repeated_repeated_div_equation. destruct Z_le_dec; try lia.
      assert (snd (repeated_div x (repeated_repeated_div (x - 1) n H)) <= repeated_repeated_div (x - 1) n H).
      { apply repeated_div_thm1; try lia. apply repeated_repeated_div_thm0. }
      assert (repeated_repeated_div (x - 1) n H <= n).
      { apply H0; try lia. }
      lia.
Qed.

Theorem repeated_repeated_div_thm10 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  forall k, 1 < k -> Z.divide k (repeated_repeated_div i n H) -> k > i.
Proof.
Admitted.

Definition value_of_highest i n (H: 1 <= n) :=
  match prime_divisor_list i n H with
  | nil => 1
  | x :: _ => x
  end.


Lemma find_proof: semax_body Vprog Gprog f_find find_spec.
Proof.
  start_function. assert (1 <= n) by lia. forward. forward_call. forward_call.
  + split.
    - assert (2 <= 2) by lia. pose proof (repeated_div_thm1 _ H1 _ H2). lia.
    - unfold new_highest. destruct Zdivide_dec; [destruct Z_le_dec |]; try lia.
  + autorewrite with norm.
    (* ??? *)
    forward_if (if prime_dec (repeated_repeated_div 3 n H1)
                then PROP ()
                     LOCAL (temp _n (Vlong (Int64.repr (repeated_repeated_div 3 n H1))))
                     SEP (data_at Ews tulong (Vlong (Int64.repr (value_of_highest 3 n H1))) (gv _highest))
                else PROP ()
                     LOCAL (temp _n (Vlong (Int64.repr 1)))
                     SEP (data_at Ews tulong (Vlong (Int64.repr (brute_force n))) (gv _highest))).
    assert (Int64.unsigned (Int64.repr 5) = 5) by reflexivity. rewrite H3 in H2. clear H3.
    assert (Int64.unsigned (Int64.repr (snd (repeated_div 3 (snd (repeated_div 2 n))))) =
            snd (repeated_div 3 (snd (repeated_div 2 n)))).
    { rewrite Int64.unsigned_repr; auto.
      assert (1 <= snd (repeated_div 2 n) <= n).
      { apply repeated_div_thm1; try lia. }
      assert (1 <= snd (repeated_div 3 (snd (repeated_div 2 n))) <= snd (repeated_div 2 n)).
      { apply repeated_div_thm1; try lia. }
      lia. }
    rewrite H3 in H2. clear H3.
    - forward_loop (
        EX (i: Z),
          PROP (let W := repeated_repeated_div (6 * i + 3) n H1 in
                0 <= i /\ if prime_dec W then True else (6 * i + 5) * (6 * i + 5) <= W)
          LOCAL (temp _n (Vlong (Int64.repr (repeated_repeated_div (6 * i + 3) n H1)));
                 temp _i (Vlong (Int64.repr (6 * i + 5))); gvars gv)
          SEP (data_at Ews tulong (Vlong (Int64.repr (value_of_highest (6 * i + 3) n H1))) (gv _highest))
      ).
      forward. entailer!. Exists 0. entailer!.
      * destruct (prime_dec (repeated_repeated_div 3 n H1)). auto.
        admit.
      * unfold new_highest. repeat destruct Zdivide_dec.
        ++ repeat if_tac; try lia. destruct Z_le_dec in H5; try lia. unfold value_of_highest.
           rewrite prime_divisor_list_equation. repeat if_tac; try lia; auto.
           simpl. rewrite prime_divisor_list_equation. repeat destruct Z_le_dec; try lia.
           repeat destruct Zdivide_dec; try tauto.
        ++ destruct Z_le_dec; try lia. unfold value_of_highest. rewrite prime_divisor_list_equation.
           destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec; auto. rewrite prime_divisor_list_equation.
           destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec; auto.
           -- exfalso. simpl in *. rewrite repeated_repeated_div_equation in d0. destruct Z_le_dec; try lia. tauto.
           -- simpl in *. exfalso. rewrite repeated_repeated_div_equation in n3. destruct Z_le_dec; try lia.
              simpl in *. rewrite repeated_repeated_div_equation in n3. destruct Z_le_dec; try lia. tauto.
        ++ destruct Z_le_dec; try lia. unfold value_of_highest. rewrite prime_divisor_list_equation.
           destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec.
           -- exfalso. rewrite repeated_repeated_div_equation in d0. destruct Z_le_dec; try lia. simpl in *.
              rewrite repeated_repeated_div_equation in d0. destruct Z_le_dec; try lia. tauto.
           -- rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec; auto.
              rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. exfalso.
              rewrite repeated_repeated_div_equation in n5. destruct Z_le_dec; try lia. tauto.
        ++ unfold value_of_highest. rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec.
           -- exfalso. rewrite repeated_repeated_div_equation in d. destruct Z_le_dec; try lia. simpl in *.
              rewrite repeated_repeated_div_equation in d. destruct Z_le_dec; try lia. tauto.
           -- rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. simpl. destruct Zdivide_dec.
              ** exfalso. rewrite repeated_repeated_div_equation in d. destruct Z_le_dec; try lia. tauto.
              ** rewrite prime_divisor_list_equation. destruct Z_le_dec; try lia. auto.
      * Intros i. forward_if.
        ++ abbreviate_semax. assert (repeated_repeated_div (6 * i + 3) n H1 >= (6 * i + 5) * (6 * i + 5)).
           { apply ltu_false_inv64 in H4. rewrite Int64.unsigned_repr in H4.
             + unfold Int64.mul in H4. rewrite Int64.unsigned_repr in H4.
               - rewrite Int64.unsigned_repr in H4; auto. destruct H3. split; try lia. admit.
               - rewrite Int64.unsigned_repr. destruct H3.
                 * split. lia. admit.
                 * split. destruct H3; lia. admit.
             + admit. }
           clear H4. destruct H3. forward_call.
           -- repeat split; try lia.
              ** admit.
              ** admit.
              ** unfold value_of_highest. admit.
              ** admit.
           -- forward_call.
              ** repeat split.
                 +++ apply repeated_div_thm1; try lia.
                 +++ pose proof (repeated_div_thm1 (6 * i + 5) ltac:(lia) (repeated_repeated_div (6 * i + 3) n H1) ltac:(lia)).
                     admit.
                 +++ rewrite Int64.unsigned_repr.
                     --- rewrite Int64.unsigned_repr. lia. lia.
                     --- split. lia. admit.
                 +++ rewrite Int64.unsigned_repr.
                     --- rewrite Int64.unsigned_repr.
                         *** admit.
                         *** lia.
                     --- split. lia. admit.
                 +++ unfold new_highest. destruct Zdivide_dec.
                     --- destruct Z_le_dec; try lia.
                     --- admit.
                 +++ unfold new_highest. destruct Zdivide_dec.
                     --- destruct Z_le_dec. admit. admit.
                     --- admit.
              ** autorewrite with norm. forward. Exists (i + 1). entailer!. repeat split.
                 +++ destruct (prime_dec (repeated_repeated_div (6 * (i + 1) + 3) n H1)); auto.
                     ring_simplify (6 * (i + 1) + 5). ring_simplify (6 * (i + 1) + 3). admit.
                 +++ do 2 f_equal. rewrite Int64.unsigned_repr.
                     --- rewrite Int64.unsigned_repr.
                         *** ring_simplify (6 * (i + 1) + 3). ring_simplify (6 * i + 5 + 2). admit.
                         *** lia.
                     --- split. lia. admit.
                 +++ do 2 f_equal. ring.
                 +++ rewrite Int64.unsigned_repr.
                     --- rewrite Int64.unsigned_repr; try lia. unfold value_of_highest. unfold new_highest.
                         destruct Zdivide_dec.
                         *** destruct Z_le_dec.
                             ++++ destruct Zdivide_dec.
                                  ---- destruct Z_le_dec.
                                       **** exfalso. clear l0. ring_simplify (6 * i + 5 + 2) in d.
                                            ring_simplify (6 * i + 5 + 2) in l. admit.
                                       **** lia.
                                  ---- ring_simplify (6 * (i + 1) + 3). exfalso. admit.
                             ++++ admit.
                         *** destruct Zdivide_dec.
                             ++++ destruct Z_le_dec.
                                  ---- ring_simplify (6 * (i + 1) + 3). exfalso. admit.
                                  ---- ring_simplify (6 * (i + 1) + 3). admit.
                             ++++ ring_simplify (6 * (i + 1) + 3). admit.
                     --- split. lia. admit.
        ++ destruct H3. destruct prime_dec in H5.
           -- forward. destruct (prime_dec (repeated_repeated_div 3 n H1)).
              ** entailer!.
                 +++ do 2 f_equal. admit.
                 +++ admit.
              ** entailer!.
                 +++ admit.
                 +++ (* ??? *) admit.
           -- forward. destruct (prime_dec (repeated_repeated_div 3 n H1)).
              ** exfalso. admit.
              ** exfalso. admit.
    - forward. destruct (prime_dec (repeated_repeated_div 3 n H1)).
      * admit.
      * admit.
    - destruct (prime_dec (repeated_repeated_div 3 n H1)).
      * forward_if (
          PROP ()
          LOCAL (gvars gv) (* Fix this *)
          SEP (data_at Ews tulong (Vlong (Int64.repr (value_of_highest 3 n H1))) (gv _highest))
        ).
        ++ exfalso. assert (repeated_repeated_div 3 n H1 = 1) by admit. rewrite H3 in p. destruct p. lia.
        ++ forward. entailer!. (*?? What does Missing_gvars gv mean? *) admit.
        ++ Fail forward. admit.
      * forward_if (
          PROP ()
          LOCAL (gvars gv) (* And also fix this *)
          SEP (data_at Ews tulong (Vlong (Int64.repr (brute_force n))) (gv _highest))
        ).
        ++ deadvars!. Fail forward. admit.
        ++ congruence.
        ++ Fail forward. admit.
Admitted.
