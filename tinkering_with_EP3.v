Require Import VST.floyd.proofauto.
Require Import FunInd.
Require Import Znumtheory.

Open Scope Z.

Function upto_aux (p: Z * Z) { measure (fun p => match p with (a, b) => Z.to_nat (b - a) end) p }: list Z :=
  match p with (a, b) => if Z_lt_ge_dec a b then a :: upto_aux (a + 1, b) else nil end.
Proof. intros. lia. Defined.

Definition upto (a b: Z) := upto_aux (a, b).

Theorem In_upto (a b: Z): forall x, In x (upto a b) <-> a <= x < b.
Proof.
  replace b with (a + (b - a)) by lia. generalize (b - a). clear b. intros.
  assert (z < 0 \/ 0 <= z) by lia. destruct H.
  + unfold upto. rewrite upto_aux_equation. destruct Z_lt_ge_dec; try lia. simpl. lia.
  + pose proof H. revert H a x. pattern z. apply Z_lt_induction; auto. clear z H0.
    intros. assert (x = 0 \/ 0 < x) by lia. destruct H1.
    - subst. unfold upto. rewrite upto_aux_equation. destruct Z_lt_ge_dec; simpl; lia.
    - assert (0 <= x - 1 < x) by lia. pose proof (H _ H2 (proj1 H2) (a + 1) x0).
      replace (a + 1 + (x - 1)) with (a + x) in * by lia. unfold upto in *.
      rewrite upto_aux_equation. destruct Z_lt_ge_dec; try lia. simpl.
      rewrite H3. lia.
Qed.

Definition prime_divisors m n := filter prime_dec (filter (fun x => Zdivide_dec x n) (upto m (n + 1))).

Theorem all_prime_divisors_thm n (H: 0 < n):
  forall k, (Z.divide k n /\ prime k) <-> In k (prime_divisors 2 n).
Proof.
  split; intros.
  + unfold prime_divisors. destruct H0. apply filter_In. split.
    - apply filter_In. split.
      * apply In_upto. split.
        ++ inversion H1. lia.
        ++ apply Z.divide_pos_le in H0; auto. lia.
      * destruct (Zdivide_dec k n); auto.
    - destruct (prime_dec k); auto.
  + unfold prime_divisors in H0. apply filter_In in H0. destruct H0. apply filter_In in H0. destruct H0.
    destruct (Zdivide_dec k n).
    - split; auto. destruct prime_dec; auto. simpl in *. congruence.
    - simpl in *. congruence.
Qed.

Definition biggest_prime_divisor n := fold_left Z.max (prime_divisors 2 n).

Function remove_factor (n k: Z) {measure Z.to_nat n}: Z :=
  if Z_le_gt_dec k 1 then n else
  if Z_le_gt_dec n 1 then n else
  if Zdivide_dec k n
      then remove_factor (Z.div n k) k
      else n.
Proof.
  intros. clear teq teq0 teq1. destruct anonymous1. subst. rewrite Z.div_mul; try lia. nia.
Defined.

Theorem remove_factor_ge_1 (n k: Z): 1 <= n -> 1 <= remove_factor n k.
Proof.
  intros. assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction.
  + intros. rewrite remove_factor_equation. repeat destruct Z_le_gt_dec; try lia.
    destruct Zdivide_dec.
    - apply H. destruct d. subst. rewrite Z.div_mul; try lia. nia. destruct d. subst. rewrite Z.div_mul; try lia.
    - auto.
  + auto.
Qed.

Theorem remove_factor_thm00 n k: 1 <= n -> 1 < k -> Z.divide k (remove_factor n k) -> False.
Proof.
  intros. assert (0 <= n) by lia. revert H H1. pattern n. apply Z_lt_induction; auto.
  intros. rewrite remove_factor_equation in H3. repeat destruct Z_le_gt_dec; try lia.
  + assert (x = 1) by lia. destruct H3. subst. assert (k >= 0) by lia. rewrite Zmult_comm in H4.
    pose proof (Zmult_one _ x0 H3 H4). lia.
  + destruct Zdivide_dec.
    - apply H in H3; auto. destruct d. subst. rewrite Z.div_mul; try lia. nia.
      destruct d. subst. rewrite Z.div_mul in *; try lia.
    - eauto.
Qed.

Theorem remove_factor_decreasing (n k: Z) (H: k > 1) (H0: n > 1) (H1: Z.divide k n): remove_factor n k < n.
Proof.
  assert (0 <= n) by lia. revert H0 H1. pattern n. apply Z_lt_induction.
  + intros. destruct H3. subst. rewrite remove_factor_equation.
    repeat destruct Z_le_gt_dec; try lia.
    destruct Zdivide_dec.
    - rewrite Z.div_mul; try lia. clear d g g0.
      assert (0 <= x0 < x0 * k) by nia.
      destruct (Z_le_gt_dec x0 1).
      * assert (x0 = 0 \/ x0 = 1) by lia. destruct H4.
        ++ subst. lia.
        ++ subst. rewrite remove_factor_equation. destruct Z_le_gt_dec.
           -- lia.
           -- destruct Z_le_gt_dec. lia. lia.
      * destruct (Zdivide_dec k x0).
        ++ pose (H0 _ H3 g d). nia.
        ++ rewrite remove_factor_equation. repeat destruct Z_le_gt_dec; try lia.
           destruct Zdivide_dec; intuition.
    - exfalso. apply n0. exists x0. auto.
  + auto.
Qed.

Function find_factors (n k s: Z) { measure Z.to_nat s }: list Z :=
  if Z_le_gt_dec s 0 then nil else
  if Z_le_gt_dec k 1 then nil else
  if Z_le_gt_dec n 1 then nil else
  if Zdivide_dec k n
    then k :: find_factors (remove_factor n k) (k + 1) (s - 1)
    else find_factors n (k + 1) (s - 1).
Proof.
  + intros. lia.
  + intros. lia.
Defined.

Definition all_prime_factors (n: Z) := find_factors n 2 n.

Fixpoint remove_factors_list (n: Z) (L: list Z): Z :=
  match L with
  | [] => n
  | x :: t => if Zdivide_dec x n then remove_factors_list (remove_factor n x) t else remove_factors_list n t
  end.

Fixpoint remove_factors_list' (n: Z) (L: list Z): list Z :=
  match L with
  | [] => []
  | x :: t => if Zdivide_dec x n then x :: remove_factors_list' (remove_factor n x) t else remove_factors_list' n t
  end.

Theorem remove_factors_list_app (n: Z) (L1 L2: list Z):
  remove_factors_list n (L1 ++ L2) = remove_factors_list (remove_factors_list n L1) L2.
Proof.
  revert n. induction L1; intros.
  + simpl. auto.
  + simpl. destruct Zdivide_dec.
    - apply IHL1.
    - apply IHL1.
Qed.

Definition remove_factors_list_ge_1 (n: Z) (L: list Z):
  1 <= n -> (forall x, In x L -> 1 < x) -> 1 <= remove_factors_list n L.
Proof.
  intros. assert (0 <= n) by lia. revert L H H0. pattern n. apply Z_lt_induction; auto.
  intros. induction L.
  + simpl. lia.
  + simpl in *. destruct Zdivide_dec.
    - apply H.
      * split.
        ++ pose proof (remove_factor_ge_1 x a H0). lia.
        ++ apply remove_factor_decreasing; auto; try lia.
           -- assert (1 < a) by (apply H2; auto). lia.
           -- assert (1 < a) by (apply H2; auto). assert (0 < x) by lia. pose proof (Z.divide_pos_le a x H4 d). lia.
      * apply remove_factor_ge_1; auto.
      * intros. apply H2. auto.
    - apply IHL. intros. apply H2. auto.
Qed.

Theorem upto_append_thm (a b: Z): a <= b -> upto a (b + 1) = upto a b ++ [b].
Proof.
  intros. unfold upto. replace b with (a + (b - a)) in * by lia. assert (0 <= b - a) by lia. revert H H0.
  generalize (b - a). clear b. intros. pose proof H0. revert a H H0.
  pattern z. apply Z_lt_induction; auto. clear z H1. intros.
  rewrite (upto_aux_equation (a, a + x + 1)), (upto_aux_equation (a, a + x)).
  repeat destruct Z_lt_ge_dec; try lia.
  + simpl. f_equal. assert (x = 1 \/ 1 < x) by lia. destruct H2.
    - subst. clear H. rewrite (upto_aux_equation (a + 1, a + 1 + 1)), (upto_aux_equation (a + 1, a + 1)).
      repeat destruct Z_lt_ge_dec; try lia. simpl. f_equal.
      rewrite upto_aux_equation. destruct Z_lt_ge_dec; try lia. auto.
    - replace (a + x + 1) with ((a + 1) + (x - 1) + 1) by lia. rewrite H; try lia.
      replace (a + 1 + (x - 1)) with (a + x) by lia. auto.
  + assert (a + x = a) by lia. rewrite H2. rewrite upto_aux_equation. destruct Z_lt_ge_dec; try lia.
    compute. auto.
Qed.

Theorem aux00 (n a: Z) (L: list Z) (H: forall x, In x L -> 1 < x):
  1 <= n -> 1 < a -> Z.divide a (remove_factors_list n L) -> Z.divide a (remove_factors_list n (L ++ [a])) -> False.
Proof.
  revert n a H. induction L; intros.
  + simpl in *. destruct Zdivide_dec.
    - apply remove_factor_thm00 in H3; auto.
    - tauto.
  + simpl in *. destruct Zdivide_dec.
    - rewrite remove_factors_list_app in H3. simpl in H3. destruct Zdivide_dec.
      * apply remove_factor_thm00 in H3; auto. apply remove_factors_list_ge_1.
        ++ apply remove_factor_ge_1. auto.
        ++ intros. apply H. auto.
      * apply (IHL (remove_factor n a) a0); auto; try tauto.
    - rewrite remove_factors_list_app in H3. simpl in H3. destruct Zdivide_dec.
      * apply remove_factor_thm00 in H3; auto. apply remove_factors_list_ge_1; auto.
      * tauto.
Qed.

Theorem aux01 (n k: Z) (H: 1 <= n) (H0: 1 < k): exists i, 0 <= i /\ n = Z.pow k i * remove_factor n k.
Proof.
  assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction; auto. clear n H1.
  intros. destruct (Zdivide_dec k x).
  + destruct d. assert (0 <= x0 < x) by nia. assert (1 <= x0) by lia.
    destruct (H _ H3 H4). destruct H5. exists (x1 + 1). split; try lia.
    subst. rewrite H6 at 1. rewrite Z.pow_add_r; try lia. rewrite (remove_factor_equation (x0 * k) k).
    repeat destruct Z_le_gt_dec; try lia. destruct Zdivide_dec.
    - rewrite Z.div_mul; try lia.
    - exfalso. apply n. exists x0. auto.
  + exists 0. split; try lia. simpl. rewrite remove_factor_equation.
    repeat destruct Z_le_gt_dec; try lia. destruct Zdivide_dec; try tauto. lia.
Qed.

Theorem aux02 (n k a: Z) (H: 1 <= n) (H0: 1 < k) (H1: 1 < a) (H2: Z.divide k (remove_factor n a)): Z.divide k n.
Proof.
  destruct H2. assert (1 <= n) by lia. destruct (aux01 n a H3 H1). destruct H4.
  rewrite H5. rewrite H2. exists (a ^ x0 * x). lia.
Qed.

Theorem aux03 (n k: Z) (L: list Z) (H: 1 <= n) (H0: 1 < k) (H1: forall x, In x L -> 1 < x)
  (H2: Z.divide k (remove_factors_list n L)): Z.divide k n.
Proof.
  revert n H H2. induction L; intros.
  + simpl in *. auto.
  + simpl in *. destruct Zdivide_dec.
    - apply IHL in H2; auto.
      * assert (1 < a). { apply H1. auto. }
        destruct (aux01 _ _ H H3). destruct H4. rewrite H5. destruct H2. rewrite H2. exists (Z.pow a x * x0). lia.
      * apply remove_factor_ge_1; auto.
    - apply IHL; auto.
Qed.

Theorem aux04 (n k: Z) (L1 L2: list Z) (H0: forall x, In x L1 -> 1 < x) (H1: forall x, In x L2 -> 1 < x):
  1 <= n -> 1 < k -> Z.divide k (remove_factors_list n (L1 ++ k :: L2)) -> False.
Proof.
  revert n k L2 H1. induction L1; intros; simpl in *.
  + destruct Zdivide_dec.
    - apply aux03 in H3; auto.
      * apply remove_factor_thm00 in H3; auto.
      * apply remove_factor_ge_1; auto.
    - apply aux03 in H3; auto.
  + destruct Zdivide_dec.
    - apply IHL1 in H3; auto. apply remove_factor_ge_1; auto.
    - apply IHL1 in H3; auto.
Qed.

Theorem aux05 (a b c: Z): a <= b <= c -> upto a c = upto a b ++ upto b c.
Proof.
  intros. replace c with (b + (c - b)) in * by lia. assert (0 <= c - b) by lia. revert H H0. generalize (c - b).
  clear c. intros. revert a b H. pattern z. apply Z_lt_induction; auto. clear z H0. intros.
  assert (x = 0 \/ 0 < x) by lia. destruct H1.
  + subst. rewrite Z.add_0_r. unfold upto. rewrite (upto_aux_equation (b, b)). destruct Z_lt_ge_dec; try lia.
    rewrite app_nil_r. auto.
  + replace (b + x) with (b + (x - 1) + 1) by lia. repeat rewrite upto_append_thm; try lia.
    rewrite H; try lia. rewrite app_assoc. auto.
Qed.

Theorem aux06 (n k: Z): 1 <= n -> 1 < k -> Z.divide k (remove_factors_list n (upto 2 k)) -> prime k.
Proof.
  intros. destruct (prime_dec k); auto. exfalso. apply not_prime_divide in n0; auto.
  destruct n0. destruct H2. assert (upto 2 k = upto 2 x ++ x :: upto (x + 1) k).
  { rewrite (aux05 2 (x + 1) k); try lia. rewrite upto_append_thm; try lia. rewrite <- app_assoc. auto. }
  rewrite H4 in H1. pose proof (aux04 n x (upto 2 x) (upto (x + 1) k)). apply H5; try lia.
  + intros. apply In_upto in H6. lia.
  + intros. apply In_upto in H6. lia.
  + destruct H3. subst. destruct H1. exists (x1 * x0). rewrite H1. lia.
Qed.

Theorem aux07 (n x k: Z): 1 <= x <= n -> 1 < k -> remove_factor x k <= n.
Proof.
  intros. assert (0 <= x) by lia. revert n k H H0. pattern x. apply Z_lt_induction; auto.
  clear x H1. intros. rewrite remove_factor_equation. repeat destruct Z_le_gt_dec; try lia.
  destruct Zdivide_dec.
  + destruct d. subst. rewrite Z.div_mul; try lia. apply H; nia.
  + lia.
Qed.

Theorem aux08 (n x: Z) (L: list Z) (H: forall x, In x L -> 1 < x):
  1 <= n -> 1 <= x <= n -> remove_factors_list x L <= n.
Proof.
  revert x. induction L.
  + simpl. lia.
  + simpl. intros. destruct Zdivide_dec.
    - apply IHL; auto.
      * intros. apply H. simpl. auto.
      * split; [apply remove_factor_ge_1; lia|]. apply aux07; try lia. apply H. simpl. auto.
    - apply IHL; try lia. intros. apply H. simpl. auto.
Qed.

Theorem aux09 (n k: Z): 1 <= n -> 1 < k -> (k | remove_factors_list n (upto 2 k)) -> (k | n).
Proof.
  intros. apply aux03 in H1; auto; try lia. intros. rewrite In_upto in H2. lia.
Qed.

Theorem aux10 (L: list Z): (forall x, In x L -> 0 < x) -> remove_factors_list 1 L = 1.
Proof.
  intros. induction L.
  + simpl. auto.
  + simpl in *. destruct Zdivide_dec.
    - apply Z.divide_1_r_nonneg in d.
      * subst. auto.
      * assert (0 < a). { apply H. auto. } lia.
    - apply IHL. intros. apply H. auto.
Qed.

Theorem aux11 (k W: Z) (H: 1 < k <= W) (H0: prime k) (H1: Z.divide k W): prime_divisors k W = k :: prime_divisors (k + 1) W.
Proof.
  intros. unfold prime_divisors. replace (upto k (W + 1)) with (k :: upto (k + 1) (W + 1)).
  + simpl. destruct Zdivide_dec; try (exfalso; tauto); simpl. destruct prime_dec; try (exfalso; tauto); simpl. auto.
  + unfold upto. rewrite (upto_aux_equation (k, W + 1)). destruct Z_lt_ge_dec; try lia. auto.
Qed.

Theorem prime_divisor_of_nonprime (n: Z) (H: ~ prime n) (H0: 1 < n): exists p, prime p /\ Z.divide p n /\ p < n.
Proof.
  assert (0 <= n) by lia. revert H H0. pattern n. apply Z_lt_induction; auto. clear n H1. intros.
  apply not_prime_divide in H0. destruct H0. destruct H0. destruct H2. assert (0 <= x0 < x) by lia.
  destruct (prime_dec x0).
  + exists x0. split; auto. split; try lia. exists x1. auto.
  + pose proof (H _ H3 n (proj1 H0)). destruct H4. destruct H4. destruct H5. destruct H5. exists x2.
    split; auto. split; try lia. exists (x1 * x3). lia.
  + auto.
Qed.

Theorem aux12 (n k s: Z):
  1 <= n -> 1 < k -> n <= s ->
  find_factors (remove_factors_list n (upto 2 k)) k s = prime_divisors k (remove_factors_list n (upto 2 k)).
Proof.
  (* The wrong direction... Can't prove this, even if this seems to be true. *)
Admitted.

Theorem equivalence (n k s: Z):
  1 <= n -> 1 < k -> n <= s ->
  find_factors n 2 s = prime_divisors 2 n.
Proof.
  intros. replace n with (remove_factors_list n (upto 2 2)).
  + rewrite aux12; auto. lia.
  + simpl. auto.
Admitted.
