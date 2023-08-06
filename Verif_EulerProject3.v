Require Import VST.floyd.proofauto.
Require Import Znumtheory FunInd.

Open Scope Z.

Fixpoint product (L: list Z): Z :=
  match L with
  | [] => 1
  | x :: t => x * product t
  end.

Theorem product_app (L1 L2: list Z): product (L1 ++ L2) = product L1 * product L2.
Proof.
  induction L1; simpl; lia.
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

Theorem fta_existence (n: Z) (H: 1 <= n): exists (L: list Z), Forall prime L /\ product L = n.
Proof.
  assert (0 <= n) by lia. revert H. pattern n. apply Z_lt_induction; auto. intros. clear n H0.
  assert (x = 1 \/ 1 < x) by lia. destruct H0.
  + subst. exists nil. simpl. repeat try split. constructor.
  + assert (2 <= x) by lia. destruct (prime_divisor_existence x H2) as [p [H3 H4]].
    destruct H4. assert (1 < p) by (inversion H3; auto).
    assert (0 <= x0 < x) by nia. assert (1 <= x0) by nia.
    assert (x0 = 1 \/ 1 < x0) by lia. destruct H8.
    - assert (x = p) by lia. exists [x]. split.
      * constructor; auto. congruence.
      * simpl. lia.
    - assert (0 <= p < x) by nia. assert (1 <= p) by nia.
      pose proof (H _ H6 H7). pose proof (H _ H9 H10). destruct H11 as [L1 H11], H12 as [L2 H12].
      exists (L1 ++ L2). destruct H11, H12. split.
      * apply Forall_app. auto.
      * rewrite product_app. lia.
Qed.

Theorem prime_divisor_of_prime_product (p: Z) (H: prime p) (L: list Z) (H0: Forall prime L):
  Z.divide p (product L) -> In p L.
Proof.
  induction L.
  + simpl in *. intros. destruct H1. assert (1 < p) by (inversion H; auto).
    symmetry in H1. rewrite Zmult_comm in H1. assert (p >= 0) by lia. pose proof (Zmult_one _ _ H3 H1).
    lia.
  + simpl in *. inversion H0; subst; clear H0. intros. apply prime_mult in H0; auto. destruct H0.
    - apply prime_div_prime in H0; auto.
    - auto.
Qed.

Theorem prime_product_one_empty_list (L: list Z): Forall prime L -> product L = 1 -> L = [].
Proof.
  intros. destruct L; auto. simpl in *. inversion H; subst; clear H. exfalso.
  assert (1 < z) by (inversion H3; auto). assert (z >= 0) by lia. pose proof (Zmult_one _ _ H1 H0).
  lia.
Qed.

Theorem Forall_elt2 A (L1 L2: list A) (x: A) (P: A -> Prop):
  Forall P (L1 ++ x :: L2) -> Forall P (L1 ++ L2).
Proof.
  induction L1.
  + simpl. intros. inversion H; subst; clear H. auto.
  + simpl. intros. inversion H; subst; clear H. apply IHL1 in H3. constructor; auto.
Qed.

Theorem prime_product_ge_one (L: list Z): Forall prime L -> product L >= 1.
Proof.
  induction L; intros.
  + simpl. lia.
  + simpl. inversion H; subst; clear H. inversion H2. pose proof (IHL H3). nia.
Qed.

Theorem product_split (L1 L2: list Z) (x: Z): x * product (L1 ++ L2) = product (L1 ++ x :: L2).
Proof.
  induction L1.
  + simpl. auto.
  + simpl. lia.
Qed.

Theorem fta_unique (n: Z) (H: 1 <= n) (L1 L2: list Z):
  Forall prime L1 -> product L1 = n ->
  Forall prime L2 -> product L2 = n ->
  Permutation L1 L2.
Proof.
  assert (0 <= n) by lia. revert H L1 L2. pattern n. apply Z_lt_induction; auto. intros. clear n H0.
  assert (x = 1 \/ 2 <= x) by lia. destruct H0.
  + subst. assert (L1 = []).
    { apply prime_product_one_empty_list; auto. }
    assert (L2 = []).
    { rewrite H0 in H5. apply prime_product_one_empty_list; auto. }
    subst. constructor.
  + pose proof (prime_divisor_existence _ H0). destruct H6. destruct H6.
    assert (Z.divide x0 (product L1)) by congruence.
    assert (Z.divide x0 (product L2)) by congruence.
    apply prime_divisor_of_prime_product in H8; auto.
    apply prime_divisor_of_prime_product in H9; auto.
    apply in_split in H8. apply in_split in H9.
    destruct H8 as [l1 [l2 H8]]. destruct H9 as [l3 [l4 H9]].
    rewrite H8, H9. apply Permutation_elt. destruct H7. rewrite H7 in *.
    assert (product (l1 ++ l2) = x1).
    { pose proof (product_split l1 l2 x0). rewrite <- H8 in H10. rewrite H3 in H10.
      assert (0 < x0) by (inversion H6; lia). nia. }
    assert (product (l3 ++ l4) = x1).
    { pose proof (product_split l3 l4 x0). rewrite <- H9 in H11. rewrite H5 in H11.
      assert (0 < x0) by (inversion H6; lia). nia. }
    assert (Forall prime (l1 ++ l2)) by (apply Forall_elt2 with (x:=x0); congruence).
    assert (Forall prime (l3 ++ l4)) by (apply Forall_elt2 with (x:=x0); congruence).
    assert (1 <= x1).
    { rewrite <- H10. pose proof (prime_product_ge_one (l1 ++ l2) H12). lia. }
    assert (1 < x0) by (inversion H6; lia).
    assert (0 <= x1 < x1 * x0) by nia.
    apply (H x1); auto.
Qed.



Definition is_biggest_prime_divisor (k n: Z) := 
  let P := fun x => Z.divide x n /\ prime x in
  P k /\ (forall i, P i -> i <= k).

Theorem aux f (Hf: 2 <= f) n (Hn: 1 <= n):
  Z.divide f n -> 1 <= n / f.
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

Theorem Zle_1_repeated_div' f n (Hf: 2 <= f) (Hn: 1 <= n) (H: Z.divide f n): 1 <= fst (repeated_div' f Hf n Hn).
Proof.
  rewrite repeated_div'_equation. destruct Zdivide_dec; try tauto.
  pose proof (Zle_0_repeated_div' f (n / f)).
  assert (1 <= n / f). { destruct H. subst. rewrite Z_div_mult; nia. }
  assert (repeated_div' f Hf (n / f) H1 = repeated_div' f Hf (n / f) (aux f Hf n Hn d)).
  { apply repeated_div'_aux; auto. }
  rewrite <- H2. pose proof (Zle_0_repeated_div' f (n / f) Hf H1). destruct repeated_div'. simpl in *. lia.
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
  + simpl. lia.
  + simpl. lia.
  + simpl. lia.
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


Require Import EulerProject3.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition new_highest f n h :=
  if Zdivide_dec f n then (if Z_le_dec f h then h else f) else h.


Definition factorize_spec: ident * funspec :=
DECLARE _factorize
  WITH gv: globals, n: Z, f: Z, h: Z
  PRE [ tulong, tulong ]
    PROP (2 <= n <= Int64.max_unsigned; 2 <= f <= Int64.max_unsigned; 0 <= h <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr n); Vlong (Int64.repr f))
    GLOBALS (gv)
    SEP (data_at Ews tulong (Vlong (Int64.repr h)) (gv _highest))
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr (snd (repeated_div f n))))
    SEP (data_at Ews tulong (Vlong (Int64.repr (new_highest f n h))) (gv _highest)).


Definition Gprog := [factorize_spec].

Lemma factorize_proof: semax_body Vprog Gprog f_factorize factorize_spec.
Proof.
  start_function. assert (Int64.unsigned (Int64.repr f) = f).
  { rewrite Int64.unsigned_repr_eq. apply Zmod_small. unfold Int64.max_unsigned in H0. lia. }
  assert (Int64.unsigned (Int64.repr n) = n).
  { rewrite Int64.unsigned_repr_eq. apply Zmod_small. unfold Int64.max_unsigned in H. lia. }
  assert (Int64.unsigned (Int64.repr h) = h).
  { rewrite Int64.unsigned_repr_eq. apply Zmod_small. unfold Int64.max_unsigned in H1. lia. }
  assert (forall i, 0 <= i -> Int64.unsigned (Int64.repr (n / f ^ i)) = n / f ^ i).
  { intros. rewrite Int64.unsigned_repr_eq. apply Zmod_small. split.
    + apply Z_div_nonneg_nonneg; try lia.
    + destruct (Z.eq_dec i 0).
      - subst. simpl (f ^ 0). rewrite Zdiv_1_r. unfold Int64.max_unsigned in H. lia.
      - assert (n / f ^ i < n). { apply Z.div_lt; try lia. apply Z.pow_gt_1; try lia. }
        unfold Int64.max_unsigned in H. lia. }
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
      * unfold repeated_div. repeat destruct Z_le_dec; try lia. apply Zle_0_repeated_div'.
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
                 +++ unfold repeated_div. repeat destruct Z_le_dec; try lia. apply Zle_1_repeated_div'. auto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia. simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest. repeat if_tac; try lia; auto. tauto.
           -- unfold new_highest in *. destruct Zdivide_dec; [destruct Z_le_dec |].
              ** rewrite H4 in H9. lia.
              ** rewrite H2 in H9. lia.
              ** elim n1. clear n1. destruct H8. exists (x * f ^ i). rewrite (repeated_div_thm f n) in H8; try lia.
                 rewrite (repeated_div_thm f n); try lia. rewrite Z.mul_comm in H8.
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
                 +++ unfold repeated_div. repeat destruct Z_le_dec; try lia. apply Zle_1_repeated_div'. auto.
                 +++ do 2 f_equal. replace (f ^ 1) with f by lia. simpl (f ^ 0). rewrite Z.div_1_r. auto.
                     unfold Int64.divu. f_equal. congruence.
              ** destruct Z.eq_dec; try lia. unfold new_highest. destruct Zdivide_dec; try tauto.
                 destruct Z_le_dec; try lia. auto.
           -- forward. entailer!. Exists (i + 1). entailer!. repeat split; try lia.
              ** rewrite (repeated_div_thm f n) in H8; try lia. rewrite Z.mul_comm in H8.
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
        clear H8. assert (n = f ^ fst (repeated_div f n) * snd (repeated_div f n)) by (apply repeated_div_thm; try lia).
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

