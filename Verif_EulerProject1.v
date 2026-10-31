Require Import VST.floyd.proofauto.
Require Import EulerProject1.


Definition sum (L: list Z) := fold_right Z.add 0 L.

Lemma sum_app (L1 L2: list Z): sum (L1 ++ L2) = sum L1 + sum L2.
Proof.
  induction L1; simpl; lia.
Qed.


Definition multiple_of_3_or_5 n: bool := (n mod 3 =? 0) || (n mod 5 =? 0).

Definition range_1_to n: list Z := map Z.succ (upto (Z.to_nat n)).

Definition sum_multiples_of_3_or_5 n :=
  sum (filter multiple_of_3_or_5 (range_1_to n)).

Definition triangular n :=
  n * (n + 1) / 2.

Definition closed_form n :=
  3 * triangular (n / 3) + 5 * triangular (n / 5) - 15 * triangular (n / 15).

Theorem triangular_of_even n (H: 0 <= n) (H0: Zeven n):
  triangular n = (n / 2) * (n + 1).
Proof.
  unfold triangular.
  apply Zeven_div2 in H0.
  remember (Z.div2 n) as x.
  rewrite H0.
  replace (2 * x * (2 * x + 1)) with (x * (x * 2 + 1) * 2) by ring.
  replace (2 * x) with (x * 2) by ring.
  repeat rewrite Z_div_mult; lia.
Qed.

Theorem triangular_of_odd n (H: 0 <= n) (H0: Zodd n):
  triangular n = n * ((n + 1) / 2).
Proof.
  unfold triangular.
  apply Zodd_div2 in H0.
  remember (Z.div2 n) as x.
  rewrite H0.
  replace ((2 * x + 1) * (2 * x + 1 + 1))
    with ((2 * x + 1) * (x + 1) * 2) by ring.
  replace (2 * x + 1 + 1) with ((x + 1) * 2) by ring.
  repeat rewrite Z_div_mult; lia.
Qed.

Theorem triangular_of_succ n (H: 0 <= n):
  triangular (n + 1) = triangular n + n + 1.
Proof.
  revert n H. apply natlike_ind; try reflexivity; intros.
  destruct (Zeven_odd_dec x).
  + pose proof (Zodd_Sn _ z).
    pose proof (Zeven_Sn _ H1).
    repeat rewrite <- Z.add_1_r in *.
    apply triangular_of_even in H2; try lia.
    apply triangular_of_odd in H1; try lia.
    rewrite H1, H2.
    apply Zeven_div2 in z.
    remember (Z.div2 x) as w.
    rewrite z.
    replace (2 * w + 1 + 1) with ((w + 1) * 2) by ring.
    repeat rewrite Z_div_mult; lia.
  + pose proof (Zeven_Sn _ z).
    pose proof (Zodd_Sn _ H1).
    repeat rewrite <- Z.add_1_r in *.
    apply triangular_of_even in H1; try lia.
    apply triangular_of_odd in H2; try lia.
    rewrite H1, H2.
    apply Zodd_div2 in z.
    remember (Z.div2 x) as w.
    rewrite z.
    replace (2 * w + 1 + 1 + 1 + 1) with ((w + 2) * 2) by ring.
    replace (2 * w + 1 + 1) with ((w + 1) * 2) by ring.
    repeat rewrite Z_div_mult; lia.
Qed.

Theorem succ_div_of_mod_eq_0 a n (Ha: 0 < a) (Hn: 0 <= n) (H: (n + 1) mod a = 0):
  (n + 1) / a = n / a + 1.
Proof.
  rewrite Z.mod_divide in H; try lia.
  destruct H as [k Hk].
  assert (n / a = k - 1).
  { replace n with ((k - 1) * a + (a - 1)) by lia.
    rewrite Z.div_add_l; try lia.
    rewrite Z.div_small; try lia. }
  rewrite Hk, Z_div_mult; try lia.
Qed.

Theorem succ_div_of_mod_ne_0 a n (Ha: 0 < a) (Hn: 0 <= n) (H: (n + 1) mod a <> 0):
  (n + 1) / a = n / a.
Proof.
  apply Z.div_unique with (r := (n + 1) mod a - 1); try lia.
  + pose proof (Z.mod_pos_bound (n + 1) a Ha). lia.
  + pose proof (Z_div_mod_eq (n + 1) a). lia.
Qed.

Theorem scaled_triangular_step_of_divide a n
  (Ha: 0 < a) (Hn: 0 <= n) (H: (n + 1) mod a = 0):
  a * triangular ((n + 1) / a) = a * triangular (n / a) + (n + 1).
Proof.
  ring_simplify.
  rewrite succ_div_of_mod_eq_0; auto.
  rewrite triangular_of_succ.
  + ring_simplify.
    apply Z.mod_divide in H; try lia.
    destruct H.
    assert (n = (x - 1) * a + (a - 1)) by lia.
    assert (n / a = x - 1).
    { rewrite H0, Z.div_add_l, Z.div_small; lia. }
    lia.
  + apply Z_div_pos; lia.
Qed.

Theorem scaled_triangular_step_of_not_divide a n
  (Ha: 0 < a) (Hn: 0 <= n) (H: (n + 1) mod a <> 0):
  a * triangular ((n + 1) / a) = a * triangular (n / a).
Proof. rewrite succ_div_of_mod_ne_0; auto. Qed.

Lemma sum_multiples_succ n (Hn: 0 <= n):
  sum_multiples_of_3_or_5 (Z.succ n) =
  sum_multiples_of_3_or_5 n +
  (if multiple_of_3_or_5 (Z.succ n) then (Z.succ n) else 0).
Proof.
  unfold sum_multiples_of_3_or_5.
  replace (range_1_to (Z.succ n)) with (range_1_to n ++ (Z.succ n) :: nil).
  + rewrite filter_app.
    simpl.
    rewrite sum_app.
    f_equal.
    destruct (multiple_of_3_or_5 (Z.succ n)); simpl; lia.
  + unfold range_1_to.
    rewrite <- map_last.
    f_equal.
    replace (Z.to_nat (Z.succ n)) with (Z.to_nat n + 1)%nat by lia.
    rewrite upto_app.
    simpl.
    do 2 f_equal.
    lia.
Qed.

Theorem sum_multiples_eq_closed_form n (Hn: 0 <= n):
  sum_multiples_of_3_or_5 n = closed_form n.
Proof.
  revert n Hn; apply natlike_ind; try reflexivity; intros.
  rewrite sum_multiples_succ; auto.
  unfold closed_form, multiple_of_3_or_5 in *.
  repeat rewrite <- Z.add_1_r.
  rewrite H0.
  remember ((x + 1) mod 3 =? 0) as b3; destruct b3; symmetry in Heqb3;
  remember ((x + 1) mod 5 =? 0) as b5; destruct b5; symmetry in Heqb5.
  + rewrite Z.eqb_eq in Heqb3, Heqb5.
    assert ((x + 1) mod 15 = 0).
    { assert (Z.lcm 3 5 = 15) by auto.
      apply Z.mod0_divide.
      apply Z.mod_divide in Heqb3; try lia.
      apply Z.mod_divide in Heqb5; try lia.
      rewrite <- H1.
      apply Z.lcm_least; auto. }
    repeat rewrite scaled_triangular_step_of_divide; try lia.
    simpl; lia.
  + assert ((x + 1) mod 5 =? 0 = true -> False) by congruence.
    rewrite Z.eqb_eq in Heqb3, H1.
    assert ((x + 1) mod 15 <> 0).
    { intro. apply H1.
      apply Z.mod_divide in H2; try lia.
      apply Z.mod0_divide.
      destruct H2. exists (3 * x0). lia. }
    rewrite (scaled_triangular_step_of_not_divide 5 x); try lia.
    rewrite (scaled_triangular_step_of_not_divide 15 x); try lia.
    rewrite (scaled_triangular_step_of_divide 3 x); try lia.
    simpl; lia.
  + assert ((x + 1) mod 3 =? 0 = true -> False) by congruence.
    rewrite Z.eqb_eq in Heqb5, H1.
    assert ((x + 1) mod 15 <> 0).
    { intro. apply H1.
      apply Z.mod_divide in H2; try lia.
      apply Z.mod0_divide.
      destruct H2. exists (5 * x0). lia. }
    rewrite (scaled_triangular_step_of_not_divide 3 x); try lia.
    rewrite (scaled_triangular_step_of_not_divide 15 x); try lia.
    rewrite (scaled_triangular_step_of_divide 5 x); try lia.
    simpl; lia.
  + assert ((x + 1) mod 3 =? 0 = true -> False) by congruence.
    assert ((x + 1) mod 5 =? 0 = true -> False) by congruence.
    rewrite Z.eqb_eq in H1, H2.
    assert ((x + 1) mod 15 <> 0).
    { intro. apply H1.
      apply Z.mod_divide in H3; try lia.
      apply Z.mod0_divide.
      destruct H3. exists (5 * x0). lia. }
    repeat rewrite (scaled_triangular_step_of_not_divide); try lia.
    simpl; lia.
Qed.



Lemma sum_multiples_of_3_or_5_nonneg n (Hn: 0 <= n):
  0 <= sum_multiples_of_3_or_5 n.
Proof.
  revert n Hn; apply natlike_ind; try reflexivity; intros.
  rewrite sum_multiples_succ; auto.
  destruct multiple_of_3_or_5; lia.
Qed.

Lemma sum_multiples_of_3_or_5_increasing_aux d (Hd: 0 <= d) n (Hn: 0 <= n):
  sum_multiples_of_3_or_5 n <= sum_multiples_of_3_or_5 (n + d).
Proof.
  revert d Hd; apply natlike_ind; intros.
  + rewrite Z.add_0_r; lia.
  + replace (n + Z.succ x) with (Z.succ (n + x)) by lia.
    rewrite sum_multiples_succ; try lia.
    destruct multiple_of_3_or_5; lia.
Qed.

Lemma sum_multiples_of_3_or_5_increasing n m (H: 0 <= m <= n):
  sum_multiples_of_3_or_5 m <= sum_multiples_of_3_or_5 n.
Proof.
  pose proof (sum_multiples_of_3_or_5_increasing_aux (n - m) ltac:(lia) m (proj1 H)).
  replace (m + (n - m)) with n in H0 by lia. auto.
Qed.




Instance CompSpecs: compspecs. make_compspecs prog. Defined.
Definition Vprog: varspecs. mk_varspecs prog. Defined.


Definition triangular_spec: ident * funspec :=
  DECLARE _triangular
  WITH number: Z
  PRE [ tuint ]
    PROP (0 <= number <= 92681)
    PARAMS (Vint (Int.repr number))
    SEP ()
  POST [ tuint ]
    PROP (0 <= triangular number <= Int.max_unsigned)
    RETURN (Vint (Int.repr (triangular number)))
    SEP ().

Definition solution_spec: ident * funspec :=
  DECLARE _solution
  WITH number: Z
  PRE [ tuint ]
    PROP (0 <= number <= 135671)
    PARAMS (Vint (Int.repr number))
    SEP ()
  POST [ tuint ]
    PROP (0 <= sum_multiples_of_3_or_5 number <= Int.max_unsigned)
    RETURN (Vint (Int.repr (sum_multiples_of_3_or_5 number)))
    SEP ().

Definition Gprog := [triangular_spec; solution_spec].

Theorem triangular_correct: semax_body Vprog Gprog f_triangular triangular_spec.
Proof.
  start_function.
  forward_if.
  + forward.
    entailer!.
    split; [| split].
    - unfold triangular.
      apply Z.div_pos; nia.
    - unfold triangular.
      change Int.max_unsigned with (8589934590 / 2).
      apply Z.div_le_mono; nia.
    - apply repr_inj_unsigned in H0.
      * unfold triangular.
        do 2 f_equal.
        apply Z.mod_divide in H0; try lia.
        destruct H0; subst.
        rewrite Z.div_mul; try lia.
        replace (x * 2 * (x * 2 + 1)) with (x * (x * 2 + 1) * 2) by ring.
        rewrite Z.div_mul; lia.
      * pose proof (Z.mod_pos_bound number 2 ltac:(lia)).
        change Int.max_unsigned with 4294967295.
        lia.
      * change Int.max_unsigned with 4294967295; lia.
  + forward.
    entailer!.
    split; [| split].
    - unfold triangular.
      apply Z.div_pos; nia.
    - unfold triangular.
      change Int.max_unsigned with (8589934590 / 2).
      apply Z.div_le_mono; nia.
    - assert (number mod 2 <> 0) by congruence.
      pose proof (Z_div_mod_eq_full number 2).
      pose proof (Z.mod_pos_bound number 2 ltac:(lia)).
      assert (number mod 2 = 1) by lia.
      rewrite H4 in H2.
      do 2 f_equal.
      unfold triangular.
      rewrite H2 at 1 4.
      replace (2 * (number / 2) + 1 + 1) with ((number / 2 + 1) * 2) by ring.
      rewrite Z.div_mul; try lia.
      replace (number * ((number / 2 + 1) * 2)) with ((number * (number / 2 + 1)) * 2) by ring.
      rewrite Z.div_mul; lia.
Qed.

Lemma solution_correct: semax_body Vprog Gprog f_solution solution_spec.
Proof.
  start_function.
  assert (0 <= number / 3 <= 92681) as H1.
  { change 92681 with (278043 / 3).
    split; [apply Z.div_pos | apply Z.div_le_mono]; lia. }
  assert (0 <= number / 5 <= 92681) as H2.
  { change 92681 with (463405 / 5).
    split; [apply Z.div_pos | apply Z.div_le_mono]; lia. }
  assert (0 <= number / 15 <= 92681) as H3.
  { change 92681 with (1390215 / 15).
    split; [apply Z.div_pos | apply Z.div_le_mono]; lia. }
  forward_call (number / 3).
  forward_call (number / 15).
  Intros w.
  forward_call (number / 5).
  forward.
  entailer!.
  split; [| split].
  + apply sum_multiples_of_3_or_5_nonneg; lia. 
  + pose proof (sum_multiples_of_3_or_5_increasing 135671 number H).
    rewrite (sum_multiples_eq_closed_form 135671) in H4; try lia.
    change (closed_form 135671) with 4294927803 in H4.
    change Int.max_unsigned with 4294967295.
    lia.
  + Opaque Z.div. simpl. Transparent Z.div.
    rewrite (mul_repr 15).
    rewrite sub_repr.
    rewrite add_repr.
    rewrite sum_multiples_eq_closed_form; try lia.
    unfold closed_form.
    do 2 f_equal.
    lia.
Qed.

