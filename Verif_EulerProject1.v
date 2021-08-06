Require Import VST.floyd.proofauto.
Require Import EulerProject1.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition nat_divide_dec a b: { Nat.divide a b } + { ~ Nat.divide a b }.
Proof.
  destruct (Zdivide_dec (Z.of_nat a) (Z.of_nat b)).
  + left. destruct d. exists (Z.to_nat x). lia.
  + right. intro. apply n. destruct H. rewrite H. exists (Z.of_nat x). lia.
Defined.

Definition criterion (n: Z): bool :=
  if (Zdivide_dec 3 n)
    then true
    else if (Zdivide_dec 5 n)
      then true
      else false.
Definition sum_Z: list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a++b) = sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; lia.
Qed.

Definition seq_Z (n: Z): list Z := map Z.of_nat (seq 1 (Z.to_nat n)).

Definition result (n: Z): Z := sum_Z (filter criterion (seq_Z n)).

Definition aux n: Z := n * (n + 1) / 2.
Definition faster_result n := 3 * aux (n / 3) + 5 * aux (n / 5) - 15 * aux (n / 15).

Eval compute in (faster_result 999).

Theorem thm_0 n (H: 0 <= n) (H0: Zeven n): aux n = (n / 2) * (n + 1).
Proof.
  unfold aux. apply Zeven_div2 in H0. remember (Z.div2 n) as x. rewrite H0.
  replace (2 * x * (2 * x + 1)) with (x * (x * 2 + 1) * 2) by ring.
  replace (2 * x) with (x * 2) by ring.
  repeat rewrite Z_div_mult; lia.
Qed.

Theorem thm_1 n (H: 0 <= n) (H0: Zodd n): aux n = n * ((n + 1) / 2).
Proof.
  unfold aux. apply Zodd_div2 in H0. remember (Z.div2 n) as x. rewrite H0.
  replace ((2 * x + 1) * (2 * x + 1 + 1)) with ((2 * x + 1) * (x + 1) * 2) by ring.
  replace (2 * x + 1 + 1) with ((x + 1) * 2) by ring.
  repeat rewrite Z_div_mult; lia.
Qed.

Theorem thm_2 n (H: 0 <= n): aux (n + 1) = aux n + n + 1.
Proof.
  revert n H. apply natlike_ind.
  + compute. auto.
  + intros. destruct (Zeven_odd_dec x).
    - pose proof (Zodd_Sn _ z). pose proof (Zeven_Sn _ H1).
      repeat rewrite <- Z.add_1_r in *.
      apply thm_0 in H2; try lia. apply thm_1 in H1; try lia. rewrite H1, H2.
      apply Zeven_div2 in z. remember (Z.div2 x) as w. rewrite z.
      replace (2 * w + 1 + 1) with ((w + 1) * 2) by ring.
      repeat rewrite Z_div_mult; lia.
    - pose proof (Zeven_Sn _ z). pose proof (Zodd_Sn _ H1).
      repeat rewrite <- Z.add_1_r in *.
      apply thm_0 in H1; try lia. apply thm_1 in H2; try lia. rewrite H1, H2.
      apply Zodd_div2 in z. remember (Z.div2 x) as w. rewrite z.
      replace (2 * w + 1 + 1 + 1 + 1) with ((w + 2) * 2) by ring.
      replace (2 * w + 1 + 1) with ((w + 1) * 2) by ring.
      repeat rewrite Z_div_mult; lia.
Qed.

Theorem thm_3 a n (Ha: 0 < a) (Hn: 0 <= n):
  (n + 1) / a = if Zdivide_dec a (n + 1) then n / a + 1 else n / a.
Proof.
  pose proof Hn as Hn'. revert Hn. pattern n. apply Z_lt_induction.
  + intros. assert (0 <= x <= a - 2 \/ a - 1 = x \/ a <= x) by lia.
    destruct H0; [|destruct H0].
    - assert (1 <= x + 1 < a) by lia. rewrite Z.div_small; try lia.
      destruct Zdivide_dec.
      * destruct d. assert (x0 = 0 \/ 1 <= x0) by lia. destruct H3.
        ++ lia.
        ++ nia.
      * rewrite Z.div_small; lia.
    - subst. replace (a - 1 + 1) with a by ring.
      rewrite Z.div_same; try lia. destruct Zdivide_dec.
      * rewrite Z.div_small; lia.
      * exfalso. apply n0. exists 1. lia.
    - assert (0 <= x - a < x) by lia. pose proof (H _ H1 (proj1 H1)).
      destruct (Zdivide_dec a (x - a + 1)).
      * destruct d. destruct Zdivide_dec.
        ++ assert (x + 1 = (x0 + 1) * a) by lia. rewrite H4.
           assert (x = x0 * a + (a - 1)) by lia. rewrite H5.
           rewrite Z_div_mult; try lia.
           rewrite Z.div_add_l; try lia.
           rewrite Z.div_small; lia.
        ++ exfalso. apply n0. exists (x0 + 1). lia.
      * destruct Zdivide_dec.
        ++ destruct d. exfalso. apply n0. exists (x0 - 1). lia.
        ++ replace (x + 1) with (1 * a + (x - a + 1)) by ring.
           rewrite Z.div_add_l; try lia.
           replace x with (1 * a + (x - a)) at 2 by ring.
           rewrite Z.div_add_l; lia.
  + auto.
Qed.

Theorem thm_4 a n (Ha: 0 < a) (Hn: 0 <= n) (H: (a | Z.succ n)): a * aux (Z.succ n / a) = a * aux (n / a) + Z.succ n.
Proof.
  ring_simplify. rewrite thm_3; auto. destruct Zdivide_dec.
  + rewrite thm_2. ring_simplify.
    destruct d. assert (n = (x - 1) * a + (a - 1)) by lia.
    assert (n / a = x - 1).
    { rewrite H1. rewrite Z.div_add_l; try lia. rewrite Z.div_small; lia. }
    rewrite H2. rewrite H1. lia. apply Z_div_pos; lia.
  + replace (Z.succ n) with (n + 1) in H by lia. tauto.
Qed.

Theorem thm_5 a n (Ha: 0 < a) (Hn: 0 <= n) (H: ~ (a | Z.succ n)): a * aux (Z.succ n / a) = a * aux (n / a).
Proof.
  ring_simplify. rewrite thm_3; auto. destruct Zdivide_dec.
  + replace (Z.succ n) with (n + 1) in H by ring. tauto.
  + auto.
Qed.

Theorem both_results_equal (n: Z) (H: 0 <= n): result n = faster_result n.
Proof.
  revert n H. apply natlike_ind.
  + compute. auto.
  + intros. unfold result, faster_result in *.
    replace (seq_Z (Z.succ x)) with (seq_Z x ++ Z.succ x :: nil).
    rewrite filter_app, sum_Z_app. rewrite H0. clear H0.
    unfold criterion. simpl. destruct (Zdivide_dec 3 (Z.succ x)).
    - simpl. replace (Z.succ x + 0) with (Z.succ x) by ring.
      rewrite thm_4; try lia; auto.
      destruct (Zdivide_dec 5 (Z.succ x)).
      * assert (15 | Z.succ x).
        { assert (Z.lcm 3 5 = 15) by reflexivity. rewrite <- H0. apply Z.lcm_least; auto. }
        rewrite thm_4; try lia; auto.
        rewrite thm_4; try lia; auto.
      * rewrite thm_5; try lia; auto.
        assert (~ (15 | Z.succ x)).
        { intro. apply n. clear n. destruct H0. exists (3 * x0). lia. }
        rewrite thm_5; try lia; auto.
     - rewrite thm_5; try lia; auto. destruct Zdivide_dec.
       * rewrite thm_4; try lia; auto.
         assert (~ (15 | Z.succ x)).
         { intro. apply n. clear n. destruct H0. exists (5 * x0). lia. }
         rewrite thm_5; try lia; auto. simpl. lia.
       * assert (~ (15 | Z.succ x)).
         { intro. apply n. destruct H0. exists (x0 * 5). lia. }
         rewrite thm_5; try lia; auto.
         rewrite thm_5; try lia; auto. simpl. lia.
    - unfold seq_Z. rewrite Z2Nat.inj_succ; auto. rewrite seq_S.
      simpl. rewrite map_app. f_equal. simpl. f_equal. lia.
Qed.

Definition aux_spec: ident * funspec :=
DECLARE _aux
  WITH number: Z
  PRE [ tuint ]
    PROP(0 <= number <= 1000)
    PARAMS(Vint (Int.repr number))
    SEP()
  POST [ tuint ]
    PROP()
    RETURN(Vint (Int.repr (aux number)))
    SEP().

Definition solution_spec: ident * funspec :=
DECLARE _solution
  WITH number: Z
  PRE [ tuint ]
    PROP(0 <= number <= 1000)
    PARAMS(Vint (Int.repr number))
    SEP()
  POST [ tuint ]
    PROP()
    RETURN(Vint (Int.repr (result number)))
    SEP().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]
    PROP() 
    RETURN (Vint (Int.repr (result 999)))
    SEP().

Definition Gprog := [aux_spec; solution_spec; main_spec].

Lemma body_aux: semax_body Vprog Gprog f_aux aux_spec.
Proof.
  start_function.
  forward.
  entailer!.
  unfold aux.
  unfold Int.divu.
  change (Int.unsigned (Int.repr 2)) with 2.
  rewrite Int.unsigned_repr.
  reflexivity.
  change Int.max_unsigned with 4294967295.
  nia.
Qed.

Lemma body_solution: semax_body Vprog Gprog f_solution solution_spec.
Proof.
  start_function.
  forward_call (number / 3).
  + entailer!. simpl. unfold Int.divu.
    rewrite Int.unsigned_repr. rewrite Int.unsigned_repr. reflexivity.
    { rep_lia. }
    { rep_lia. }
  + split.
    - apply Z.div_pos. lia. lia.
    - assert (number / 3 <= 333).
      change 333 with (1000/3). apply Z.div_le_mono. lia. lia. lia.
  + forward_call (number / 5).
    - entailer!. simpl. unfold Int.divu.
      rewrite Int.unsigned_repr. rewrite Int.unsigned_repr. reflexivity.
      { rep_lia. }
      { rep_lia. }
    - split.
      * apply Z.div_pos. lia. lia.
      * assert (number / 5 <= 200).
        change 200 with (1000/5). apply Z.div_le_mono. lia. lia. lia.
    - forward_call (number / 15).
      ++ entailer!. simpl. unfold Int.divu.
         repeat rewrite Int.unsigned_repr. reflexivity.
         { rep_lia. }
         { rep_lia. }
      ++ split.
         -- apply Z.div_pos. lia. lia.
         -- assert (number / 15 <= 66).
            change 66 with (1000/15). apply Z.div_le_mono. lia. lia. lia.
      ++ deadvars!. forward.
         -- entailer!.
            assert (0 <= number / 15 <= 66).
            { split.
              + apply Z.div_pos. lia. lia.
              + change 66 with (1000 / 15). apply Z.div_le_mono. lia. lia. }
            assert (0 <= number / 15 * (number / 15 + 1) <= 4422) by nia.
            assert (0 <= number / 15 * (number / 15 + 1) / 2 <= 2211).
            { split.
              + apply Z.div_pos. lia. lia.
              + change 2211 with (4422 / 2). apply Z.div_le_mono. lia. lia. }
            assert (0 <= number / 3 <= 333).
            { split.
              + apply Z.div_pos. lia. lia.
              + change 333 with (1000 / 3). apply Z.div_le_mono. lia. lia. }
            assert (0 <= number / 3 * (number / 3 + 1) <= 111222) by nia.
            assert (0 <= number / 3 * (number / 3 + 1) / 2 <= 55611).
            { split.
              + apply Z.div_pos. lia. lia.
              + change 55611 with (111222 / 2). apply Z.div_le_mono. lia. lia. }
            assert (0 <= number / 5 <= 200).
            { split.
              + apply Z.div_pos. lia. lia.
              + change 200 with (1000 / 5). apply Z.div_le_mono. lia. lia. }
            assert (0 <= number / 5 * (number / 5 + 1) <= 40200) by nia.
            assert (0 <= number / 5 * (number / 5 + 1) / 2 <= 20100).
            { split.
              + apply Z.div_pos. lia. lia.
              + change 20100 with (40200 / 2). apply Z.div_le_mono. lia. lia. }
            unfold aux. repeat rewrite Int.signed_repr; try rep_lia.
         -- entailer!. rewrite both_results_equal; try lia.
            unfold faster_result. reflexivity.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function. forward_call 999.
  + lia.
  + forward. clear Delta.
    
