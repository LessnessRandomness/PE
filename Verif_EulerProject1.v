Require Import VST.floyd.proofauto.
Require Import EulerProject1.
Instance CompSpecs: compspecs. make_compspecs prog. Defined.
Definition Vprog: varspecs. mk_varspecs prog. Defined.


Definition criterion (n: Z): bool :=
  if (Zdivide_dec 3 n)
    then true
    else if (Zdivide_dec 5 n)
      then true
      else false.
Definition sum_Z: list Z -> Z := fold_right Z.add 0.

Lemma sum_Z_app:
  forall a b, sum_Z (a ++ b) = sum_Z a + sum_Z b.
Proof.
  intros. induction a; simpl; lia.
Qed.

Definition seq_Z (n: Z): list Z := map Z.of_nat (seq 1 (Z.to_nat n)).

Definition result (n: Z): Z := sum_Z (filter criterion (seq_Z n)).

Definition aux n: Z := n * (n + 1) / 2.
Definition faster_result n := 3 * aux (n / 3) + 5 * aux (n / 5) - 15 * aux (n / 15).


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
  destruct (Zdivide_dec a (n + 1)) as [Hd | Hd].
  + destruct Hd as [k Hk]. assert (n / a = k - 1). 
    { replace n with ((k - 1) * a + (a - 1)) by lia.
      rewrite Z.div_add_l; try lia. rewrite Z.div_small; try lia. }
    rewrite Hk, Z_div_mult; try lia.
  + assert ((n + 1) mod a <> 0).
    { intro. apply Hd. apply Zmod_divide; try lia. }
    apply Z.div_unique with (r := (n + 1) mod a - 1); try lia.
    - left. pose proof (Z.mod_pos_bound (n + 1) a Ha). lia.
    - pose proof (Z_div_mod_eq (n + 1) a). lia.
Qed.

Theorem thm_4 a n (Ha: 0 < a) (Hn: 0 <= n) (H: (a | n + 1)):
  a * aux ((n + 1) / a) = a * aux (n / a) + (n + 1).
Proof.
  ring_simplify. rewrite thm_3; auto. destruct Zdivide_dec; try tauto.
  rewrite thm_2. ring_simplify. destruct d.
  assert (n = (x - 1) * a + (a - 1)) by lia. assert (n / a = x - 1).
  { rewrite H1, Z.div_add_l, Z.div_small; lia. }
  rewrite H2, H1. lia. apply Z_div_pos; lia.
Qed.

Theorem thm_5 a n (Ha: 0 < a) (Hn: 0 <= n) (H: ~ (a | Z.succ n)):
  a * aux ((n + 1) / a) = a * aux (n / a).
Proof.
  ring_simplify. rewrite thm_3; auto. destruct Zdivide_dec; auto. tauto.
Qed.

Lemma step_result (n : Z) (H : 0 <= n) :
  result (Z.succ n) = result n + (if criterion (Z.succ n) then Z.succ n else 0).
Proof.
  unfold result. replace (seq_Z (Z.succ n)) with (seq_Z n ++ Z.succ n :: nil).
  + rewrite filter_app. simpl. rewrite sum_Z_app. f_equal.
    destruct criterion; auto. simpl. ring.
  + unfold seq_Z. rewrite Z2Nat.inj_succ; auto. rewrite seq_S. simpl.
    rewrite map_app. f_equal. rewrite map_cons. simpl (map _ []).
    f_equal. lia.
Qed.

Theorem both_results_equal (n: Z) (H: 0 <= n): result n = faster_result n.
Proof.
  revert n H. apply natlike_ind.
  + compute. auto.
  + intros. rewrite step_result; auto. unfold faster_result in *.
    unfold criterion. repeat rewrite <- Z.add_1_r.
    destruct (Zdivide_dec 3 (x + 1)), (Zdivide_dec 5 (x + 1)).
    - assert (15 | x + 1).
      { assert (Z.lcm 3 5 = 15) by auto. rewrite <- H1.
        apply Z.lcm_least; auto. }
      repeat rewrite thm_4; try lia; auto.
    - assert (~ (15 | x + 1)).
      { intro. apply n. destruct H1. exists (3 * x0). lia. }
      rewrite (thm_5 5 x); try lia; auto. rewrite (thm_5 15 x); try lia; auto.
      rewrite thm_4; try lia; auto.
    - assert (~ (15 | x + 1)).
      { intro. apply n. destruct H1. exists (5 * x0). lia. }
      rewrite (thm_5 3 x); try lia; auto. rewrite (thm_5 15 x); try lia; auto.
      rewrite thm_4; try lia; auto.
    - assert (~ (15 | x + 1)).
      { intro. apply n. destruct H1. exists (5 * x0). lia. }
      repeat rewrite thm_5; try lia; auto.
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
     SEP(TT).

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
  + split.
    - apply Z.div_pos; lia.
    - assert (number / 3 <= 333).
      { change 333 with (1000 / 3). apply Z.div_le_mono; lia. }
      lia.
  + forward_call (number / 5).
    - split.
      * apply Z.div_pos; lia.
      * assert (number / 5 <= 200).
        { change 200 with (1000 / 5). apply Z.div_le_mono; lia. }
        lia.
    - forward_call (number / 15).
      ++ split.
         -- apply Z.div_pos; lia.
         -- assert (number / 15 <= 66).
            { change 66 with (1000 / 15). apply Z.div_le_mono; lia. }
            lia.
      ++ deadvars!. forward.
         entailer!. rewrite both_results_equal; try lia. auto.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function. forward_call 999.
  remember (result 999) as W. clear HeqW. time forward.
Qed.
