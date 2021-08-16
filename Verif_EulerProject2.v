Require Import VST.floyd.proofauto.

Definition sequence A := nat -> A.

Definition increasing (f: sequence Z) := forall (n: nat), f n < f (S n).

Theorem thm0 (g: sequence nat) (H: forall n, (g n < g (S n))%nat) (a b: nat) (H0: (a < b)%nat): (g a < g b)%nat.
Proof.
  induction H0.
  + apply H.
  + pose (H m). lia.
Qed.

Theorem thm1 (g: sequence nat) (H: forall n, (g n < g (S n))%nat) (a b: nat) (H0: (g a < g b)%nat): (a < b)%nat.
Proof.
  revert b H0. induction a; intros.
  + destruct b.
    - lia.
    - lia.
  + pose (H a). assert (g a < g b)%nat by lia. apply IHa in H1.
    inversion H1.
    - subst. lia.
    - lia.
Qed.

Theorem thm2 (f: sequence Z) (H: increasing f) (a b: nat) (H0: (a <= b)%nat): f a <= f b.
Proof.
  induction H0.
  + lia.
  + pose (H m). lia.
Qed.

Theorem thm3 (f: sequence Z) (H: increasing f) (a b: nat) (H0: f a <= f b): (a <= b)%nat.
Proof.
  revert b H0. induction a; intros.
  + destruct b; lia.
  + pose (H a). assert (f a <= f b) by lia. apply IHa in H1. inversion H1.
    - subst. lia.
    - lia.
Qed.

Definition unnamed0 (g: sequence nat) (H: forall i, (g i < g (S i))%nat) (M: nat) (H0: g 0%nat = 0%nat):
  { n | forall i, (i < n <-> g i <= M)%nat }.
Proof.
  induction M.
  + exists 1%nat. split; intros.
    - assert (i = 0)%nat by lia. subst. lia.
    - assert (g i = 0)%nat by lia. clear H2. destruct i.
      * lia.
      * pose (H i). lia.
  + destruct IHM. destruct (le_dec (g x) (S M)).
    - exists (S x). split; intros.
      * assert (i0 <= x)%nat by lia. clear H1. inversion H2.
        ++ subst. auto.
        ++ subst. assert (i0 < S m)%nat by lia. apply i in H3. lia.
      * inversion l.
        ++ clear l. assert (i0 <= x \/ x < i0)%nat by lia. destruct H2; try lia.
           apply (thm0 g H) in H2. lia.
        ++ subst. apply i in H3. lia.
    - exists x. split; intros.
      * apply i in H1. lia.
      * assert (g i0 < g x)%nat by lia. apply (thm1 g H) in H2. auto.
Defined.

Definition unnamed1 (f: sequence Z) (H: increasing f) (max: Z): { n | forall i, (i < n)%nat <-> f i <= max }.
Proof.
  destruct (Z_lt_le_dec max (f 0%nat)).
  + exists 0%nat. split; intros.
    - lia.
    - induction i.
      * lia.
      * pose (H i). lia.
  + pose (fun (n: nat) => Z.to_nat (f n - f 0%nat)) as g.
    assert (forall i, (g i < g (S i))%nat) as H0.
    { intros. unfold g. induction i.
      + pose (H 0%nat). lia.
      + pose (H (S i)). lia. }
    assert (g 0%nat = 0%nat) as H1.
    { unfold g. lia. }
    pose proof (unnamed0 g H0 (Z.to_nat (max - f 0%nat)) H1) as H2.
    destruct H2. exists x. split; intros.
    - apply i in H2. unfold g in H2. lia.
    - apply i. unfold g. lia.
Defined.

Fixpoint recurrent_sequence (k1 k2 a b: Z) (n: nat): Z :=
  match n with
  | O => a
  | S O => b
  | S (S m as n') => k1 * recurrent_sequence k1 k2 a b m + k2 * recurrent_sequence k1 k2 a b n'
  end.

Definition fib := recurrent_sequence 1 1 1 2.

Theorem recurrent_sequence_unfold (k1 k2 a b: Z) (n: nat):
  recurrent_sequence k1 k2 a b (S (S n)) = k1 * recurrent_sequence k1 k2 a b n + k2 * recurrent_sequence k1 k2 a b (S n).
Proof.
  reflexivity.
Qed.

Theorem fib_increasing: increasing fib.
Proof.
  unfold increasing.
  assert (forall n, fib n < fib (S n) < fib (S (S n))).
  { induction n.
    + unfold fib. simpl. lia.
    + destruct IHn. split; auto.
      unfold fib in *. repeat rewrite recurrent_sequence_unfold in *. lia. }
  intros. apply H.
Qed.

Theorem fib_even_thm (n: nat):
  Zodd (fib (3 * n)) /\ Zeven (fib (S (3 * n))) /\ Zodd (fib (S (S (3 * n)))).
Proof.
  induction n.
  + simpl. auto.
  + destruct IHn as [H [H0 H1]]. repeat split.
    - replace (fib (3 * S n)) with (fib (3 * n) + 2 * fib (S (3 * n))).
      apply Zodd_ex_iff. apply Zodd_ex_iff in H. destruct H.
      exists (x + fib (S (3 * n))). lia.
      { replace (3 * S n)%nat with (S (S (S (3 * n))))%nat by lia.
        unfold fib. repeat rewrite recurrent_sequence_unfold. lia. }
    - replace (fib (S (3 * S n))) with (fib (S (3 * n)) + 2 * fib (S (S (3 * n)))).
      apply Zeven_ex_iff. apply Zeven_ex_iff in H0.
      destruct H0. exists (x + fib (S (S (3 * n)))). lia.
      { replace (3 * S n)%nat with (S (S (S (3 * n))))%nat by lia.
        unfold fib. repeat rewrite recurrent_sequence_unfold. lia. }
    - replace (fib (S (S (3 * S n)))) with (2 * fib (S (3 * n)) + 3 * fib (S (S (3 * n)))).
      apply Zodd_ex_iff. apply Zodd_ex_iff in H1. destruct H1.
      exists (fib (S (3 * n)) + 3 * x + 1). lia.
      { replace (3 * (S n))%nat with (S (S (S (3 * n))))%nat by lia.
        unfold fib. repeat rewrite recurrent_sequence_unfold. lia. }
Qed.

Definition even_fib := recurrent_sequence 1 4 2 8.

Theorem even_fib_increasing: increasing even_fib.
Proof.
  unfold increasing. intros.
  assert (even_fib n < even_fib (S n) < even_fib (S (S n))).
  { induction n.
    + compute; auto.
    + destruct IHn. split; auto. unfold even_fib in *.
      repeat rewrite recurrent_sequence_unfold in *.
      lia. }
  apply H.
Qed.

Theorem even_fib_thm (n: nat): even_fib n = fib (S (3 * n)).
Proof.
  assert (even_fib n = fib (S (3 * n)) /\ even_fib (S n) = fib (S (3 * S n))).
  { induction n.
    + simpl. compute. auto.
    + destruct IHn. split; auto.
      replace (even_fib (S (S n))) with (even_fib n + 4 * even_fib (S n)).
      rewrite H, H0.
      replace (3 * S (S n))%nat with (S (S (S (S (S (S (3 * n)))))))%nat by lia.
      replace (3 * S n)%nat with (S (S (S (3 * n))))%nat by lia.
      unfold fib. repeat rewrite recurrent_sequence_unfold. ring.
      { unfold even_fib. repeat rewrite recurrent_sequence_unfold. ring. } }
  apply H.
Qed.

Definition sum_Z: list Z -> Z := fold_right Z.add 0.
Theorem sum_Z_app (l1 l2: list Z): sum_Z (l1 ++ l2) = sum_Z l1 + sum_Z l2.
Proof.
  revert l2. induction l1.
  + simpl. lia.
  + simpl. intro. rewrite IHl1. lia.
Qed.

Definition increasing_sequence_with_max_value (f: sequence Z) (H: increasing f) (max: Z): list Z :=
  map f (seq 0 (proj1_sig (unnamed1 f H max))).

Eval compute in (increasing_sequence_with_max_value fib fib_increasing 6).
Eval compute in (proj1_sig (unnamed1 fib fib_increasing 6)).

(* Theorem increasing_sequence_with_max_value_thm (f: sequence Z) (H: increasing f) (max: Z):
  increasing_sequence_with_max_value f H (max + 1) =
  increasing_sequence_with_max_value f H max ++
    if Z_le_lt_dec (f (S (proj1_sig (unnamed1 f H max)))) (max + 1)
    then [f (S (proj1_sig (unnamed1 f H max)))]
    else [].
Proof.
  unfold increasing_sequence_with_max_value.
  repeat destruct unnamed1. simpl.
  destruct Z_le_lt_dec.
  + pose (H x0). assert (f x0 <= max) by lia.
    apply i0 in H0. lia.
  + 
*)

Theorem aux0 (f: sequence Z) (H: increasing f) (max: Z):
  (proj1_sig (unnamed1 f H (max + 1)) =
  proj1_sig (unnamed1 f H max) + 
  if Z_lt_le_dec (max + 1) (f (proj1_sig (unnamed1 f H max)))
  then 0
  else if Z.eq_dec (max + 1) (f (proj1_sig (unnamed1 f H max)))
    then 1
    else 0)%nat.
Proof.
  destruct Z_lt_le_dec; simpl in *.
  + repeat destruct unnamed1 in *; simpl in *.
    replace (x + 0)%nat with x by lia.
    assert (f x <= max + 1 -> False) by lia.
    rewrite <- i0 in H0. assert (x0 <= x)%nat by lia.
    inversion H1.
    - auto.
    - subst. clear H0 H1. assert (x0 < S m)%nat by lia.
      apply i in H0. assert (f x0 <= max + 1) by lia.
      apply i0 in H1. lia.
  + repeat destruct unnamed1 in *; simpl in *. destruct Z.eq_dec.
    - rewrite e in i0. assert (forall i, f i <= f x <-> (i <= x)%nat).
      { split. apply thm3; auto. apply thm2; auto. }
      setoid_rewrite H0 in i0. destruct x0.
      * exfalso. pose proof (i0 x). pose proof (le_n x). apply H1 in H2. lia.
      * assert (x0 < S x0)%nat by lia. apply i0 in H1.
        assert (x <= x)%nat by lia. apply i0 in H2. lia.
    - assert (f x <= max) by lia. apply i in H0. lia.
Qed.

Definition result_simple (max: Z): Z :=
  sum_Z (filter Z.even (increasing_sequence_with_max_value fib fib_increasing max)).

Definition result_more_effective (max: Z): Z :=
  sum_Z (increasing_sequence_with_max_value even_fib even_fib_increasing max).

Theorem Zeven_sum (a b: Z): Zeven (a + b) -> (Zeven a /\ Zeven b \/ Zodd a /\ Zodd b).
Proof.
  intros. destruct (Zeven_odd_dec a), (Zeven_odd_dec b); try tauto.
  + pose proof (Zeven_plus_Zodd _ _ z z0). apply Zodd_not_Zeven in H0. tauto.
  + pose proof (Zodd_plus_Zeven _ _ z z0). apply Zodd_not_Zeven in H0. tauto.
Qed.

Theorem Zodd_sum (a b: Z): Zodd (a + b) -> (Zeven a /\ Zodd b \/ Zodd a /\ Zeven b).
Proof.
  intros. destruct (Zeven_odd_dec a), (Zeven_odd_dec b); try tauto.
  + pose proof (Zeven_plus_Zeven _ _ z z0). apply Zodd_not_Zeven in H. tauto.
  + pose proof (Zodd_plus_Zodd _ _ z z0). apply Zodd_not_Zeven in H. tauto.
Qed.

Theorem fib_unfold n: fib (S (S n)) = fib n + fib (S n).
Proof.
  unfold fib. rewrite recurrent_sequence_unfold. lia.
Qed.

Theorem aux1 (n: nat):
  let P: nat -> Prop :=
    fun n => (Zeven (fib n) <-> exists m, n = (3 * m + 1)%nat) /\
    (Zodd (fib n) <-> exists m, n = (3 * m)%nat \/ n = (3 * m + 2)%nat) in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { induction n; split; intros; split; intros; split; intros.
    + rewrite Zeven_ex_iff in H. destruct H. change (fib 0) with 1 in H. lia.
    + rewrite Zeven_ex_iff. destruct H. lia.
    + exists 0%nat. left. reflexivity.
    + rewrite Zodd_ex_iff. exists 0. reflexivity.
    + exists 0%nat. reflexivity.
    + rewrite Zeven_ex_iff. exists 1. reflexivity.
    + rewrite Zodd_ex_iff in H. destruct H. change (fib 1) with 2 in H. lia.
    + destruct H. lia.
    + apply IHn in H. auto.
    + apply IHn. auto.
    + apply IHn in H. auto.
    + apply IHn. auto.
    + rewrite fib_unfold in H. apply Zeven_sum in H. destruct H.
      - destruct H. apply IHn in H, H0. destruct H, H0. lia.
      - destruct H. apply IHn in H, H0. destruct H, H0. exists x0. lia.
    + rewrite fib_unfold. destruct H.
      assert (exists m, S n = (3 * m)%nat \/ S n = (3 * m + 2)%nat).
      { exists x. lia. }
      apply IHn in H0. assert (exists m, n = (3 * m)%nat \/ n = (3 * m + 2)%nat).
      { exists (x - 1)%nat. lia. }
      apply IHn in H1. apply Zodd_plus_Zodd; auto.
    + rewrite fib_unfold in H. apply Zodd_sum in H. destruct H.
      - destruct H. apply IHn in H, H0. destruct H, H0. exists (S x0). lia.
      - destruct H. apply IHn in H, H0. destruct H, H0. exists x0. lia.
    + rewrite fib_unfold. destruct H. destruct H.
      - assert (exists m, S n = 3 * m \/ S n = 3 * m + 2)%nat.
        { exists (x - 1)%nat. lia. }
        apply IHn in H0. assert (exists m, n = 3 * m + 1)%nat.
        { exists (x - 1)%nat. lia. }
        apply IHn in H1. apply Zeven_plus_Zodd; auto.
      - assert (exists m, S n = 3 * m + 1)%nat.
        { exists x. lia. }
        apply IHn in H0. assert (exists m, n = 3 * m \/ n = 3 * m + 2)%nat.
        { exists x. lia. }
        apply IHn in H1. apply Zodd_plus_Zeven; auto. }
  apply H.
Qed.

Theorem aux2 (n: Z) (L: list Z): fold_right Z.add n L = fold_right Z.add 0 L + n.
Proof.
  induction L.
  + simpl. lia.
  + simpl. lia.
Qed.

Theorem aux3 (n: nat): sum_Z (filter Z.even (map fib (seq 0 n))) = sum_Z (map even_fib (seq 0 ((n + 1) / 3))).
Proof.
  induction n.
  + simpl. auto.
  + replace (S n + 1)%nat with (n + 2)%nat by lia. rewrite seq_S. change (0 + n)%nat with n.
    rewrite map_app. change (map fib [n]) with ([fib n]).
    rewrite filter_app. simpl filter. remember (Z.even (fib n)) as W.
    destruct W.
    - unfold sum_Z in *. rewrite fold_right_app. simpl fold_right at 1.
      replace (fib n + 0) with (fib n) by lia.
      rewrite aux2. symmetry in HeqW. rewrite Zeven_bool_iff in HeqW.
      apply aux1 in HeqW. destruct HeqW. subst.
      replace ((3 * x + 1 + 1) / 3)%nat with x in IHn.
      replace ((3 * x + 1 + 2) / 3)%nat with (S x)%nat.
      rewrite IHn. rewrite seq_S. change (0 + x)%nat with x.
      rewrite map_app. change (map even_fib [x]) with ([even_fib x]).
      rewrite fold_right_app. simpl fold_right. replace (even_fib x + 0) with (even_fib x) by lia.
      rewrite even_fib_thm. rewrite (aux2 (fib (S (3 * x)))).
      replace (S (3 * x))%nat with (3 * x + 1)%nat by lia. reflexivity.
      { replace (3 * x + 1 + 2)%nat with ((x + 1) * 3)%nat by lia. rewrite Nat.div_mul; lia. }
      { replace (3 * x + 1 + 1)%nat with (2 + x * 3)%nat by lia.
        rewrite Nat.div_add. simpl. reflexivity. lia. }
    - unfold sum_Z in *. rewrite fold_right_app. simpl fold_right at 1.
      symmetry in HeqW. assert (Z.odd (fib n) = true).
      { rewrite <- Z.negb_even. rewrite HeqW. reflexivity. }
      rewrite Zodd_bool_iff in H. clear HeqW. apply aux1 in H. 
      destruct H. destruct H.
      * subst. replace ((3 * x + 2) / 3)%nat with x.
        replace ((3 * x + 1) / 3)%nat with x in IHn. auto.
        { replace (3 * x + 1)%nat with (1 + x * 3)%nat by lia.
          rewrite Nat.div_add. simpl. reflexivity. lia. }
        { replace (3 * x + 2)%nat with (2 + x * 3)%nat by lia.
          rewrite Nat.div_add. simpl. reflexivity. lia. }
      * subst. replace ((3 * x + 2 + 2) / 3)%nat with (x + 1)%nat.
        replace ((3 * x + 2 + 1) / 3)%nat with (x + 1)%nat in IHn. auto.
        { replace (3 * x + 2 + 1)%nat with ((x + 1) * 3)%nat by lia. rewrite Nat.div_mul; lia. }
        { replace (3 * x + 2 + 2)%nat with (1 + (x + 1) * 3)%nat by lia.
          rewrite Nat.div_add. simpl. reflexivity. lia. }
Qed.

Theorem aux4 (n: nat): (exists m, n = 3 * m \/ n = 3 * m + 1 \/ n = 3 * m + 2)%nat.
Proof.
  apply (lt_wf_ind n). clear n. intros.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ 3 <= n)%nat by lia.
  destruct H0 as [H0 | [H0 | [H0 | H0]]].
  + subst. exists 0%nat. lia.
  + subst. exists 0%nat. lia.
  + subst. exists 0%nat. lia.
  + assert (n - 3 < n)%nat by lia. destruct (H _ H1).
    destruct H2 as [H2 | [H2 | H2]].
    - exists (S x). lia.
    - exists (S x). lia.
    - exists (S x). lia.
Qed.

Theorem even_fib_bigger_than_0 (n: nat): 0 < even_fib n.
Proof.
  assert (0 < even_fib n /\ 0 < even_fib (S n)).
  { induction n.
    + change (even_fib 0) with 2. change (even_fib 1) with 8. lia.
    + destruct IHn. split; auto. unfold even_fib in *. rewrite recurrent_sequence_unfold.
      lia. }
  apply H.
Qed.

Theorem aux5 (n m: nat): (n <= m)%nat -> sum_Z (map even_fib (seq 0 n)) <= sum_Z (map even_fib (seq 0 m)).
Proof.
  intro. induction H.
  + lia.
  + rewrite seq_S. simpl. rewrite map_app. simpl.
    replace (sum_Z (map even_fib (seq 0 m) ++ [even_fib m])) with (sum_Z (map even_fib (seq 0 m)) + even_fib m).
    pose proof (even_fib_bigger_than_0 m). lia.
    { unfold sum_Z. rewrite fold_right_app. simpl.
      rewrite <- aux2. replace (even_fib m + 0) with (even_fib m) by lia. reflexivity. }
Qed.

Theorem aux6 (n m: nat): sum_Z (map even_fib (seq 0 n)) <= sum_Z (map even_fib (seq 0 m)) -> (n <= m)%nat.
Proof.
  intros. assert (n <= m \/ m < n)%nat by lia. destruct H0; auto.
  unfold lt in H0. apply aux5 in H0.
  rewrite seq_S in H0. simpl in H0. rewrite map_app in H0. simpl in H0.
  unfold sum_Z in *. rewrite fold_right_app in H0. simpl in H0.
  replace (even_fib m + 0) with (even_fib m) in H0 by lia.
  rewrite aux2 in H0. pose proof (even_fib_bigger_than_0 m). lia.
Qed.

Theorem aux7 (n m: nat): sum_Z (map even_fib (seq 0 n)) = sum_Z (map even_fib (seq 0 m)) -> n = m.
Proof.
  intro. assert (sum_Z (map even_fib (seq 0 n)) <= sum_Z (map even_fib (seq 0 m))) by lia.
  apply aux6 in H0. assert (sum_Z (map even_fib (seq 0 m)) <= sum_Z (map even_fib (seq 0 n))) by lia.
  apply aux6 in H1. lia.
Qed.


Theorem both_results_equal (max: Z): result_simple max = result_more_effective max.
Proof.
  unfold result_simple, result_more_effective.
  assert (max <= 0 \/ 0 < max) by lia. destruct H.
  + unfold increasing_sequence_with_max_value.
    repeat destruct unnamed1. simpl.
    assert (x = O).
    { assert (forall i, fib i <= max -> False).
      { induction i1.
        + unfold fib. simpl. lia.
        + pose proof (fib_increasing i1). lia. }
      pose proof (H0 0)%nat. setoid_rewrite <- i in H1. lia. }
    subst. simpl. assert (x0 = O).
    { assert (forall i, even_fib i <= max -> False).
      { induction i1.
        + unfold even_fib. simpl. lia.
        + pose proof (even_fib_increasing i1). lia. }
      pose proof (H0 0)%nat. setoid_rewrite <- i0 in H1. lia. }
    subst. simpl. auto.
  + assert (0 <= max) by lia. pattern max. revert H0. apply natlike_ind.
    - simpl. auto.
    - intros. replace (Z.succ x) with (x + 1) by lia.
      unfold increasing_sequence_with_max_value in *.
      repeat rewrite aux0. repeat (destruct Z_lt_le_dec; destruct Z.eq_dec; destruct Z_lt_le_dec; try destruct Z.eq_dec).
      * lia.
      * exfalso. repeat destruct unnamed1. simpl in *.
        clear l0. rewrite aux3 in H1. apply aux7 in H1. subst. rewrite even_fib_thm in e.
        destruct (aux4 x0). destruct H1 as [H1 |[H1 | H1]].
        ++ rewrite H1 in e. replace ((3 * x1 + 1) / 3)%nat with x1 in e.
           rewrite <- H1 in e. pose (fib_increasing x0). lia.
           { replace (3 * x1 + 1)%nat with (1 + x1 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ rewrite H1 in e. replace ((3 * x1 + 1 + 1) / 3)%nat with x1 in e.
           replace (S (3 * x1))%nat with (3 * x1 + 1)%nat in e by lia. rewrite <- H1 in e. lia.
           { replace (3 * x1 + 1 + 1)%nat with (2 + x1 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ rewrite H1 in e. replace ((3 * x1 + 2 + 1) / 3)%nat with (S x1) in e.
           replace (S (3 * S x1))%nat with (S (S (3 * x1 + 2)))%nat in e by lia.
           rewrite <- H1 in e. pose proof (fib_increasing x0). pose proof (fib_increasing (S x0)). lia.
           { replace (3 * x1 + 2 + 1)%nat with ((S x1) * 3)%nat by lia.
             rewrite Nat.div_mul. auto. lia. }
      * repeat rewrite Nat.add_0_r. auto.
      * repeat rewrite Nat.add_0_r. auto.
      * repeat destruct unnamed1 in *. simpl in *. rewrite Nat.add_0_r. assert (forall x, x + 1 = S x)%nat by lia. rewrite H2.
        rewrite seq_S. simpl. unfold sum_Z in *. rewrite map_app. simpl. rewrite filter_app. rewrite fold_right_app.
        simpl. remember (Z.even (fib x0)) as W. destruct W.
        ++ exfalso. symmetry in HeqW. rewrite Zeven_bool_iff in HeqW. clear l H2.
           apply aux1 in HeqW. destruct HeqW. subst. rewrite aux3 in H1. apply aux7 in H1.
           replace ((3 * x2 + 1 + 1) / 3)%nat with x2 in H1. subst. rewrite even_fib_thm in l0.
           replace (S (3 * x1))%nat with (3 * x1 + 1)%nat in l0 by lia. lia.
           { replace (3 * x2 + 1 + 1)%nat with (2 + x2 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ auto.
      * repeat destruct unnamed1 in *. simpl in *. assert (forall x, x + 1 = S x)%nat by lia.
        repeat rewrite H2. repeat rewrite seq_S. simpl. repeat rewrite map_app.
        simpl. repeat rewrite filter_app. simpl. remember (Z.even (fib x0)) as W.
        destruct W.
        ++ rewrite sum_Z_app. simpl. replace (fib x0 + 0) with (fib x0) by lia.
           rewrite H1. rewrite sum_Z_app. simpl. replace (even_fib x1 + 0) with (even_fib x1) by lia.
           symmetry in HeqW. rewrite Zeven_bool_iff in HeqW. apply aux1 in HeqW. destruct HeqW.
           subst. rewrite even_fib_thm. f_equal. rewrite even_fib_thm in e0. congruence.
        ++ exfalso. pose proof (Zodd_even_bool (fib x0)). rewrite <- HeqW in H3. simpl in H3.
           rewrite Zodd_bool_iff in H3. apply aux1 in H3. destruct H3. destruct H3.
           -- subst. rewrite aux3 in H1. replace ((3 * x2 + 1) / 3)%nat with x2 in H1.
              apply aux7 in H1. subst. rewrite even_fib_thm in e0. pose proof (fib_increasing (3 * x1)%nat).
              lia.
              { replace (3 * x2 + 1)%nat with (1 + x2 * 3)%nat by lia.
                rewrite Nat.div_add. simpl. auto. lia. }
           -- subst. rewrite aux3 in H1. apply aux7 in H1.
              replace ((3 * x2 + 2 + 1) / 3)%nat with (S x2) in H1.
              subst. rewrite even_fib_thm in *. replace (S (3 * S x2)) with (S (S (S (S (3 * x2))))) in e0 by lia.
              pose proof (fib_increasing (S (S (3 * x2)))). pose proof (fib_increasing (S (S (S (3 * x2))))).
              replace (3 * x2 + 2)%nat with (S (S (3 * x2))) in e by lia. lia.
              { replace (3 * x2 + 2 + 1)%nat with ((S x2) * 3)%nat by lia.
                rewrite Nat.div_mul. auto. lia. }
      * repeat destruct unnamed1 in *. simpl in *. replace (x0 + 1)%nat with (S x0) by lia.
        rewrite seq_S. simpl. rewrite map_app. rewrite filter_app. simpl.
        replace (x1 + 0)%nat with x1 by lia. remember (Z.even (fib x0)) as W. destruct W.
        ++ exfalso. symmetry in HeqW. apply Zeven_bool_iff in HeqW. apply aux1 in HeqW. destruct HeqW.
           subst. rewrite aux3 in H1. apply aux7 in H1. subst.
           replace ((3 * x2 + 1 + 1) / 3)%nat with x2 in *. rewrite even_fib_thm in *.
           replace (3 * x2 + 1)%nat with (S (3 * x2))%nat in e by lia. lia.
           { replace (3 * x2 + 1 + 1)%nat with (2 + x2 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ rewrite sum_Z_app. simpl. lia.
      * repeat destruct unnamed1 in *. simpl in *. repeat rewrite Nat.add_0_r. auto.
      * repeat destruct unnamed1 in *. simpl in *.
        assert (fib x0 <= x) by lia. apply i in H2. lia.
      * repeat destruct unnamed1 in *. simpl in *.
        repeat rewrite Nat.add_0_r. auto.
Qed.


Require Import EulerProject2.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE [] main_pre prog tt gv
  POST [ tint ]
     PROP()
     RETURN (Vint (Int.repr (result_simple 1000000)))
     SEP(TT).

Definition Gprog := [main_spec].

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function. forward. forward. forward.
  forward_while (EX i: Z,
    PROP (0 <= even_fib (Z.to_nat i) <= 1000000)
    LOCAL (temp _a (Vint (Int.repr (match (Z.to_nat i) with | O => 0 | S n => even_fib n end)));
           temp _b (Vint (Int.repr (even_fib (Z.to_nat i))));
           temp _result (Vint (Int.repr (sum_Z (map even_fib (seq 0 (Z.to_nat i))))));
           gvars gv)
    SEP (TT)).
  + Exists 0. entailer!. simpl. change (even_fib 0) with 2. lia.
  + entailer!.
  + forward. forward. remember (Z.to_nat i) as W. destruct W.
    - forward. forward. entailer!. Exists 1. entailer!.
    - forward. forward. entailer!. Exists (i + 1).
      replace (Z.to_nat (i + 1)) with (S (S W)) by lia. entailer!. repeat split.
      * pose proof (even_fib_increasing (S W)). lia.
      * unfold even_fib.
        rewrite recurrent_sequence_unfold. ring_simplify. admit.
      * unfold even_fib. rewrite recurrent_sequence_unfold. f_equal. f_equal. lia.
      * rewrite seq_S. simpl.
        rewrite map_app. rewrite sum_Z_app. simpl. f_equal. f_equal. lia.
  + lia.
Admitted.
