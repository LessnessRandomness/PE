Set Implicit Arguments.
Require Import VST.floyd.proofauto.

Definition sequence A := nat -> A.
Definition increasing (f: sequence Z) := forall (n: nat), f n < f (S n).


(* Theorems about increasing sequences *)

Theorem increasing_thm0 (f: sequence Z) (H: increasing f) (a b: nat) (H0: (a < b)%nat): f a < f b.
Proof.
  induction H0.
  + apply H.
  + pose (H m). lia.
Qed.

Theorem increasing_thm1 (f: sequence Z) (H: increasing f) (a b: nat) (H0: f a < f b): (a < b)%nat.
Proof.
  revert b H0. induction a; intros.
  + destruct b.
    - lia.
    - lia.
  + pose (H a). assert (f a < f b) by lia. apply IHa in H1.
    inversion H1.
    - subst. lia.
    - lia.
Qed.

Theorem increasing_thm2 (f: sequence Z) (H: increasing f) (a b: nat) (H0: (a <= b)%nat): f a <= f b.
Proof.
  induction H0.
  + lia.
  + pose (H m). lia.
Qed.

Theorem increasing_thm3 (f: sequence Z) (H: increasing f) (a b: nat) (H0: f a <= f b): (a <= b)%nat.
Proof.
  revert b H0. induction a; intros.
  + destruct b; lia.
  + pose (H a). assert (f a <= f b) by lia. apply IHa in H1. inversion H1.
    - subst. lia.
    - lia.
Qed.

(* Let's define function that finds the last element of increasing sequence that's less or equal to given limit value *)

Require Import FunInd.

Function last_value_le_aux (f: sequence Z) (H: increasing f) (M: Z) (i: nat)
  { measure (fun i => Z.to_nat (M - f i)) i }: nat :=
  let W := f i in
  if Z_lt_le_dec M W
    then i
    else if Z.eq_dec M W
           then S i
           else last_value_le_aux H M (S i).
Proof.
  abstract (intros; destruct Z_lt_le_dec; [| destruct Z.eq_dec; [| pose proof (H i)]]; lia).
Defined.

Definition last_value_le (f: sequence Z) (H: increasing f) (M: Z) := last_value_le_aux H M 0%nat.

Theorem last_value_le_aux_thm0 (f: sequence Z) (H: increasing f) (M: Z) (k: nat):
  (k <= last_value_le_aux H M k)%nat.
Proof.
  apply last_value_le_aux_ind; intros; lia.
Qed.

Theorem last_value_le_aux_thm1 (f: sequence Z) (H: increasing f) (M: Z) (i: nat):
  forall k, (i <= k)%nat -> ((k < last_value_le_aux H M i)%nat <-> f k <= M).
Proof.
  apply last_value_le_aux_ind.
  + intros. destruct Z_lt_le_dec.
    - split; intros; try lia.
      unfold W in *. assert (f k < f i0) by lia. apply increasing_thm1 in H2; auto.
    - split; intros; lia.
  + intros. destruct Z_lt_le_dec; try lia.
    destruct Z.eq_dec; try congruence; split; intros. 
    - assert (k = i0) by lia. subst. unfold W. auto.
    - unfold W in *. subst. apply increasing_thm3 in H1; auto; lia.
  + intros. destruct Z_lt_le_dec; try lia.
    destruct Z.eq_dec; try congruence.
    inversion H1; subst.
    - split; intros; unfold W in *; auto.
      apply last_value_le_aux_thm0.
    - apply H0. lia.
Qed.

Theorem last_value_le_thm (f: sequence Z) (H: increasing f) (M: Z):
  forall i, (i < last_value_le H M)%nat <-> f i <= M.
Proof.
  intros. apply last_value_le_aux_thm1. lia.
Qed.

(*
Define fibonacci numbers in traditional recursive way
(starting from values 1 and 2, following rules of Project Euler Problem 2)
and then in more efficient way. Prove that they both are equivalent.
Accumulator function taken from https://github.com/madsbuch/fibonacci/blob/master/coq/fib.v
*)

Fixpoint recurrent_sequence (k1 k2 a b: Z) (n: nat) :=
  match n with
  | O => a
  | S O => b
  | S (S i as m) => k1 * recurrent_sequence k1 k2 a b m + k2 * recurrent_sequence k1 k2 a b i
  end.

Fixpoint accumulator (k1 k2 a b: Z) (n: nat): Z :=
  match n with
  | O => b
  | S n' => accumulator k1 k2 (k1 * a + k2 * b) a n'
  end.

(* Prove equivalence of both definitions *)

Theorem recurrent_sequence_unfold (k1 k2 a b: Z) (n: nat):
  recurrent_sequence k1 k2 a b (S (S n)) = k1 * recurrent_sequence k1 k2 a b (S n) + k2 * recurrent_sequence k1 k2 a b n.
Proof.
  reflexivity.
Qed.

Theorem accumulator_O (k1 k2 a b: Z): accumulator k1 k2 a b O = b.
Proof.
  reflexivity.
Qed.

Theorem accumulator_S (k1 k2 a b: Z) (n: nat): accumulator k1 k2 a b (S n) = accumulator k1 k2 (k1 * a + k2 * b) a n.
Proof.
  reflexivity.
Qed.

Theorem accumulator_thm0 (k1 k2 a b: Z) (n m: nat):
  accumulator k1 k2 (recurrent_sequence k1 k2 a b (S (S (S n)))) (recurrent_sequence k1 k2 a b (S (S n))) m =
  k1 * accumulator k1 k2 (recurrent_sequence k1 k2 a b (S (S n))) (recurrent_sequence k1 k2 a b (S n)) m +
  k2 * accumulator k1 k2 (recurrent_sequence k1 k2 a b (S n)) (recurrent_sequence k1 k2 a b n) m.
Proof.
  revert n. induction m; intros.
  + repeat rewrite accumulator_O in *. rewrite <- recurrent_sequence_unfold. reflexivity.
  + intros. repeat rewrite accumulator_S. repeat rewrite <- recurrent_sequence_unfold.
    apply IHm.
Qed.

Theorem both_formulations_equivalent (k1 k2 a b: Z) (n: nat):
  recurrent_sequence k1 k2 a b n = accumulator k1 k2 b a n.
Proof.
  assert (recurrent_sequence k1 k2 a b n = accumulator k1 k2 b a n /\
          recurrent_sequence k1 k2 a b (S n) = accumulator k1 k2 b a (S n)).
  { induction n.
    + simpl. lia.
    + destruct IHn. split; auto. rewrite recurrent_sequence_unfold.
      rewrite H, H0. repeat rewrite accumulator_S.
      change (k1 * b + k2 * a) with (recurrent_sequence k1 k2 a b 2) at 1 3.
      change b with (recurrent_sequence k1 k2 a b 1) at 2 3.
      change a with (recurrent_sequence k1 k2 a b 0) at 4.
      change (k1 * (k1 * b + k2 * a) + k2 * b) with (recurrent_sequence k1 k2 a b 3).
      symmetry. apply accumulator_thm0. }
  apply H.
Qed.

(* Theorems about fibonacci numbers *)

Definition fibonacci := recurrent_sequence 1 1 1 2.
Definition fibonacci_efficient := accumulator 1 1 2 1.

Theorem fibonacci_greater_than_0 (n: nat): 0 < fibonacci n.
Proof.
  assert (0 < fibonacci n /\ 0 < fibonacci (S n)).
  { unfold fibonacci. induction n.
    - simpl. lia.
    - destruct IHn; split; auto. rewrite recurrent_sequence_unfold. lia. }
  apply H.
Qed.

Theorem fibonacci_increasing: increasing fibonacci.
Proof.
  unfold increasing. assert (forall n, fibonacci n < fibonacci (S n) < fibonacci (S (S n))).
  { unfold fibonacci. induction n.
    + simpl. lia.
    + destruct IHn; split; auto. pose proof (fibonacci_greater_than_0 n). unfold fibonacci in H1.
      repeat rewrite recurrent_sequence_unfold. lia. }
  intros. apply H.
Qed.

Theorem fibonacci_efficient_increasing: increasing fibonacci_efficient.
Proof.
  unfold increasing. intro. unfold fibonacci_efficient.
  repeat rewrite <- both_formulations_equivalent. apply fibonacci_increasing.
Qed.

(* Useful theorem about parity of fibonacci numbers *)

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


Theorem aux1 (n: nat):
  let P: nat -> Prop :=
    fun n => (Zeven (fibonacci n) <-> exists m, n = (3 * m + 1)%nat) /\
    (Zodd (fibonacci n) <-> exists m, n = (3 * m)%nat \/ n = (3 * m + 2)%nat) in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { induction n; split; intros; split; intros; split; intros.
    + rewrite Zeven_ex_iff in H. destruct H. change (fibonacci 0) with 1 in H. lia.
    + rewrite Zeven_ex_iff. destruct H. lia.
    + exists 0%nat. left. reflexivity.
    + rewrite Zodd_ex_iff. exists 0. reflexivity.
    + exists 0%nat. reflexivity.
    + rewrite Zeven_ex_iff. exists 1. reflexivity.
    + rewrite Zodd_ex_iff in H. destruct H. change (fibonacci 1) with 2 in H. lia.
    + destruct H. lia.
    + apply IHn in H. auto.
    + apply IHn. auto.
    + apply IHn in H. auto.
    + apply IHn. auto.
    + unfold fibonacci in *. rewrite recurrent_sequence_unfold in H. apply Zeven_sum in H. destruct H.
      - destruct H. ring_simplify (1 * recurrent_sequence 1 1 1 2 (S n)) in H.
        ring_simplify (1 * recurrent_sequence 1 1 1 2 n) in H0. apply IHn in H, H0. destruct H, H0. lia.
      - destruct H. ring_simplify (1 * recurrent_sequence 1 1 1 2 (S n)) in H.
        ring_simplify (1 * recurrent_sequence 1 1 1 2 n) in H0. apply IHn in H, H0. destruct H, H0. exists x. lia. 
    + unfold fibonacci in *. rewrite recurrent_sequence_unfold. destruct H.
      assert (exists m, S n = (3 * m)%nat \/ S n = (3 * m + 2)%nat).
      { exists x. lia. }
      apply IHn in H0. assert (exists m, n = (3 * m)%nat \/ n = (3 * m + 2)%nat).
      { exists (x - 1)%nat. lia. }
      apply IHn in H1. apply Zodd_plus_Zodd.
      - ring_simplify (1 * recurrent_sequence 1 1 1 2 (S n)); auto.
      - ring_simplify (1 * recurrent_sequence 1 1 1 2 n); auto.
    + unfold fibonacci in *. rewrite recurrent_sequence_unfold in H. apply Zodd_sum in H. destruct H.
      - destruct H. ring_simplify (1 * recurrent_sequence 1 1 1 2 (S n)) in H.
        ring_simplify (1 * recurrent_sequence 1 1 1 2 n) in H0. apply IHn in H, H0. destruct H, H0. exists x. lia.
      - destruct H. ring_simplify (1 * recurrent_sequence 1 1 1 2 (S n)) in H.
        ring_simplify (1 * recurrent_sequence 1 1 1 2 n) in H0. apply IHn in H, H0. destruct H, H0. exists (S x). lia.
    + unfold fibonacci in *. rewrite recurrent_sequence_unfold. destruct H. destruct H.
      - assert (exists m, S n = 3 * m \/ S n = 3 * m + 2)%nat.
        { exists (x - 1)%nat. lia. }
        apply IHn in H0. assert (exists m, n = 3 * m + 1)%nat.
        { exists (x - 1)%nat. lia. }
        replace (1 * recurrent_sequence 1 1 1 2 (S n) + 1 * recurrent_sequence 1 1 1 2 n) with
                (recurrent_sequence 1 1 1 2 n + recurrent_sequence 1 1 1 2 (S n)) by ring.
        apply IHn in H1. apply Zeven_plus_Zodd; auto.
      - assert (exists m, S n = 3 * m + 1)%nat.
        { exists x. lia. }
        apply IHn in H0. assert (exists m, n = 3 * m \/ n = 3 * m + 2)%nat.
        { exists x. lia. }
        replace (1 * recurrent_sequence 1 1 1 2 (S n) + 1 * recurrent_sequence 1 1 1 2 n) with
                (recurrent_sequence 1 1 1 2 n + recurrent_sequence 1 1 1 2 (S n)) by ring.
        apply IHn in H1. apply Zodd_plus_Zeven; auto. }
  apply H.
Qed.


(* Theorems about even fibonacci numbers *)

Definition even_fibonacci_efficient := accumulator 4 1 8 2.

Theorem even_fibonacci_efficient_greater_than_1 (n: nat): 1 < even_fibonacci_efficient n.
Proof.
  assert (1 < even_fibonacci_efficient n /\ 1 < even_fibonacci_efficient (S n)).
  { unfold even_fibonacci_efficient. repeat rewrite <- both_formulations_equivalent. induction n.
    + simpl. lia.
    + destruct IHn; split; auto. rewrite recurrent_sequence_unfold. lia. }
  apply H.
Qed.

Theorem even_fibonacci_efficient_increasing: increasing even_fibonacci_efficient.
Proof.
  unfold increasing. intros.
  assert (even_fibonacci_efficient n < even_fibonacci_efficient (S n) < even_fibonacci_efficient (S (S n))).
  { induction n.
    + simpl. unfold even_fibonacci_efficient. simpl. lia.
    + pose proof (even_fibonacci_efficient_greater_than_1 n) as H1.
      unfold even_fibonacci_efficient in *. destruct IHn; split; auto.
      repeat rewrite <- both_formulations_equivalent in *.
      repeat rewrite recurrent_sequence_unfold. lia. }
  apply H.
Qed.

Theorem even_fibonacci_efficient_thm (n: nat): even_fibonacci_efficient n = fibonacci (S (3 * n)).
Proof.
  assert (even_fibonacci_efficient n = fibonacci (S (3 * n)) /\
          even_fibonacci_efficient (S n) = fibonacci (S (3 * S n))).
  { induction n.
    + simpl. unfold even_fibonacci_efficient, fibonacci. simpl. auto.
    + destruct IHn; split; auto. unfold even_fibonacci_efficient, fibonacci in *.
      repeat rewrite <- both_formulations_equivalent in *.
      rewrite recurrent_sequence_unfold. ring_simplify.
      replace (3 * S (S n))%nat with (S (S (S (S (S (S (3 * n)))))))%nat by lia.
      replace (3 * S n)%nat with (S (S (S (3 * n))))%nat in H0 by lia.
      repeat rewrite recurrent_sequence_unfold in *. ring_simplify. ring_simplify in H0. lia. }
  apply H.
Qed.

(* Main part *)

Definition sum_Z: list Z -> Z := fold_right Z.add 0.

Theorem sum_Z_app (l1 l2: list Z): sum_Z (l1 ++ l2) = sum_Z l1 + sum_Z l2.
Proof.
  revert l2. induction l1.
  + simpl. lia.
  + simpl. intro. rewrite IHl1. lia.
Qed.

Definition increasing_sequence_with_max_value (f: sequence Z) (H: increasing f) (M: Z): list Z :=
  map f (seq 0 (last_value_le H M)).

Definition result_simple (M: Z): Z :=
  sum_Z (filter Z.even (increasing_sequence_with_max_value fibonacci_increasing M)).

Definition result_more_efficient (M: Z): Z :=
  sum_Z (increasing_sequence_with_max_value even_fibonacci_efficient_increasing M).


Theorem fold_right_thm0 (n: Z) (L: list Z): fold_right Z.add n L = fold_right Z.add 0 L + n.
Proof.
  induction L.
  + simpl. lia.
  + simpl. lia.
Qed.

Theorem aux3 (n: nat): sum_Z (filter Z.even (map fibonacci (seq 0 n))) = sum_Z (map even_fibonacci_efficient (seq 0 ((n + 1) / 3))).
Proof.
  induction n.
  + simpl. auto.
  + replace (S n + 1)%nat with (n + 2)%nat by lia. rewrite seq_S. change (0 + n)%nat with n.
    rewrite map_app. change (map fibonacci [n]) with ([fibonacci n]).
    rewrite filter_app. simpl filter. remember (Z.even (fibonacci n)) as W.
    destruct W.
    - unfold sum_Z in *. rewrite fold_right_app. simpl fold_right at 1.
      replace (fibonacci n + 0) with (fibonacci n) by lia.
      rewrite fold_right_thm0. symmetry in HeqW. rewrite Zeven_bool_iff in HeqW.
      apply aux1 in HeqW. destruct HeqW. subst.
      replace ((3 * x + 1 + 1) / 3)%nat with x in IHn.
      replace ((3 * x + 1 + 2) / 3)%nat with (S x)%nat.
      rewrite IHn. rewrite seq_S. change (0 + x)%nat with x.
      rewrite map_app. change (map even_fibonacci_efficient [x]) with ([even_fibonacci_efficient x]).
      rewrite fold_right_app. simpl fold_right.
      replace (even_fibonacci_efficient x + 0) with (even_fibonacci_efficient x) by lia.
      rewrite even_fibonacci_efficient_thm. rewrite (fold_right_thm0 (fibonacci (S (3 * x)))).
      replace (S (3 * x))%nat with (3 * x + 1)%nat by lia. reflexivity.
      { replace (3 * x + 1 + 2)%nat with ((x + 1) * 3)%nat by lia. rewrite Nat.div_mul; lia. }
      { replace (3 * x + 1 + 1)%nat with (2 + x * 3)%nat by lia.
        rewrite Nat.div_add. simpl. reflexivity. lia. }
    - unfold sum_Z in *. rewrite fold_right_app. simpl fold_right at 1.
      symmetry in HeqW. assert (Z.odd (fibonacci n) = true).
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

Theorem sum_Z_thm0 (n m: nat):
  (n <= m)%nat -> sum_Z (map even_fibonacci_efficient (seq 0 n)) <= sum_Z (map even_fibonacci_efficient (seq 0 m)).
Proof.
  intro. induction H.
  + lia.
  + rewrite seq_S. simpl. rewrite map_app. simpl.
    replace (sum_Z (map even_fibonacci_efficient (seq 0 m) ++ [even_fibonacci_efficient m])) with
            (sum_Z (map even_fibonacci_efficient (seq 0 m)) + even_fibonacci_efficient m).
    pose proof (even_fibonacci_efficient_greater_than_1 m). lia.
    { unfold sum_Z. rewrite fold_right_app. simpl.
      rewrite <- fold_right_thm0. ring_simplify (even_fibonacci_efficient m + 0). reflexivity. }
Qed.

Theorem sum_Z_thm1 (n m: nat):
  sum_Z (map even_fibonacci_efficient (seq 0 n)) <= sum_Z (map even_fibonacci_efficient (seq 0 m)) -> (n <= m)%nat.
Proof.
  intros. assert (n <= m \/ m < n)%nat by lia. destruct H0; auto.
  unfold lt in H0. apply sum_Z_thm0 in H0.
  rewrite seq_S in H0. simpl in H0. rewrite map_app in H0. simpl in H0.
  unfold sum_Z in *. rewrite fold_right_app in H0. simpl in H0.
  ring_simplify (even_fibonacci_efficient m + 0) in H0.
  rewrite fold_right_thm0 in H0. pose proof (even_fibonacci_efficient_greater_than_1 m). lia.
Qed.

Theorem sum_Z_thm2 (n m: nat):
  sum_Z (map even_fibonacci_efficient (seq 0 n)) = sum_Z (map even_fibonacci_efficient (seq 0 m)) -> n = m.
Proof.
  intro.
  assert (sum_Z (map even_fibonacci_efficient (seq 0 n)) <= sum_Z (map even_fibonacci_efficient (seq 0 m))) by lia.
  apply sum_Z_thm1 in H0.
  assert (sum_Z (map even_fibonacci_efficient (seq 0 m)) <= sum_Z (map even_fibonacci_efficient (seq 0 n))) by lia.
  apply sum_Z_thm1 in H1. lia.
Qed.

Theorem last_value_le_inc (f: sequence Z) (H: increasing f) (M: Z):
  (last_value_le H (M + 1) =
  last_value_le H M + 
  if Z_lt_le_dec (M + 1) (f (last_value_le H M))
  then 0
  else if Z.eq_dec (M + 1) (f (last_value_le H M))
    then 1
    else 0)%nat.
Proof.
  pose proof (last_value_le_thm H (M + 1)). pose proof (last_value_le_thm H M). destruct Z_lt_le_dec. 
  + replace (last_value_le H M + 0)%nat with (last_value_le H M) by lia.
    assert (f (last_value_le H M) <= M + 1 -> False) by lia.
    setoid_rewrite <- H0 in H2. assert (last_value_le H (M + 1) <= last_value_le H M)%nat by lia.
    inversion H3.
    - auto.
    - exfalso. assert (last_value_le H (M + 1) < S m)%nat by lia. rewrite H4 in H6. apply H1 in H6.
      assert (f (last_value_le H (M + 1)) <= M + 1) by lia. apply H0 in H7. lia.
  + destruct Z.eq_dec.
    - assert (forall i, f i <= f (last_value_le H M) <-> (i <= last_value_le H M)%nat).
      { split; intros.
        + apply (increasing_thm3 H). auto.
        + apply (increasing_thm2 H). auto. }
      setoid_rewrite e in H0 at 2. setoid_rewrite H2 in H0.
      destruct (last_value_le H (M + 1)).
      * exfalso. pose proof (H0 (last_value_le H M)). lia.
      * assert (n < S n)%nat by lia. apply H0 in H3.
        pose proof (le_n (last_value_le H M)). apply H0 in H4. lia.
    - exfalso. assert (f (last_value_le H M) <= M) by lia. apply H1 in H2. lia.
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

Theorem both_results_equal (M: Z): result_simple M = result_more_efficient M.
Proof.
  unfold result_simple, result_more_efficient.
  assert (M <= 0 \/ 0 < M) by lia. destruct H.
  + unfold increasing_sequence_with_max_value.
    assert (last_value_le fibonacci_increasing M = 0)%nat.
    { pose proof (fibonacci_greater_than_0 0). unfold last_value_le. rewrite last_value_le_aux_equation.
      destruct Z_lt_le_dec; lia. }
    assert (last_value_le even_fibonacci_efficient_increasing M = 0)%nat.
    { pose proof (even_fibonacci_efficient_greater_than_1 0). unfold last_value_le. rewrite last_value_le_aux_equation.
      destruct Z_lt_le_dec; lia. }
    rewrite H0, H1. simpl. auto.
  + assert (0 <= M) by lia. pattern M. revert H0. apply natlike_ind.
    - simpl. auto.
    - intros. replace (Z.succ x) with (x + 1) by lia.
      unfold increasing_sequence_with_max_value in *. repeat rewrite last_value_le_inc.
      pose proof (last_value_le_thm fibonacci_increasing x).
      pose proof (last_value_le_thm even_fibonacci_efficient_increasing x).
      repeat (destruct Z_lt_le_dec; destruct Z.eq_dec; destruct Z_lt_le_dec; try destruct Z.eq_dec).
      * lia.
      * exfalso. rewrite aux3 in H1. apply sum_Z_thm2 in H1. rewrite even_fibonacci_efficient_thm in e.
        rewrite <- H1 in e. destruct (aux4 (last_value_le fibonacci_increasing x)). destruct H4 as [H4 |[H4 | H4]].
        ++ rewrite H4 in e. replace ((3 * x0 + 1) / 3)%nat with x0 in e.
           rewrite <- H4 in e. pose (fibonacci_increasing (last_value_le fibonacci_increasing x)). lia.
           { replace (3 * x0 + 1)%nat with (1 + x0 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ rewrite H4 in e. replace ((3 * x0 + 1 + 1) / 3)%nat with x0 in e.
           replace (S (3 * x0))%nat with (3 * x0 + 1)%nat in e by lia. rewrite <- H4 in e. lia.
           { replace (3 * x0 + 1 + 1)%nat with (2 + x0 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ rewrite H4 in e. replace ((3 * x0 + 2 + 1) / 3)%nat with (S x0) in e.
           replace (S (3 * S x0))%nat with (S (S (3 * x0 + 2)))%nat in e by lia.
           rewrite <- H4 in e. pose proof (fibonacci_increasing (last_value_le fibonacci_increasing x)).
           pose proof (fibonacci_increasing (S (last_value_le fibonacci_increasing x))). lia.
           { replace (3 * x0 + 2 + 1)%nat with ((S x0) * 3)%nat by lia.
             rewrite Nat.div_mul. auto. lia. }
      * repeat rewrite Nat.add_0_r. auto.
      * repeat rewrite Nat.add_0_r. auto.
      * rewrite Nat.add_0_r. assert (forall x, x + 1 = S x)%nat by lia. rewrite H4. rewrite seq_S. simpl.
        unfold sum_Z. rewrite map_app. simpl. rewrite filter_app. rewrite fold_right_app. simpl.
        remember (Z.even (fibonacci (last_value_le fibonacci_increasing x))) as W. destruct W.
        ++ exfalso. symmetry in HeqW. rewrite Zeven_bool_iff in HeqW. clear l H4.
           apply aux1 in HeqW. destruct HeqW. rewrite H4 in *. rewrite aux3 in H1.
           apply sum_Z_thm2 in H1. replace ((3 * x0 + 1 + 1) / 3)%nat with x0 in H1.
           rewrite even_fibonacci_efficient_thm in l0. rewrite <- H1 in *.
           replace (S (3 * x0))%nat with (3 * x0 + 1)%nat in l0 by lia. lia.
           { replace (3 * x0 + 1 + 1)%nat with (2 + x0 * 3)%nat by lia.
             rewrite Nat.div_add. simpl. auto. lia. }
        ++ auto.
      * assert (forall x, x + 1 = S x)%nat by lia. repeat rewrite H4. repeat rewrite seq_S. simpl.
        repeat rewrite map_app. simpl. repeat rewrite filter_app. simpl.
        remember (Z.even (fibonacci (last_value_le fibonacci_increasing x))) as W.
        destruct W.
        ++ rewrite sum_Z_app. simpl. ring_simplify (fibonacci (last_value_le fibonacci_increasing x) + 0).
           rewrite H1. rewrite sum_Z_app. simpl.
           ring_simplify (even_fibonacci_efficient (last_value_le even_fibonacci_efficient_increasing x) + 0).
           symmetry in HeqW. rewrite Zeven_bool_iff in HeqW. apply aux1 in HeqW. destruct HeqW.
           rewrite H5 in *. rewrite even_fibonacci_efficient_thm. f_equal. rewrite even_fibonacci_efficient_thm in e0.
           congruence.
        ++ exfalso. pose proof (Zodd_even_bool (fibonacci (last_value_le fibonacci_increasing x))). rewrite <- HeqW in H5.
           simpl in H5. rewrite Zodd_bool_iff in H5. apply aux1 in H5. destruct H5. destruct H5.
           -- rewrite H5 in *. rewrite aux3 in H1. replace ((3 * x0 + 1) / 3)%nat with x0 in H1.
              apply sum_Z_thm2 in H1. subst. rewrite even_fibonacci_efficient_thm in e0.
              pose proof (fibonacci_increasing (3 * last_value_le even_fibonacci_efficient_increasing x)%nat). lia.
              { replace (3 * x0 + 1)%nat with (1 + x0 * 3)%nat by lia.
                rewrite Nat.div_add. simpl. auto. lia. }
           -- rewrite H5 in *. rewrite aux3 in H1. replace ((3 * x0 + 2 + 1) / 3)%nat with (S x0) in H1.
              apply sum_Z_thm2 in H1. rewrite <- H1 in *. rewrite even_fibonacci_efficient_thm in *.
              replace (S (3 * S x0))%nat with (S (S (S (S (3 * x0)))))%nat in e0 by lia.
              pose proof (fibonacci_increasing (S (S (3 * x0)))). pose proof (fibonacci_increasing (S (S (S (3 * x0))))).
              replace (3 * x0 + 2)%nat with (S (S (3 * x0))) in e by lia. lia.
              { replace (3 * x0 + 2 + 1)%nat with ((S x0) * 3)%nat by lia.
                rewrite Nat.div_mul. auto. lia. }
      * assert (forall x, x + 1 = S x)%nat by lia. rewrite H4. rewrite seq_S. simpl. rewrite map_app, filter_app. simpl.
        replace (last_value_le even_fibonacci_efficient_increasing x + 0)%nat with
                (last_value_le even_fibonacci_efficient_increasing x) by lia.
        remember (Z.even (fibonacci (last_value_le fibonacci_increasing x))) as W. destruct W.
        ++ exfalso. symmetry in HeqW. apply Zeven_bool_iff in HeqW. apply aux1 in HeqW. destruct HeqW.
           rewrite H5 in *. rewrite aux3 in H1. apply sum_Z_thm2 in H1. rewrite <- H1 in *.
           replace ((3 * x0 + 1 + 1) / 3)%nat with x0 in *. rewrite even_fibonacci_efficient_thm in *.
           replace (3 * x0 + 1)%nat with (S (3 * x0))%nat in e by lia. lia.
           { replace (3 * x0 + 1 + 1)%nat with (2 + x0 * 3)%nat by lia.
            rewrite Nat.div_add. simpl. auto. lia. }
        ++ rewrite sum_Z_app. simpl. lia.
      * repeat rewrite Nat.add_0_r. auto.
      * exfalso. assert (fibonacci (last_value_le fibonacci_increasing x) <= x) by lia. apply H2 in H4. lia.
      * repeat rewrite Nat.add_0_r. auto.
Qed.

Theorem increasing_thm4 (f: sequence Z) (H: increasing f) (n: nat):
  (n < last_value_le H (f n))%nat.
Proof.
  pose proof (last_value_le_thm H (f n) n). assert (f n <= f n) by lia.
  apply H0 in H1. auto.
Qed.

Theorem increasing_thm5 (f: sequence Z) (H: increasing f) (n: nat) (M: Z):
  (last_value_le H M = S n) <-> (f n <= M < f (S n)).
Proof.
  pose proof (last_value_le_thm H). split; intros.
  + split.
    - apply H0. lia.
    - assert (M < f (S n) <-> (f (S n) <= M -> False)) by lia.
      rewrite H2. rewrite <- H0. lia.
  + destruct H1. rewrite <- H0 in H1. assert (f (S n) <= M -> False) by lia.
    rewrite <- H0 in H3. lia.
Qed.

Theorem increasing_thm6 (f: sequence Z) (H: increasing f) (n: nat):
  last_value_le H (f n) = S n.
Proof.
  rewrite increasing_thm5. pose (H n). lia.
Qed.

Theorem thm03 (n: nat):
  result_simple (even_fibonacci_efficient (S n)) = result_simple (even_fibonacci_efficient n) + even_fibonacci_efficient (S n).
Proof.
  repeat rewrite both_results_equal. unfold result_more_efficient.
  unfold increasing_sequence_with_max_value. rewrite increasing_thm6. rewrite increasing_thm6.
  repeat rewrite seq_S. simpl. rewrite map_app. rewrite sum_Z_app. f_equal. simpl. lia.
Qed.

Theorem even_fibonacci_efficient_unfold (n: nat):
  even_fibonacci_efficient (S (S n)) = 4 * even_fibonacci_efficient (S n) + even_fibonacci_efficient n.
Proof.
  unfold even_fibonacci_efficient. repeat rewrite <- both_formulations_equivalent.
  rewrite recurrent_sequence_unfold. lia.
Qed.

Theorem thm04 (n: nat):
  let P: nat -> Prop := fun n => 4 * even_fibonacci_efficient n <= even_fibonacci_efficient (S n) in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { unfold P in *. induction n.
    + compute. split; congruence.
    + destruct IHn; split; auto. repeat rewrite even_fibonacci_efficient_unfold in *.
      lia. }
  apply H.
Qed.

Theorem thm05 (n: nat):
  let P: nat -> Prop := fun n => 4 * even_fibonacci_efficient (S n) <= 17 * even_fibonacci_efficient n in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { unfold P in *. induction n.
    + compute. split; congruence.
    + destruct IHn; split; auto. repeat rewrite even_fibonacci_efficient_unfold in *. lia. }
  apply H.
Qed.

Theorem thm06 (M: Z) (H: 1 <= M):
  4 * even_fibonacci_efficient (last_value_le even_fibonacci_efficient_increasing M) <= 17 * M.
Proof.
  remember (last_value_le even_fibonacci_efficient_increasing M) as W. destruct W.
  + change (even_fibonacci_efficient 0) with 2. lia.
  + symmetry in HeqW. pose proof (increasing_thm5 even_fibonacci_efficient_increasing).
    pose proof (proj1 (H0 W M) HeqW). destruct H1. pose proof (thm05 W). simpl in H3. lia.
Qed.

Theorem thm07 (M: Z):
  M < even_fibonacci_efficient (S (last_value_le even_fibonacci_efficient_increasing M)).
Proof.
  remember (last_value_le even_fibonacci_efficient_increasing M) as W. destruct W.
  + change (even_fibonacci_efficient 1) with 8. symmetry in HeqW. assert (M < 2).
    { unfold last_value_le in HeqW. rewrite last_value_le_aux_equation in HeqW.
      destruct Z_lt_le_dec.
      + change (even_fibonacci_efficient 0) with 2 in l. auto.
      + destruct Z.eq_dec; try lia. pose proof (last_value_le_aux_thm0 even_fibonacci_efficient_increasing M 1). lia. }
    lia.
  + symmetry in HeqW. pose proof (increasing_thm5 even_fibonacci_efficient_increasing W M).
    pose proof ((proj1 H) HeqW). destruct H0. rewrite even_fibonacci_efficient_unfold.
    pose proof (even_fibonacci_efficient_greater_than_1 W). lia.
Qed.

Theorem thm08 (n: nat) (M: Z):
  let P: nat -> Prop := fun n => even_fibonacci_efficient (S n) <= 4 * M -> even_fibonacci_efficient n <= M in P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { induction n.
    + unfold P. split.
      - intros. change (even_fibonacci_efficient 1) with 8 in H.
        change (even_fibonacci_efficient 0) with 2. lia.
      - intros. change (even_fibonacci_efficient 2) with 34 in H.
        change (even_fibonacci_efficient 1) with 8. lia.
    + destruct IHn; split; auto. unfold P in *. repeat rewrite even_fibonacci_efficient_unfold in *.
      intros. ring_simplify in H1. pose proof (even_fibonacci_efficient_greater_than_1 n).
      pose proof (even_fibonacci_efficient_greater_than_1 (S n)). lia. }
  apply H.
Qed.



Require Import EulerProject2.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition result_spec: ident * funspec :=
DECLARE _result
  WITH M: Z
  PRE [ tuint ]
    PROP(0 <= M <= 1000000)
    PARAMS(Vint (Int.repr M))
    SEP()
  POST [ tuint ]
    PROP()
    RETURN(Vint (Int.repr (result_simple M)))
    SEP().

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog tt gv
  POST [ tint ]  
     PROP() 
     RETURN (Vint (Int.repr (result_simple 1000000)))
     SEP(TT).

Definition Gprog := [result_spec; main_spec].

Lemma body_result: semax_body Vprog Gprog f_result result_spec.
Proof.
  start_function. do 3 forward.
  assert (M <= 1 \/ 2 <= M) by lia. destruct H0.
  + forward_while (EX i: nat,
      PROP (i = 0%nat)
      LOCAL (temp _max (Vint (Int.repr M));
             temp _a (Vint (Int.repr 0));
             temp _b (Vint (Int.repr 2));
             temp _sum (Vint (Int.repr 0)))
      SEP ()).
    - entailer!. Exists 0%nat. entailer!.
    - entailer!.
    - lia.
    - deadvars!. forward. entailer!. do 2 f_equal. rewrite both_results_equal.
      unfold result_more_efficient. unfold increasing_sequence_with_max_value.
      unfold last_value_le in *. rewrite last_value_le_aux_equation.
      change (even_fibonacci_efficient 0) with 2. destruct Z_lt_le_dec.
      * simpl. auto.
      * lia.
  + forward_while (EX i: nat,
      PROP ((0 <= i <= last_value_le even_fibonacci_efficient_increasing M)%nat)
      LOCAL (temp _max (Vint (Int.repr M));
             temp _a (Vint (Int.repr (match i with O => 0 | S n => even_fibonacci_efficient n end)));
             temp _b (Vint (Int.repr (even_fibonacci_efficient i)));
             temp _sum (Vint (Int.repr (result_simple (match i with O => 0 | S n => even_fibonacci_efficient n end)))))
      SEP ()).
    - entailer!. Exists 0%nat. entailer!.
    - entailer!.
    - do 4 forward. entailer!.
      * pose proof (even_fibonacci_efficient_greater_than_1 i).
        rewrite Int.unsigned_repr in HRE. destruct H1. rewrite Int.signed_repr. rep_lia.
        { apply (increasing_thm2 even_fibonacci_efficient_increasing) in H3.
          assert (1 <= M) by lia. apply thm06 in H4. rep_lia. }
        { split; try rep_lia. destruct H1. apply (increasing_thm2 even_fibonacci_efficient_increasing) in H3.
          assert (1 <= M) by lia. apply thm06 in H4. rep_lia. }
      * Exists (S i). entailer!. repeat split.
        ++ rewrite Int.unsigned_repr in HRE. clear H1. assert (even_fibonacci_efficient i <= M) by lia. clear HRE.
           rewrite <- (last_value_le_thm even_fibonacci_efficient_increasing) in H1. auto.
           { split.
             + pose proof (even_fibonacci_efficient_greater_than_1 i). lia.
             + destruct H1. apply (increasing_thm2 even_fibonacci_efficient_increasing) in H2.
               assert (1 <= M) by lia. apply thm06 in H3. rep_lia. }
        ++ destruct i; try reflexivity. rewrite even_fibonacci_efficient_unfold. reflexivity.
        ++ destruct i; try reflexivity. rewrite thm03. reflexivity.
    - deadvars!. forward. entailer!. destruct i.
      * change (Int.unsigned (Int.repr (even_fibonacci_efficient 0))) with 2 in HRE. lia.
      * rewrite Int.unsigned_repr in HRE. do 2 f_equal. repeat rewrite both_results_equal.
        destruct H1. clear H1. unfold result_more_efficient. unfold increasing_sequence_with_max_value.
        do 3 f_equal. rewrite increasing_thm6. symmetry. rewrite increasing_thm5. split; auto.
        inversion H2.
        ++ symmetry in H3. rewrite increasing_thm5 in H3. lia.
        ++ apply Peano.le_n_S in H3. rewrite H1 in H3. clear H1 H2 m.
           assert (even_fibonacci_efficient (S i) <= M -> False) by lia.
           rewrite <- (last_value_le_thm even_fibonacci_efficient_increasing) in H1.
           assert (last_value_le even_fibonacci_efficient_increasing M <= S i)%nat by lia. lia.
        ++ split.
           -- pose proof (even_fibonacci_efficient_greater_than_1 (S i)). lia.
           -- destruct H1. apply (increasing_thm2 even_fibonacci_efficient_increasing) in H2.
              assert (1 <= M) by lia. apply thm06 in H3. rep_lia.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function. forward_call 1000000.
  remember (result_simple 1000000) as W. clear HeqW. forward.
Qed.

