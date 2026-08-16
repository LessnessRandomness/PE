Set Implicit Arguments.
Require Import VST.floyd.proofauto.
From Stdlib Require Import Peano.

Open Scope Z.

Definition sequence A := nat -> A.
Definition increasing (f: sequence Z) := forall (n: nat), f n < f (S n).


(* Theorems about increasing sequences *)

Theorem increasing_lt_compat (f: sequence Z) (H: increasing f) (a b: nat)
  (H0: (a < b)%nat): f a < f b.
Proof.
  induction H0.
  + apply H.
  + pose (H m). lia.
Qed.

Theorem increasing_lt_compat_inv (f: sequence Z) (H: increasing f) (a b: nat)
  (H0: f a < f b): (a < b)%nat.
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

Theorem increasing_le_compat (f: sequence Z) (H: increasing f) (a b: nat)
  (H0: (a <= b)%nat): f a <= f b.
Proof.
  induction H0.
  + lia.
  + pose (H m). lia.
Qed.

Theorem increasing_le_compat_inv (f: sequence Z) (H: increasing f) (a b: nat)
  (H0: f a <= f b): (a <= b)%nat.
Proof.
  revert b H0. induction a; intros.
  + destruct b; lia.
  + pose (H a). assert (f a <= f b) by lia. apply IHa in H1. inversion H1.
    - subst. lia.
    - lia.
Qed.

(* Let's define function that finds the last element of increasing sequence
  that's less or equal to given limit value *)

From Stdlib Require Import FunInd.

Function last_value_le_aux (f: sequence Z) (H: increasing f) (M: Z) (i: nat)
  { measure (fun i => Z.to_nat (M - f i)) i }: nat :=
  let W := f i in
  if Z_lt_le_dec M W
    then i
    else if Z.eq_dec M W
           then S i
           else last_value_le_aux H M (S i).
Proof.
  abstract (intros; destruct Z_lt_le_dec; [| destruct Z.eq_dec;
    [| pose proof (H i)]]; lia).
Defined.

Definition last_value_le (f: sequence Z) (H: increasing f) (M: Z) :=
  last_value_le_aux H M 0%nat.

Theorem last_value_le_aux_le_self (f: sequence Z) (H: increasing f) (M: Z) (k: nat):
  (k <= last_value_le_aux H M k)%nat.
Proof.
  apply last_value_le_aux_ind; intros; lia.
Qed.

Theorem last_value_le_aux_spec (f: sequence Z) (H: increasing f) (M: Z) (i: nat):
  forall k, (i <= k)%nat -> ((k < last_value_le_aux H M i)%nat <-> f k <= M).
Proof.
  apply last_value_le_aux_ind.
  + intros. destruct Z_lt_le_dec.
    - split; intros; try lia.
      unfold W in *. assert (f k < f i0) by lia. apply increasing_lt_compat_inv in H2; auto.
    - split; intros; lia.
  + intros. destruct Z_lt_le_dec; try lia.
    destruct Z.eq_dec; try congruence; split; intros. 
    - assert (k = i0) by lia. subst. unfold W. auto.
    - unfold W in *. subst. apply increasing_le_compat_inv in H1; auto; lia.
  + intros. destruct Z_lt_le_dec; try lia.
    destruct Z.eq_dec; try congruence.
    inversion H1; subst.
    - split; intros; unfold W in *; auto.
      apply last_value_le_aux_le_self.
    - apply H0. lia.
Qed.

Theorem last_value_le_spec (f: sequence Z) (H: increasing f) (M: Z):
  forall i, (i < last_value_le H M)%nat <-> f i <= M.
Proof.
  intros. apply last_value_le_aux_spec. lia.
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
  | S (S i as m) => k1 * recurrent_sequence k1 k2 a b m +
                    k2 * recurrent_sequence k1 k2 a b i
  end.

Fixpoint accumulator (k1 k2 a b: Z) (n: nat): Z :=
  match n with
  | O => b
  | S n' => accumulator k1 k2 (k1 * a + k2 * b) a n'
  end.

(* Prove equivalence of both definitions *)

Theorem recurrent_sequence_unfold (k1 k2 a b: Z) (n: nat):
  recurrent_sequence k1 k2 a b (S (S n)) =
  k1 * recurrent_sequence k1 k2 a b (S n) + k2 * recurrent_sequence k1 k2 a b n.
Proof. reflexivity. Qed.

Theorem accumulator_O (k1 k2 a b: Z): accumulator k1 k2 a b O = b.
Proof. reflexivity. Qed.

Theorem accumulator_S (k1 k2 a b: Z) (n: nat):
  accumulator k1 k2 a b (S n) = accumulator k1 k2 (k1 * a + k2 * b) a n.
Proof. reflexivity. Qed.

Theorem accumulator_linear (k1 k2 a b: Z) (n m: nat):
  accumulator k1 k2 (recurrent_sequence k1 k2 a b (S (S (S n)))) (recurrent_sequence k1 k2 a b (S (S n))) m =
  k1 * accumulator k1 k2 (recurrent_sequence k1 k2 a b (S (S n))) (recurrent_sequence k1 k2 a b (S n)) m +
  k2 * accumulator k1 k2 (recurrent_sequence k1 k2 a b (S n)) (recurrent_sequence k1 k2 a b n) m.
Proof.
  revert n. induction m; intros.
  + repeat rewrite accumulator_O in *. rewrite <- recurrent_sequence_unfold.
    reflexivity.
  + intros. repeat rewrite accumulator_S.
    repeat rewrite <- recurrent_sequence_unfold. apply IHm.
Qed.

Theorem recurrent_sequence_accumulator_equiv (k1 k2 a b: Z) (n: nat):
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
      symmetry. apply accumulator_linear. }
  apply H.
Qed.

(* Theorems about fibonacci numbers *)

Definition fibonacci := recurrent_sequence 1 1 1 2.
Definition fibonacci_efficient := accumulator 1 1 2 1.

Theorem fibonacci_pos (n: nat): 0 < fibonacci n.
Proof.
  assert (0 < fibonacci n /\ 0 < fibonacci (S n)).
  { unfold fibonacci. induction n.
    - simpl. lia.
    - destruct IHn; split; auto. rewrite recurrent_sequence_unfold. lia. }
  apply H.
Qed.

Theorem fibonacci_increasing: increasing fibonacci.
Proof.
  unfold increasing.
  assert (forall n, fibonacci n < fibonacci (S n) < fibonacci (S (S n))).
  { unfold fibonacci. induction n.
    + simpl. lia.
    + destruct IHn; split; auto. pose proof (fibonacci_pos n).
      unfold fibonacci in H1. repeat rewrite recurrent_sequence_unfold. lia. }
  intros. apply H.
Qed.

Theorem fibonacci_efficient_increasing: increasing fibonacci_efficient.
Proof.
  unfold increasing. intro. unfold fibonacci_efficient.
  repeat rewrite <- recurrent_sequence_accumulator_equiv. apply fibonacci_increasing.
Qed.

(* Useful theorem about parity of fibonacci numbers *)

Theorem fibonacci_parity_period (n : nat) :
  Z.even (fibonacci (n + 3)) = Z.even (fibonacci n).
Proof.
  induction n using (well_founded_induction lt_wf). destruct n; [| destruct n].
  + simpl. auto.
  + simpl. auto.
  + replace (S (S n) + 3)%nat with (S (S (S (S (S n))))) by lia.
    unfold fibonacci. rewrite recurrent_sequence_unfold, Z.mul_1_l, Z.mul_1_l.
    replace (S (S (S (S n)))) with (S n + 3)%nat by lia.
    replace (S (S (S n))) with (n + 3)%nat by lia. rewrite Z.even_add.
    rewrite H; try lia. rewrite H; try lia. rewrite <- Z.even_add. f_equal.
    unfold fibonacci. rewrite recurrent_sequence_unfold. ring.
Qed.

Theorem fibonacci_even_iff (n: nat):
  let P: nat -> Prop :=
    fun n => (Z.even (fibonacci n) = true <-> (exists m, n = 3 * m + 1)%nat) in
  P n.
Proof.
  induction n using (well_founded_induction lt_wf).
  destruct n; [| destruct n; [| destruct n]].
  + simpl. constructor; intros; try congruence. destruct H0; lia.
  + simpl. constructor; intros; auto. exists 0%nat; auto.
  + simpl. constructor; intros; try congruence. destruct H0; lia.
  + replace (S (S (S n))) with (n + 3)%nat by lia. intros. unfold P.
    rewrite fibonacci_parity_period. rewrite H; try lia.
    constructor; intros.
    - destruct H0. exists (x + 1)%nat. lia.
    - destruct H0. exists (x - 1)%nat. lia.
Qed.


(* Theorems about even fibonacci numbers *)

Definition even_fibonacci_efficient := accumulator 4 1 8 2.

Theorem even_fib_gt_1 (n: nat): 1 < even_fibonacci_efficient n.
Proof.
  assert (1 < even_fibonacci_efficient n /\ 1 < even_fibonacci_efficient (S n)).
  { unfold even_fibonacci_efficient.
    repeat rewrite <- recurrent_sequence_accumulator_equiv. induction n.
    + simpl. lia.
    + destruct IHn; split; auto. rewrite recurrent_sequence_unfold. lia. }
  apply H.
Qed.

Theorem even_fib_increasing: increasing even_fibonacci_efficient.
Proof.
  unfold increasing. intros.
  assert (even_fibonacci_efficient n < even_fibonacci_efficient (S n) <
  even_fibonacci_efficient (S (S n))).
  { induction n.
    + simpl. unfold even_fibonacci_efficient. simpl. lia.
    + pose proof (even_fib_gt_1 n) as H1.
      unfold even_fibonacci_efficient in *. destruct IHn; split; auto.
      repeat rewrite <- recurrent_sequence_accumulator_equiv in *.
      repeat rewrite recurrent_sequence_unfold. lia. }
  apply H.
Qed.

Theorem even_fib_fibonacci_index (n: nat):
  even_fibonacci_efficient n = fibonacci (S (3 * n)).
Proof.
  assert (even_fibonacci_efficient n = fibonacci (S (3 * n)) /\
          even_fibonacci_efficient (S n) = fibonacci (S (3 * S n))).
  { induction n.
    + simpl. unfold even_fibonacci_efficient, fibonacci. simpl. auto.
    + destruct IHn; split; auto. unfold even_fibonacci_efficient, fibonacci in *.
      repeat rewrite <- recurrent_sequence_accumulator_equiv in *.
      rewrite recurrent_sequence_unfold. ring_simplify.
      replace (3 * S (S n))%nat with (S (S (S (S (S (S (3 * n)))))))%nat by lia.
      replace (3 * S n)%nat with (S (S (S (3 * n))))%nat in H0 by lia.
      repeat rewrite recurrent_sequence_unfold in *. ring_simplify.
      ring_simplify in H0. lia. }
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

Definition increasing_sequence_with_max_value (f: sequence Z) (H: increasing f)
  (M: Z): list Z := map f (seq 0 (last_value_le H M)).

Definition result_simple (M: Z): Z :=
  sum_Z (filter Z.even (increasing_sequence_with_max_value fibonacci_increasing M)).

Definition result_more_efficient (M: Z): Z :=
  sum_Z (increasing_sequence_with_max_value even_fib_increasing M).


Theorem sum_Z_cons (n: Z) (L: list Z):
  fold_right Z.add n L = fold_right Z.add 0 L + n.
Proof.
  induction L.
  + simpl. lia.
  + simpl. lia.
Qed.

Theorem nat_mod3_cases (n : nat) :
  ((~ exists m, n = 3 * m + 1) <-> exists m, n = 3 * m \/ n = 3 * m + 2)%nat.
Proof.
  constructor; intros.
  + pose proof (Nat.div_mod_eq n 3).
    pose proof (Nat.mod_bound_pos n 3 ltac:(lia) ltac:(lia)).
    assert (n mod 3 = 0 \/ n mod 3 = 1 \/ n mod 3 = 2)%nat by lia.
    destruct H2 as [H2 | [H2 | H2]].
    - exists (n / 3)%nat. lia.
    - exfalso. apply H. exists (n / 3)%nat. lia.
    - exists (n / 3)%nat. lia.
  + intro. destruct H, H0. lia.
Qed.

Theorem sum_even_fib_equiv (n: nat): sum_Z (filter Z.even (map fibonacci (seq 0 n))) =
  sum_Z (map even_fibonacci_efficient (seq 0 ((n + 1) / 3))).
Proof.
  induction n.
  + simpl. auto.
  + replace (S n + 1)%nat with (n + 2)%nat by lia. rewrite seq_S.
    change (0 + n)%nat with n. rewrite map_app.
    change (map fibonacci [n]) with ([fibonacci n]). rewrite filter_app.
    simpl filter. remember (Z.even (fibonacci n)) as W. destruct W.
    - unfold sum_Z in *. rewrite fold_right_app. simpl fold_right at 1.
      replace (fibonacci n + 0) with (fibonacci n) by lia.
      rewrite sum_Z_cons. symmetry in HeqW.
      apply fibonacci_even_iff in HeqW. destruct HeqW. subst.
      replace ((3 * x + 1 + 1) / 3)%nat with x in IHn.
      replace ((3 * x + 1 + 2) / 3)%nat with (S x)%nat.
      rewrite IHn. rewrite seq_S. change (0 + x)%nat with x. rewrite map_app.
      change (map even_fibonacci_efficient [x]) with ([even_fibonacci_efficient x]).
      rewrite fold_right_app. simpl fold_right.
      replace (even_fibonacci_efficient x + 0) with (even_fibonacci_efficient x) by lia.
      rewrite even_fib_fibonacci_index.
      rewrite (sum_Z_cons (fibonacci (S (3 * x)))).
      replace (S (3 * x))%nat with (3 * x + 1)%nat by lia. reflexivity.
      { replace (3 * x + 1 + 2)%nat with ((x + 1) * 3)%nat by lia. rewrite Nat.div_mul; lia. }
      { replace (3 * x + 1 + 1)%nat with (2 + x * 3)%nat by lia.
        rewrite Nat.div_add. simpl. reflexivity. lia. }
    - unfold sum_Z in *. rewrite fold_right_app. simpl fold_right at 1.
      symmetry in HeqW. assert (~ (Z.even (fibonacci n) = true)) by congruence.
      rewrite fibonacci_even_iff in H. rewrite nat_mod3_cases in H. destruct H as [x [H | H]].
      * subst n. replace ((3 * x + 2) / 3)%nat with x.
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



Theorem last_value_le_gt_index (f: sequence Z) (H: increasing f) (n: nat):
  (n < last_value_le H (f n))%nat.
Proof.
  pose proof (last_value_le_spec H (f n) n). assert (f n <= f n) by lia.
  apply H0 in H1. auto.
Qed.

Theorem last_value_le_eq_S_iff (f: sequence Z) (H: increasing f) (n: nat) (M: Z):
  (last_value_le H M = S n) <-> (f n <= M < f (S n)).
Proof.
  pose proof (last_value_le_spec H). split; intros.
  + split.
    - apply H0. lia.
    - assert (M < f (S n) <-> (f (S n) <= M -> False)) by lia.
      rewrite H2. rewrite <- H0. lia.
  + destruct H1. rewrite <- H0 in H1. assert (f (S n) <= M -> False) by lia.
    rewrite <- H0 in H3. lia.
Qed.

Theorem last_value_le_at_value (f: sequence Z) (H: increasing f) (n: nat):
  last_value_le H (f n) = S n.
Proof.
  rewrite last_value_le_eq_S_iff. pose (H n). lia.
Qed.


Theorem div3_lt_equiv (k i : nat) :
  (i < (k + 1) / 3 <-> S (3 * i) < k)%nat.
Proof.
  intros. replace k with (k + 1 - 1)%nat at 2 by lia.
  rewrite (Nat.div_mod_eq (k + 1) 3) at 2.
  pose proof (Nat.mod_bound_pos (k + 1) 3 ltac:(lia) ltac:(lia)). nia.
Qed.

Lemma last_value_le_zero (f : sequence Z) (H : increasing f) (M : Z)
    (Hf : M < f 0%nat) : last_value_le H M = 0%nat.
Proof.
  unfold last_value_le. rewrite last_value_le_aux_equation.
  destruct Z_lt_le_dec; lia.
Qed.

Theorem last_value_le_even_fib (M : Z) :
  last_value_le even_fib_increasing M
  = ((last_value_le fibonacci_increasing M + 1) / 3)%nat.
Proof.
  destruct (Z_le_dec M 0).
  + rewrite last_value_le_zero. rewrite last_value_le_zero. auto.
    { replace (fibonacci 0) with 1 by (compute; auto). lia. }
    { replace (even_fibonacci_efficient 0) with 2 by (compute; auto). lia. }
  + remember (last_value_le fibonacci_increasing M) as k.
    assert (forall (i : nat),
      (i < (k + 1) / 3)%nat <-> even_fibonacci_efficient i <= M).
    { intros. rewrite div3_lt_equiv.
      rewrite even_fib_fibonacci_index.
      rewrite <- (last_value_le_spec fibonacci_increasing M). rewrite Heqk.
      reflexivity. }
    assert (forall (i : nat),
        (i < last_value_le even_fib_increasing M)%nat <->
        (i < (k + 1) / 3)%nat).
    { intro i. rewrite last_value_le_spec. symmetry. auto. }
    assert (last_value_le even_fib_increasing M <= (k + 1) / 3)%nat.
    { destruct (le_dec (last_value_le even_fib_increasing M) ((k + 1) / 3))%nat; auto.
      exfalso. rewrite Nat.nle_gt in n0. rewrite H0 in n0. lia. }
    assert ((k + 1) / 3 <= last_value_le even_fib_increasing M)%nat.
    { destruct (le_dec ((k + 1) / 3) (last_value_le even_fib_increasing M))%nat; auto.
      rewrite Nat.nle_gt in n0. rewrite <- H0 in n0. lia. }
    lia.
Qed.

Theorem both_results_equal (M: Z) : result_simple M = result_more_efficient M.
Proof.
  assert (M <= 0 \/ 0 < M) by lia. destruct H.
  + unfold result_simple, result_more_efficient, increasing_sequence_with_max_value.
    assert (last_value_le fibonacci_increasing M = 0)%nat.
    { pose proof (fibonacci_pos 0). unfold last_value_le.
      rewrite last_value_le_aux_equation. destruct Z_lt_le_dec; lia. }
    assert (last_value_le even_fib_increasing M = 0)%nat.
    { pose proof (even_fib_gt_1 0).
      unfold last_value_le. rewrite last_value_le_aux_equation.
      destruct Z_lt_le_dec; lia. }
    rewrite H0, H1. simpl. auto.
  + unfold result_simple, result_more_efficient.
    unfold increasing_sequence_with_max_value.
    rewrite last_value_le_even_fib; auto. apply sum_even_fib_equiv.
Qed.


Theorem result_simple_even_fib_step (n: nat):
  result_simple (even_fibonacci_efficient (S n)) =
  result_simple (even_fibonacci_efficient n) + even_fibonacci_efficient (S n).
Proof.
  repeat rewrite both_results_equal.
  unfold result_more_efficient, increasing_sequence_with_max_value.
  rewrite last_value_le_at_value, last_value_le_at_value. repeat rewrite seq_S. simpl.
  rewrite map_app, sum_Z_app. f_equal. simpl. lia.
Qed.

Theorem even_fib_recurrence (n: nat):
  even_fibonacci_efficient (S (S n)) =
  4 * even_fibonacci_efficient (S n) + even_fibonacci_efficient n.
Proof.
  unfold even_fibonacci_efficient. repeat rewrite <- recurrent_sequence_accumulator_equiv.
  rewrite recurrent_sequence_unfold. lia.
Qed.

Theorem even_fib_ge_4x (n: nat):
  let P: nat -> Prop := fun n => 4 * even_fibonacci_efficient n <= even_fibonacci_efficient (S n) in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { unfold P in *. induction n.
    + compute. split; congruence.
    + destruct IHn; split; auto.
      repeat rewrite even_fib_recurrence in *. lia. }
  apply H.
Qed.

Theorem even_fib_4x_le_17x (n: nat):
  let P: nat -> Prop := fun n => 4 * even_fibonacci_efficient (S n) <= 17 * even_fibonacci_efficient n in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { unfold P in *. induction n.
    + compute. split; congruence.
    + destruct IHn; split; auto.
      repeat rewrite even_fib_recurrence in *. lia. }
  apply H.
Qed.

Theorem thm06 (M: Z) (H: 1 <= M):
  4 * even_fibonacci_efficient (last_value_le even_fib_increasing M) <= 17 * M.
Proof.
  remember (last_value_le even_fib_increasing M) as W. destruct W.
  + change (even_fibonacci_efficient 0) with 2. lia.
  + symmetry in HeqW.
    pose proof (last_value_le_eq_S_iff even_fib_increasing).
    pose proof (proj1 (H0 W M) HeqW). destruct H1. pose proof (even_fib_4x_le_17x W).
    simpl in H3. lia.
Qed.

Theorem M_lt_next_even_fib (M: Z):
  M < even_fibonacci_efficient (S (last_value_le even_fib_increasing M)).
Proof.
  remember (last_value_le even_fib_increasing M) as W. destruct W.
  + change (even_fibonacci_efficient 1) with 8. symmetry in HeqW. assert (M < 2).
    { unfold last_value_le in HeqW. rewrite last_value_le_aux_equation in HeqW.
      destruct Z_lt_le_dec.
      + change (even_fibonacci_efficient 0) with 2 in l. auto.
      + destruct Z.eq_dec; try lia.
        pose proof (last_value_le_aux_le_self even_fib_increasing M 1).
        lia. }
    lia.
  + symmetry in HeqW. pose proof (last_value_le_eq_S_iff even_fib_increasing W M).
    pose proof ((proj1 H) HeqW). destruct H0.
    rewrite even_fib_recurrence.
    pose proof (even_fib_gt_1 W). lia.
Qed.

Theorem even_fib_le_4M_imp_prev_le_M (n: nat) (M: Z):
  let P: nat -> Prop := fun n => even_fibonacci_efficient (S n) <= 4 * M ->
    even_fibonacci_efficient n <= M in
  P n.
Proof.
  intro. assert (P n /\ P (S n)).
  { induction n.
    + unfold P. split.
      - intros. change (even_fibonacci_efficient 1) with 8 in H.
        change (even_fibonacci_efficient 0) with 2. lia.
      - intros. change (even_fibonacci_efficient 2) with 34 in H.
        change (even_fibonacci_efficient 1) with 8. lia.
    + destruct IHn; split; auto. unfold P in *.
      repeat rewrite even_fib_recurrence in *.
      intros. ring_simplify in H1.
      pose proof (even_fib_gt_1 n).
      pose proof (even_fib_gt_1 (S n)). lia. }
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
      PROP ((0 <= i <= last_value_le even_fib_increasing M)%nat)
      LOCAL (temp _max (Vint (Int.repr M));
             temp _a (Vint (Int.repr (match i with O => 0 | S n => even_fibonacci_efficient n end)));
             temp _b (Vint (Int.repr (even_fibonacci_efficient i)));
             temp _sum (Vint (Int.repr
               (result_simple (match i with O => 0 | S n => even_fibonacci_efficient n end)))))
      SEP ()).
    - entailer!. Exists 0%nat. entailer!.
    - entailer!.
    - do 4 forward. entailer!.
      * Exists (S i). entailer!. repeat split.
        ++ rewrite Int.unsigned_repr in HRE. clear H1.
           assert (even_fibonacci_efficient i <= M) by lia. clear HRE.
           rewrite <- (last_value_le_spec even_fib_increasing) in H1. auto.
           { split.
             + pose proof (even_fib_gt_1 i). lia.
             + destruct H1. apply (increasing_le_compat even_fib_increasing) in H2.
               assert (1 <= M) by lia. apply thm06 in H3. rep_lia. }
        ++ destruct i; try reflexivity. rewrite even_fib_recurrence. reflexivity.
        ++ destruct i; try reflexivity. rewrite result_simple_even_fib_step. reflexivity.
    - deadvars!. forward. entailer!. destruct i.
      * change (Int.unsigned (Int.repr (even_fibonacci_efficient 0))) with 2 in HRE. lia.
      * rewrite Int.unsigned_repr in HRE. do 2 f_equal. repeat rewrite both_results_equal.
        destruct H1. clear H1. unfold result_more_efficient.
        unfold increasing_sequence_with_max_value.
        do 3 f_equal. rewrite last_value_le_at_value. symmetry. rewrite last_value_le_eq_S_iff.
        split; auto. inversion H2.
        ++ symmetry in H3. rewrite last_value_le_eq_S_iff in H3. lia.
        ++ apply Peano.le_n_S in H3. rewrite H1 in H3. clear H1 H2 m.
           assert (even_fibonacci_efficient (S i) <= M -> False) by lia.
           rewrite <- (last_value_le_spec even_fib_increasing) in H1.
           assert (last_value_le even_fib_increasing M <= S i)%nat by lia. lia.
        ++ split.
           -- pose proof (even_fib_gt_1 (S i)). lia.
           -- destruct H1. apply (increasing_le_compat even_fib_increasing) in H2.
              assert (1 <= M) by lia. apply thm06 in H3. rep_lia.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function. forward_call 1000000.
  remember (result_simple 1000000) as W. clear HeqW. forward.
Qed.
