Require Import ZArith Znumtheory Recdef Lia.
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

Theorem repeated_div_aux_thm0 (i n: Z) (H: 1 <= n):
  1 <= repeated_repeated_div i n H.
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

Theorem repeated_div_aux_thm2 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  forall x, 2 <= x <= i -> (x | repeated_repeated_div i n H) -> False.
Proof.
Admitted.

Theorem repeated_div_aux_thm3 (i n: Z) (H: 1 <= n) (H0: 2 <= i):
  Z.divide (i + 1) (repeated_repeated_div i n H) -> prime (i + 1).
Proof.
  intros. destruct (prime_dec (i + 1)); auto. exfalso. apply not_prime_divide in n0; try lia.
  destruct n0 as [k [H2 H3]]. destruct H3. assert (Z.divide k (repeated_repeated_div i n H)).
  { destruct H1. exists (x0 * x). lia. }
  apply repeated_div_aux_thm2 in H4; auto. lia.
Qed.