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
