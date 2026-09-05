Require Import VST.floyd.proofauto.
From Stdlib Require Import Znumtheory ZArith Bool List.
Import ListNotations.
Require Import PrimeFactors Math_EulerProject5.

Open Scope Z.

Require Import EulerProject5.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition max_prime_power_spec :=
  DECLARE _max_prime_power
    WITH p : Z, bound : Z
    PRE  [ tint, tint ]
      PROP (2 <= p <= 100;
            1 <= bound <= 100)
      PARAMS (Vint (Int.repr p); Vint (Int.repr bound))
      SEP ()
    POST [ tuint ]
      PROP (Z.pow p (get_exp_le_bound bound p) <= bound)
      RETURN (Vint (Int.repr (Z.pow p (get_exp_le_bound bound p))))
      SEP ().

Definition bool_list_of_function (n : Z) (f : Z -> bool) : list val :=
  map Val.of_bool (map f (upto (Z.to_nat n))).

Definition sieve_primes_spec :=
  DECLARE _sieve_primes
    WITH n : Z, arr : val, f_init : Z -> bool, sh : share
    PRE [ tptr tbool, tint ]
      PROP (2 <= n <= 100; writable_share sh)
      PARAMS (arr; Vint (Int.repr n))
      SEP (data_at sh (tarray tbool (n + 1)) (bool_list_of_function (n + 1) f_init) arr)
    POST [ tvoid ]
      PROP ()
      LOCAL ()
      SEP (data_at sh (tarray tbool (n + 1))
            (bool_list_of_function (n + 1)
              (fun i => if Z_le_dec i 1 then f_init i else sieve n i))
            arr).


Definition Gprog := [max_prime_power_spec; sieve_primes_spec].


Lemma max_prime_power_proof : 
  semax_body Vprog Gprog f_max_prime_power max_prime_power_spec.
Proof.
  start_function. forward.
  forward_while
    (EX k : Z,
      PROP (0 <= k; p ^ k <= p * bound)
      LOCAL (temp _p (Vint (Int.repr p));
             temp _bound (Vint (Int.repr bound));
             temp _power (Vint (Int.repr (p ^ k))))
      SEP ()).
  + Exists 0. ring_simplify (p ^ 0). entailer!.
  + entailer!.
  + forward. entailer!. Exists (k + 1). entailer!.
    rewrite Z.pow_add_r; try lia. ring_simplify (p ^ 1). split; auto. 
    rewrite Int.unsigned_repr in HRE; try nia.
    unfold Int.max_unsigned. simpl. nia.
  + deadvars!. forward.
    - entailer!. replace Int.zero with (Int.repr 0) by auto.
      assert (p = 0).
      { replace Int.zero with (Int.repr 0) by auto.
        apply repr_inj_unsigned in H3; auto.
        + unfold Int.max_unsigned; simpl; lia.
        + unfold Int.max_unsigned; simpl; lia. }
      lia.
    - entailer!. split.
      * destruct (Z_le_dec p bound).
        ++ apply prime_pow_le_bound_le_n; try lia.
        ++ assert (get_exp_le_bound bound p = 0).
           { rewrite get_exp_le_bound_equation.
             remember (2 <=? p) as B1. remember (p <=? bound) as B2.
             symmetry in HeqB1, HeqB2. destruct B1, B2; auto.
             exfalso. rewrite Z.leb_le in HeqB2. lia. }
           rewrite H3. ring_simplify (p ^ 0). lia.
      * f_equal. rewrite divu_repr.
        ++ f_equal. destruct (Z.eq_dec k 0).
           -- subst k. exfalso. ring_simplify (p ^ 0) in HRE.
              rewrite Int.unsigned_repr in HRE; try lia.
              unfold Int.max_unsigned; simpl; lia.
           -- assert (1 <= k) by lia. clear n.
              assert (p ^ (k - 1) <= bound).
              { replace k with (k - 1 + 1) in H2 by ring.
                rewrite Z.pow_add_r in H2; try lia. ring_simplify (p ^ 1) in H2.
                nia. }
              assert (k - 1 = get_exp_le_bound bound p).
              { pose proof (get_exp_le_bound_spec bound p (proj1 H) (proj1 H0)).
                destruct H5. pose proof (H6 _ H4).
                assert (get_exp_le_bound bound p <= k - 1).
                { destruct (Z_lt_ge_dec (k - 1) (get_exp_le_bound bound p)); try lia.
                  rewrite Int.unsigned_repr in HRE.
                  + assert (k <= get_exp_le_bound bound p) by lia.
                    apply (Z.pow_le_mono_r p) in H8; try lia.
                  + unfold Int.max_unsigned; simpl; nia. }
                lia. }
              replace k with (k - 1 + 1) by ring. rewrite Z.pow_add_r; try lia.
              ring_simplify (p ^ 1). rewrite Z.div_mul; try lia. congruence.
        ++ unfold Int.max_unsigned; simpl; nia.
        ++ unfold Int.max_unsigned; simpl; lia.
Qed.


Lemma sieve_primes_proof :
  semax_body Vprog Gprog f_sieve_primes sieve_primes_spec.
Proof.
  start_function.
  assert (forall L1 L2, L1 = L2 ->
          data_at sh (tarray tbool (n + 1)) L1 arr |-- data_at sh (tarray tbool (n + 1)) L2 arr) as Harr.
  { intros. rewrite H0. auto. }
  forward_loop
    (EX i : Z,
      PROP (2 <= i <= n + 1)
      LOCAL (temp _i (Vint (Int.repr i));
             temp _is_prime arr;
             temp _n (Vint (Int.repr n)))
      SEP (data_at sh (tarray tbool (n + 1))
            (bool_list_of_function (n + 1)
               (fun k => if Z_le_dec k 1 then f_init k
                         else if Z_lt_dec k i then true
                         else f_init k))
            arr))
  break:
    (PROP ()
     LOCAL (temp _is_prime arr; temp _n (Vint (Int.repr n)))
     SEP (data_at sh (tarray tbool (n + 1))
           (bool_list_of_function (n + 1)
              (fun k => if Z_le_dec k 1 then f_init k else if Z_le_dec k n then true else f_init k))
           arr)).
  + forward. Exists 2. entailer!. apply Harr.
    unfold bool_list_of_function. f_equal. apply map_ext. intros a.
    destruct Z_le_dec; auto. destruct Z_lt_dec; auto. lia.
  + Intros i. forward_if.
    - abbreviate_semax. forward. forward. Exists (i + 1). entailer!.
      apply Harr. unfold bool_list_of_function.
      replace (Vint Int.one) with (Val.of_bool true) by auto.
      rewrite upd_Znth_map. f_equal. apply Znth_eq_ext.
      * rewrite Zlength_upd_Znth, Zlength_map, Zlength_map. auto.
      * intros. rewrite Zlength_upd_Znth, Zlength_map in H5.
        rewrite Zlength_upto in H5.
        replace (Z.of_nat (Z.to_nat (n + 1))) with (n + 1) in H5 by lia.
        rewrite upd_Znth_eq. rewrite length_map. rewrite upto_length.
        rewrite Znth_map, Znth_map, Znth_map; try lia.
        ++ rewrite Znth_upto; try lia. rewrite Znth_upto; try lia.
           repeat destruct Z.eq_dec.
           -- destruct Z_le_dec; try lia. destruct Z_lt_dec; try lia.
           -- repeat destruct Z_lt_dec; try lia; auto.
        ++ rewrite Zlength_upto. lia.
        ++ rewrite Znth_upto; try lia. rewrite Zlength_upto. lia.
        ++ rewrite Zlength_upto; try lia.
        ++ rewrite Zlength_map. rewrite Zlength_upto. lia.
    - assert (i = n + 1) by lia. subst i. forward. entailer!. apply Harr.
      unfold bool_list_of_function. rewrite map_map, map_map. apply map_ext.
      intros. f_equal. destruct Z_lt_dec; try lia.
      * destruct (Z_le_dec a n); try lia. auto.
      * destruct (Z_le_dec a n); try lia. auto.
  + forward_loop
      (EX i : Z,
        PROP (2 <= i; (i - 1) * (i - 1) <= n)
        LOCAL (temp _i__1 (Vint (Int.repr i));
               temp _is_prime arr;
               temp _n (Vint (Int.repr n)))
        SEP (data_at sh (tarray tbool (n + 1))
          (bool_list_of_function (n + 1)
            (fun k => if Z_le_dec k 1 then f_init k
                      else if Z_le_dec k n then sieve_loop (2, i - 1) n (init_state n) k
                      else f_init k))
          arr)).
    - forward. Exists 2. entailer!. simpl (2 - 1).
      rewrite sieve_loop_equation. simpl. unfold init_state. apply Harr.
      unfold bool_list_of_function. f_equal. apply map_ext. intros. 
      destruct Z_le_dec; auto. destruct Z_le_dec; auto.
      assert (2 <= a) by lia. rewrite (proj2 (Z.leb_le _ _) H3).
      rewrite (proj2 (Z.leb_le _ _) l). auto.
    - Intros i. assert (i * i <= 121) by nia. forward_if.
      * abbreviate_semax. forward. 
        ++ entailer!. nia.
        ++ entailer!. remember (Znth i _) as W.
           assert (W = Val.of_bool true \/ W = Val.of_bool false).
           { unfold bool_list_of_function in HeqW. rewrite Znth_map in HeqW.
             + destruct (Znth i _) in HeqW; auto.
             + rewrite Zlength_map. rewrite Zlength_upto. nia. }
           destruct H7; rewrite H7; simpl; auto.
        ++ forward_if
            (PROP ()
            LOCAL (temp _i__1 (Vint (Int.repr i));
                   temp _is_prime arr;
                   temp _n (Vint (Int.repr n)))
            SEP (data_at sh (tarray tbool (n + 1))
              (bool_list_of_function (n + 1)
                (fun k => if Z_le_dec k 1 then f_init k
                          else if Z_le_dec k n then sieve_loop (2, i) n (init_state n) k
                          else f_init k))
              arr)).
           -- deadvars!. forward_loop
               (EX j : Z,
                 PROP (i * i <= j; j <= n + i; (i | j))
                 LOCAL (temp _j (Vint (Int.repr j));
                        temp _i__1 (Vint (Int.repr i));
                        temp _is_prime arr;
                        temp _n (Vint (Int.repr n)))
                 SEP (data_at sh (tarray tbool (n + 1))
                   (bool_list_of_function (n + 1)
                     (fun k => if Z_le_dec k 1 then f_init k
                               else if Z_le_dec k n then
                                    (if (Z.leb (i * i) k && Z.ltb k j && (k mod i =? 0))%bool then false
                                     else sieve_loop (2, i - 1) n (init_state n) k)
                               else f_init k))
                   arr)).
              ** forward. Exists (i * i). entailer!.
                 +++ exists i; auto.
                 +++ apply Harr.
                     unfold bool_list_of_function. f_equal. apply map_ext. intro.
                     destruct Z_le_dec; auto. destruct Z_le_dec; auto.
                     remember (_ && _ && _) as B. destruct B; auto. symmetry in HeqB.
                     rewrite andb_true_iff, andb_true_iff in HeqB.
                     destruct HeqB as [[HeqB1 HeqB2] HeqB3].
                     rewrite Z.leb_le in HeqB1. rewrite Z.ltb_lt in HeqB2. lia.
              ** Intros j. forward_if.
                 +++ abbreviate_semax. assert (0 <= j <= 110) by nia.
                     rewrite Int.signed_repr in H8; try rep_lia. forward.
                     forward. entailer!.
                     --- assert (0 <= j + i <= 121) by nia. rep_lia.
                     --- Exists (j + i). entailer!.
                         *** destruct H7. rewrite H7. exists (x + 1). ring.
                         *** apply Harr. replace (Vint Int.zero) with (Val.of_bool false) by auto.
                             unfold bool_list_of_function. rewrite upd_Znth_map.
                             f_equal. apply Znth_eq_ext.
                             ++++ rewrite Zlength_upd_Znth, Zlength_map, Zlength_map. auto.
                             ++++ intros. rewrite Zlength_upd_Znth, Zlength_map, Zlength_upto in H13.
                                  replace (Z.of_nat (Z.to_nat (n + 1))) with (n + 1) in H13 by lia.
                                  destruct (Z.eq_dec i0 j).
                                  ---- subst i0. rewrite Znth_upd_Znth_same.
                                       **** rewrite Znth_map.
                                            +++++ rewrite Znth_upto.
                                                  ----- destruct Z_le_dec; try nia.
                                                        destruct Z_le_dec; try lia.
                                                        remember (_ && _ && _) as B. destruct B; auto. symmetry in HeqB.
                                                        rewrite (proj2 (Z.leb_le _ _) H5) in HeqB; auto.
                                                        assert (j < j + i) by lia. rewrite (proj2 (Z.ltb_lt _ _) H14) in HeqB.
                                                        simpl in HeqB. rewrite Z.eqb_neq in HeqB. unfold not in HeqB.
                                                        rewrite Z.mod_divide in HeqB; try lia. tauto.
                                                  ----- lia.
                                            +++++ rewrite Zlength_upto. lia.
                                       **** rewrite Zlength_map, Zlength_upto. lia.
                                       **** auto.
                                  ---- rewrite upd_Znth_diff; auto.
                                       **** rewrite Znth_map, Znth_map.
                                            +++++ rewrite Znth_upto; try lia.
                                                  destruct Z_le_dec; auto. destruct Z_le_dec; try lia.
                                                  remember (i * i <=? i0) as b1. remember (i0 mod i =? 0) as b2.
                                                  remember (i0 <? j) as b3. remember (i0 <? j + i) as b4.
                                                  assert (b1 && b3 && b2 = b1 && b4 && b2).
                                                  { symmetry in Heqb1, Heqb2, Heqb3, Heqb4. destruct b2.
                                                    + rewrite Z.eqb_eq in Heqb2. rewrite Z.mod_divide in Heqb2; try lia.
                                                      destruct b1; simpl; auto. destruct b3, b4; simpl; auto.
                                                      - rewrite Z.ltb_lt in Heqb3. rewrite Z.ltb_ge in Heqb4. lia.
                                                      - rewrite Z.ltb_ge in Heqb3. rewrite Z.ltb_lt in Heqb4.
                                                        destruct Heqb2, H7. assert (j < i0 < j + i) by lia. rewrite H14, H7 in H15.
                                                        assert (x0 < x < x0 + 1) by nia. lia.
                                                    + rewrite andb_comm. simpl. rewrite andb_comm. simpl. auto. }
                                                  rewrite H14; auto.
                                            +++++ rewrite Zlength_upto; lia.
                                            +++++ rewrite Zlength_upto; lia.
                                       **** rewrite Zlength_map, Zlength_upto. lia.
                                       **** rewrite Zlength_map, Zlength_upto. lia.
                 +++ assert (0 <= j <= 110) by nia. rewrite Int.signed_repr in H8; try rep_lia. forward.
                     entailer!. apply Harr. unfold bool_list_of_function. f_equal.
                     apply map_ext. intros. destruct Z_le_dec; auto. destruct Z_le_dec; auto.
                     remember (_ && _ && _) as B. symmetry in HeqB. destruct B.
                     --- rewrite andb_true_iff, andb_true_iff in HeqB. rewrite Z.leb_le, Z.ltb_lt in HeqB.
                         rewrite Z.eqb_eq in HeqB. rewrite Z.mod_divide in HeqB; try lia. symmetry. clear H11 H12 H4.
                         assert (sieve_inv (i + 1) n (sieve_loop (2, i) n (init_state n))).
                         { apply sieve_loop_correct; try nia. apply sieve_inv_init. }
                         specialize (H4 a ltac:(lia) l).
                         assert (sieve_loop (2, i) n (init_state n) a = true -> False).
                         { rewrite H4. intros. destruct H11.
                           + apply prime_alt in H11. destruct H11, HeqB.
                             pose proof (H12 i ltac:(nia)). auto.
                           + unfold not in H11. destruct (prime_divisor_existence i); try lia. destruct H12.
                             assert (x < i + 1). { apply Zdivide_le in H13; try (destruct H12; lia). }
                             pose proof (H11 x H12 H14). apply H15. rewrite Z.mod_divide; try (destruct H12; lia).
                             destruct HeqB. exact (Z.divide_trans _ _ _ H13 H17). }
                         destruct sieve_loop; tauto.
                     --- clear H11 H12 H4. rewrite andb_false_iff, andb_false_iff in HeqB.
                         assert (sieve_inv i n (sieve_loop (2, i - 1) n (init_state n))).
                         { destruct (Z_le_dec 3 i).
                           + replace i with (i - 1 + 1) at 1 by ring. apply sieve_loop_correct; try nia.
                             apply sieve_inv_init.
                           + assert (i = 2) by lia. subst i. simpl. rewrite sieve_loop_equation; simpl.
                             apply sieve_inv_init. }
                         assert (sieve_inv (i + 1) n (sieve_loop (2, i) n (init_state n))).
                         { apply sieve_loop_correct; try nia. apply sieve_inv_init. }
                         pose proof (H4 a ltac:(lia) l). pose proof (H11 a ltac:(lia) l).
                         destruct HeqB as [[HeqB1 | HeqB2] | HeqB3].
                         *** rewrite Z.leb_gt in HeqB1.
                             assert ((sieve_loop (2, i - 1) n (init_state n) a = true) <->
                                     (sieve_loop (2, i) n (init_state n) a = true)).
                             { rewrite H12, H13. split; intros; destruct H14 as [Hp | Hf].
                               + left; auto.
                               + destruct (prime_dec a); auto.
                                 exfalso. destruct (composite_has_small_prime_factor a) as [q [Hq [Hq1 Hq2]]]; auto; try lia.
                                 assert (q < i) by nia. exact (Hf q Hq H14 Hq2).
                               + auto.
                               + right. intros. apply Hf; auto; try lia. }
                             destruct sieve_loop.
                             ++++ symmetry. rewrite <- H14; auto.
                             ++++ assert (sieve_loop (2, i) n (init_state n) a = true -> False).
                                  { rewrite <- H14. congruence. }
                                  destruct sieve_loop; auto.
                         *** rewrite Z.ltb_ge in HeqB2. lia.
                         *** rewrite Z.eqb_neq in HeqB3. unfold not in HeqB3.
                             assert ((sieve_loop (2, i - 1) n (init_state n) a = true) <->
                                     (sieve_loop (2, i) n (init_state n) a = true)).
                             { rewrite H12, H13. split; intros; destruct H14 as [Hp | Hf].
                               + auto.
                               + right. intros. destruct (Z.eq_dec q i).
                                 - unfold not. subst q. auto.
                                 - apply Hf; try lia; auto.
                               + auto.
                               + right. intros. apply Hf; auto; try lia. }
                             destruct sieve_loop.
                             ++++ symmetry. rewrite <- H14; auto.
                             ++++ assert (sieve_loop (2, i) n (init_state n) a = true -> False).
                                  { rewrite <- H14; congruence. }
                                  destruct sieve_loop; auto.
           -- assert (sieve_loop (2, i - 1) n (init_state n) i = false).
              { destruct Z_lt_dec in H4; try lia. unfold bool_list_of_function in H4.
                rewrite map_map in H4. rewrite nth_map' with (d' := 0) in H4.
                + rewrite invariants.nth_upto in H4.
                  - replace (Z.of_nat (Z.to_nat i)) with i in H4 by lia.
                    destruct Z_le_dec; try lia. destruct Z_le_dec in H4; try nia.
                    unfold typed_false in H4. unfold strict_bool_val in H4. simpl in H4.
                    destruct (sieve_loop (2, i - 1) n (init_state n) i); simpl in H4; try congruence.
                  - nia.
                + rewrite upto_length. nia. }
              deadvars!. forward. entailer!. apply Harr. unfold bool_list_of_function.
              f_equal. apply map_ext. intros. destruct Z_le_dec; auto. destruct Z_le_dec; auto.
              assert (sieve_inv i n (sieve_loop (2, i - 1) n (init_state n))).
              { destruct (Z_le_dec 3 i).
                + replace i with (i - 1 + 1) at 1 by ring. apply sieve_loop_correct; try nia.
                  apply sieve_inv_init.
                + assert (i = 2) by lia. subst i. simpl. rewrite sieve_loop_equation; simpl.
                  apply sieve_inv_init. }
              assert (sieve_inv (i + 1) n (sieve_loop (2, i) n (init_state n))).
              { apply sieve_loop_correct; try nia. apply sieve_inv_init. }
              assert (~ prime i).
              { pose proof (H9 i ltac:(lia) ltac:(nia)). rewrite H5 in H11.
                assert (false = true -> False) by congruence. tauto. }
              assert (Heq : (sieve_loop (2, i - 1) n (init_state n) a = true) <->
                (sieve_loop (2, i) n (init_state n) a = true)).
              { rewrite (H9 a ltac:(lia) l), (H10 a ltac:(lia) l).
                split; intros; auto; destruct H12; auto.
                + right. intros. apply H12; auto. assert (q <> i) by congruence. lia.
                + right. intros. apply H12; auto. lia. }
              destruct (sieve_loop (2, i - 1) n (init_state n) a).
              ** symmetry. rewrite <- Heq; auto.
              ** assert (sieve_loop (2, i) n (init_state n) a = true -> False).
                 { assert (false = true -> False) by congruence. tauto. }
                 destruct (sieve_loop (2, i) n (init_state n) a); auto.
           -- forward. Exists (i + 1). entailer!. apply Harr. unfold bool_list_of_function.
              f_equal. apply map_ext. intros. destruct Z_le_dec; auto. destruct Z_le_dec; auto.
              ring_simplify (i + 1 - 1). auto.
      * forward. entailer!. assert (i - 1 = Z.sqrt n).
        { pose proof (Z.sqrt_spec n ltac:(lia)). simpl in H7. nia. }
        assert (bool_list_of_function (n + 1)
                 (fun k => if Z_le_dec k 1 then f_init k else
                   if Z_le_dec k n then sieve_loop (2, i - 1) n (init_state n) k else f_init k) =
                bool_list_of_function (n + 1)
                 (fun k => if Z_le_dec k 1 then f_init k else sieve n k)).
        { unfold bool_list_of_function. f_equal. apply map_ext_Forall.
          unfold sieve. rewrite H7.
          assert (forall x, In x (upto (Z.to_nat (n + 1))) <-> 0 <= x <= n).
          { intros. rewrite In_upto. lia. }
          rewrite Forall_forall. intros. rewrite H8 in H9. destruct Z_le_dec; auto.
          destruct Z_le_dec; try lia. auto. }
        rewrite H8; auto.
Qed.


