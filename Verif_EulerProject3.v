Require Import VST.floyd.proofauto.
Require Import FunInd.
Require Import Znumtheory.

Open Scope Z.

Fixpoint product_of_factors_with_powers (L: list (Z * Z)): Z :=
  match L with
  | [] => 1
  | (x, p) :: t => Z.pow x p * product_of_factors_with_powers t
  end.

Function upto_aux (p: Z * Z) { measure (fun p => match p with (a, b) => Z.to_nat (b - a) end) p }: list Z :=
  match p with (a, b) => if Z_lt_ge_dec a b then a :: upto_aux (a + 1, b) else nil end.
Proof. intros. lia. Defined.

Definition upto (a b: Z) := upto_aux (a, b).

Definition prime_divisors m n := filter prime_dec (filter (fun x => Zdivide_dec x n) (upto m (n + 1))).

Function get_factor_power (n k: Z) {measure Z.to_nat n}: Z :=
  if Z_le_gt_dec k 1 then 0 else
  if Z_le_gt_dec n 1 then 0 else
  if Zdivide_dec k n
      then get_factor_power (Z.div n k) k + 1
      else 0.
Proof.
  intros. clear teq teq0 teq1. destruct anonymous1. subst. rewrite Z.div_mul; try lia. nia.
Defined.

Theorem fundamental_theorem_of_arithmetics (n: Z) (L: list (Z * Z)):
  1 <= n -> product_of_factors_with_powers L = n -> NoDup (map fst L) ->
  (forall x, In x (map fst L) -> prime x) -> Permutation L (map (fun x => (x, get_factor_power n x)) (prime_divisors 2 n)). 
Proof.
Admitted.