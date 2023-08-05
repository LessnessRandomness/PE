Require Import VST.floyd.proofauto.
Open Scope Z.

Require Import test.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition get_counter_spec: ident * funspec :=
DECLARE _get_counter
  WITH gv: globals, c: Z
  PRE []
    PROP ()
    PARAMS ()
    SEP (data_at Ews tint (Vint (Int.repr c)) (gv _COUNTER))
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (c + 1)))
    SEP (data_at Ews tint (Vint (Int.repr (c + 1))) (gv _COUNTER)).


Definition Gprog := [get_counter_spec].

Lemma get_counter_proof: semax_body Vprog Gprog f_get_counter get_counter_spec.
Proof.
  start_function. Fail forward.
Admitted.