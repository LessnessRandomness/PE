Require Import VST.floyd.proofauto.
Require Import test.
Open Scope Z.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition get_counter_spec: ident * funspec :=
DECLARE _get_counter
  WITH gv: globals, c: Z
  PRE []
    PROP (Int.min_signed <= c /\ c + 1 <= Int.max_signed)
    (* NOT enough: try it!
    PROP (Int.min_signed <= c + 1 <= Int.max_signed) *)
    PARAMS ()
    GLOBALS (gv)
    SEP (data_at Ews tint (Vint (Int.repr c)) (gv _COUNTER))
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (c + 1)))
    SEP (data_at Ews tint (Vint (Int.repr (c + 1))) (gv _COUNTER)).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE [] main_pre prog tt gv
  POST [ tint ]
     PROP()
     RETURN (Vint (Int.repr 0))
     SEP(TT).


Definition Gprog := [get_counter_spec; main_spec].

Lemma get_counter_proof: semax_body Vprog Gprog f_get_counter get_counter_spec.
Proof.
  start_function.
  repeat forward.
Qed.

Lemma body_main: semax_body Vprog Gprog f_main main_spec.
Proof.
  start_function.
  repeat forward.
Qed.
