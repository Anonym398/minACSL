Require Export operations_term.
Local Open Scope Z_scope.
Local Coercion Z.of_nat: nat >-> Z.
Arguments ValC {_} _.
Arguments VInteger {_} _.
Context `{Env K}.

Lemma eq_paper : 5 + divZ 4 - 2 = 1 + divZ 4 + 2.
Proof.
  lia.
Qed.

  
Lemma eq_paper2 : forall en, ~(comp_valt EqOp en (VInteger 8) (VInteger 0))/\
                                         (comp_valt EqOp en (VInteger (divZ 4)) (VInteger (divZ 4))).
  Proof.
    intros.
    split.
    intro excluded_middle.
    inversion excluded_middle.
    inversion H4.
    apply comp_valInt.
    apply eq_int.
  Qed.
