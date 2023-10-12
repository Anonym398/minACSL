Require Export operations_term.
Local Open Scope Z_scope.
Local Open Scope int_type_scope.
Local Coercion Z.of_nat: nat >-> Z.
Lemma eq_paper : 5 + divZ 4 - 2 = 1 + divZ 4 + 2.
Proof.
  lia.
Qed.
