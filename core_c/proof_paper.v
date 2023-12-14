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

(* Axiom tructest : forall a b : Z, (if decide (a=b) then 1 else 0) = 1 -> a=b. *)

(*   Print simplify_equality. *)
(* Lemma eq_paper3 : forall en t1, *)
(*     ~(eq_val en (VStruct t1 [intV{sintT} 2; intV{sintT} 1]) *)
(*         (VStruct t1 [intV{sintT} 2; intV{sintT} 5])) . *)
(* Proof. *)
(*   intros. *)
(*   intro excluded_middle. *)
(*   inversion excluded_middle. *)
(*   inversion H2. *)
(*   inversion H12. *)
(*   inversion H17. *)
(*   inversion H23. *)
(*   simplify_equality'. *)
(*   apply (tructest (int_cast (int_promote sintT ∪ int_promote sintT) 1) *)
(*            (int_cast (int_promote sintT ∪ int_promote sintT) 5)) in H25. *)
(*   apply inj int_cast in H *)
(*   discriminate H25. *)
  
(*   apply eq_ in excluded_middle. *)


