Require Export memory_map values.
Require Import pointer_casts.
Require Export expressions type_system.
Require Import Arith.
Local Open Scope ctype_scope.
Local Open Scope Z_scope.
Local Open Scope int_type_scope.
Local Coercion Z.of_nat: nat >-> Z.
Print base_val_flatten.
Section operations_definitions2.
  Context `{Env K}.

  Inductive val_term (K : iType) : iType :=
  | ValC : val K -> val_term K
  | VInteger : Z -> val_term K.

  Arguments ValC {_} _.
  Arguments VInteger {_} _.
  
  (* Besoin de mettre le type en argument pour derefnull !!*)
  Parameter derefNull : ptr K -> type K -> val_term K.

  (* Divide by zero : return non specified Z *)
  Parameter divZ : Z -> Z.

  Inductive tbinop :=
  | TArithOp : arithop -> tbinop
  | TShiftOp : shiftop -> tbinop
  | TBitOp : bitop -> tbinop.

  Definition tbin_to_bin (op : tbinop):=
    match op with
    | TArithOp opa => ArithOp opa
    | TShiftOp ops => ShiftOp ops
    | TBitOp opb => BitOp opb
    end.

  (* Arithop for terms *)
  Definition arithopZ (op : arithop)(x y : Z) : Z :=
    match op, y with
    | DivOp, 0 => divZ x
    | DivOp, _ => x/y
    | PlusOp, _=> x+y
    | MinusOp, _ => x-y
    | MultOp, _ => x*y
    | ModOp, _ => x mod y
    end.

  Definition tval_binop (en : env K) (op : tbinop) (vt1 vt2 : val_term K): val_term K :=
    match vt1,vt2,op with
    | VInteger n1, VInteger n2, TArithOp aop => VInteger (arithopZ aop n1 n2)
    | ValC v1, ValC v2, _ => ValC (val_binop en (tbin_to_bin op) v1 v2)
    | _,_,_ => vt1
    end.

  
  Inductive tunop :=
  | TNegOp : tunop
  | TComplOp : tunop.

  Definition tun_to_un (op : tunop):=
    match op with
    | TNegOp  => NegOp 
    | TComplOp  => ComplOp 
    end.

  Definition tval_unop (op : tunop) (v : val_term K) : val_term K :=
    match v, op with
    | VInteger n, TNegOp => VInteger (-n)
    | ValC v,_ => ValC(val_unop (tun_to_un op) v)
    | _,_ => v
    end.
  
  (* New arithop function which takes the divZ constructor when there is a division by zero *)
  Definition new_arithop (op : arithop)(x y : Z) (τi1 τi2 : int_type K) : Z  :=
    match op, sign τi1, y with
    | DivOp, _, 0 => divZ x
    | _, _, _ => int_arithop op x τi1 y τi2
    end.

  (* New operation on int which take divide by zero in account *)
  Definition new_int_binop (op : binop) (x1 x2 : Z) (τi1 τi2 : int_type K) : Z :=
    match op with
    | ArithOp op => new_arithop op x1 x2 τi1 τi2
    | _ => int_binop op x1 τi1 x2 τi2
    end.
  (* New operation on base_vale which take divide by zero in account *)
  Definition new_base_val_binop (en : env K) (op : binop) (v1 v2 : base_val K): base_val K :=
    match v1, v2 with
    | VInt τi1 x1, VInt τi2 x2 => VInt (int_binop_type_of op τi1 τi2) (new_int_binop op x1 x2 τi1 τi2)
    |_,_ => base_val_binop en op v1 v2
    end.


  (* New operation on base_vale which take divide by zero in account *)
  Definition new_val_binop (en : env K) (op : binop) (v1 v2 : val K) : val K :=
    match v1, v2 with
    | VBase vb1, VBase vb2 => VBase (new_base_val_binop en op vb1 vb2)
    | _,_ => val_binop en op v1 v2
    end.

  Inductive comparable : val K -> Prop :=
  | cmp_base : forall b, comparable (VBase b)
  | cmp_struct : forall t l, comparable_list l -> comparable (VStruct t l)
  | cmp_union : forall v i t, comparable v -> comparable (VUnion t i v)
  | cmp_unionall : forall l t, comparable_list l -> comparable (VUnionAll t l)
  with
    comparable_list : list (val K) -> Prop :=
  | cmp_nil : comparable_list []
  | cmp_cons : forall v l, comparable v -> comparable_list l -> comparable_list (v::l).
 


   (* Comparison of values *)
  Inductive eq_val : env K -> val K -> val K -> Prop :=
  | eq_base : forall(en : env K) (vb1 vb2 : base_val K),
      new_base_val_binop en (CompOp EqOp) vb1 vb2 = VInt sintT 1 ->
      eq_val en (VBase vb1) (VBase vb2)
  | eq_struct : forall (en : env K)
                      (lval1 lval2 : list (val K)) (tag1 tag2 : tag),
      eq_list  en lval1 lval2 
      -> eq_val en (VStruct tag1 lval1) (VStruct tag2 lval2)
  | eq_union1 : forall (en : env K)(v1 v2 vu1 vu2 : val K)(tag1 tag2 : tag)(n1 n2 : nat),
      v1 = VUnion tag1 n1 vu1 ->
      v2 = VUnion tag2 n2 vu2  ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2
  | eq_union2 : forall (en : env K) (v1 v2 vu1 : val K)
                       (tag1 tag2 : tag)(n1 : nat) (lval2 : list (val K)),
      v1 = VUnion tag1 n1 vu1 ->
      v2 = VUnionAll tag2 lval2 ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2
  | eq_union3 : forall (en : env K) (v1 v2 vu2 : val K)
                       (tag1 tag2 : tag)(n2 : nat) (lval1 : list (val K)),
      v2 = VUnion tag2 n2 vu2 ->
      v1 = VUnionAll tag1 lval1 ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2
  | eq_union4 : forall (en : env K) (v1 v2 : val K)
                       (tag1 tag2 : tag) (lval1 lval2 : list (val K)),
      v2 = VUnionAll tag2 lval2 ->
      v1 = VUnionAll tag1 lval1 ->
      val_flatten en v1 = val_flatten en v2 ->
      eq_val en v1 v2
  (* Comparison of list of values *)
  with eq_list : env K -> list (val K) -> list (val K) -> Prop :=
  | eq_list_empty : forall (en : env K) ,
      eq_list  en [] []
  | eq_list_cons : forall (en : env K) (v1 v2 : val K) (lvq1 lvq2: list (val K)),
      eq_val en v1 v2 ->
      eq_list en lvq1 lvq2 ->
      eq_list en (v1::lvq1) (v2::lvq2).
  
  (* Comparison of values *)
  Inductive comp_val : compop -> env K -> val K -> val K -> Prop :=
  | eq_value : forall (en : env K)(v1 v2 : val K),
      eq_val en v1 v2 -> comp_val EqOp en v1 v2
  | comp_other : forall (op : compop)(en : env K) (v1 v2 : val K),
      new_val_binop en (CompOp op) v1 v2 = VBase (VInt sintT 1) ->
      comp_val op en v1 v2.
  Print compop.
  Inductive comp_int : compop -> Z -> Z -> Prop :=
  | eq_int : forall (x: Z) ,comp_int EqOp x x
  | lt_int : forall (x y : Z), x < y -> comp_int LtOp x y
  | le_int : forall (x y : Z), x <= y -> comp_int LtOp x y.
  

  Inductive comp_valt : compop -> env K -> val_term K -> val_term K -> Prop :=
  | comp_valc : forall (en : env K)(v1 v2 : val K)(op : compop),
      comp_val op en v1 v2 -> comp_valt op en (ValC v1) (ValC v2)
  | comp_valInt : forall (en : env K)(x y : Z)(op : compop),
      comp_int op x y -> comp_valt op en (VInteger x) (VInteger y).

  (* Assume that equality furnished in CH2O is symmetric*)
  Axiom eq_val_sym : forall(v1 v2 : base_val K)(en : env K),
      new_base_val_binop en (CompOp EqOp) v1 v2 = (intV{sintT} 1)%B ->
      new_base_val_binop en (CompOp EqOp) v2 v1 = (intV{sintT} 1)%B.
  
  (* Assume that equality furnished in CH2O is reflexive*)
  Axiom eq_val_refl : forall(v : base_val K)(en : env K),
      new_base_val_binop en (CompOp EqOp) v v = (intV{sintT} 1)%B.
  
  (* Assume that equality furnished in CH2O is transitive *)
  Axiom eq_val_trans : forall (v1 v2 v3 : base_val K)(en : env K),
      new_base_val_binop en (CompOp EqOp) v1 v2 = (intV{sintT} 1)%B ->
      new_base_val_binop en (CompOp EqOp) v2 v3 = (intV{sintT} 1)%B ->
      new_base_val_binop en (CompOp EqOp) v1 v3 = (intV{sintT} 1)%B.
  Section val_ind.


    Context (P : val K → Prop). (* The inductive property *)
  Context (HBase : ∀ b, P (VBase b)). (* VBase case *)
  Context (HStructNil :∀t, P (VStruct t [])). (* VStruct [] case *)
  Context (HStructCons : ∀ v l t t', P v → P (VStruct t l) → P (VStruct t' (v::l))).
    (* VStruct (v::l) case *)
  Context (HArrayNil :∀ t, P (VArray t [])). (* VArray [] case *)
  Context (HArrayCons : ∀ v l t, P v → P (VArray t l) → P (VArray t (v::l))).
  (* VStruct (v::l) case *)
  Context (HUnion :∀ t i v, P (VUnion t i v)).
  Context (HUnionAllNil : ∀ t, P (VUnionAll t [])).
  Context (HUnionAllCons : ∀ v l t t', P v -> P (VUnionAll t l) -> P(VUnionAll t' (v::l))).
  
  Fixpoint val_ind' v :=
    match v as v' return P v' with
    | VBase v => HBase v (* If v is a base, apply HBase *)
    | VStruct t l =>
        (* If it is a struct, do a recusion on the list
           We need to define the list function internally
           and not as a joined recursion else termination checker
           will complain *)
        let fix val_list_ind l := match l as l' return P (VStruct t l') with
                                  | [] => HStructNil t
                                  | v::l => HStructCons v l t _ (val_ind' v) (val_list_ind l)
                                  end in val_list_ind l
    | VArray t l =>
        let fix val_list_ind l := match l as l' return P (VArray t l') with
                                  | [] => HArrayNil t
                                  | v::l => HArrayCons v l t (val_ind' v) (val_list_ind l)
                                  end in val_list_ind l
    | VUnion t i v => HUnion t i v
    | VUnionAll t l =>
        let fix val_list_ind l := match l as l' return P (VUnionAll t l') with
                                  | [] => HUnionAllNil t
                                  | v::l => HUnionAllCons v l t _ (val_ind' v) (val_list_ind l)
                                  end in val_list_ind l
    end.
  End val_ind.

  Lemma eq_val_reflexive v en : comparable v -> eq_val en v v.
    Proof.
      apply (val_ind'(λ v, comparable v → eq_val en v v)).
      -  constructor. apply eq_val_refl.
      - constructor. constructor.
      - intros v' l t t' IH IH1 Hcmp. constructor.
        inversion Hcmp.

        inversion H1. constructor.
        + apply IH. assumption.
        + specialize (IH1 (cmp_struct t l H6)). inversion IH1. assumption.
          discriminate. discriminate. discriminate. discriminate.
      - intros. inversion H0.
      - intros ? ? ? ? IH Harray. inversion Harray.
      - intros. apply (eq_union1 en (VUnion t i v0) (VUnion t i v0) v0 v0 t t i i). reflexivity.
        reflexivity. reflexivity.
      - intros. apply (eq_union4 en (VUnionAll t []) (VUnionAll t []) t t [] []). reflexivity.
        reflexivity. reflexivity.
      - intros.
        apply (eq_union4 en (VUnionAll t' (v0 :: l)) (VUnionAll t' (v0 :: l)) t' t' (v0::l)(v0::l)).
        reflexivity.
        reflexivity. reflexivity.
    Qed.
    
  Scheme eq_val_rec := Induction for eq_val Sort Prop
      with eq_list_rec := Induction for eq_list Sort Prop.


  Lemma eq_val_symmetric : forall(v1 v2 : val K)(en : env K),
      eq_val en v1 v2 -> eq_val en v2 v1.
  Proof.
    intros vl vr en.
    apply (eq_val_rec
             (λ en vl vr (_:eq_val en vl vr), eq_val en vr vl)
             (λ en ll lr (_: eq_list en ll lr), eq_list en lr ll)).
    - intros. apply (eq_base en0 vb2 vb1). apply (eq_val_sym vb1 vb2 en0).
      assumption.
    - intros.  apply (eq_struct en0 lval2 lval1 tag2 tag1). assumption.
    - intros. apply (eq_union1 en0 v2 v1 vu2 vu1 tag2 tag1 n2 n1).
      assumption. assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_union3 en0 v2 v1 vu1 tag2 tag1 n1 lval2).
      assumption. assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_union2 en0 v2 v1 vu2 tag2 tag1 n2 lval1).
      assumption. assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_union4 en0 v2 v1 tag2 tag1 lval2 lval1). assumption.
      assumption. rewrite <- e1. reflexivity.
    - intros. apply (eq_list_empty en0).
    - intros. apply (eq_list_cons).
      assumption. assumption.
  Qed.
  Print eq_union1.
  
  Lemma eq_val_transitive : forall (v1 v2 v3 : val K) (en : env K),
      eq_val en v1 v2 -> eq_val en v2 v3 -> eq_val en v1 v3. 
  Proof.
    intros v1 v2 v3 en H12.
    
    apply (eq_val_rec
             (λ en v1 v2 (_ : eq_val en v1 v2), ∀ v3, eq_val en v2 v3 → eq_val en v1 v3)
             (λ en l1 l2 (_ : eq_list en l1 l2), ∀ l3, eq_list en l2 l3 → eq_list en l1 l3)).
    - intros en0 vb1 vb2 Hvb12 v3' H23. inversion H23. constructor.
      apply (eq_val_trans vb1 vb2 vb3 en0). assumption. assumption.
      discriminate. discriminate. discriminate. discriminate.
    - intros en0 lval1 lval2 tag1 tag2 Hl12 IHl v3' H23. inversion H23.
      constructor. apply IHl. assumption. discriminate. discriminate. discriminate. discriminate.
      
    - intros en0 v1' v2' vu1 vu2 tag1 tag2 n1 n2 H1 H2 H12' v3' H23.
      inversion H23.
      rewrite -> H2 in H4. discriminate. rewrite -> H2 in H4. discriminate.
      apply (eq_union1 en0 v1' v3' vu1 vu3 tag1 tag3 n1 n3).
      assumption. assumption. rewrite -> H4 in H12'. assumption.
      apply (eq_union2 en0 v1' v3' vu1 tag1 tag3 n1 lval2). assumption. assumption.
      rewrite -> H4 in H12'. assumption.
      rewrite -> H2 in H3. discriminate.
      rewrite -> H2 in H3. discriminate.
    - intros en0 v1' v2' vu1 tag1 tag2 n1 lval2 H1 H2 H12' v3' H23. inversion H23. 
      rewrite <- H4 in H2. discriminate.
      rewrite <- H4 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      apply (eq_union1 en0 v1' v3' vu1 vu2 tag1 tag3 n1 n2).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      apply (eq_union2 en0 v1' v3' vu1 tag1 tag3 n1 lval0). assumption. assumption.
      rewrite <- H12' in H4. assumption.
    - intros en0 v1' v2' vu2 tag1 tag2 n2 lval1 H2 H1 H12' v3' H23. inversion H23.
      rewrite <- H4 in H2. discriminate.
      rewrite <- H4 in H2. discriminate.
      apply (eq_union3 en0 v1' v3' vu0 tag1 tag3 n0 lval1).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      apply (eq_union4 en0 v1' v3' tag1 tag3 lval1 lval2).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      rewrite -> H2 in H3. discriminate.
      rewrite -> H2 in H3. discriminate.
    - intros en0 v1' v2' tag1 tag2 lval1 lval2 H2 H1 H12' v3' H23. inversion H23.
      rewrite <- H4 in H2. discriminate.
      rewrite <- H4 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      rewrite -> H0 in H2. discriminate.
      apply (eq_union3 en0 v1' v3' vu2 tag1 tag3 n2 lval1).
      assumption. assumption. rewrite <- H12' in H4. assumption.
      apply (eq_union4 en0 v1' v3' tag1 tag3 lval1 lval3).
      assumption. assumption. rewrite <- H12' in H4. assumption.
    - intros en0 l3 Hl. inversion Hl. constructor.
    - intros en0 v0 v4 lv1 lv2 H04 IH Hl12 IHl l3 Hv41213.
      inversion Hv41213. constructor.
      apply IH. assumption.
      apply IHl. assumption.
    - exact H12.
  Qed.
End operations_definitions2.
