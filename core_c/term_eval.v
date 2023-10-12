Require Export terms type_system operations_term.
Local Open Scope term_scope.
Require Import List.
Import ListNotations.
Local Coercion Z.of_nat: nat >-> Z.
Notation lrval_term K := (ptr K + val_term K)%type.
Arguments ValC {_} _.
Arguments VInteger {_} _.
(*Function that evaluates ACSL terms*)
Fixpoint term_eval `{Env K} (t: term K) (en : env K)
  (rho : stack K) (m : mem K) : option (lrval_term K) :=
  match t with
  | TVar x  =>
      '(o,τ) ← rho !! x;
Some (inl (Ptr (addr_top o τ)))
| TVal v => Some v
| TRtoL t1 => v ← term_eval t1 en rho m ≫= maybe inr;
let vc := match v with
          | ValC v1 => Some v1
          | _ => None
          end
in
match vc with
| Some v1 =>
p ← maybe (VBase ∘ VPtr)  v1;
guard (ptr_alive' m p);
Some (inl p)
| _ => None
end
| TRofL t => p ← term_eval t en rho m ≫= maybe inl;
Some (inr (ValC (ptrV p)))
| TBinOp op t1 t2 =>  v1 ← term_eval t1 en rho m ≫= maybe inr;
v2 ← term_eval t2 en rho m ≫= maybe inr;
Some (inr (tval_binop en op v1 v2))

| TLoad t => a ← term_eval t en rho m  ≫= maybe (inl ∘ Ptr);
guard (mem_forced en a m);
let v :=  m !!{en} a in
match v with
| Some vc => match vc with
             | VBase(VInt _ x) => Some (inr (VInteger x))
             | _ => Some (inr (ValC vc))
             end
| None => None
end

  
| TUnOp op t => v ← term_eval t en rho m ≫= maybe inr;
Some (inr (tval_unop op v))
| TEltL t rs =>  a ← term_eval t en rho m ≫= maybe (inl ∘ Ptr);
guard (addr_strict en a);
Some (inl (Ptr (addr_elt en rs a)))
     
| TEltR t rs => v ← term_eval t en rho m ≫= maybe (inr);
let vc := match v with
         |ValC v1 => Some v1
         | _ => None
         end
in
match vc with
| Some vc' =>
v' ← vc' !!{en} rs;
Some (inr  (ValC v'))
| _ => None
end

| TBaseAddr t => v ← term_eval t en rho m ≫= maybe inr;
let vc := match v with
          | ValC v1 => Some v1
          | _ => None
          end
in
match vc with
| Some v1 => p ← maybe (VBase ∘ VPtr)  v1;
guard (ptr_alive' m p);
match p with
| Ptr a => Some (inl (Ptr (addr_top (addr_index a)(addr_type_object a))))
| _ => None
end
| _ => None
end


| TOffset t => v ← term_eval t en rho m ≫= maybe inr;
let vc := match v with
          | ValC v1 => Some v1
          | _ => None
          end
in 
match vc with
| Some v1 => p ← maybe (VBase ∘ VPtr)  v1;
guard (ptr_alive' m p);
match p with
| Ptr a => Some (inr (ValC(VBase(VInt (IntType Signed ptr_rank) ((ref_object_offset en (addr_ref_base a)) + addr_byte a)))))
| _ => None
end
| _ => None
end

| TBlckLen t => v ← term_eval t en rho m ≫= maybe inr;
let vc := match v with
          | ValC v1 => Some v1
          | _ => None
          end
in
match vc with
| Some v1 => p ← maybe (VBase ∘ VPtr)  v1;
guard (ptr_alive' m p);
match p with
| Ptr a => Some (inr (ValC(VBase (VInt (IntType Signed ptr_rank)(size_of en (addr_type_object a))))))
| _ => None
end
| _ => None
end
    
end.

Definition term_eval_right `{Env K} (t: term K) (en : env K)
  (rho : stack K) (m : mem K) : option(val_term K) :=
  term_eval t en rho m ≫= maybe inr.

Definition term_eval_left `{Env K} (t: term K) (en : env K)
  (rho : stack K) (m : mem K) : option(ptr K) :=
  term_eval t en rho m ≫= maybe inl.
