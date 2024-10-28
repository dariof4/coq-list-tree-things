From Coq Require Import List Arith ZArith.
Import ListNotations.


Variable A : Type.

Fixpoint len {B : Type} (x : list B) : nat :=
    match x with
    | [] => 0
    | (x :: xs) => len xs + 1
    end.

Fixpoint mapp {B : Type} (x y : list B) : list B :=
  match x with
  | [] => y
  | x::xs => x :: mapp xs y
  end.
  

Fixpoint mrev {B : Type} (x : list B) : list B :=
  match x with
  | [] => []
  | x :: xs => mapp (mrev xs) [x]
  end.


Theorem mapp_empty : forall (B : Type) (x : list B) , mapp x [] = x.
Proof.

induction x.
simpl; reflexivity.
simpl; rewrite IHx; reflexivity.
Qed.

Theorem mapp_app : forall (B : Type) (l1 l2 l3 : list B) , mapp ( mapp l1 l2) l3 = mapp l1 (mapp l2 l3).
Proof.
induction l1.
intro l2; intro l3.
simpl; reflexivity.
intro l2; intro l3.
simpl; rewrite IHl1; reflexivity.
Qed.

Theorem rev_mapp : forall (B : Type) (l1 l2 : list B) , mrev (mapp l1 l2) = mapp (mrev l2) (mrev l1).
Proof.
induction l1; intro l2.
simpl; rewrite mapp_empty; reflexivity.
simpl; rewrite IHl1; rewrite mapp_app; reflexivity.
Qed.

Theorem len_app : forall (B : Type) (l1 l2 : list B) , len (mapp l1 l2) = len l1 + len l2.
Proof.
induction l1; intro l2.
simpl; reflexivity.
simpl; rewrite IHl1; ring_simplify; reflexivity.
Qed.

Theorem len_mrev : forall (B : Type) (l1 : list B) , len (mrev l1) = len l1.
Proof.
induction l1.
unfold mrev; reflexivity.
simpl mrev; simpl mrev; rewrite len_app; simpl len; rewrite IHl1; reflexivity.
Qed.

Fixpoint belList (x : list nat) (y : nat) : bool :=
  match x with
  | [] => false
  | x :: xs => if Nat.eqb x y then true else belList xs y
  end.
  
Theorem belList_app : forall (l1 l2 : list nat) (b : nat) , belList (mapp l1 l2) b = orb (belList l1 b) (belList l2 b).
Proof.
induction l1 ; intro l2 ; intro b.
simpl mapp; simpl belList; simpl orb; reflexivity.
simpl mapp; destruct (Nat.eqb a b) eqn:eqab.
simpl belList; rewrite eqab; simpl orb; reflexivity.
simpl belList; rewrite eqab; rewrite IHl1; reflexivity.
Qed.


Inductive bt : Type :=
  | lmd : bt
  | node : bt -> bt -> bt.
  
Fixpoint size (t : bt) : nat :=
  match t with
  | lmd => 0
  | node t1 t2 => size t1 + size t2 + 1
  end.
  
Fixpoint height (t : bt) : Z :=
  match t with
  | lmd => -1
  | node t1 t2 => Z.max (height t1) (height t2) + 1
  end.


Theorem hei_siz : forall (t : bt) , Z.le (height t) (Z.of_nat (size t)).
Proof.
induction t.
simpl height; simpl size; simpl Z.of_nat; auto with zarith.
simpl height; simpl size; destruct (Z.compare (height t1) (height t2)) eqn:ht.
unfold Z.max.
rewrite ht.
assert (ht1 : size t1 <= size t1 + size t2).
exact (Nat.le_add_r (size t1) (size t2)).
apply inj_le in ht1.
apply (Z.le_trans (height t1) (Z.of_nat (size t1)) (Z.of_nat (size t1 + size t2))) in ht1.
rewrite (Nat2Z.inj_add (size t1 + size t2) 1).
simpl Z.of_nat.
assert (h1 : Z.le 1 1).
reflexivity.
apply Z.add_le_mono.
exact ht1.
exact h1.
exact IHt1.

unfold Z.max.
rewrite ht.
assert (ht1 : size t2 <= size t2 + size t1).
exact (Nat.le_add_r (size t2) (size t1)).
apply inj_le in ht1.
apply (Z.le_trans (height t2) (Z.of_nat (size t2)) (Z.of_nat (size t2 + size t1))) in ht1.
rewrite (Nat2Z.inj_add (size t1 + size t2) 1).
simpl Z.of_nat.
assert (h1 : Z.le 1 1).
reflexivity.
apply Z.add_le_mono.
rewrite Nat.add_comm.
exact ht1.
exact h1.
exact IHt2.

unfold Z.max.
rewrite ht.
assert (ht1 : size t1 <= size t1 + size t2).
exact (Nat.le_add_r (size t1) (size t2)).
apply inj_le in ht1.
apply (Z.le_trans (height t1) (Z.of_nat (size t1)) (Z.of_nat (size t1 + size t2))) in ht1.
rewrite (Nat2Z.inj_add (size t1 + size t2) 1).
simpl Z.of_nat.
assert (h1 : Z.le 1 1).
reflexivity.
apply Z.add_le_mono.
exact ht1.
exact h1.
exact IHt1.

Qed.
