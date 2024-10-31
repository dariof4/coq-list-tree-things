From Coq Require Import Arith NArith Bool Peano.

Inductive btn :=
| lam : btn
| nod : nat -> btn -> btn -> btn.

Fixpoint btn_max (t : btn) : nat :=
  match t with
  | lam => 0
  | nod n t1 t2 => Nat.max (Nat.max n (btn_max t1)) (btn_max t2)
  end.


Inductive n_ext :=
  | inf : n_ext
  | na : nat -> n_ext.

Definition min_ext (n m : n_ext) : n_ext :=
  match n,m with
  | inf, m' => m'
  | n', inf => n'
  | na n', na m' => na (Nat.min n' m')
  end.

Fixpoint btn_min (t : btn) : n_ext :=
  match t with
  | lam => inf
  | nod n t1 t2 => min_ext (min_ext (na n) (btn_min t1)) (btn_min t2)
  end.

Definition greater_than_ext (n m : n_ext) :=
  match n, m with
  | inf, na _ => True
  | _, inf => False
  | na n', na m' => n' > m'
  end.

Notation "A >e B" := (greater_than_ext A B) (at level 70).
Definition le_ext (n m : n_ext) :=
  match n, m with
  | _, inf => True
  | inf, na _ => False
  | na n', na m' => n' <= m'
  end.
  
Notation "A <=e B" := (le_ext A B) (at level 70).
Definition lt_ext (n m : n_ext) :=
  match n, m with
  | inf, _ => False
  | na _, inf => True
  | na n', na m' => n' < m'
  end.
Notation "A <e B" := (lt_ext A B) (at level 70).


Theorem gt_lt : forall (n m : nat) , n > m <-> m < n.
Proof.
tauto.
Qed.

(*
Theorem gt_ext_swap : forall (n m : n_ext) , n >e m <-> m <e n.
Proof.
destruct n.
destruct m.
simpl greater_than_ext.
tauto.

tauto.
destruct m.
tauto.
simpl.
apply gt_lt.
Qed.
*)

Theorem not_le_ext : forall (n m : n_ext) , ~ n >e m <-> n <=e m.
Proof.
split.
destruct n.
destruct m.
simpl le_ext.
tauto.
simpl greater_than_ext.
tauto.
destruct m.
simpl le_ext.
tauto.
simpl le_ext.
simpl greater_than_ext.
apply Nat.le_ngt.

destruct n.
destruct m.
tauto.
tauto.
destruct m.
tauto.
simpl.
apply Nat.le_ngt.
Qed.


Fixpoint ordinatoPP (t : btn) : Prop :=
  match t with
  | lam => True
  | nod n t1 t2 => (btn_max t1) <= n /\ (greater_than_ext (btn_min t2) (na n)) /\ (ordinatoPP t1) /\ (ordinatoPP t2)
  end.
  
Fixpoint ins (n : nat) (t : btn) : btn :=
  match t with
  | lam => nod n lam lam
  | nod m t1 t2 => if Nat.leb n m then nod m (ins n t1) t2 else nod m t1 (ins n t2)
  end.
 
 
Lemma le_max : forall (n m o : nat) , Nat.max m o <= n <-> m <= n /\ o <= n.
Proof.
intro n.
intro m.
intro o.
split.
intro h.
split.
rewrite (Nat.le_max_l m o).
apply h.
rewrite (Nat.le_max_r m o).
apply h.

intro h.
destruct h.
destruct (Nat.max_dec m o).
rewrite e.
exact H.
rewrite e.
exact H0.
Qed.

  
Lemma le_bmax : forall (n m : nat) (t : btn) , m <= n /\ btn_max t <= n -> btn_max (ins m t) <= n.
Proof.
intro n.
intro m.
induction t.
intro h.
simpl.
rewrite Nat.max_0_r.
rewrite Nat.max_0_r.
destruct h.
apply H.

intro h.
simpl ins.
destruct h.
simpl btn_max in H0.
apply le_max in H0.
destruct H0 as [H0 H2].
apply le_max in H0.
destruct H0 as [H0 H1].
destruct (m <=? n0) eqn:hn.
simpl btn_max.
apply le_max.
split.
apply le_max.
split.
exact H0.
apply IHt1.
split.
exact H.
exact H1.
exact H2.

simpl btn_max.
apply le_max.
split.
apply le_max.
split.
exact H0.
exact H1.
apply IHt2.
split.
exact H.
exact H2.
Qed.

Lemma min_ext_dec : forall (n m : n_ext) , {min_ext n m = n} + {min_ext n m = m}.
Proof.
destruct n.
destruct m.
simpl min_ext.
tauto.

simpl min_ext.
tauto.
destruct m.
simpl min_ext.
tauto.
simpl min_ext.
destruct (Nat.min_dec n n0).
rewrite e.
tauto.
rewrite e.
tauto.
Qed.

Lemma min_ext_case : forall (n m : n_ext) (P : n_ext -> Type) , P n -> P m -> P (min_ext n m).
Proof.
destruct n.

simpl min_ext.
tauto.

destruct m.
simpl min_ext.
tauto.
destruct (min_ext_dec (na n) (na n0)).
rewrite e.
tauto.
rewrite e.
tauto.
Qed.

Lemma le_min_ext : forall (n m o : n_ext) , min_ext m o >e n <-> m >e n /\ o >e n.
Proof.
intros n m o.
split.

intro h.
split.

destruct (min_ext_dec m o) eqn:hello.
Admitted.


Arguments min_ext : simpl never.
Lemma gee_bmin : forall (n m : nat) (t : btn) , m > n /\ btn_min t >e (na n) -> btn_min (ins m t) >e (na n).
Proof.
intros n m.
induction t.
intro h.
destruct h.
simpl ins.
unfold btn_min.
simpl min_ext.
simpl greater_than_ext.
exact H.

intro h.
destruct h.
simpl in H0.
apply le_min_ext in H0.
destruct H0 as [H0 H2].
apply le_min_ext in H0.
destruct H0 as [H0 H1].

simpl ins.
destruct (m <=? n0) eqn:hn.
apply Nat.leb_le in hn.

simpl btn_min.
apply le_min_ext.
split.
apply le_min_ext.
split.
rewrite gt_lt in H.
apply (Nat.lt_le_trans n m n0 H) in hn.
rewrite <- gt_lt in hn.
simpl.
exact hn.
apply IHt1.
split.
exact H.
exact H1.
exact H2.

simpl btn_min.
apply le_min_ext.
split.
apply le_min_ext.
split.
exact H0.
exact H1.
apply IHt2.
split.
exact H.
exact H2.

Qed.


Theorem ordered : forall (n : nat) (t : btn) , ordinatoPP(t) -> ordinatoPP(ins n t).
Proof.
intro n.
induction t.
intro h.
simpl ins.
unfold ordinatoPP.
simpl btn_max.
simpl btn_min.
simpl greater_than_ext.
split.
exact (le_0_n n).
tauto.

intro h.
simpl ins.
destruct h.
destruct H0 as [H0 H1].
destruct H1 as [H1 H2].
destruct (n <=? n0) eqn:hn.
apply Nat.leb_le in hn.

simpl ordinatoPP.
split.
apply le_bmax.
split.
exact hn.
exact H.
split.

exact H0.
split.
apply IHt1.
exact H1.
exact H2.

simpl ordinatoPP.
split.
exact H.
split.
apply Nat.leb_nle in hn.
apply not_le in hn.

apply gee_bmin.
split.
exact hn.
exact H0.
split.
exact H1.
exact (IHt2 H2).
Qed.

