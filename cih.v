Theorem example1 : forall a b: Prop, a /\ b -> b /\ a.
  intros a b H.
  split.
  destruct H as [H1 H2].
  exact H2.
  destruct H as [H1 H2].
  exact H1.
Qed.

Theorem example2 : forall A B, A \/ B -> B \/ A.
  intros A B H.
  destruct H as [H1 | H2].
  right.
  exact H1.
  left.
  exact H2.
Qed.

Check le_n.
Check le_S.

Theorem example3 : 3 <= 5.      (* dependent type here! *)
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Require Export Arith.

Check le_trans.

Theorem example4 : forall x y, x <= 10 -> 10 <= y -> x <= y.
  intros x y x10 y10.
  apply le_trans with (m := 10).
  exact x10.                    (* can also use assuption *)
  exact y10.
Qed.


Theorem example5 : forall x y, (x + y) * (x + y) = x * x + 2 * x * y + y * y.
  intros x y.
  SearchRewrite (_ * (_ + _)).
  rewrite mult_plus_distr_l.
  SearchRewrite ((_ + _) * _).
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_r.
  SearchRewrite (_ + (_ + _)).
  rewrite plus_assoc.
  rewrite <- plus_assoc with (n := x * x).
  SearchPattern (?x * ?y = ?y * ?x).
  rewrite mult_comm with (n := y) (m := x).
  SearchRewrite (S _ * _).
  pattern (x * y) at 1; rewrite <- mult_1_l.
  rewrite <- mult_succ_l with (m := (x * y)). (* or can simply use rewrite <- mult_succ_l *)
  SearchRewrite (_ * (_ * _)).
  rewrite -> mult_assoc with (n := 2) (m := x) (p := y). (* or can simply use rewrite mult_assoc *)
  reflexivity.
Qed.

Require Import Omega.

Theorem omega_example : forall f x y, 0 < x -> 0 < f x -> 3 * f x <= 2 * y -> f x <= y.
  intros; omega.
Qed.

Fixpoint sum_n n :=
  match n with
    O => O
  | S p => p + sum_n p
end.
                    
Check sum_n.

Theorem sum_n_p : forall n, 2 * sum_n n + n = n * n.
  induction n.                  (* 归纳证明 *)
  reflexivity.
  assert (SnSn : S n * S n = n * n + 2 * n + 1).
  ring.
  rewrite -> SnSn.
  rewrite <- IHn.
  simpl.                        (* replace with the sum_n symbolic computation *)
  ring.
Qed.

Require Import Bool.

Fixpoint evenb n :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p
end.

Check evenb.

Theorem evenb_p : forall n, evenb n = true -> exists x, n = 2 * x.
  assert (Main : forall n, (evenb n = true -> exists x, n = 2 * x) /\ (evenb (S n) = true -> exists x, S n = 2 * x)).
  induction n.
  split.                        (* split conjunction *)
  exists O; ring.
  simpl.
  intros H.
  discriminate.
  split.
  destruct IHn as [_ IHn'].
  exact IHn'.
  simpl.
  intros H.
  destruct IHn as [IHn' _].
  assert (H' : exists x, n = 2 * x).
  apply IHn'.
  exact H.
  destruct H' as [x q].
  exists (x + 1).
  rewrite -> q.
  ring.
  intros n ev.
  destruct (Main n) as [H _].
  apply H.
  exact ev.
Qed.

Require Import List.
Print beq_nat.

Fixpoint leb (n : nat) : nat -> bool :=
  match n with
    | O => fun _ : nat => true
    | S n' => fun m : nat => match m with
                         | O => false
                         | S m' => leb n' m'
                       end
  end.

Eval compute in leb 3 3.
Eval compute in leb 3 6.
Eval compute in leb 6 3.

Fixpoint insert n l :=
  match l with
    nil => n :: nil
  | h :: t => if leb n h then n :: l else h :: insert n t
end.

Fixpoint count n l :=
  match l with
    nil => 0
  | h :: t => let r := count n t in if beq_nat n h then 1 + r else r
end.

(* induction nat O | S _ *)
(* induction list nil | _ :: _ *)

Theorem insert_incr : forall n l, count n (insert n l) = 1 + count n l.
  intros n l.
  induction l.
  simpl.
  SearchAbout beq_nat.
  rewrite <- beq_nat_refl.
  reflexivity.                  (* or ring *)
  simpl.
  case (leb n a).
  simpl.
  rewrite <- beq_nat_refl.
  reflexivity.
  simpl.
  case (beq_nat n a).
  rewrite IHl; reflexivity.
  rewrite IHl; reflexivity.
Qed.

(* define new datatypes *)

Inductive bin : Type :=          (* binary tree *)
  | L : bin                     (* leaf *)
  | N : bin -> bin -> bin.        (* node *)

Check N L (N L L).              (* nonsense but match the specification *)

Definition is_single_node (t : bin) : bool :=
  match t with
    | N L L => false
    | _ => true
  end.

Fixpoint flatten_aux (t1 t2 : bin) : bin :=
  match t1 with
    | L => N L t2
    | N t1' t2' => flatten_aux t1' (flatten_aux t2' t2)
  end.

Fixpoint flatten (t : bin) : bin :=
  match t with
    | L => L
    | N t1 t2 => flatten_aux t1 (flatten t2)
  end.

Fixpoint size (t : bin) : nat :=
  match t with
   | L => 1
   | N t1 t2 => 1 + size t1 + size t2
  end.

Eval compute in flatten_aux (N L L) L.
Eval compute in size (N (N L L) L).
Eval compute in size (N L L).

(* prove properties of functions *)

Theorem example_size : forall t, is_single_node t = false -> size t = 3.
  intro t.
  destruct t.                   (* the tactic destruct is quite similiar to induction but one is for hypothesis and one is for conclution *)
  simpl.
  intro H.
  discriminate H.               (* just got a contradiction assume true = false *)
  destruct t1.
  destruct t2.
  simpl.
  reflexivity.                  (* or use auto instead *)
  simpl.
  intro H.
  discriminate H.
  simpl.
  intro H; discriminate.
Qed.

Theorem flatten_aux_size : forall t1 t2, size (flatten_aux t1 t2) = size t1 + size t2 + 1.
  induction t1.
  intro t2.
  simpl.
  ring.
  intro t2.
  simpl.
  rewrite IHt1_1.
  rewrite IHt1_2.
  ring.
Qed.

Theorem not_subterm_self_1 : forall x y, ~ x = N x y.
  induction x.
  intro y.
  intro H.
  discriminate.
  intro y.
  intro abs.
  injection abs.
  intros h2 h1.
  assert (IHx1' : x1 <> N x1 x2).
  apply IHx1.
  case IHx1'.
  exact h1.
Qed.

Print nat.

Fixpoint nat_fact (n : nat) : nat :=
  match n with
    | O => 1
    | S p => S p * nat_fact p
  end.

Fixpoint fib (n : nat) : nat :=
  match n with
    | O => 0
    | S q => match q with
              | O => 1
              | S p => fib p + fib q
            end
  end.

Inductive even : nat -> Prop :=       (* even x is a proposition *)
  | evenO : even O
  | evenS : forall x : nat , even x -> even (S (S x)).

(*
judgement and inference rule

             n even
 ——————    ————————————
 0 even    S(S(n)) even

       ——————
       0 even
    ————————————
    S(S(0)) even
 ——————————————————
 S(S(S(S(0)))) even
*)

Theorem even_mult : forall x, even x -> exists y, x = 2 * y.
  intros x H.
  elim H.                       (* elim and induction are almose the same here *)
  exists 0.
  reflexivity.
  intros xO HevenO IHx.
  destruct IHx as [y Heq].
  rewrite Heq.
  exists (S y).
  ring.
Qed.

Theorem not_even_1 : ~even 1.
  intros even1.
  inversion even1.
Qed.

Theorem even_inv : forall x, even (S (S x)) -> even x. (* inversion of evenS *)
  intros x H.
  inversion H.
  exact H1.
Qed.

(*
Inductive properties can be used to express very complex notions. For instance, the semantics of a programming language can be defined as an inductive definition, using dozens of constructors, each one describing a an elementary step of computation.
*)
