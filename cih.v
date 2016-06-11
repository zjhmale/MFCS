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

