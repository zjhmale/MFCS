Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[]" := nil.
(* notice the white spaces *)
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint append (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (append t l2)
  end.

(* a macro like pre-compiled process *)
Notation "x ++ y" := (append x y) (at level 60, right associativity).

Definition hd (default : nat) (l : natlist) : nat := match l with
  | nil => default
  | h :: t => h
end.

Definition tl (l : natlist) : natlist := match l with
  | nil => nil
  | h :: t => t
end.

Theorem nil_app : forall l:natlist, [] ++ l = l.
Proof. reflexivity. Qed.

Theorem length_pred : forall l:natlist, pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l'].
  reflexivity.
  reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1.
  reflexivity.
  simpl.
  rewrite -> IHl1.              (* rewrite left use right *)
  reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist, length (l1 ++ l2) = length l1 + length l2.

Proof.
  intros l1 l2.
  induction l1.
  reflexivity.
  simpl.
  rewrite -> IHl1.
  reflexivity.
Qed.

Definition plus3 := plus 3.

Check plus3.

Theorem unfold_example : forall m n, 3 + n = m -> plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem eq_add_S : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m eq.
  inversion eq.
  reflexivity.
Qed.

(* polymorphism *)

Theorem trans_eq : forall {X: Type} (n m o : X), n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  exact eq2.                    (* or rewrite -> eq2. reflexivity. *)
Qed.

Theorem trans_eq_example : forall (a b c d e f : nat), [a;b] = [c;d] -> [c;d] = [e;f] -> [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m := [c;d]).
  exact eq1.                    (* or apply eq1. *)
  exact eq2.                    (* or apply eq2. *)
Qed.

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n + m).

Theorem eight_is_beautiful : beautiful 8.
Proof.
  apply b_sum with (n := 3) (m := 5).
  exact b_3.
  exact b_5.
Qed.

Theorem eight_is_beautiful_s : beautiful 8.
Proof.
  apply (b_sum 3 5 b_3 b_5).
Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3 + n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5 + n).

Theorem gorgeous_beautiful : forall n, gorgeous n -> beautiful n.

Proof.
  intros.
  induction H as [|n'|n'].
  exact b_0.
  apply b_sum.
  exact b_3.
  exact IHgorgeous.
  apply b_sum.
  exact b_5.
  exact IHgorgeous.
Qed.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem SSev_even : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  subst.                        (* optional step *)
  apply E'.                     (* or exact E' *)
Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
  intros.
  inversion H.
  split.
  apply H1.
  apply H0.
Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
  intros.
  unfold not.
  intros.
  apply H0.
  exact H.
  Show Proof.
Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intro n.
  reflexivity.
Qed.

Theorem plus_1_n : forall n : nat, 1 + n = S n.
Proof.
  intro n.
  reflexivity.
Qed.

Theorem mult_O_n : forall n : nat, 0 * n = 0.
Proof.
  intro n.
  reflexivity.
Qed.

Theorem plus_id_example : forall n m : nat, n = m -> n + n = n + m.
Proof.
  intros n m.
  intro H.
  rewrite -> H.                 (* rewrite left use right *)
  reflexivity.
Qed.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
          | O => true
          | S m' => false
          end
    |S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Theorem plus_1_neq_0 : forall n : nat, beq_nat (n + 1) 0 = false.
Proof.
  intro n.
  destruct n as [| n'].
  simpl.
  reflexivity.
  simpl.                        (* the simpl tactic can be ommited *)
  reflexivity.
Qed.


Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Theorem andb_true_elim : forall b c : bool, andb b c = true -> b = true.

Proof.
  intros b c H.
  destruct b.
  reflexivity.
  rewrite <- H.
  simpl.
  reflexivity.
Qed.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.