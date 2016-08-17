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