Require Import List.
Import ListNotations.

Require Import Nat.
Require Import Bool.

Open Scope list_scope.

Inductive semigroup (A : Type) (Op : A -> A -> A) : Prop :=
| Semigroup_intro :
    (forall (a1 a2 a3 : A), Op a1 (Op a2 a3) = Op (Op a1 a2) a3) -> semigroup A Op.

Check add.

Theorem nat_semigroup : semigroup nat add.
Proof.
  apply Semigroup_intro.
  intros.
  induction a1.
  + reflexivity.
  + simpl. f_equal. induction a2; auto.
Qed.
  
Theorem list_semigroup : forall A, semigroup (list A) (@app A).
Proof.
  intro. apply Semigroup_intro. intros.
  induction a1.
  + reflexivity.
  + simpl. f_equal. induction a2; auto.
Qed.

Inductive monoid A Op (sg : semigroup A Op) (U : A) : Prop :=
| Monoid_intro :
    semigroup A Op -> (forall (a : A), Op U a = Op a U /\ Op U a = a) -> monoid A Op sg U.

Theorem nat_monoid : monoid nat add nat_semigroup 0.
Proof.
  apply Monoid_intro. apply nat_semigroup.
  intro. split.
  + simpl. auto.
  + reflexivity.
Qed.

Theorem list_monoid : forall A, monoid (list A) (@app A) (@list_semigroup A) [].
Proof.
  intro. apply Monoid_intro. apply list_semigroup.
  intro. split.
  + rewrite app_nil_r. reflexivity.
  + reflexivity.
Qed.

Inductive functor (F : Type -> Type) : (forall t1 t2, (t1 -> t2) -> F t1 -> F t2) -> Prop :=
| Functor_intro
    (fmap : forall t1 t2, (t1 -> t2) -> F t1 -> F t2)
    (l1   : forall t f, fmap t t id f = f)
    (l2   : forall t1 t2 t3, forall (f : F t1) (p : t2 -> t3) (q : t1 -> t2),
              fmap t1 t3 (fun a => p (q a)) f = fmap t2 t3 p (fmap t1 t2 q f)) :
    functor F fmap.

Theorem list_functor : functor list map.
Proof.
  apply Functor_intro.
  + intros. induction f. reflexivity. simpl. rewrite IHf. reflexivity.
  + intros. induction f. reflexivity. simpl. f_equal. apply IHf.
Qed.

Inductive monad : (Type -> Type) -> Prop :=
| Monad_intro
    (F        : Type -> Type)
    (fmap     : forall t1 t2, (t1 -> t2) -> F t1 -> F t2)
    (Fp       : functor F fmap)
    (lift     : forall t, t -> F t)
    (bind     : forall t1 t2, F t1 -> (t1 -> F t2) -> F t2)
    (left_id  : forall t1 t2 a f, bind t1 t2 (lift t1 a) f = f a)
    (right_id : forall t m, bind t t m (lift t) = m)
    (assoc    : forall t1 t2 t3 m f g,
                  bind t2 t3 (bind t1 t2 m f) g = bind t1 t3 m (fun x => bind t2 t3 (f x) g)) :
    monad F.

Definition singleton (A : Type) (x : A) := [x].

Fixpoint concat {A : Type} (l : list (list A)) : list A :=
  match l with
  | []     => []
  | h :: t => app h (concat t)
  end.

Definition concatMap (A : Type) (B : Type) (l : list A) (f : A -> list B) : list B :=
  concat (map f l).

Theorem list_monad : monad list.
Proof.
  apply Monad_intro with (fmap := map) (lift := singleton) (bind := concatMap).
  + apply list_functor.
  + intros. unfold concatMap. simpl. rewrite app_nil_r. reflexivity.
  + intros. unfold concatMap. induction m.
    - reflexivity.
    - simpl. f_equal. apply IHm.
  + intros. induction m as [|h t].
    - reflexivity.
    - unfold concatMap in *. simpl. rewrite <- IHt. 
      assert (forall A (l1 : list (list A)) (l2 : list (list A)),
                concat l1 ++ concat l2 = concat (l1 ++ l2)) as H.
        intros. induction l1; auto.
          simpl. rewrite <- app_assoc. rewrite IHl1. auto.
      rewrite H. f_equal. rewrite map_app. reflexivity.
Qed.

Definition map_option (A B : Type) (f : A -> B) (opt : option A) :=
  match opt with
  | None => None
  | Some t => Some (f t)
  end.

Definition append_option A OpA (sg : semigroup A OpA) (a b : option A) : option A :=
  match a, b with
  | None, None => None
  | None, Some b' => Some b'
  | Some a', None => Some a'
  | Some a', Some b' => Some (OpA a' b')
  end.

Theorem option_semigroup : forall A OpA (sg : semigroup A OpA),
  semigroup (option A) (append_option A OpA sg).
Proof.
  intros. apply Semigroup_intro. intros. destruct a1.
  + destruct a2.
    - destruct a3.
      * simpl. f_equal. inversion sg. apply H.
      * simpl. reflexivity.
    - destruct a3; simpl; reflexivity.
  + destruct a2; destruct a3; auto.
Qed.

Theorem option_monoid : forall A OpA (sg : semigroup A OpA),
  monoid (option A) (append_option A OpA sg) (option_semigroup A OpA sg) None.
Proof.
  intros. apply Monoid_intro. apply option_semigroup.
  intros. split. auto. destruct a; auto.
Qed.

Definition option_map A B (f : A -> B) (o : option A) : option B :=
  match o with
  | None => None
  | Some a => Some (f a)
  end.

Theorem option_functor : functor option option_map.
Proof.
  apply Functor_intro; intros; destruct f; auto.
Qed.

Definition option_bind A B (o1 : option A) (f : A -> option B) : option B :=
  match o1 with
  | None => None
  | Some a => f a
  end.

Theorem option_monad : monad option.
Proof.
  apply Monad_intro with (fmap := option_map) (lift := Some) (bind := option_bind).
  + apply option_functor.
  + intros. auto.
  + intros. destruct m; auto.
  + intros. destruct m; auto.
Qed.

(* https://coq.inria.fr/refman/Reference-Manual009.html *)
(* http://poleiro.info/posts/2013-06-27-structuring-proofs-with-bullets.html *)

Theorem andb_comm : forall (b1 b2 : bool), b1 && b2 = b2 && b1.
Proof.
  intros.
  destruct b1.
  + destruct b2.
    - simpl. reflexivity.
    - simpl. reflexivity.
  + destruct b2.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.
