Module PNPEX.
  
From mathcomp.ssreflect
Require Import ssreflect ssrfun eqtype ssrnat ssrbool seq.

Section Chapter2.

(* Exercise 2.1 *)

Fixpoint alternate (s1 : seq nat) (s2 : seq nat) : seq nat :=
  match s1, s2 with
    | nil, nil => nil
    | nil, _   => s2
    | _  , nil => s1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end.
                   

Compute alternate [:: 1;2;3] [:: 4;5;6] = [:: 1;4;2;5;3;6].
Compute alternate [:: 1] [:: 4;5;6] = [:: 1;4;5;6].
Compute alternate [:: 1;2;3] [:: 4] = [:: 1;4;2;3].

End Chapter2.

Section Chapter3.
  
(* Exercise 3.1 *)

Theorem all_imp_ist A (P Q: A -> Prop): 
  (forall x: A, P x -> Q x) -> (forall y, P y) -> forall z, Q z. 
Proof.
  move=> H1 H2 z.
  by apply H1.
Qed.

Inductive my_ex A (S: A -> Prop) : Prop := my_ex_intro x of S x.

Theorem ex_imp_ex A (S T: A -> Prop):
  (exists a: A, S a) -> (forall x: A, S x -> T x) -> exists b: A, T b.
Proof.
  case=> a Hs Hst.
  exists a.
  apply Hst.
  apply Hs.
Qed.

(* Exercise 3.2 *)

Goal forall A (S: A -> Prop), my_ex A S <-> exists y: A, S y.
Proof.
  firstorder.
Qed.

(* Exercise 3.3 *)

Require Import Classical_Prop.

Definition peirce_law := forall P Q: Prop, ((P -> Q) -> P) -> P.
Definition peirce := peirce_law.
Definition double_neg := forall P: Prop, ~ ~ P -> P.
Definition excluded_middle := forall P: Prop, P \/ ~P.
Definition de_morgan_not_and_not := forall P Q: Prop, ~ ( ~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q: Prop, (P -> Q) -> (~P \/ Q).

Lemma peirce_dn: peirce -> double_neg.
Proof.
  rewrite /peirce /double_neg /peirce_law.
  firstorder.
  apply H with (Q := P).
  move=> H1.
  suff: P.
  exact H1.
  apply NNPP.
  exact H0.
Qed.

Lemma dn_em : double_neg -> excluded_middle.
Proof.
  rewrite /double_neg /excluded_middle.
  (* firstorder. *)
  (* apply classic. *)
  compute.
  intros.
  apply H.
  intuition.
Qed.

Lemma em_dmnan: excluded_middle -> de_morgan_not_and_not.
Proof.
  rewrite /excluded_middle /de_morgan_not_and_not.
  compute.
  intros.
  specialize (H (P \/ Q)).
  inversion H.
  done.
  intuition.
Qed.

Lemma dmnan_ito : de_morgan_not_and_not -> implies_to_or.
Proof.
  rewrite /de_morgan_not_and_not /implies_to_or.
  compute.
  intros.
  specialize (H (P -> False) Q).
  intuition.
Qed.

Lemma ito_peirce : implies_to_or -> peirce.
Proof.
  rewrite /implies_to_or /peirce.
  compute.
  intros.
  specialize (H P P).
  intuition.
Qed.

End Chapter3.

Section Chapter4.
  
(* Exercise 4.1 *)

Set Implicit Arguments.
Inductive my_eq (A : Type) (x : A) : A -> Prop :=  my_eq_refl : my_eq x x.
Notation "x === y" := (my_eq x y) (at level 70).

Lemma disaster2: 1 === 2 -> False.
Proof.
  move=> H.
  pose D x := if x is 1 then False else True.
  have D2: D 2.
  by [].
  case: H D2.
  move=> /=.
  done.
Qed.

(* Exercise 4.2 *)

Definition maxn m n := if m < n then n else m.

Lemma max_l m n: n <= m -> maxn m n = m.
Proof.
  rewrite /maxn.
  case: leqP=>//.
Qed.

Lemma max_is_max m n: n <= maxn m n /\ m <= maxn m n.
Proof.
  rewrite /maxn.
  case leqP=>//.
  move=>H.
  split.
  by apply leqnn.
  rewrite ltn_neqAle in H.
  by case /andP: H.
Qed.

Lemma maxnE m n : maxn m n = m + (n - m).
Proof. by rewrite /maxn addnC; case: leqP => [/eqnP-> | /ltnW/subnK]. Qed.

Lemma succ_max_distr_r n m : (maxn n m).+1 = maxn (n.+1) (m.+1).
Proof.
  rewrite !maxnE.
  rewrite addSn.
  done.
Qed.

Lemma plus_max_distr_l m n p: maxn (p + n) (p + m) = p + maxn n m.
Proof.
  rewrite !maxnE.
  rewrite subnDl.
  rewrite addnA.
  done.
Qed.

(* Exercice 4.3 *)

Inductive nat_rels m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : nat_rels m n true false false
  | CompareNatGt of m > n : nat_rels m n false true false
  | CompareNatEq of m = n : nat_rels m n false false true.

Lemma natrelP m n : nat_rels m n (m < n) (n < m) (m == n).
Proof.
  rewrite ltn_neqAle eqn_leq.
  case: ltnP; first by constructor.
  by rewrite leq_eqVlt orbC; case: leqP; constructor; first exact/eqnP.
Qed.

(* Exercise 4.4 *)

Definition minn m n := if m < n then m else n.

Lemma addn_min_max m n : minn m n + maxn m n = m + n.
Proof.
  rewrite /minn /maxn.
  case: ltngtP => // [_|->] //.
  apply: addnC.
Qed.

End Chapter4.

End PNPEX.
