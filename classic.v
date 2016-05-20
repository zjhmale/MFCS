Variables P Q R : Prop.

Theorem one : (P /\ ~ P) -> Q.

Proof.
  intro pnpH.
  destruct pnpH as [pH npH].
  cut False.                        (* assume a contradiction *)
  intro fH.
  case fH.
  apply npH.                    (* ~p <-> p -> False *)
  exact pH.
Qed.

Theorem C : (P -> Q -> R) -> (Q -> P -> R).

Proof.
  intro pqrH.
  intro qH.
  intro pH.
  apply pqrH.
  exact pH.
  exact qH.
Qed.

(* simply use auto *)

Theorem C1 : (P -> Q -> R) -> (Q -> P -> R).

Proof.
  auto.
Qed.

Section auto.
  Variables P1 P2 P3 P4 P5 P6 : Prop.
  
  Theorem had : (P1 -> P2) -> (P2 -> P3) -> (P3 -> P4) -> (P4 -> P5) -> (P5 -> P6) -> (P1 -> P6).
  Proof.
    auto 6.
  Qed.

  (* suger *)
  Goal (P1 \/ P1) -> P1.
  tauto.
  Save p1.

  Print p1.
End auto.

Require Import Coq.Logic.Classical.

Print classic. (* Axiom tnd : P \/ ~ P. *)

Theorem nnpp : ~~ P -> P.

Proof.
  cut (P \/ ~P).
  intro pnpH.
  case pnpH.
  intros pH nnpH.
  exact pH.
  intros npH nnpH.
  unfold not in npH.
  unfold not in nnpH.
  contradict nnpH.              (* a small trick *)
  exact npH.
  apply classic.
Qed.