Require Import Coq.Arith.Arith.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

(*
 *
 * the BNF grammar for this simple language:
 *
 *  <exp> ::= 
 *         |  <X>
 *         |  <exp> + <exp>
 *         |  <exp> * <exp>
 *         |  <exp> < <exp>
 *         |  <integer contant>
 *         |  (<exp>)
 *
 *  <cmd> ::= 
 *         |  skip
 *         |  <X> = <exp>
 *         |  ifNZ <exp> { <cmd> } else { <cmd> }
 *         |  whileNZ <exp> { <cmd> }
 *         |  <cmd>; <cmd>
 *
 *)

Definition name := string.

(* Abstract syntax of arithmetic expressions *)
Inductive exp : Type :=
  Var : name -> exp
| Add : exp  -> exp -> exp
| Dec : exp  -> exp
| Mul : exp  -> exp -> exp
| Lt  : exp  -> exp -> exp
| Lit : nat    -> exp.

Definition arith : exp := Mul (Lit 3) (Add (Lit 4) (Lit 5)).

(* Abstract syntax of commands *)
Inductive cmd : Type :=
  Skip    : cmd
| Assn    : name -> exp -> cmd
| IfNZ    : exp  -> cmd -> cmd -> cmd
| WhileNZ : exp  -> cmd -> cmd
| Seq     : cmd  -> cmd -> cmd.

Definition X := String "X" EmptyString.
Definition ANS := String "A" (String "N" (String "S" EmptyString)).

Definition factorial : cmd :=
  let x := "X"%string in
  let ans := "ANS"%string in
  Seq (Assn x (Lit 6))
      (Seq (Assn ans (Lit 1))
           (WhileNZ (Var x)
                    (Seq (Assn ans (Mul (Var ans) (Var x)))
                         (Assn x (Dec (Var x)))))).
      
(* Interpreter *)

Definition state := name -> nat.
Definition init_state := fun x : name => 0.

Fixpoint beq_string (s1 s2 : string) : bool :=
  match s1, s2 with
    | EmptyString, EmptyString => true
    | EmptyString, String _ _  => false
    | String _ _, EmptyString  => false
    | String h1 t1, String h2 t2 =>
      if beq_nat (nat_of_ascii h1) (nat_of_ascii h2)
      then beq_string t1 t2
      else false
  end.

Notation "x == y" := (beq_string x y) (at level 60).

Definition update (s : state) (x : name) (v : nat) :=
  fun (y : name) => if x == y then v else s y.

Fixpoint bl_nat (n m : nat) : bool :=
  match n, m with
    | O, O       => false
    | O, S _     => true
    | S _, O     => false
    | S n1, S m1 => bl_nat n1 m1
  end.

Fixpoint neq_nat (n m : nat) : bool :=
  match n, m with
    | O, O       => false
    | O, S _     => true
    | S _, O     => true
    | S n1, S m1 => neq_nat n1 m1
  end.

Fixpoint interpret_exp (s : state) (e : exp) : nat :=
  match e with
    | Var x     => s x
    | Add e1 e2 => (interpret_exp s e1) + (interpret_exp s e2)
    | Dec e     => (interpret_exp s e) - 1
    | Mul e1 e2 => (interpret_exp s e1) * (interpret_exp s e2)
    | Lt  e1 e2 => if (bl_nat (interpret_exp s e1) (interpret_exp s e2)) then 1 else 0
    | Lit i     => i
  end.

Fixpoint interpret_cmd (s : state) (c : cmd) (i : nat) : state :=
  match i with
    | O    => s
    | S i' => 
      match c with
        | Skip         => s
        | Assn x e     => update s x (interpret_exp s e)
        | IfNZ e c1 c2 =>
          if (neq_nat (interpret_exp s e) 0) then interpret_cmd s c1 i' else interpret_cmd s c2 i'
        | WhileNZ e c  =>
          interpret_cmd s (IfNZ e (Seq c (WhileNZ e c)) Skip) i'
        | Seq c1 c2    =>
          let s1 := interpret_cmd s c1 i' in
          interpret_cmd s1 c2 i'
      end
  end.

Compute (interpret_cmd init_state factorial 1000) "ANS"%string = 720.

Compute (interpret_cmd init_state (Seq (Assn "X"%string (Lit 6)) (Assn "X"%string (Dec (Var "X"%string)))) 10) "X"%string = 5.

Compute "123"%string == "122"%string = false.
