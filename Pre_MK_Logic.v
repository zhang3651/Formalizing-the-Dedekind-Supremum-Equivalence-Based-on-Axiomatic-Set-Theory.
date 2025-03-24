(**********************************************************************)
(*  This is part of Pre_ML, it is distributed under the terms of the  *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2023-2028                            *)
(*  Si Chen, Guowei Dou, Yaoshun Fu, Shukun Leng and Wensheng Yu      *)
(**********************************************************************)

(** Pre_MK_Logic *)
 
(* 引进记号 *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' ∃ x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[' 'λ' x .. y ']' , t").

(* 初等逻辑模块 *)

Module Logic.

Axiom classic : ∀ P, P \/ ~P.

Proposition peirce : ∀ P, (~P -> P) -> P.
Proof.
  intros; destruct (classic P); auto.
Qed.

Proposition NNPP : ∀ P, ~~P <-> P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Proposition notandor : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition inp : ∀ {P Q : Prop}, (P -> Q) -> (~Q) -> (~P).
Proof.
  intros; intro; auto.
Qed.

Proposition imply_to_and : ∀ P Q : Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros; split. apply NNPP; red.
  intro; apply H; intro; absurd P; trivial. tauto.
Qed.

Proposition not_all_not_ex :
  ∀ U P, ~ (∀ n : U, ~ P n) -> ∃ n : U, P n.
Proof.
  intros. apply NNPP. intro. elim H.
  intros. intro. elim H0; eauto.
Qed.

Proposition not_ex_all_not :
 ∀ U P, ~ (∃ n : U, P n) -> ∀ n : U, ~ P n.
Proof.
  intros. intro. elim H; eauto.
Qed.

(* 一些简单的策略 *)

Ltac New H := pose proof H.

Ltac TF P := destruct (classic P).

Ltac Absurd := apply peirce; intros.

(* 批处理条件或目标中"与"和"或"策略 *)

Ltac deand :=
  match goal with
   | H: ?a /\ ?b |- _ => destruct H; deand
   | _ => idtac
  end.

Ltac deor :=
  match goal with
   | H: ?a \/ ?b |- _ => destruct H; deor
   | _ => idtac 
  end.

Ltac deandG :=
  match goal with
    |- ?a /\ ?b => split; deandG
    | _ => idtac
  end.

End Logic.

Export Logic.