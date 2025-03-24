(**********************************************************************)
(*  This is part of FA_R1, it is distributed under the terms of the   *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2023-2028                            *)
(*  Si Chen, Guowei Dou, Yaoshun Fu, Shukun Leng and ωensheng Yu      *)
(**********************************************************************)

(** FA_R1 *)
 
(* 读入库文件 *)
Require Export MK_Theorems1.

(* NATURAL NUMBERS *)

(* SECTION I Axioms *)

Definition One := PlusOne Φ.

(*自然数集*)
Definition Nat := ω ~ One.

Fact EnOne : Ensemble One.
Proof.
  exists ω. apply MKT134, MKT135.
Qed.

Fact EnNat : Ensemble Nat.
Proof.
  New MKT138. apply MKT33 with ω; eauto.
  red; intros. appA2H H0. tauto.
Qed.

Global Hint Resolve EnOne EnNat : core.

Fact frem : ∀ f, f|(Φ) = Φ.
Proof.
  intros; eqext; try emf.
  appA2H H. destruct H0. appA2H H1. destruct H2 as [x [y]].
  destruct H2 as [?[]]. emf.
Qed.

Fact domem : dom(Φ) = Φ.
Proof.
  intros; eqext; try emf. appA2H H. destruct H0. emf.
Qed.

Fact funp : ∀ {x z},
  Ensemble x -> z ∈ PlusOne x -> z ∈ x \/ z = x.
Proof.
  intros. appA2H H0. destruct H1; auto. right. apply MKT41; auto.
Qed.

Fact exexp : ∀ {x}, Ensemble x -> Ensemble (PlusOne x).
Proof.
  intros. apply AxiomIV; auto.
Qed.

Global Hint Resolve exexp : core.

Definition OnTo F A B := Function F /\ dom(F) = A /\ ran(F) ⊂ B.

(*后继函数*)
Definition Nsuc := \{\ λ u v, u ∈ Nat /\ v = PlusOne u\}\.

Notation " x ⁺ " := Nsuc[x](at level 0).

Fact OTNp : OnTo Nsuc Nat Nat.
Proof.
  repeat split; unfold Nsuc; auto; try red; intros; [|eqext|].
  - appoA2H H. appoA2H H0. deand. subst; auto.
  - appA2H H. destruct H0. appoA2H H0; tauto.
  - appA2G. exists (PlusOne z); appoA2G. rxo.
  - appA2H H. destruct H0. appoA2H H0. destruct H1. subst.
    apply setminp in H1 as []. apply setminP; auto. intro.
    apply funp in H3 as []; subst; auto; try emf.
    eapply MKT135; eauto.
Qed.

Fact SucinNat : ∀ {x}, x ∈ Nat -> x⁺ ∈ Nat.
Proof.
  intros. destruct OTNp as [? []]. apply H2, Property_dm; auto.
  rewrite H1; auto.
Qed.

Global Hint Resolve SucinNat : core.

Fact NSp : ∀ x, x ∈ Nat -> x⁺ = PlusOne x.
Proof.
  intros. destruct OTNp as [? []]. symmetry.
  apply Property_Fun; auto. appoA2G. rxo.
Qed.

Theorem FAA1 : One ∈ Nat.
Proof.
  appA2G. split; [apply MKT134, MKT135|appA2G; apply MKT101].
Qed.

Global Hint Resolve FAA1 : core.

Theorem FAA2 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x = y -> x⁺ = y⁺.
Proof.
  intros. subst. auto.
Qed.

Theorem FAA3 : ∀ x, x ∈ Nat -> x⁺ <> One.
Proof.
  intros; intro. rewrite NSp in H0; auto.
  apply setminp in H as []. apply H1. rewrite <- H0. appA2G.
Qed.

Theorem FAA4 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x⁺ = y⁺ -> x = y.
Proof.
  intros. rewrite NSp, NSp in H1; auto.
  apply setminp in H. apply setminp in H0.
  apply MKT136; tauto.
Qed.

Theorem FAA5 : ∀ M, M ⊂ Nat -> One ∈ M
  -> (∀ u, u ∈ M -> u⁺ ∈ M) -> M = Nat.
Proof.
  intros. eqext. auto. apply setminp in H2 as []. revert H3.
  apply Mathematical_Induction with (n:=z); intros; auto.
  - elim H3. appA2G.
  - TF (k ∈ One); [apply funp in H6 as [];
    subst; auto; try emf|]. rewrite <- NSp; auto.
Qed.

(*自然数的数学归纳法*)
Theorem MathInd : ∀ P : Class -> Prop, P One 
  ->(∀ k, k ∈ Nat -> P k -> P k⁺) -> (∀ n, n ∈ Nat -> P n).
Proof.
  intros. assert (\{λ x, x ∈ Nat /\ P x \} = Nat).
  { apply FAA5; try red; intros.
    - appA2H H2; tauto.
    - appA2G.
    - appA2H H2. destruct H3. appA2G. }
  rewrite <- H2 in H1. appA2H H1; tauto.
Qed.

Ltac MI x := apply MathInd with (n:=x); auto; intros.

Ltac MP :=
  match goal with
  | H  : ?P,
    H0 : ?P -> ?Q
    |- _ => pose proof H0 H; clear H0; MP
  | |- _ => idtac
  end.

(* SECTION II Addition *)

Declare Scope Nat_scope.

Delimit Scope Nat_scope with Nat.

Open Scope Nat_scope.

Theorem FAT1 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x <> y -> x⁺ <> y⁺.
Proof.
  intros; intro. apply H1, FAA4; auto.
Qed.

Theorem FAT2 : ∀ x, x ∈ Nat -> x⁺ <> x.
Proof.
  intros. MI x.
  - apply FAA3, FAA1.
  - apply FAT1; auto.
Qed.

Theorem FAT3 : ∀ x, x ∈ Nat -> x <> One -> ∃ u, u ∈ Nat /\ x = u⁺.
Proof.
  intros. revert H0. MI x.
  - elim H0; auto.
  - eauto.
Qed.

Fact N1orS : ∀ {x}, x ∈ Nat -> x = One \/ ∃ u, u ∈ Nat /\ x = u⁺.
Proof.
  intros. TF (x = One); auto. right; apply FAT3; auto.
Qed.

Fact NreW : ∀ {x}, x ∈ Nat -> ∃ v, v ∈ ω /\ x = PlusOne v.
Proof.
  intros. MI x; eauto. destruct H1 as [v []]; subst.
  rewrite NSp; eauto.
Qed.

Fact Emp1 : ∀ {x}, Φ <> PlusOne x.
Proof.
  intros; intro. TF (Ensemble x).
  - apply @ MKT16 with x. rewrite H. appA2G.
  - apply H0, (MKT33 (PlusOne x));
    [rewrite <- H; auto|red; intros; appA2G].
Qed.

Fact ωreN : ∀ {x}, x ∈ ω -> PlusOne x ∈ Nat.
Proof.
  intros. apply setminP; auto. intro.
  apply funp in H0 as []; subst; auto. try emf.
  eapply Emp1; eauto. 
Qed.

(* 递归定理补充引理 *)
Fact odp : ∀ h u, Function h -> Ordinal dom(h)
  -> u ∈ dom(h) -> dom(h|(PlusOne u))= PlusOne u.
Proof.
  intros. rewrite MKT126b; auto. eqext.
  - deHin; auto.
  - deGin; auto. apply funp in H2 as []; subst; auto; eauto.
    eapply H0; eauto.
Qed.

Fact odv : ∀ h u, Function h -> Ordinal dom(h) -> u ∈ dom(h) 
  -> (h|(PlusOne u))[u] = h[u].
Proof.
  intros. apply MKT126c; auto. rewrite odp; auto. appA2G.
Qed.

Fact free : ∀ f x, Function f -> Ensemble x -> Ensemble (f|(x)).
Proof.
  intros. apply MKT75;[apply MKT126a|rewrite MKT126b]; auto.
  eapply MKT33; eauto. red; intros. deHin; auto.
Qed.

(*递归定理 0*)
Lemma RecursionWex : ∀ {F A a}, Ensemble A -> a ∈ A
  -> OnTo F A A -> ∃ h, OnTo h ω A /\ h[Φ] = a /\ ∀n, n ∈ ω
  -> h[PlusOne n] = F[h[n]].
Proof.
  intros. destruct H1 as [?[]].
  set (g := \{\ λ u v, ((u=Φ /\ v=a) \/ (∃ z, z ∈ ω
    /\ dom(u)=PlusOne z /\ v=F[u[z]])) \}\).
  Local Ltac l1 := deand; deor; deand; subst; auto.
  assert (K1: Function g).
  { unfold g; split; intros; auto. appoA2H H4. appoA2H H5. l1.
    - destruct H6. deand. rewrite domem in H6.
      destruct (Emp1 H6).
    - destruct H7. deand. rewrite domem in H6.
      destruct (Emp1 H6).
    - destruct H6, H7. deand. subst. rewrite H7 in H9.
      apply MKT136 in H9; subst; auto. }
  assert (K2: ran(g) ⊂ A).
  { red; intros. appA2H H4. destruct H5. appoA2H H5.
    destruct H6. l1. destruct H6. deand. subst.
    apply H3, Property_dm, MKT69b'; auto. }
  assert (K3: ∀ f u, Function f -> Ordinal dom(f) -> u ∈ ω
    -> u ∈ dom(f) -> f[u] ∈ A -> g[f|(PlusOne u)] = F[f[u]]).
  { intros. subst. apply Property_dm in H8; auto.
    symmetry. apply Property_Fun; auto.
    appoA2G; [rxo; apply free; eauto|]. rewrite odp; auto.
    right. exists u. rewrite odv; auto. }
  assert (K4 : ∀ u, u ∈ ω -> Ordinal_Number u).
  { intros. appA2G. eapply MKT111; eauto. }
  destruct (MKT128a g) as [h]. deand.
  assert ([Φ,a] ∈ h).
  { rewrite MKT70; auto. appoA2G. rewrite H6, frem; auto.
    apply Property_Fun; auto. appoA2G. }
  assert (dom(h) ⊂ ω).
  { destruct (Th110ano Property_W H5); auto.
    assert (Ordinal_Number ω). { appA2G. } apply H6 in H9.
    assert (h|(ω) ∈ dom(g)).
    { apply MKT69b', MKT19. rewrite <- H9.
      apply MKT19, MKT69b; auto. }
    appA2H H10. destruct H11. appoA2H H11. l1.
    + destruct (@ MKT16 [Φ,a]). pattern Φ at 2.
      rewrite <- H12. appA2G. split; auto. appoA2G.
    + destruct H12. deand. subst. rewrite MKT126b in H12;
      auto. New H8. apply H5 in H8. apply MKT30 in H8.
      apply MKT134 in H2. rewrite H8 in H12.
      rewrite H12 in H2. destruct (MKT101 _ H2). }
  assert (dom(h) = ω).
  { apply MKT137; intros; auto.
    - eapply Property_dom; eauto.
    - New H9. appA2H H9. destruct H11.
      assert (h|(u) ∈ dom(g)).
      { apply MKT69b'. rewrite <- H6; auto.
        apply MKT69b; auto. }
      apply MKT69b'. rewrite H6; auto. New H12.
      apply Property_dm, K2 in H12; auto.
      rewrite <- H2, <- H6 in H12; auto. subst. New H12.
      apply Property_dm in H12; auto. rewrite K3; eauto. }
  apply Property_Fun in H7; auto. symmetry in H7.
  assert (ran(h) ⊂ A).
  { red; intros. appA2H H10. destruct H11. New H11.
    apply Property_dom in H12. rewrite H9 in H12.
    apply Property_Fun in H11; auto. subst.
    apply Mathematical_Induction with (n := x); auto; intros.
    New H2. rewrite <- H9 in H2. rewrite H6, K3; auto.
    apply H3, Property_dm; auto. }
  assert (∀ u, u ∈ ω -> h[PlusOne u] = F[h[u]]).
  { intros. New H11. rewrite <- H9 in H11.
    rewrite H6, K3; auto. apply H10, Property_dm; auto. }
  exists h. unfold OnTo. auto.
Qed.

Theorem RecursionWun : ∀ h1 h2 F A a, OnTo h1 ω A -> h1[Φ] = a
  -> (∀n, n ∈ ω -> h1[PlusOne n] = F[h1[n]]) -> OnTo h2 ω A -> h2[Φ] = a
  -> (∀n, n ∈ ω -> h2[PlusOne n] = F[h2[n]]) -> h1 = h2.
Proof.
  intros. red in H, H2. deand. subst. apply MKT71; auto.
  intros. TF (x ∈ ω).
  - apply Mathematical_Induction with (n := x); auto; intros.
    rewrite H1, H4, H10; auto.
  - repeat rewrite MKT69a; [|rewrite H5|rewrite H7]; auto.
Qed.

(*自然数递归定理 1*)
Lemma RecursionNex : ∀ {F A a}, Ensemble A -> a ∈ A -> OnTo F A A
  -> ∃ h, OnTo h Nat A /\ h[One] = a /\ ∀ n, n ∈ Nat -> h[n⁺] = F[h[n]].
Proof.
  intros. destruct (RecursionWex H H0 H1) as [f [H2 []]].
  red in H2. deand.
  set (h := \{\λ u v, ∃ w, w ∈ ω /\ u = PlusOne w
    /\ v = f[w] \}\).
  assert (Function h).
  { red; [split; unfold h; intros|..]; auto.
    appoA2H H7. appoA2H H8. destruct H9, H10. deand. subst.
    apply MKT136 in H11; subst; auto. }
  assert (∀ u, u ∈ ω -> h[PlusOne u] = f[u]).
  { intros. symmetry. apply Property_Fun; auto. appoA2G.
    New H8. rewrite <- H5 in H8. apply MKT69b in H8. rxo. }
  assert (OnTo h Nat A).
  { red. deandG; auto; [eqext|red; intros].
    - appA2H H9. destruct H10. appoA2H H10. destruct H11.
      deand. subst. apply ωreN; auto.
    - apply NreW in H9 as [x []]; subst. appA2G. exists f[x].
      appoA2G. rxo. apply MKT19, MKT69b. rewrite H5; auto.
    - appA2H H9. destruct H10. appoA2H H10. destruct H11.
      deand. subst. rewrite <- H5 in H11.
      apply H6, Property_dm; auto. }
  exists h; split; auto; split; intros.
  - symmetry. eapply Property_Fun; auto. appoA2G.
  - rewrite NSp; auto. apply NreW in H10 as [x []]; subst.
    rewrite H8, H8; auto.
Qed.

Theorem RecursionNun : ∀ h1 h2 F A a, OnTo h1 Nat A -> h1[One] = a 
  -> (∀n, n ∈ Nat -> h1[n⁺] = F[h1[n]]) -> OnTo h2 Nat A -> h2[One] = a 
  -> (∀n, n ∈ Nat -> h2[n⁺] = F[h2[n]]) -> h1 = h2.
Proof.
  intros. red in H, H2. deand. subst. apply MKT71; auto.
  intros. TF (x ∈ Nat).
  - MI x. rewrite H1, H4, H10; auto.
  - repeat rewrite MKT69a; [|rewrite H5|rewrite H7]; auto.
Qed.

Definition NArith F a := ∩\{ λ h, OnTo h Nat Nat /\ h[One] = a 
  /\ ∀ n, n ∈ Nat -> h[n⁺] = F[h[n]] \}.

(*加m函数*)
Definition addN := λ m, NArith Nsuc m⁺.

Fact addnT : ∀ {n}, n ∈ Nat -> OnTo (addN n) Nat Nat /\ (addN n)[One] = n⁺ 
  /\ ∀ m, m ∈ Nat -> (addN n)[m⁺] = ((addN n)[m])⁺.
Proof.
  intros. destruct (RecursionNex EnNat (SucinNat H) OTNp) as [h].
  deand. assert (addN n = h).
  { inversion H0. deand. eqext.
    - appA2H H6. apply H7. appA2G.
      apply MKT75; [|rewrite H4]; auto.
    - appA2G. intros. appA2H H7. deand.
      erewrite RecursionNun; eauto. }
  subst; split; auto.
Qed.

Notation " x + y " := (addN x)[y] : Nat_scope.

Theorem FAT4a : ∀ m, m ∈ Nat -> m + One = m⁺.
Proof.
  intros. apply addnT; auto.
Qed.

Theorem FAT4b : ∀ m n, m ∈ Nat -> n ∈ Nat -> m + n⁺ = (m + n)⁺.
Proof.
  intros. apply addnT; auto.
Qed.

Theorem AddNp : ∀ {x y}, x ∈ Nat -> y ∈ Nat -> (x + y) ∈ Nat.
Proof.
  intros. MI y; [rewrite FAT4a| rewrite FAT4b]; auto.
Qed.

Corollary FAT4ai : ∀ m, m ∈ Nat -> One + m = m⁺.
Proof.
  intros. MI m; auto.
  - apply FAT4a; auto.
  - rewrite FAT4b, H1; auto.
Qed.

Corollary FAT4bi : ∀ m n, m ∈ Nat -> n ∈ Nat -> m⁺ + n = (m + n)⁺.
Proof.
  intros. MI n.
  - repeat rewrite FAT4a; auto.
  - repeat rewrite FAT4b; auto. rewrite H2; auto.
Qed.

Global Hint Resolve AddNp : core.

Hint Rewrite FAT4a FAT4b FAT4ai FAT4bi: NatRew.

Ltac simN := autorewrite with NatRew in *; auto.

Theorem FAT5 : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> (x + y) + z = x + (y + z).
Proof.
  intros. MI z; simN. rewrite H3; auto.
Qed.

Theorem FAT6 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x + y = y + x.
Proof.
  intros. MI y; simN. rewrite H2; auto.
Qed.

Theorem FAT7 : ∀ {x y}, x ∈ Nat -> y ∈ Nat -> y <> x + y.
Proof.
  intros. MI y; intro; simN; [apply (FAA3 x)|apply H2, FAA4]; auto.
Qed.

Theorem FAT8 : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat 
  -> y <> z ->  x + y <> x + z.
Proof.
  intros. MI x; intro; simN; [apply H2, FAA4|apply H4, FAA4]; auto.
Qed.

Theorem FAT9 : ∀ {x y}, x ∈ Nat -> y ∈ Nat -> x = y 
  \/ (∃ u, u ∈ Nat /\ x = y + u) \/ (∃ v, v ∈ Nat /\ y = x + v).
Proof.
  intros. MI y.
  - destruct (N1orS H) as [|[? []]]; subst; auto.
    right; left; exists x0; simN.
  - destruct H2 as [? | [[u ] | [v []]]]; subst.
    + right; right; exists One; simN.
    + destruct H2, (N1orS H2) as [|[? []]]; subst; simN.
      right; left; exists x0. simN.
    + right; right. exists v⁺. simN.
Qed.

(* SECTION III Ordering *)

Definition gtn x y := ∃ u, u ∈ Nat /\ x = y + u.

Notation " x > y " := (gtn x y) : Nat_scope.

Definition ltn x y := ∃ v, v ∈ Nat /\ y = x + v.

Notation " x < y " := (ltn x y) : Nat_scope.

Theorem FAT10 : ∀ {x y}, x ∈ Nat -> y ∈ Nat -> x = y \/ x > y \/ x < y.
Proof.
  intros. apply FAT9; auto.
Qed.

Theorem FAT11 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x > y -> y < x.
Proof.
  intros. auto.
Qed.

Theorem FAT12 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x < y -> y > x.
Proof.
  intros. auto.
Qed.

Notation " x ≥ y " := (x > y \/ y = x)(at level 77) : Nat_scope.

Notation " x ≤ y " := (x < y \/ x = y)(at level 77) : Nat_scope.

Theorem FAT13 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x ≥ y -> y ≤ x.
Proof.
  intros; auto.
Qed.

Theorem FAT14 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x ≤ y -> y ≥ x.
Proof.
  intros; auto.
Qed.

Theorem FAT15 : ∀ {x y z}, x < y -> y < z -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x < z.
Proof.
  intros. destruct H, H, H0, H0. subst. exists (x0 + x1).
  rewrite FAT5; auto.
Qed.

Theorem FAT16 : ∀ {x y z}, x ≤ y /\ y < z \/ x < y /\ y ≤ z 
  -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x < z.
Proof.
  intros. destruct H as [[[]]|[H []]]; subst; auto;
  eapply FAT15; eauto.
Qed.

Theorem FAT17 : ∀ x y z, x ≤ y -> y ≤ z -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x ≤ z.
Proof.
  intros. destruct H; [left; eapply FAT16; eauto|subst; auto].
Qed.

Theorem FAT18 : ∀ {x y}, x ∈ Nat -> y ∈ Nat -> x + y > x.
Proof.
  intros. red; eauto.
Qed.

Theorem FAT19a : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x > y
  -> x + z > y + z.
Proof.
  intros. destruct H2, H2. exists x0. subst.
  repeat rewrite FAT5; auto. rewrite (FAT6 z); auto.
Qed.

Theorem FAT19b : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x = y
  -> x + z = y + z.
Proof.
  intros. subst; auto.
Qed.

Theorem FAT19c : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x < y
  -> x + z < y + z.
Proof.
  intros. apply FAT19a; auto.
Qed.

Lemma elNf : ∀ {x y}, x < y -> x = y -> x ∈ Nat -> y ∈ Nat -> False.
Proof.
  intros. destruct H, H. subst. rewrite FAT6 in H0, H2; auto.
  apply FAT7 in H0; auto.
Qed.

Lemma egNf : ∀ {x y}, x > y -> x = y -> x ∈ Nat -> y ∈ Nat -> False.
Proof.
  intros. symmetry in H0. eapply elNf; eauto.
Qed.

Lemma lgNf : ∀ {x y}, x < y -> x > y -> x ∈ Nat -> y ∈ Nat -> False.
Proof.
  intros. eapply FAT15 in H; eauto. eapply egNf in H; eauto.
Qed.

Lemma legNf : ∀ {x y}, x ≤ y -> x > y -> x ∈ Nat -> y ∈ Nat -> False.
Proof.
  intros. destruct H; [eapply lgNf|eapply egNf]; eauto.
Qed.

Ltac ELN :=
  match goal with
    H: ?n1 < ?n2
    |- _ => destruct (elNf H); auto
  end.

Ltac EGN :=
  match goal with
    H: ?n1 > ?n2
    |- _ => destruct (egNf H); auto
  end.

Ltac LGN :=
  match goal with
    H: ?n1 < ?n2
    |- _ => destruct (lgNf H); auto
  end.

Ltac LEGN :=
  match goal with
    H: ?n1 ≤ ?n2
    |- _ => destruct (legNf H); auto
  end.

Ltac GELN :=
  match goal with
    H: ?n1 ≥ ?n2
    |- _ => destruct (legNf H); auto
  end.

Ltac NordF := try ELN; try EGN; try LGN; try LEGN; try GELN.

Theorem FAT20a : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x + z > y + z
  -> x > y.
Proof.
  intros. destruct (FAT10 H H0) as [H3 | [H3 | H3]]; auto;
  [apply (FAT19b z) in H3|apply (FAT19c z) in H3]; auto; NordF.
Qed.

Theorem FAT20b : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x + z = y + z
  -> x = y.
Proof.
  intros. destruct (FAT10 H H0) as [H3 | [H3 | H3]]; auto;
  [apply (FAT19a z) in H3|apply (FAT19c z) in H3]; auto; NordF.
Qed.

Theorem FAT20c : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x + z < y + z
  -> x < y.
Proof.
  intros. eapply FAT20a; eauto.
Qed.

Theorem FAT21 : ∀ x y z u, x > y -> z > u -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> u ∈ Nat -> x + z > y + u.
Proof.
  intros. apply (FAT19a z) in H; apply (FAT19a y) in H0; auto.
  rewrite FAT6, (FAT6 u) in H0; auto. eapply FAT15; eauto.
Qed.

Theorem FAT22 : ∀ x y z u, x ≥ y /\ z > u \/ x > y /\ z ≥ u -> x ∈ Nat
  -> y ∈ Nat -> z ∈ Nat -> u ∈ Nat -> x + z > y + u.
Proof.
  intros. destruct H as [[[]]|[H []]]; subst.
  - eapply FAT21; eauto.
  - rewrite FAT6, (FAT6 x); auto. apply FAT19a; auto.
  - eapply FAT21; eauto.
  - apply FAT19a; auto.
Qed.

Lemma leplN : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x ≤ y <-> x + z ≤ y + z.
Proof.
  split; intros; destruct H2; [left |right |left |right]; 
  [apply FAT19a |apply FAT19b |eapply FAT20a |eapply FAT20b];
  eauto.
Qed.

Theorem FAT23 : ∀ x y z u, x ≥ y -> z ≥ u -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> u ∈ Nat -> x + z ≥ y + u.
Proof.
  intros. destruct H0.
  - left. apply FAT22; auto.
  - subst. apply leplN; auto.
Qed.

Theorem FAT24 : ∀ {x}, x ∈ Nat -> x ≥ One.
Proof.
  intros. destruct (N1orS H) as [H0 |[u []]]; subst; auto.
  left. exists u; simN.
Qed.

Theorem FAT25a : ∀ {x y}, y > x -> x ∈ Nat -> y ∈ Nat -> y ≥ x + One.
Proof.
  intros. destruct H, H. subst. apply FAT23; auto. apply FAT24; auto.
Qed.

Theorem FAT25b : ∀ x y, x ∈ Nat -> y ∈ Nat -> y ≥ x + One -> y > x.
Proof.
  intros. destruct H1.
  - red. red in H1. destruct H1 as [z[]].
    exists (One + z). split; auto. rewrite <- FAT5; auto.
  - red. exists One. split; auto.
Qed.

Theorem FAT26a : ∀ {x y}, y < x + One -> x ∈ Nat -> y ∈ Nat -> y ≤ x.
Proof.
  intros. destruct (FAT10 H0 H1) as [H2 | [H2 | H2]]; auto.
  apply FAT25a in H2; auto. NordF.
Qed.

Theorem FAT26b : ∀ x y, x ∈ Nat -> y ∈ Nat -> y ≤ x -> y < x + One.
Proof.
  intros. destruct H1.
  - red. red in H1. destruct H1 as [z[]].
    exists (z + One). split; auto. rewrite H2. rewrite <- FAT5; auto.
  - red. exists One. split; auto. rewrite H1; auto.
Qed.

Theorem FAT27 : ∀ S, S ⊂ Nat -> S ≠ Φ -> ∃ a, a ∈ S /\ (∀ c, c ∈ S -> a ≤ c).
Proof.
  intros. set (ℳ := \{ λ x, x ∈ Nat /\ (∀ y, y ∈ S -> x ≤ y) \}).
  assert (One ∈ ℳ).
  { appA2G. split; auto; intros. apply FAT24; auto. }
  assert (~ ∀ z, z ∈ ℳ -> z⁺ ∈ ℳ).
  { intro. assert (∀ z, z ∈ Nat -> z ∈ ℳ). { apply MathInd; auto. }
    NEele H0. pose proof (H _ H0). pose proof (SucinNat H4).
    apply H3 in H5. appA2H H5. destruct H6. apply H7 in H0.
    pose proof (FAT18 H4 FAA1). simN. NordF. }
  assert (∃ m, m ∈ ℳ /\ ~ m⁺ ∈ ℳ).
  { Absurd. elim H2; intros. Absurd. elim H3; eauto. }
  destruct H3 as [m []]. exists m; split; intros; auto.
  - Absurd. elim H4. appA2H H3. destruct H6. appA2G. split; auto.
    intros. pose proof H8. apply H7 in H8. destruct H8.
    + apply FAT25a in H8; simN.
    + subst. tauto.
  - appA2H H3. destruct H6. auto.
Qed.

Definition minN x y := ∩\{ λ z, z ∈ Nat /\ x = y + z \}.

Notation " x - y " := (minN x y) : Nat_scope.

Fact MinNUn : ∀ {x y z}, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x + y = z
  -> y = z - x.
Proof.
  intros. eqext.
  - appA2G; intros. appA2H H4. destruct H5; subst.
    rewrite FAT6, (FAT6 x) in H6; auto.
    apply FAT20b in H6; subst; auto.
  - appA2H H3. apply H4. appA2G.
Qed.

Fact MinNEx : ∀ {x y}, y > x -> x ∈ Nat -> y ∈ Nat -> x + (y - x) = y.
Proof.
  intros. destruct H as [z []]. pose proof H2.
  symmetry in H2. apply MinNUn in H2; subst; auto.
Qed.

Fact MinNT : ∀ {x y z}, z > x -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x + y = z <-> y = z - x.
Proof.
  split; intros; [apply MinNUn |rewrite H3; apply MinNEx]; auto.
Qed.

Fact MinNp : ∀ {x y}, y > x -> x ∈ Nat -> y ∈ Nat -> (y - x) ∈ Nat.
Proof.
  intros. destruct H as [z []]. symmetry in H2.
  apply MinNUn in H2; subst; auto.
Qed.

Global Hint Resolve MinNp : core.

(* SECTION IV Multiplication *)

Definition mulN := λ m, NArith (addN m) m.

Fact addmT : ∀ {n}, n ∈ Nat -> OnTo (mulN n) Nat Nat /\ (mulN n)[One] = n
  /\ ∀ m, m ∈ Nat -> (mulN n)[m⁺] = (mulN n)[m] + n.
Proof.
  intros. destruct (addnT H) as [? _].
  destruct (RecursionNex EnNat H H0) as [h]. deand.
  assert (mulN n = h).
  { inversion H1. deand. eqext.
    - appA2H H7. apply H8. appA2G. apply MKT75; [|rewrite H5]; auto.
    - appA2G. intros. appA2H H8. deand.
      erewrite RecursionNun; eauto. }
  rewrite H4. deandG; auto. intros. rewrite H3, FAT6; auto. red in H1.
  deand. apply H7, Property_dm; auto. rewrite H6; auto.
Qed.

Notation " x · y " := (mulN x)[y](at level 40) : Nat_scope.

Theorem FAT28a : ∀ m, m ∈ Nat -> m · One = m.
Proof.
  intros. apply addmT; auto.
Qed.

Theorem FAT28b : ∀ m n, m ∈ Nat -> n ∈ Nat -> m · n⁺ = m · n + m.
Proof.
  intros. apply addmT; auto.
Qed.

Theorem MulNp : ∀ x y, x ∈ Nat -> y ∈ Nat -> (x · y) ∈ Nat.
Proof.
  intros. MI y; [rewrite FAT28a | rewrite FAT28b]; auto.
Qed.

Global Hint Resolve MulNp : core.

Corollary FAT28ai : ∀ m, m ∈ Nat -> One · m = m.
Proof.
  intros. MI m; auto.
  - apply FAT28a; auto.
  - rewrite FAT28b, H1; simN.
Qed.

Corollary FAT28bi : ∀ m n, m ∈ Nat -> n ∈ Nat -> m⁺ · n = m · n + n.
Proof.
  intros. MI n.
  - repeat rewrite FAT28a; simN.
  - repeat rewrite FAT28b; simN. rewrite H2.
    repeat rewrite FAT5; auto. rewrite (FAT6 k); auto.
Qed.

Hint Rewrite FAT28a FAT28b FAT28ai FAT28bi: NatRew.

Theorem FAT29 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x · y = y · x.
Proof.
  intros. MI x; simN. rewrite H2; auto.
Qed.

Theorem FAT30a : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x · (y + z) = x · y + x · z.
Proof.
  intros. MI z; simN. rewrite H3, FAT5; auto.
Qed.

Theorem FAT30b : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> (x + y) · z = x · z + y · z.
Proof.
  intros. rewrite FAT29, (FAT29 x), (FAT29 y); auto.
  apply FAT30a; auto.
Qed.

Theorem FAT31 : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x · y · z = x · (y · z).
Proof.
  intros. MI z; simN. rewrite FAT30a, H3; auto.
Qed.

Theorem FAT32a : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> x > y
  -> x · z > y · z.
Proof.
  intros. destruct H2, H2. exists (x0 · z). subst.
  split; auto. apply FAT30b; auto.
Qed.

Theorem FAT32b : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x = y -> x · z = y · z.
Proof.
  intros. subst; auto.
Qed.

Theorem FAT32c : ∀ {x y} z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x < y -> x · z < y · z.
Proof.
  intros. eapply FAT32a; eauto.
Qed.

Theorem FAT33a : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x · z > y · z -> x > y.
Proof.
  intros. destruct (FAT10 H H0) as [H3 | [H3 | H3]]; auto;
  [apply (FAT32b z) in H3| apply (FAT32c z) in H3]; auto; NordF.
Qed.

Theorem FAT33b : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x · z = y · z -> x = y.
Proof.
  intros. destruct (FAT10 H H0) as [H3 | [H3 | H3]]; auto;
  [apply (FAT32a z) in H3| apply (FAT32c z) in H3]; auto; NordF.
Qed.

Theorem FAT33c : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x · z < y · z -> x < y.
Proof.
  intros. eapply FAT33a; eauto.
Qed.

Corollary letiN : ∀ x y z, x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> x ≤ y <-> x · z ≤ y · z.
Proof.
  split; intros; destruct H2; [left |right |left |right]; 
  [apply FAT32a |apply FAT32b |eapply FAT33a |eapply FAT33b];
  eauto.
Qed.

Theorem FAT34 : ∀ x y z u, x > y -> z > u -> x ∈ Nat -> y ∈ Nat
  -> z ∈ Nat -> u ∈ Nat -> x · z > y · u.
Proof.
  intros. apply (FAT32a z) in H; apply (FAT32a y) in H0; auto.
  rewrite FAT29, (FAT29 u) in H0; auto. eapply FAT15; eauto.
Qed.

Theorem FAT35 : ∀ x y z u, x ≥ y /\ z > u \/ x > y /\ z ≥ u -> x ∈ Nat
  -> y ∈ Nat -> z ∈ Nat -> u ∈ Nat -> x · z > y · u.
Proof.
  intros. destruct H as [[[]]|[H []]]; subst.
  - eapply FAT34; eauto.
  - rewrite FAT29, (FAT29 x); auto. apply FAT32a; auto.
  - eapply FAT34; eauto.
  - apply FAT32a; auto.
Qed.

Theorem FAT36 : ∀ x y z u, x ≥ y -> z ≥ u -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> u ∈ Nat -> x · z ≥ y · u.
Proof.
  intros. destruct H.
  - left. apply FAT35; auto.
  - subst. rewrite FAT29, (FAT29 x); auto. apply letiN; auto.
Qed.

Fact MinNd : ∀ x y z, y > x -> x ∈ Nat -> y ∈ Nat -> z ∈ Nat
  -> (y - x) · z = (y · z) - (x · z).
Proof with auto.
  intros. apply (FAT32a z) in H as H3... apply MinNUn...
  rewrite <- FAT30b... apply FAT32b... apply MinNEx...
Qed.

Close Scope Nat_scope.

(*分数*)
(*分数集*)

(* FRACTIONS *)

(* SECTION I Definition and Equivalence *)

Declare Scope FC_scope.

Delimit Scope FC_scope with FC.

Open Scope FC_scope.

Definition FC := Nat × Nat.

Fact EnFC : Ensemble FC.
Proof.
  intros. apply MKT74; apply EnNat.
Qed.

Notation " p ¹ " := (First p)(at level 0) : FC_scope.

Notation " p ² " := (Second p)(at level 0) : FC_scope.

(*等价*)
Definition eqv f1 f2 := (f1¹ · f2²)%Nat = (f2¹ · f1²)%Nat.

Notation " f1 ~ f2 " := (eqv f1 f2): FC_scope.

Fact fr0 : ∀ {a b}, a ∈ Nat -> b ∈ Nat -> [a,b] ∈ FC.
Proof.
  intros. apply AxiomII'; repeat split; auto. rxo.
Qed.

Fact fr1 : ∀ f, f ∈ FC -> f² ∈ Nat.
Proof.
  intros. unfold FC in H. appA2H H. destruct H0 as [x [y[H0[]]]].
  assert (f² = y). { rewrite H0. apply MKT54b; rxo. }
  rewrite H3. auto.
Qed.

Fact fr2 : ∀ f, f ∈ FC -> f¹ ∈ Nat.
Proof.
  intros. unfold FC in H. appA2H H. destruct H0 as [x [y[H0[]]]].
  assert (f¹ = x). { rewrite H0. apply MKT50; rxo. }
  rewrite H3. auto.
Qed.

Global Hint Resolve fr0 fr1 fr2 : core.

Fact fra1 : ∀ x y, x ∈ Nat -> y ∈ Nat -> [x,y]¹ = x.
Proof.
  intros. apply MKT54a; rxo.
Qed.

Fact fra2 : ∀ x y, x ∈ Nat -> y ∈ Nat -> [x,y]² = y.
Proof.
  intros. apply MKT54b; rxo.
Qed.

Ltac Ge := try rewrite fra1 in *; try rewrite fra2 in *; auto 6.

Theorem FAT37 : ∀ f, f ~ f.
Proof.
  intros. red; auto.
Qed.

Theorem FAT38 : ∀ {f1 f2}, f1 ~ f2 -> f2 ~ f1.
Proof.
  intros. red in H|-*. auto.
Qed.

Ltac t37 := 
  match goal with
  |- eqv ?f ?f => apply FAT37
  end.

Ltac t38 := 
  match goal with
  H: eqv ?f1 ?f2
  |- eqv ?f2 ?f1 => apply FAT38; auto
  end.

Ltac frs := try t37; try t38.

Lemma Lemma_FAT39 : ∀ x y z u, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> u ∈ Nat
  -> ((x · y) · (z · u))% Nat = ((x · u) · (z · y))% Nat.
Proof.
  intros. rewrite FAT31, <- (FAT31 y); auto.
  rewrite (FAT29 (y · z)% Nat), <- FAT31, (FAT29 y); auto.
Qed.

Theorem FAT39 : ∀ {f1 f2 f3}, f1 ~ f2 -> f2 ~ f3 -> f1 ∈ FC -> f2 ∈ FC
  -> f3 ∈ FC -> f1 ~ f3.
Proof.
  intros. unfold eqv in *. 
  apply FAT32b with (z:=(f2¹·f3²)%Nat) in H; auto.
  rewrite Lemma_FAT39, H0, (Lemma_FAT39 f2¹),
  (FAT29 (f2¹·f2²)%Nat) in H; auto. apply FAT33b in H; auto.
Qed.

Theorem FAT40 : ∀ f x, f ∈ FC -> x ∈ Nat -> f ~ ([f¹ · x, f² · x]%Nat).
Proof.
  intros. red. rewrite fra1, fra2; auto.
  rewrite FAT31, (FAT29 x); auto.
Qed.

(* SECTION II Ordering *)

Definition gtf f1 f2 := (f1¹ · f2² > f2¹ · f1²)%Nat.

Notation " x > y " := (gtf x y) : FC_scope.

Definition ltf f1 f2 := (f1¹ · f2² < f2¹ · f1²)%Nat.

Notation " x < y " := (ltf x y) : FC_scope.

Theorem FAT41 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC
  -> (f1 ~ f2) \/ (f1 > f2) \/ (f1 < f2).
Proof.
  intros. apply FAT10; auto.
Qed.

Theorem FAT42 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> f1 > f2 -> f2 < f1.
Proof.
  intros. apply FAT11; auto.
Qed.

Theorem FAT43 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> f1 < f2 -> f2 > f1.
Proof.
  intros. apply FAT12; auto.
Qed.

Theorem FAT44 : ∀ {f1 f2 f3 f4}, f1 > f2 -> f1 ~ f3 -> f2 ~ f4
  -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC -> f3 > f4.
Proof with auto.
  intros. unfold eqv, gtf in *.
  apply FAT32b with (z:=(f3¹·f1²)%Nat) in H1...
  pattern (f3¹·f1²)%Nat at 2 in H1; rewrite <- H0 in H1.
  rewrite Lemma_FAT39, (Lemma_FAT39 f4¹) in H1...
  apply FAT32a with (z:=(f4¹·f3²)%Nat) in H...
  rewrite FAT29, <- H1, FAT29 in H...
  rewrite (FAT29 (f2¹·f1²)%Nat) in H... apply FAT33a in H...
Qed.

Theorem FAT45 : ∀ {f1 f2 f3 f4}, f1 < f2 -> f1 ~ f3 -> f2 ~ f4
  -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC -> f3 < f4.
Proof.
  intros. eapply FAT44; eauto.
Qed.

Definition gef f1 f2 := (f1 > f2) \/ (f2 ~ f1).

Notation " x ≳ y " := (gef x y) (at level 55) : FC_scope.

Definition lef f1 f2 := (f1 < f2) \/ (f1 ~ f2).

Notation " x ≲ y " := (lef x y) (at level 55) : FC_scope.

Fact elFf : ∀ {x y}, x < y -> x ~ y -> x ∈ FC -> y ∈ FC -> False.
Proof.
  intros. red in H, H0. NordF.
Qed.

Fact egFf : ∀ {x y}, x > y -> x ~ y -> x ∈ FC -> y ∈ FC -> False.
Proof.
  intros. red in H, H0. NordF.
Qed.

Fact lgFf : ∀ {x y}, x < y -> x > y -> x ∈ FC -> y ∈ FC -> False.
Proof.
  intros. red in H, H0. NordF.
Qed.

Fact legFf : ∀ {x y}, x ≲ y -> x > y -> x ∈ FC -> y ∈ FC -> False.
Proof.
  intros. red in H, H0. unfold ltf, eqv in H. NordF.
Qed.

Ltac ELF :=
  match goal with
    H: ltf ?n1 ?n2
    |- _ => destruct (elFf H); auto
  end.

Ltac EGF :=
  match goal with
    H: gtf ?n1 ?n2
    |- _ => destruct (egFf H); auto
  end.

Ltac LGF :=
  match goal with
    H: ltf ?n1 ?n2
    |- _ => destruct (lgFf H); auto
  end.

Ltac LEGF :=
  match goal with
    H: lef ?n1 ?n2
    |- _ => destruct (legFf H); auto
  end.

Ltac GELF :=
  match goal with
    H: (gef ?n1 ≥ ?n2)%Nat
    |- _ => destruct (legNf H); auto
  end.

Ltac FordF := try ELF; try EGF; try LGF; try LEGF; try GELF.

Theorem FAT46 : ∀ {f1 f2 f3 f4}, f1 ≳ f2 -> f1 ~ f3 -> f2 ~ f4
  -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC -> f3 ≳ f4.
Proof.
  intros. destruct H.
  - left. eapply FAT44; eauto.
  - right. eapply FAT39; eauto. eapply FAT39; eauto. frs.
Qed.

Theorem FAT47 : ∀ {f1 f2 f3 f4}, f1 ≲ f2 -> f1 ~ f3 -> f2 ~ f4
  -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC -> f3 ≲ f4.
Proof.
  intros. eapply FAT46; eauto.
Qed.

Theorem FAT48 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> f1 ≳ f2 -> f2 ≲ f1.
Proof.
  intros. apply FAT13; auto.
Qed.

Theorem FAT49 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> f1 ≲ f2 -> f2 ≳ f1.
Proof.
  intros. apply FAT14; auto.
Qed.

Theorem FAT50 : ∀ {f1 f2 f3}, f1 < f2 -> f2 < f3 -> f1 ∈ FC
  -> f2 ∈ FC -> f3 ∈ FC -> f1 < f3.
Proof with auto.
  intros. unfold ltf in *. apply FAT33c with (z:=(f2¹·f2²)%Nat)...
  rewrite Lemma_FAT39, (FAT29 (f3¹·f1²)%Nat), (Lemma_FAT39 f2¹)...
  eapply FAT34; eauto.
Qed.

Theorem FAT51 : ∀ {f1 f2 f3}, (f1 ≲ f2 /\ f2 < f3) \/ (f1 < f2 /\ f2 ≲ f3)
  -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f1 < f3.
Proof.
  intros; destruct H as [[[|]]|[? [|]]].
  - eapply FAT50; eauto.
  - eapply FAT45; eauto; frs.
  - eapply FAT50; eauto.
  - eapply FAT45; eauto; frs.
Qed.

Theorem FAT52 : ∀ {f1 f2 f3}, f1 ≲ f2 -> f2 ≲ f3 -> f1 ∈ FC -> f2 ∈ FC
  -> f3 ∈ FC -> f1 ≲ f3.
Proof.
  intros; destruct H.
  - left; eapply FAT51; eauto.
  - destruct H0.
    + left; eapply FAT45; eauto; frs.
    + right; eapply FAT39; eauto.
Qed.

Theorem FAT53 : ∀ {f1}, f1 ∈ FC -> ∃ f2, f2 ∈ FC /\ f2 > f1.
Proof with auto.
  intros. exists [f1¹+f1¹,f1²]%Nat. split... red. Ge.
  rewrite FAT30b... apply FAT18...
Qed.

Theorem FAT54 : ∀ {f1}, f1 ∈ FC -> ∃ f2, f2 ∈ FC /\ f2 < f1.
Proof with auto.
  intros. exists [f1¹,f1²+f1²]%Nat. split... red. Ge.
  rewrite FAT30a... apply FAT18...
Qed.

Theorem FAT55 : ∀ {f1 f3}, f1 ∈ FC -> f3 ∈ FC -> f1 < f3
  -> ∃ f2, f2 ∈ FC /\ f1 < f2 /\ f2 < f3.
Proof with auto.
  intros. exists [f1¹+f3¹,f1²+f3²]%Nat. split...
  split; red; Ge; rewrite FAT30a, FAT30b...
  - rewrite FAT6, (FAT6 (f1¹·f1²))%Nat... apply FAT19a...
  - apply FAT19c...
Qed.

(* SECTION III Addition *)

Definition addF f1 f2 := [f1¹·f2²+f2¹·f1²,f1²·f2²]%Nat.

Notation "f1 + f2" := (addF f1 f2) : FC_scope.

Fact AddFp : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> (f1 + f2) ∈ FC.
Proof with auto.
  intros. apply AxiomII'. repeat split... rxo;
  exists Nat...
Qed.

Global Hint Resolve AddFp : core.

Theorem FAT56 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> f4 ∈ FC -> f1 ~ f2 -> f3 ~ f4 -> (f1 + f3) ~ (f2 + f4).
Proof with auto.
  intros. unfold addF, eqv in *. repeat Ge.
  repeat rewrite FAT30b... rewrite (Lemma_FAT39 f4¹), <- H4...
  rewrite (Lemma_FAT39 f3¹), (FAT29 f2² f1²); try apply FAT19b...
  rewrite (FAT29 f2² f4²), Lemma_FAT39, H3...
  repeat rewrite <- FAT31; try apply FAT32b...
  repeat rewrite FAT31... rewrite (FAT29 f4² f1²)...
Qed.
 
Theorem FAT57 : ∀ x x0 x1, x ∈ Nat -> x0 ∈ Nat -> x1 ∈ Nat
  -> eqv (addF ([x0,x]) ([x1,x])) ([x0+x1,x])%Nat.
Proof with auto.
  intros. unfold addF, eqv. repeat Ge.
  rewrite <- FAT30b; try apply FAT31...
Qed.

Theorem FAT58 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> (f1 + f2) ~ (f2 + f1).
Proof with auto.
  intros; unfold addF, eqv. repeat Ge.
  rewrite (FAT6 (f1¹·f2²))%Nat, (FAT29 f1²)...
Qed.

Theorem FAT59 : ∀ {f1 f2 f3}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> ((f1 + f2) + f3) ~ (f1 + (f2 + f3)).
Proof with auto 7.
  intros; unfold addF, eqv. repeat Ge. repeat rewrite FAT30b...
  repeat rewrite FAT31... 
  rewrite <- (FAT31 f1² f3²), (FAT29 f1² f3²), FAT31...
  rewrite <- (FAT31 f1² _ (f1²·(f2²·f3²)))%Nat, 
  (FAT29 f1² f2²), FAT31, FAT5...
Qed.

Theorem FAT60 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> (f1 + f2) > f1.
Proof with auto.
  intros; unfold addF, gtf. repeat Ge.
  rewrite FAT30b, FAT31, (FAT29 f2² f1²)... apply FAT18...
Qed.

Theorem FAT61 : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x > y
  -> (x + z) > (y + z).
Proof with auto.
  intros. unfold gtf, addF in *. repeat Ge.
  repeat rewrite <- FAT31... apply FAT32a...
  rewrite FAT30b, FAT30b, (FAT31 z¹), (FAT29 x²), <- FAT31...
  apply FAT19a... rewrite FAT31, FAT31, (FAT29 z²), (FAT29 z²)...
  rewrite <- FAT31, <- FAT31... apply FAT32a... 
Qed.

Theorem FAT62a : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x > y
  -> (x + z) > (y + z).
Proof.
  intros. apply FAT61; auto.
Qed.

Theorem FAT62b : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x ~ y
  -> (x + z) ~ (y + z).
Proof.
  intros. eapply FAT56; eauto. frs.
Qed.

Theorem FAT62c : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x < y
  -> (x + z) < (y + z).
Proof.
  intros. apply FAT62a; auto.
Qed.

(* Theorem FAT62d : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> 
  x ≲ y -> (x + z) ≲ (y + z).
Proof.
  intros. destruct H2;
  [left; apply FAT62a|right; apply FAT62b]; auto.
Qed. *)

Theorem FAT63a : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> (x + z) > (y + z)
  -> x > y.
Proof.
  intros. destruct (FAT41 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT62b with (z:=z) in H3; auto. FordF.
  - apply FAT62c with (z:=z) in H3; auto. FordF.
Qed.

Theorem FAT63b : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> (x + z) ~ (y + z)
  -> x ~ y .
Proof.
  intros. destruct (FAT41 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT62a with (z:=z) in H3; auto. FordF.
  - apply FAT62c with (z:=z) in H3; auto. FordF.
Qed.

Theorem FAT63c : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> (x + z) < (y + z)
  -> x < y.
Proof.
  intros. eapply FAT63a; eauto.
Qed. 

Theorem FAT64 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> f1 > f2 -> f3 > f4 -> (f1 + f3) > (f2 + f4).
Proof with auto.
  intros. apply (FAT61 _ _ f3) in H3; apply (FAT61 _ _ f2) in H4...
  apply (@ FAT44 _ _ (addF f1 f3) (addF f3 f2)) in H3; frs;
  try apply FAT58...
  apply (@ FAT44 _ _ (addF f3 f2) (addF f2 f4)) in H4; frs;
  try apply FAT58... eapply FAT50; eauto.
Qed.

Theorem FAT65 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> (f1 ≳ f2 /\ f3 > f4) \/ (f1 > f2 /\ f3 ≳ f4) -> (f1 + f3) > (f2 + f4).
Proof with auto.
  intros. destruct H3 as [[[H3 | H5] H4] | [H3 [H4 | H5]]].
  - apply FAT64; auto. 
  - apply FAT62a with (z:=f1) in H4;
    apply FAT62b with (z:=f4) in H5...
    eapply FAT44; eauto; try apply FAT58... apply FAT38.
    eapply FAT39; eauto; try apply FAT58...
  - apply FAT64; auto.
  - apply FAT62a with (z:=f3) in H3;
    apply FAT62b with (z:=f2) in H5...
    eapply FAT44; eauto; frs. pose proof (FAT58 H0 H1).
    eapply FAT39; eauto. apply FAT38. clear H4.
    eapply FAT39; eauto. apply FAT58...
Qed.

Theorem FAT66 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> f1 ≳ f2 -> f3 ≳ f4 -> (f1 + f3) ≳ (f2 + f4).
Proof with auto.
  intros. destruct H3.
  - left. apply FAT65...
  - destruct H4.
    + left. apply FAT65; unfold gef...
    + right. apply FAT56...
Qed.

Definition minF f1 f2 := [(f1¹·f2²) - (f2¹·f1²),f1²·f2²]%Nat.

Notation " x - y " := (minF x y) : FC_scope.

Fact MinFp : ∀ {f1 f2}, f2 > f1 -> f1 ∈ FC -> f2 ∈ FC -> (f2 - f1) ∈ FC.
Proof.
  intros. unfold minF. apply AxiomII'. repeat split; auto. rxo;
  exists Nat; auto.
Qed.

Global Hint Resolve MinFp : core.

Fact MinFT : ∀ f1 f2 f3, f3 > f1 -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> (f1 + f2) ~ f3 <-> f2 ~ (f3 - f1).
Proof with auto.
  intros. unfold eqv, addF, minF. repeat Ge. split; intros.
  - rewrite MinNd... apply MinNT; [apply FAT32a|..]...
    rewrite FAT30b in H3... do 2 rewrite FAT31 in H3...
    rewrite (FAT29 f2²), (FAT29 f1²) in H3...
    repeat rewrite FAT31...
  - rewrite MinNd in H3...
    apply MinNT in H3; [idtac|apply FAT32a|..]...
    do 2 rewrite FAT31 in H3... rewrite FAT30b...
    repeat rewrite FAT31... rewrite (FAT29 f2²), (FAT29 f1²)... 
Qed.

Fact MinFEx : ∀ {f1 f2}, f2 > f1 -> f1 ∈ FC -> f2 ∈ FC
  -> (f1 + (f2 - f1)) ~ f2.
Proof with auto.
  intros. unfold eqv, addF. Ge... unfold minF. Ge...
  rewrite <- FAT31, <- FAT30b, <- FAT31, (FAT29 f2²),
  <- (FAT31 _ f1²), MinNEx...
Qed.

Fact MinFUn : ∀ f1 f2 f3, f3 > f1 -> f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> (f1 + f2) ~ f3 -> f2 ~ (f3 - f1).
Proof.
  intros. apply FAT38 in H3. pose proof (MinFEx H H0 H2).
  eapply FAT39 in H3; eauto. pose proof (FAT58 H0 H1).
  eapply FAT39 in H5; eauto. pose proof (FAT58 H0 (MinFp H H0 H2)).
  apply FAT38 in H5. eapply FAT39 in H6; eauto.
  apply FAT63b in H6; auto.
Qed.

Theorem FAT67a : ∀ {f1 f2}, f2 > f1 -> f1 ∈ FC -> f2 ∈ FC
  -> ∃ f3, f3 ∈ FC /\ (f1 + f3) ~ f2.
Proof.
  intros. exists (minF f2 f1). split; auto. apply MinFEx; auto.
Qed.

Theorem FAT67b : ∀ {f1 f2 f3 f4}, f2 > f1 -> f1 ∈ FC -> f2 ∈ FC
  -> f3 ∈ FC -> f4 ∈ FC -> (f1 + f3) ~ f2 -> (f1 + f4) ~ f2 -> f3 ~ f4.
Proof.
  intros. apply MinFUn in H4; apply MinFUn in H5; auto.
  apply FAT38 in H5. eapply FAT39; eauto.
Qed.

(* SECTION IV Multiplication *)

Definition mulF f1 f2 := [f1¹ · f2¹, f1² · f2²]%Nat.

Notation " x · y " := (mulF x y)(at level 40) : FC_scope.

Fact MulFp : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> (f1 · f2) ∈ FC.
Proof with auto.
  intros. apply AxiomII'; repeat split... rxo;
  exists Nat...
Qed.

Global Hint Resolve MulFp : core.

Lemma Lemma_FAT68 : ∀ x y z u, x ∈ Nat -> y ∈ Nat -> z ∈ Nat -> u ∈ Nat
  -> ((x · y) · (z · u) = (x · z) · (y · u))%Nat.
Proof with auto.
 intros; repeat rewrite <- FAT31; try apply FAT32b...
 repeat rewrite FAT31; try rewrite (FAT29 z)...
Qed.

Theorem FAT68 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> f4 ∈ FC -> f1 ~ f2 -> f3 ~ f4 -> (f1 · f3) ~ (f2 · f4).
Proof with auto.
  intros. unfold mulF, eqv in *. repeat Ge.
  apply FAT32b with (z:=(f3¹·f4²)%Nat) in H3...
  pattern (f3¹·f4²)%Nat at 2 in H3;
  rewrite H4, Lemma_FAT68 in H3...
  rewrite H3; apply Lemma_FAT68...
Qed.

Theorem FAT69 : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> (f1 · f2) ~ (f2 · f1).
Proof with auto.
  intros. unfold mulF, eqv in *. repeat Ge.
  rewrite (FAT29 f1² f2²); try (apply FAT32b, FAT29)...
Qed.

Theorem FAT70 : ∀ {f1 f2 f3}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> ((f1 · f2) · f3) ~ (f1 · (f2 · f3)).
Proof with auto.
  intros; unfold mulF, eqv. repeat Ge. repeat rewrite FAT31...
Qed.

Theorem FAT71 : ∀ {f1 f2 f3}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> (f1 · (f2 + f3)) ~ ((f1 · f2) + (f1 · f3)).
Proof with auto 6.
  intros; unfold mulF, addF, eqv.
  repeat Ge. rewrite FAT30a, FAT30b, FAT30b,
  (FAT31 _ f2¹), (FAT29 f1² f3²), (FAT31 _ f3¹)...
  pattern (f1² · f2²)%Nat at 3. rewrite (FAT29 f1² f2²)...
  rewrite (FAT29 _ (f2²·f3²)%Nat)... repeat rewrite <- FAT31... 
Qed.

Theorem FAT72a : ∀ {x y} z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x > y
  -> (x · z) > (y · z).
Proof with auto.
  intros. unfold gtf, mulF in *. repeat Ge.
  repeat rewrite <- FAT31... apply FAT32a...
  repeat rewrite FAT31... rewrite (FAT29 z¹), (FAT29 z¹)...
  repeat rewrite <- FAT31... apply FAT32a... 
Qed.

Theorem FAT72b : ∀ {x y} z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x ~ y
  -> (x · z) ~ (y · z).
Proof.
  intros. eapply FAT68; eauto. frs.
Qed.

Theorem FAT72c : ∀ {x y} z, x ∈ FC -> y ∈ FC -> z ∈ FC -> x < y
  -> (x · z) < (y · z).
Proof.
  intros. apply FAT72a; auto.
Qed.

Theorem FAT73a : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> (x · z) > (y · z)
  -> x > y.
Proof.
  intros. destruct (FAT41 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT72b with (z0:=z) in H3; auto. FordF.
  - apply FAT72c with (z0:=z) in H3; auto. FordF.
Qed.

Theorem FAT73b : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> (x · z) ~ (y · z)
  -> x ~ y .
Proof.
  intros. destruct (FAT41 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT72a with (z0:=z) in H3; auto. FordF.
  - apply FAT72c with (z0:=z) in H3; auto. FordF.
Qed.

Theorem FAT73c : ∀ x y z, x ∈ FC -> y ∈ FC -> z ∈ FC -> (x · z) < (y · z)
  -> x < y.
Proof.
  intros. eapply FAT73a; eauto.
Qed.

Theorem FAT74 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> f1 > f2 -> f3 > f4 -> (f1 · f3) > (f2 · f4).
Proof with auto.
  intros. apply (FAT72a f3) in H3; apply (FAT72a f2) in H4...
  eapply FAT50; eauto. eapply FAT44; eauto; apply FAT69...
Qed.

Theorem FAT75 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> (f1 ≳ f2 /\ f3 > f4) \/ (f1 > f2 /\ f3 ≳ f4) -> (f1 · f3) > (f2 · f4).
Proof with auto.
  intros. destruct H3 as [[[H3 | H5] H4] | [H3 [H4 | H5]]].
  - apply FAT74; auto.
  - apply FAT72a with (z:=f1) in H4;
    apply FAT72b with (z:=f4) in H5...
    eapply FAT44; eauto; [apply FAT69|]... apply FAT38.
    eapply FAT39; eauto. apply FAT69...
  - apply FAT74; auto.
  - apply FAT72a with (z:=f3) in H3;
    apply FAT72b with (z:=f2) in H5... eapply FAT44; eauto; frs.
    eapply FAT39; try apply FAT69; eauto.
    apply FAT38. eapply FAT39; eauto. apply FAT69...
Qed.

Theorem FAT76 : ∀ {f1 f2 f3 f4}, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> f1 ≳ f2 -> f3 ≳ f4 -> (f1 · f3) ≳ (f2 · f4).
Proof with auto.
  intros. destruct H3.
  - left. apply FAT75...
  - destruct H4.
    + left. apply FAT75; unfold gef...
    + right. apply FAT68...
Qed.

Theorem FAT77a : ∀ f1 f2, f1 ∈ FC -> f2 ∈ FC
  -> ∃ f3, f3 ∈ FC /\ (f2 · f3) ~ f1.
Proof.
  intros. exists [(f1¹ · f2²), (f1² · f2¹)]%Nat. split.
  - auto.
  - red. unfold mulF. repeat Ge.
    rewrite (FAT29 f1² _); auto. repeat rewrite <- FAT31; auto.
    assert (((f2¹ · f1¹) · f2²) = ((f1¹ · f2²) · f2¹))%Nat.
    { rewrite FAT31; auto. apply FAT29; auto. } rewrite H1; auto.
Qed.

Theorem T77b : ∀ f1 f2 f3 f4, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC -> f4 ∈ FC
  -> (f2 · f3) ~ f1 -> (f2 · f4) ~ f1 -> f3 ~ f4.
Proof.
  intros. pose proof (FAT39 H3 (FAT38 H4)).
  apply FAT73b with (z:=f2); auto. 
  apply (@ FAT39 _ (f2·f3)); auto. apply FAT69; auto.
  apply (@ FAT39 _ (f2·f4)); auto. apply FAT69; auto.
Qed.

Definition divF f1 f2 := f1 · ([f2², f2¹]).

Fact DivFp : ∀ f1 f2, f1 ∈ FC -> f2 ∈ FC -> (divF f1 f2) ∈ FC.
Proof.
  intros; unfold divF; auto.
Qed.

Global Hint Resolve DivFp : core.

Fact DivFEx : ∀ {f1 f2}, f1 ∈ FC -> f2 ∈ FC -> (f1 · (divF f2 f1)) ~ f2.
Proof with auto 8.
  intros. unfold eqv, divF, mulF. repeat Ge...
  rewrite FAT31, FAT29, FAT31, FAT31...
Qed.

Fact DivFUn : ∀ f1 f2 f3, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> (f1 · f2) ~ f3 -> f2 ~ (divF f3 f1).
Proof with auto.
  intros. unfold eqv, divF, mulF in *. repeat Ge...
  rewrite FAT31, <- H2, FAT29, (FAT29 _ f3²), FAT31...
Qed.

Fact DivFT : ∀ f1 f2 f3, f1 ∈ FC -> f2 ∈ FC -> f3 ∈ FC
  -> (f1 · f2) ~ f3 <-> f2 ~ (divF f3 f1).
Proof with auto.
  intros. unfold eqv, divF, mulF. repeat Ge. split; intros.
  - rewrite FAT31, <- H2, FAT29, (FAT29 _ f3²), FAT31...
  - rewrite <- FAT31, <- H2, FAT31, (FAT29 f1¹), FAT31...
Qed.

Close Scope FC_scope.

(* SECTION V Rational Numbers and Integers *)

(*有理数*)
Declare Scope rC_scope.

Delimit Scope rC_scope with rC.

Open Scope rC_scope.

(*有理数集*)
Definition rC :=
  \{λ S, ∃ F, F ∈ FC /\ S = \{λ f, f ∈ FC /\ f ~ F \} \}%FC.

(*与f等价的类组成的集合*)
Definition eqf F := \{ λ f, f ∈ FC /\ f ~ F \}%FC.

Fact EnrC : Ensemble rC.
Proof.
  apply MKT33 with (x:=pow(FC)).
  - apply MKT38a, EnFC.
  - red; intros. apply AxiomII in H as [H [F []]].
    apply AxiomII; split; auto. red; intros.
    subst. apply AxiomII in H2 as [H2 []]; auto.
Qed.

Fact finr : ∀ {f r}, f ∈ r -> r ∈ rC -> f ∈ FC.
Proof.
  intros. apply AxiomII in H0 as [_ [F []]]; subst.
  apply AxiomII in H; tauto.
Qed.

Global Hint Resolve finr : core.

Fact rne : ∀ {r}, r ∈ rC -> ∃ F, F ∈ r.
Proof.
  intros. apply AxiomII in H as [_ [f []]]; subst.
  exists f. apply AxiomII. repeat split; rxo.
Qed.

Ltac gef H f := destruct (rne H) as [f].

Fact finF : ∀ {r F}, r ∈ rC -> F ∈ r -> r = \{λ f, f ∈ FC /\ f ~ F \}%FC .
Proof.
  intros. apply AxiomII in H as [_ [f []]]. subst.
  apply AxiomII in H0 as [_ []]. apply AxiomI; split; intros; 
  apply AxiomII in H2 as [H2 []]; [apply FAT38 in H1; auto|];
  eapply FAT39 in H1; eauto; apply AxiomII; auto.
Qed.

Theorem FAT78 : ∀ r, r ∈ rC -> r = r.
Proof.
  auto.
Qed.

Theorem FAT79 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> r1 = r2 -> r2 = r1.
Proof.
  auto.
Qed.

Theorem FAT80 : ∀ r1 r2 r3, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> r1 = r2 -> r2 = r3 -> r1 = r3.
Proof.
  intros. rewrite H2; auto.
Qed.

Definition gtr r1 r2 := ∀ f1 f2, f1 ∈ r2 -> f2 ∈ r1 -> (f2 > f1)%FC.

Notation " x > y " := (gtr x y) : rC_scope.

Definition ltr r1 r2 := ∀ f1 f2, f1 ∈ r1 -> f2 ∈ r2 -> (f1 < f2)%FC.

Notation " x < y " := (ltr x y) : rC_scope.

Theorem FAT81 : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC
  -> r1 = r2 \/ r1 > r2 \/ r1 < r2.
Proof.
  intros. apply AxiomII in H as [_ [f1 []]].
  apply AxiomII in H0 as [_ [f2 []]]. subst. 
  destruct (FAT41 H H0) as [H3 | [H3 | H3]].
  - left. apply AxiomI; split; intros;
    apply AxiomII in H1 as [H1 []]; 
    apply AxiomII; repeat split; auto.
    + eapply FAT39; eauto.
    + apply FAT38 in H3. eapply FAT39; eauto.
  - right; left; red; intros. apply AxiomII in H1 as [H1 []].
    apply AxiomII in H2 as [H2 []].
    eapply FAT44; eauto; apply FAT38; auto.
  - right; right; red; intros.
    apply AxiomII in H1 as [H1 []]. apply AxiomII in H2 as [H2 []].
    eapply FAT44; eauto; apply FAT38; auto.
Qed.

Theorem FAT82 : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> r1 > r2 -> r2 < r1.
Proof.
  auto.
Qed.

Theorem FAT83 : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> r1 < r2 -> r2 > r1.
Proof.
  auto.
Qed.

Definition ger r1 r2 := (r1 > r2) \/ (r2 = r1).

Notation " x ≥ y " := (ger x y)(at level 77) : rC_scope.

Definition ler r1 r2 := (r1 < r2) \/ (r1 = r2).

Notation " x ≤ y " := (ler x y)(at level 77) : rC_scope.

Fact elrf : ∀ {x y}, x < y -> x = y -> x ∈ rC -> y ∈ rC -> False.
Proof.
  intros. subst. gef H1 r. apply (finr H0) in H1.
  pose proof (H _ _ H0 H0). FordF.
Qed.

Fact egrf : ∀ {x y}, x > y -> x = y -> x ∈ rC -> y ∈ rC -> False.
Proof.
  intros. symmetry in H0. eapply elrf; eauto.
Qed.

Fact lgrf : ∀ {x y}, x < y -> x > y -> x ∈ rC -> y ∈ rC -> False.
Proof.
  intros. gef H1 r1. gef H2 r2. apply (finr H3) in H1.
  apply (finr H4) in H2. pose proof (H _ _ H3 H4).
  pose proof (H0 _ _ H4 H3). FordF.
Qed.

Fact legrf : ∀ {x y}, x ≤ y -> x > y -> x ∈ rC -> y ∈ rC -> False.
Proof.
  intros. destruct H; [eapply lgrf|eapply egrf]; eauto.
Qed.

Ltac ELr :=
  match goal with
    H: ltr ?n1 ?n2
    |- _ => destruct (elrf H); auto
  end.

Ltac EGr :=
  match goal with
    H: gtr ?n1 ?n2
    |- _ => destruct (egrf H); auto
  end.

Ltac LGr :=
  match goal with
    H: ltr ?n1 ?n2
    |- _ => destruct (lgrf H); auto
  end.

Ltac LEGr :=
  match goal with
    H: ler ?n1 ?n2
    |- _ => destruct (legrf H); auto
  end.

Ltac GELr :=
  match goal with
    H: ger ?n1 ?n2
    |- _ => destruct (legrf H); auto
  end.

Ltac rordF := try ELr; try EGr; try LGr; try LEGr; try GELr.

Theorem FAT84 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> r1 ≥ r2 -> r2 ≤ r1.
Proof.
  auto.
Qed.

Theorem FAT85 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> r1 ≤ r2 -> r2 ≥ r1.
Proof.
  auto.
Qed.

Fact RF0a : ∀ f , f ∈ FC -> f ∈ eqf f.
Proof.
  intros. appA2G. split; auto. apply FAT37.
Qed.

Fact RF0b : ∀ f f1 , f ∈ eqf f1 -> f ∈ FC.
Proof.
  intros. appA2H H. tauto.
Qed.

Global Hint Resolve RF0b : core.

Fact RF1 : ∀ X , X ∈ rC -> exists f, f ∈ X /\ f ∈ FC.
Proof.
  intros. appA2H H. destruct H0 as [f[]]. rewrite H1. exists f.
  split; auto. apply RF0a; auto.
Qed.

Fact RF2 :  ∀ f1 f2 , f1 ∈ FC -> f2 ∈ FC -> (f1 ~ f2)%FC
  -> eqf f1 = eqf f2.
Proof.
  intros. apply AxiomI. split; intros.
  - unfold eqf in *. appA2H H2. appA2G. split.
    + tauto.
    + destruct H3. eapply FAT39; eauto.
  - unfold eqf in *. appA2H H2. appA2G. split.
    + tauto.
    + destruct H3. eapply FAT39; eauto. apply FAT38; auto.
Qed.

Fact RF3 : ∀ X f , X ∈ rC -> f ∈ FC -> f ∈ X -> X = eqf f.
Proof.
  intros. appA2H H. destruct H2 as [f1[]]. rewrite H3 in H1.
  appA2H H1. destruct H4. apply RF2 in H5; auto. rewrite H5; auto.
Qed.

Fact RF4 : ∀ X , X ∈ rC -> exists f, f ∈ X /\ f ∈ FC /\ X = eqf f.
Proof.
  intros. New H. apply RF1 in H. destruct H as [f[]]. exists f.
  repeat split; auto. apply RF3; auto.
Qed.

Ltac RF :=
  match goal with
    | H: ?X ∈ rC
      |- _ => apply RF4 in H; destruct H as [?f [? [? ?]]]; RF 
    | H: ?X = eqf ?f
      |- _ => rewrite H; RF
    | |- _ => idtac
  end.

Theorem FAT86 : ∀ r1 r2 r3, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros. red. intros. red in H2,H3. RF. 
  eapply FAT50; eauto; rewrite H11 in H4;
  rewrite H7 in H5; eauto.
Qed.

Theorem FAT87 : ∀ r1 r2 r3, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> (r1 ≤ r2 /\ r2 < r3) \/ (r1 < r2 /\ r2 ≤ r3) -> r1 < r3.
Proof.
  intros. destruct H2 as [[[|]H3]|[H3[|]]].
  - apply FAT86 with r2; auto.
  - rewrite H2; auto.
  - apply FAT86 with r2; auto.
  - rewrite H2 in H3; auto.
Qed.

Theorem FAT88 : ∀ r1 r2 r3, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> r1 ≤ r2 -> r2 ≤ r3 -> r1 ≤ r3.
Proof.
  intros. red. destruct H2,H3.
  - left; apply FAT86 with r2; auto.
  - rewrite H3 in H2; tauto.
  - rewrite H2; tauto.
  - rewrite H2; tauto.
Qed.

Theorem FAT89 : ∀ r1, r1 ∈ rC -> ∃ r2, r2 ∈ rC /\ r2 > r1.
Proof.
  intros. RF. apply FAT53 in H0. destruct H0 as [f0[]].
  exists (eqf f0). split.
  - appA2G. assert (eqf f0 ⊂ FC).
    { red. intros. appA2H H3. tauto. }
    eapply MKT33. apply EnFC. auto.
  - red. intros. appA2H H3. appA2H H4. destruct H5,H6.
    eapply FAT44; eauto; try t38. rewrite H1 in H; eauto.
Qed.

Theorem FAT90 : ∀ r1, r1 ∈ rC -> ∃ r2, r2 ∈ rC /\ r2 < r1.
Proof.
  intros. RF. apply FAT54 in H0. destruct H0 as [f0[]].
  exists (eqf f0). split.
  - appA2G. assert (eqf f0 ⊂ FC).
    { red. intros. appA2H H3. tauto. }
    eapply MKT33. apply EnFC. auto.
  - red. intros. appA2H H3. appA2H H4. destruct H5,H6.
    eapply FAT45; eauto;  try t38. rewrite H1 in H; eauto.
Qed.

Theorem FAT91 : ∀ r1 r2,  r1 ∈ rC -> r2 ∈ rC -> r1 < r2
  -> ∃ r3, r3 ∈ rC /\ r1 < r3 /\ r3 < r2.
Proof.
  intros. RF. red in H1. assert (f0 < f)%FC. { apply H1; auto. }
  apply FAT55 in H6; auto. destruct H6 as [f3[H6[H7]]].
  exists (eqf f3). split.
  - appA2G. assert (eqf f3 ⊂ FC).
    { red. intros. appA2H H9. tauto. }
    eapply MKT33. apply EnFC. auto.
  - split.
    + red. intros. appA2H H9; appA2H H10. destruct H11,H12.
      eapply FAT45; auto. apply H7. t38. t38. auto. auto.
    + red. intros. appA2H H9; appA2H H10. destruct H11,H12.
      eapply FAT45; eauto; t38.
Qed.

Definition addr r1 r2 := \{ λ f, f ∈ FC
  /\ ∃ f1 f2, f1 ∈ r1 /\ f2 ∈ r2 /\ f ~ (f1 + f2) \}%FC.

Notation "r1 + r2" := (addr r1 r2) : rC_scope.

Fact Addrp : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> (r1 + r2) ∈ rC.
Proof with auto.
  intros. apply AxiomII; split.
  - apply MKT33 with (x:=FC); [apply EnFC|].
    red; intros. apply AxiomII in H1. tauto.
  - apply AxiomII in H as [_ [f1 []]].
    apply AxiomII in H0 as [_ [f2 []]].
    exists (addF f1 f2). split...
    apply AxiomI; split; intros; subst.
    + apply AxiomII in H3 as [H3 [f3 [f4 [? [? []]]]]].
      apply AxiomII in H1 as [_ []]. apply AxiomII in H2 as [_ []].
      apply AxiomII; repeat split...
      eapply FAT39; eauto. apply FAT56...
    + apply AxiomII in H3 as [H3 []]. apply AxiomII; repeat split...
      exists f1, f2; repeat split; auto; apply AxiomII;
      repeat split; rxo.
Qed.

Global Hint Resolve Addrp : core.

Theorem FAT92 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> r1 + r2  = r2 + r1.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1 [f1 [f2 [? [? []]]]]].
    apply (finr H2) in H; apply (finr H3) in H0.
    pose proof (FAT58 H H0). eapply FAT39 in H5; eauto.
    apply AxiomII; repeat split; auto. exists x, f2. auto.
  - apply AxiomII in H1 as [H1 [f1 [f2 [? [? []]]]]].
    apply (finr H2) in H0; apply (finr H3) in H.
    pose proof (FAT58 H0 H). eapply FAT39 in H5; eauto.
    apply AxiomII; repeat split; auto. exists x, f2; auto.
Qed.

Fact RF5 : ∀ X f1 f2 , X ∈ rC -> f1 ∈ X -> f2 ∈ X -> (f1 ~ f2)%FC.
Proof.
  intros. RF. rewrite H3 in H0,H1. appA2H H0. appA2H H1. 
  destruct H4,H5. eapply FAT39; eauto. t38.
Qed.

Fact RF6 : ∀ X f1 f2 , X ∈ rC -> f1 ∈ X -> f2 ∈ FC -> (f1 ~ f2)%FC
  -> f2 ∈ X.
Proof.
  intros. appA2H H. destruct H3 as [f[]]. subst. appA2H H0.
  destruct H4. appA2G. split; auto. eapply FAT39; eauto. t38.
Qed.

Global Hint Resolve RF5 : core.

Fact RFp : ∀ X Y f1 f2 , X ∈ rC -> Y ∈ rC -> X = eqf f1 -> Y = eqf f2
  -> f1 ∈ FC -> f2 ∈ FC -> f1 ∈ X -> f2 ∈ Y
  -> ∃ f, f ∈ X + Y /\ f ∈ FC /\ (f ~ (f1 + f2))%FC /\ (X + Y) = eqf f.
Proof.
  intros. exists (f1 + f2)%FC. repeat split; auto.
  - unfold addr. appA2G. split; auto. exists f1, f2.
    repeat split; auto.
  - unfold eqf. apply AxiomI. split; intros.
    + appA2G. appA2H H7. destruct H8 as [H8[f3[f4[H11[]]]]].
      split; auto. assert ((f3 + f4) ~ (f1 + f2))%FC.
      { eapply FAT56; eauto. } eapply FAT39; eauto.
    + appA2G. appA2H H7. destruct H8. split; auto. exists f1,f2.
      repeat split; auto.
Qed.

Ltac PRF X Y f1 f2 := pose proof RFp X Y f1 f2; MP.

Ltac rprH X Y:= 
  match goal with
      H: X ∈ rC,
      H1: Y ∈ rC
    |- _ => assert ((X + Y) ∈ rC) by auto
  end.

Theorem FAT93 : ∀ {r1 r2 r3}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> ((r1 + r2) + r3) = (r1 + (r2 + r3)).
Proof.
  intros. pose proof RF4 _ H as [f1[H2[H3]]].
  pose proof RF4 _ H0 as [f2[H5[H6]]].
  pose proof RF4 _ H1 as [f3[H8[H9]]].
  PRF r1 r2 f1 f2. PRF r2 r3 f2 f3. 
  destruct H11 as [f12[H11[H13[H14]]]].
  destruct H12 as [f23[H12[H16[H17]]]].
  rprH r1 r2. rprH r2 r3. PRF (r1 + r2) r3 f12 f3.
  PRF r1 (r2 + r3) f1 f23.
  destruct H21 as [f0[H21[H23[H24]]]].
  destruct H22 as [f[H22[H26[H27]]]].
  rewrite H25. rewrite H28. apply RF2; auto.
  assert ((f12 + f3) ~ ((f1 + f2) + f3))%FC.
  { eapply FAT56; eauto. }
  assert ((f1 + f23) ~ (f1 + (f2 + f3)))%FC.
  { eapply FAT56; eauto. }
  eapply FAT39; eauto. eapply FAT39; eauto.
  assert (f1 + f2 + f3 ~ (f1 + (f2 + f3)))%FC.
  { apply FAT59; auto. } eapply FAT39; eauto.
  assert (f1 + (f2 + f3) ~ (f1 + f23))%FC. t38.
  eapply FAT39; eauto. t38.
Qed.

Lemma Lemma_FAT94 : ∀ f1 f2, f1 ∈ FC -> f2 ∈ FC
  -> (f1 > f2)%FC <-> eqf f1 > eqf f2.
Proof.
  split; intros.
  - red. intros. appA2H H2. appA2H H3. destruct H4,H5.
    eapply FAT44; eauto; t38.
  - red in H1. apply H1; appA2G; split; auto; t37.
Qed.

Theorem FAT94 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> r1 + r2 > r1.
Proof.
  intros. pose proof RF4 _ H as [f1[H2[H3]]].
  pose proof RF4 _ H0 as [f2[H5[H6]]]. PRF r1 r2 f1 f2.
  destruct H7 as [f[H7[H8[H9]]]]. rewrite H10. rewrite H1.
  apply Lemma_FAT94; auto. pose proof @ FAT60 f1 f2. MP.
  eapply FAT44; eauto. t38.
Qed.

Theorem FAT95 : ∀ r1 r2 r3, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> r1 > r2 -> r1 + r3 > r2 + r3.
Proof.
  intros. pose proof RF4 _ H as [f1[H3[H4]]].
  pose proof RF4 _ H0 as [f2[H6[H7]]]. 
  pose proof RF4 _ H1 as [f3[H9[H10]]].
  PRF r1 r3 f1 f3. PRF r2 r3 f2 f3.
  destruct H12 as [f13[H12[H14[H15]]]].
  destruct H13 as [f23[H13[H17[H18]]]].
  rewrite H16,H19. apply Lemma_FAT94; auto.
  rewrite H5,H8 in H2. apply <- Lemma_FAT94 in H2; auto.
  pose proof FAT61 f1 f2 f3. MP.
  eapply FAT44; eauto; t38.
Qed.

Theorem FAT96a : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> x > y -> (x + z) > (y + z).
Proof with auto.
  intros. red; intros. apply AxiomII in H3 as [_[?[f3[f4[?[]]]]]].
  apply AxiomII in H4 as [_ [? [f5 [f6 [? []]]]]].
  rewrite (finF H1 H6) in H9. apply AxiomII in H9 as [_ []].
  pose proof (H2 _ _ H5 H8).
  apply finr in H8; apply finr in H6; apply finr in H5...
  apply FAT62a with (z:=f6) in H12...
  assert (gtf (addF f5 f6) (addF f3 f4)).
  { eapply FAT44; eauto; [apply FAT37|].
    apply FAT56... apply FAT37. }
  clear H2. apply FAT38 in H7. apply FAT38 in H10.
  eapply FAT44; eauto.
Qed.

Theorem FAT96b : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> x = y -> (x + z) = (y + z).
Proof.
  intros. subst; auto.
Qed.

Theorem FAT96c : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> x < y -> (x + z) < (y + z).
Proof.
  intros. apply FAT96a; auto.
Qed.

Theorem FAT97a : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> (x + z) > (y + z) -> x > y.
Proof.
  intros. destruct (FAT81 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT96b with (z:=z) in H3; auto. rordF.
  - apply FAT96c with (z:=z) in H3; auto. rordF.
Qed.

Theorem FAT97b : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> (x + z) = (y + z) -> x = y .
Proof.
  intros. destruct (FAT81 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT96a with (z:=z) in H3; auto. rordF.
  - apply FAT96c with (z:=z) in H3; auto. rordF.
Qed.

Theorem FAT97c : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> (x + z) < (y + z) -> x < y.
Proof.
  intros. eapply FAT97a; eauto.
Qed.

Theorem FAT98 : ∀ {r1 r2 r3 r4}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> r1 > r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof.
  intros. pose proof FAT96a r1 r2 r3. MP.
  assert (r2 + r3 ∈ rC). auto.
  eapply FAT86; eauto. apply FAT82; auto. rewrite FAT92; auto.
  rewrite @ FAT92 with r2 r4; auto. eapply FAT96a; auto.
Qed.

Theorem FAT99 : ∀ r1 r2 r3 r4, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> (r1 ≥ r2 /\ r3 > r4) \/ (r1 > r2 /\ r3 ≥ r4) -> r1 + r3 > r2 + r4.
Proof.
  intros. destruct H3 as [[[H3 | H4] H5] | [H3 [H5 | H4]]].
  - apply FAT98; auto.
  - rewrite H4. rewrite FAT92; auto.
    rewrite @ FAT92 with r1 r4; auto. apply FAT96a; auto.
  - apply FAT98; auto.
  - rewrite H4. apply FAT96a; auto.
Qed.

Theorem FAT100 : ∀ r1 r2 r3 r4, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> (r1 ≥ r2 /\ r3 ≥ r4) -> r1 + r3 ≥ r2 + r4.
Proof.
  intros. destruct H3 as [[|][|]].
  - left. apply FAT98; auto.
  - left. rewrite H4. apply FAT96a; auto.
  - left. rewrite H3. rewrite FAT92; auto.
    rewrite @ FAT92 with r1 r4; auto. apply FAT96a; auto.
  - right. rewrite H3,H4. auto.
Qed.

Theorem FAT101a : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> r1 > r2
  -> ∃ r3, r3 ∈ rC /\ (r2 + r3) = r1.
Proof.
  intros. pose proof RF4 _ H as [f1[H3[H4]]].
  pose proof RF4 _ H0 as [f2[H5[H6]]].
  rewrite H2,H7 in H1. apply Lemma_FAT94 in H1; auto.
  apply FAT67a in H1; auto. destruct H1 as [f[]].
  exists (eqf f). split.
  - appA2G. assert ((eqf f) ⊂ FC ).
    { red. intros. appA2H H9. tauto. }
    eapply MKT33. apply EnFC. auto.
  - rewrite H2,H7. apply AxiomI. split; intros.
    + appA2H H9. appA2G. destruct H10. split; auto.
      destruct H11 as [f3[f4[H11[]]]].
      appA2H H11. appA2H H12. destruct H14,H15.
      pose proof @ FAT56 f3 f2 f4 f. MP.
      eapply FAT39; eauto. eapply FAT39; eauto.
    + appA2H H9. appA2G. destruct H10. split; auto.
      exists f2, f. repeat split; try apply RF0a; auto.
      eapply FAT39; eauto. t38.
Qed.

Theorem T101b : ∀ r1 r2 r3 r4, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> (r2 + r4) = r1 -> (r2 + r3) = r1 -> r3 = r4.
Proof.
  intros. rewrite <- H3 in H4. rewrite FAT92 in H4; auto.
  rewrite @ FAT92 with r2 r4 in H4; auto.
  apply FAT97b in H4; auto.
Qed.

Definition minr r1 r2 := \{ λ f, f ∈ FC
  /\ ∃ f1 f2, f1 ∈ r1 /\ f2 ∈ r2 /\ f ~ (f1 - f2) \}%FC.

Notation " x - y " := (minr x y) : rC_scope.

Fact Minrp : ∀ {r1 r2}, r2 > r1 -> r1 ∈ rC -> r2 ∈ rC -> (r2 - r1) ∈ rC.
Proof with auto.
  intros. apply AxiomII; split.
  - apply MKT33 with (x:=FC); [apply EnFC|].
    red; intros. apply AxiomII in H2. tauto.
  - gef H0 f1. gef H1 f2. pose proof (finr H2 H0).
    pose proof (finr H3 H1). exists (minF f2 f1).
    split; auto. apply AxiomI; split; intros.
    + apply AxiomII in H6 as [? [f3 [f4 [? [? []]]]]].
      apply AxiomII; repeat split... apply MinFT...
      pose proof (finr H8 H0).
      pose proof (finr H7 H1). apply MinFT in H9...
      rewrite (finF H1 H3) in H7. apply AxiomII in H7 as [_ []].
      rewrite (finF H0 H8) in H2. apply AxiomII in H2 as [_ []]. 
      eapply FAT39; eauto. eapply FAT39; eauto.
      apply FAT56... apply FAT37.
    + apply AxiomII in H6 as [? []].
      apply AxiomII; repeat split... eauto.
Qed.

Global Hint Resolve Minrp : core.

Fact MinrEx : ∀ {r1 r2}, r1 < r2 -> r1 ∈ rC -> r2 ∈ rC -> r1 + (r2 - r1) = r2.
Proof with auto.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H2 as [? [? [f1 [f2 [? []]]]]].
    apply AxiomII in H5 as [? [? [f3 [f4 [? []]]]]].
    rewrite (finF H1 H8). apply AxiomII; repeat split...
    apply MinFT in H10; auto; try eapply finr; eauto;
    [|apply H]... rewrite (finF H0 H4) in H9.
    apply AxiomII in H9 as [_ []].
    apply finr in H4; apply finr in H8; auto. apply FAT38 in H11.
    eapply FAT39; eauto... eapply FAT39; eauto...
    apply FAT56... apply FAT37.
  - gef H0 f1. pose proof (finr H3 H0). pose proof (finr H2 H1).
    apply AxiomII; repeat split; rxo. exists f1, (minF z f1).
    pose proof (H _ _ H3 H2). repeat split... 
    + apply AxiomII; repeat split; rxo. exists z, f1.
      repeat split; auto.
    + apply FAT38, MinFT... apply FAT37.
Qed.

Fact MinrUn : ∀ {r1 r2 r3}, r3 > r1 -> r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> r1 + r2 = r3 -> r2 = (r3 - r1).
Proof with auto.
  intros. destruct (FAT81 H1 (Minrp H H0 H2)) as [?|[?|?]]; auto.
  - apply FAT96a with (z:=r1) in H4...
    rewrite (@ FAT92 _ r1), (@ FAT92 _ r1), MinrEx in H4... rordF.
  - apply FAT96a with (z:=r1) in H4...
    rewrite (@ FAT92 _ r1), (@ FAT92 _ r1), MinrEx in H4...
    symmetry in H3. rordF.
Qed.

Definition mulr r1 r2 := \{ λ f, f ∈ FC
  /\ ∃ f1 f2, f1 ∈ r1 /\ f2 ∈ r2 /\ f ~ (f1 · f2) \}%FC.

Notation " x · y " := (mulr x y)(at level 40) : rC_scope.

Fact Mulrp : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> (r1 · r2) ∈ rC.
Proof with auto.
  intros. apply AxiomII; split.
  - apply MKT33 with (x:=FC); [apply EnFC|].
    red; intros. apply AxiomII in H1. tauto.
  - apply AxiomII in H as [_ [f1 []]].
    apply AxiomII in H0 as [_ [f2 []]].
    exists (mulF f1 f2). split...
    apply AxiomI; split; intros; subst.
    + apply AxiomII in H3 as [H3 [f3 [f4 [? [? []]]]]].
      apply AxiomII in H1 as [_ []]. apply AxiomII in H2 as [_ []].
      apply AxiomII; repeat split...
      eapply FAT39; eauto. apply FAT68...
    + apply AxiomII in H3 as [H3 []]. apply AxiomII; repeat split...
      exists f1, f2; repeat split; auto;
      apply AxiomII; repeat split; rxo.
Qed.

Global Hint Resolve Mulrp : core.

Theorem FAT102 : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> r1 · r2 = r2 · r1.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [H1 [f1 [f2 [? [? []]]]]].
    apply (finr H2) in H; apply (finr H3) in H0.
    pose proof (FAT69 H H0). eapply FAT39 in H5; eauto.
    apply AxiomII; repeat split; auto. exists x, f2. auto.
  - apply AxiomII in H1 as [H1 [f1 [f2 [? [? []]]]]].
    apply (finr H2) in H0; apply (finr H3) in H.
    pose proof (FAT69 H0 H). eapply FAT39 in H5; eauto.
    apply AxiomII; repeat split; auto. exists x, f2; auto.
Qed.

Fact RFm : ∀ X Y f1 f2, X ∈ rC -> Y ∈ rC -> X = eqf f1 -> Y = eqf f2
  -> f1 ∈ FC -> f2 ∈ FC -> f1 ∈ X -> f2 ∈ Y
  -> ∃ f, f ∈ X · Y /\ f ∈ FC /\ (f ~ (f1 · f2))%FC /\ (X · Y) = eqf f.
Proof.
  intros. exists (f1 · f2)%FC. repeat split; auto.
  - unfold mulr. appA2G. split; auto. exists f1, f2.
    repeat split; auto.
  - unfold eqf. apply AxiomI. split; intros.
    + appA2G. appA2H H7. destruct H8 as [H8[f3[f4[H11[]]]]].
      split; auto. rewrite H1 in H11. rewrite H2 in H9.
      appA2H H11. appA2H H9. destruct H12,H13.
      pose proof @ FAT68 f3 f1 f4 f2. MP. eapply FAT39; eauto.
    + appA2G. appA2H H7. destruct H8. split; auto. exists f1,f2.
      repeat split; auto.
Qed.

Theorem FAT103 : ∀ {r1 r2 r3}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> ((r1 · r2) · r3) = (r1 · (r2 · r3)).
Proof.
  intros. pose proof RF4 _ H as [f1[H2[H3]]].
  pose proof RF4 _ H0 as [f2[H5[H6]]].
  pose proof RF4 _ H1 as [f3[H8[H9]]].
  pose proof RFm r1 r2 f1 f2. MP.
  pose proof RFm r2 r3 f2 f3. MP. destruct H11 as [f12[H11[H13[]]]].
  destruct H12 as [f23[H12[H16[]]]]. assert ((r1 · r2) ∈ rC). auto.
  assert ((r2 · r3) ∈ rC). auto.
  pose proof RFm (r1 · r2) r3 f12 f3. MP. 
  pose proof RFm r1 (r2 · r3) f1 f23. MP.
  destruct H21 as [f[H21[H23[H24 H25]]]].
  destruct H22 as [f0[H22[H26[H27 H28]]]].
  rewrite H25,H28. apply RF2; auto.
  assert (f12 · f3 ~ (f1 · f2) · f3 )%FC.
  { apply FAT72b; auto. }
  assert (f1 · f23 ~ f1 · (f2 · f3))%FC.
  { pose proof @ FAT69 f1 f23. MP.
    pose proof @ FAT69 f1 (f2 · f3)%FC. MP.
  eapply FAT68; eauto. } 
  eapply FAT39; auto. apply H24. eapply FAT39; auto. apply H29.
  assert ((f1 · f2) · f3 ~ f1 · (f2 · f3))%FC.
  { apply FAT70; auto. }
  eapply FAT39; auto. apply H31.
  assert (f1 · (f2 · f3) ~ (f1 · f23))%FC. t38.
  eapply FAT39; auto. apply H32. t38. auto. auto. auto. auto.
Qed.

Theorem FAT104a : ∀ {r1 r2 r3}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> (r1 · (r2 + r3)) = ((r1 · r2) + (r1 · r3)).
Proof.
  intros. pose proof RF4 _ H as [f1[H2[H3]]].
  pose proof RF4 _ H0 as [f2[H5[H6]]].
  pose proof RF4 _ H1 as [f3[H8[H9]]].
  pose proof RFm r1 r2 f1 f2. MP.
  pose proof RFm r1 r3 f1 f3. MP.
  pose proof RFp r2 r3 f2 f3. MP.
  destruct H11 as [f12[H11[H14[]]]].
  destruct H12 as [f13[H12[H17[]]]].
  destruct H13 as [fyz[H13[H20[]]]].
  assert (r2 + r3 ∈ rC). auto. assert (r1 · r2 ∈ rC ). auto.
  assert (r1 · r3 ∈ rC). auto.
  pose proof RFm r1 (r2 + r3) f1 fyz. MP. 
  pose proof RFp (r1 · r2) (r1 · r3) f12 f13. MP.
  destruct H26 as [f0[H26[H28[]]]].
  destruct H27 as [f[H27[H31[]]]].
  rewrite H30,H33. apply RF2; auto.
  assert (f1 · fyz ~ f1 · (f2 + f3))%FC.
  { pose proof @ FAT69 f1 fyz. MP.
    pose proof @ FAT69 f1 (f2 + f3). MP. eapply FAT68; eauto. }
  assert ((f12 + f13) ~ (f1 · f2 + f1 · f3))%FC. 
  { eapply FAT56; auto. }
  eapply FAT39; auto. apply H29. eapply FAT39; auto. apply H34.
  assert (f1 · (f2 + f3) ~ (f1 · f2 + f1 · f3))%FC.
  { apply FAT71; auto. } eapply FAT39; auto. apply H36.
  assert ((f1 · f2 + f1 · f3) ~ (f12 + f13))%FC. t38.
  eapply FAT39; auto. apply H37. t38. auto. auto. auto. auto.
Qed.

Theorem FAT104b : ∀ {r1 r2 r3}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> ((r2 + r3) · r1) = ((r2 · r1) + (r3 · r1)).
Proof.
  intros. rewrite FAT102; auto. rewrite @ FAT102 with r2 r1; auto.
  rewrite @ FAT102 with r3 r1; auto. apply FAT104a; auto.
Qed.

Theorem FAT105a : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC
  -> x > y -> (x · z) > (y · z).
Proof with auto.
  intros. red; intros. apply AxiomII in H3 as [_[?[f3[f4[?[]]]]]].
  apply AxiomII in H4 as [_[?[f5[f6[?[]]]]]].
  rewrite (finF H1 H6) in H9. apply AxiomII in H9 as [_[]].
  pose proof (H2 _ _ H5 H8).
  apply finr in H8; apply finr in H6; apply finr in H5...
  apply @ FAT72a with (z:=f6) in H12...
  assert (gtf (mulF f5 f6) (mulF f3 f4)).
  { eapply FAT44; eauto; [apply FAT37|].
    apply FAT68... apply FAT37. }
  clear H2. apply FAT38 in H7. apply FAT38 in H10.
  eapply FAT44; eauto.
Qed.

Theorem FAT105b : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC -> x = y
  -> (x · z) = (y · z).
Proof.
  intros. subst; auto.
Qed.

Theorem FAT105c : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC -> x < y
  -> (x · z) < (y · z).
Proof.
  intros. apply FAT105a; auto.
Qed.

Theorem FAT106a : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC -> (x · z) > (y · z)
  -> x > y.
Proof.
  intros. destruct (FAT81 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT105b with (z:=z) in H3; auto. rordF.
  - apply FAT105c with (z:=z) in H3; auto. rordF.
Qed.

Theorem FAT106b : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC -> (x · z) = (y · z)
  -> x = y .
Proof.
  intros. destruct (FAT81 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT105a with (z:=z) in H3; auto. rordF.
  - apply FAT105c with (z:=z) in H3; auto. rordF.
Qed.

Theorem FAT106c : ∀ x y z, x ∈ rC -> y ∈ rC -> z ∈ rC -> (x · z) < (y · z)
  -> x < y.
Proof.
  intros. eapply FAT106a; eauto.
Qed.

Theorem FAT107 : ∀ {r1 r2 r3 r4}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> r1 > r2 -> r3 > r4 -> (r1 · r3) > (r2 · r4).
Proof.
  intros.
  pose proof RF4 _ H as [f1[H5[H6]]].
  pose proof RF4 _ H0 as [f2[H8[H9]]].
  pose proof RF4 _ H1 as [f3[H11[H12]]].
  pose proof RF4 _ H2 as [f4[H14[H15]]].
  pose proof RFm r1 r3 f1 f3. MP.
  pose proof RFm r2 r4 f2 f4. MP. rewrite H7,H10 in H3.
  apply <- Lemma_FAT94 in H3; auto. rewrite H13,H16 in H4.
  apply <- Lemma_FAT94 in H4; auto.
  destruct H17 as [f13[H17[H19[]]]].
  destruct H18 as [f24[H18[H22[]]]].
  rewrite H21,H24. apply Lemma_FAT94; auto.
  assert (f1 · f3 > f2 · f4)%FC. 
  { eapply FAT75; eauto. left. split; auto. left. auto. }
  eapply FAT44; auto. apply H25. t38. t38. auto. auto.
Qed.

Theorem FAT108 : ∀ r1 r2 r3 r4, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> (r1 ≥ r2 /\ r3 > r4) \/ (r1 > r2 /\ r3 ≥ r4) -> (r1 · r3) > (r2 · r4).
Proof.
  intros. destruct H3 as [[[H3 | H4] H5] | [H3 [H5 | H4]]].
  - apply FAT107; auto.
  - apply FAT105a with (z:=r2) in H5; auto. rewrite <- H4.
    rewrite FAT102; auto. rewrite (@ FAT102 r2 r4); auto.
  - apply FAT107; auto.
  - rewrite H4. apply FAT105a; auto.
Qed.

Theorem FAT109 : ∀ r1 r2 r3 r4, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> (r1 ≥ r2 /\ r3 ≥ r4) -> (r1 · r3) ≥ (r2 · r4).
Proof.
  intros. destruct H3 as [[|][|]].
  - left. apply FAT107; auto.
  - left. rewrite H4. apply FAT105a; auto.
  - left. rewrite H3. rewrite FAT102; auto.
    rewrite (@ FAT102 r1 r4); auto. apply FAT105a; auto.
  - right. rewrite H3,H4; auto.
Qed.

Lemma Lemma_FAT110 : ∀ f, f ∈ FC -> exists r, r ∈ rC /\ r = eqf f.
Proof.
  intros. exists (eqf f). split; auto. appA2G.
  assert ((eqf f) ⊂ FC ). 
  { red. intros. appA2H H0. tauto. }
  eapply MKT33. apply EnFC. auto.
Qed.

Theorem FAT110a : ∀ r1 r2,  r1 ∈ rC -> r2 ∈ rC
  -> ∃ r3, r3 ∈ rC /\ r2 · r3 = r1.
Proof.
  intros. pose proof RF4 _ H as [f1[H2[H3]]].
  pose proof RF4 _ H0 as [f2[H5[H6]]]. pose proof FAT77a f1 f2.
  MP. destruct H7 as [f[]]. pose proof Lemma_FAT110 f. MP.
  destruct H10 as [r3[]]. exists r3. split; auto.
  assert (f ∈ r3). { rewrite H10. apply RF0a; auto. }
  pose proof RFm r2 r3 f2 f. MP. destruct H12 as [f0[H12[H13[]]]].
  rewrite H15,H1. apply RF2; auto. eapply FAT39; eauto.
Qed.

Theorem T110b : ∀ r1 r2 r3 r4, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC -> r4 ∈ rC
  -> (r2 · r3) = r1 -> (r2 · r4) = r1 -> r3 = r4 .
Proof.
  intros. rewrite <- H3 in H4. apply FAT106b with r2; auto.
  rewrite FAT102; auto. rewrite @ FAT102 with r4 r2; auto.
Qed.

Theorem FAT111a : ∀ x y, x ∈ Nat -> y ∈ Nat -> ([x, One] > [y, One])%FC
  ->( x > y)%Nat.
Proof.
  intros. red in H1. rewrite fra1 in H1; auto.
  rewrite fra2 in H1; auto. rewrite fra1 in H1; auto.
  rewrite fra2 in H1; auto. apply FAT33a with (z:= One); auto.
Qed.

Theorem FAT111b : ∀ x y, x ∈ Nat -> y ∈ Nat -> ([x, One] ~ [y, One])%FC
  -> x = y.
Proof.
  intros. red in H1. rewrite fra1 in H1; auto.
  rewrite fra2 in H1; auto. rewrite fra1 in H1; auto.
  rewrite fra2 in H1; auto. apply FAT33b with (z:= One); auto.
Qed.

Theorem FAT111c : ∀ x y, x ∈ Nat -> y ∈ Nat -> ([x, One] < [y, One])%FC
  -> (x < y)%Nat.
Proof.
  intros. red in H1. rewrite fra1 in H1; auto.
  rewrite fra2 in H1; auto. rewrite fra1 in H1; auto.
  rewrite fra2 in H1; auto. apply FAT33c with (z:= One); auto.
Qed.

(*整数n(自然数到有理数)(若n是自然数时)*)
Definition Ntor n := \{ λ f, f ∈ FC /\ f ~ ([n,One]) \}%FC.

(*整数集*)
Definition Nt := \{ λ S, ∃n, n ∈ Nat /\ S = Ntor n \}.

Fact N2rT : ∀ n, n ∈ Nat -> Ntor n ∈ rC.
Proof.
  intros. apply AxiomII; split; [|exists [n,One]; split; auto].
  - apply MKT33 with (x:=FC); [apply EnFC|].
    red; intros. apply AxiomII in H0. tauto.
Qed.

Global Hint Resolve N2rT : core.

Fact Ntor1 : ∀ n1 n2, n1 ∈ Nat -> n2 ∈ Nat -> (n1 > n2)%Nat
  -> Ntor n1 > Ntor n2.
Proof.
  intros. red. intros. appA2H H2. appA2H H3. destruct H4,H5.
  assert ([n1, One] > [n2, One])%FC.
  { red. repeat Ge. apply FAT32a; auto. }
  eapply FAT44; eauto; t38.
Qed.

Fact Ntor2a : ∀ n1 n2, n1 ∈ Nat -> n2 ∈ Nat -> Ntor n1 = Ntor n2 -> n1 = n2.
Proof.
  intros. destruct (@ FAT10 n1 n2); auto.
  destruct H2; apply Ntor1 in H2; rordF; auto.
Qed.

Fact Ntor2b : ∀ n1 n2, n1 ∈ Nat -> n2 ∈ Nat -> n1 = n2 -> Ntor n1 = Ntor n2.
Proof.
  intros. subst. auto.
Qed.

Theorem FAT112a : ∀ x y, x ∈ Nat -> y ∈ Nat
  -> (([x, One] + [y, One])%FC ~ [(x + y)%Nat, One])%FC.
Proof.
  intros. unfold addF. red. repeat Ge.
  repeat rewrite FAT30b; auto. repeat rewrite FAT31; auto.
Qed.

Theorem FAT112b : ∀ x y, x ∈ Nat -> y ∈ Nat
  -> (([x, One] · [y, One])%FC ~ [(x · y)%Nat, One])%FC.
Proof.
  intros. unfold mulF. red. repeat Ge.
  repeat rewrite FAT28a; auto.
Qed.

Definition Zsuc :=
  \{\ λ u v, exists n, n ∈ Nat /\ u = (Ntor n) /\ v = Ntor (n⁺)\}\.

Fact zsucp : ∀ n, n ∈ Nat -> Zsuc [Ntor n] = Ntor (n⁺).
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H0. apply H1. appA2G. apply AxiomII'; repeat split; rxo.
  - appA2G. intros. appA2H H1. apply AxiomII' in H2.
    destruct H2 as [?[n0[?[]]]]. apply Ntor2a in H4; auto.
    subst; auto.
Qed.

Theorem FAT113a : (Ntor One) ∈ Nt.
Proof.
  appA2G.
Qed.

Theorem FAT113b : ∀ x y, x ∈ Nt -> y ∈ Nt -> x = y -> Zsuc[x] = Zsuc[y].
Proof.
  intros. subst; auto.
Qed.

Theorem FAT113c : ∀ x, x ∈ Nt -> Zsuc[x] <> (Ntor One).
Proof.
  intros. intro. appA2H H. destruct H1 as [n[]]. subst.
  rewrite zsucp in H0; auto.
  apply Ntor2a in H0; auto.  pose proof (FAA3 n H1). contradiction.
Qed.

Theorem FAT113d : ∀ x y, x ∈ Nt -> y ∈ Nt -> Zsuc[x] = Zsuc[y] -> x = y.
Proof.
  intros. appA2H H. appA2H H0. destruct H2 as [n1[]].
  destruct H3 as [n2[]]. subst. rewrite zsucp in H1; auto.
  rewrite zsucp in H1; auto. apply Ntor2a in H1; auto.
  apply FAA4 in H1; auto. rewrite H1; auto.
Qed.

Theorem FAT113e : ∀ M, M ⊂ Nt -> (Ntor One) ∈ M
  -> (∀ u, u ∈ M -> Zsuc[u] ∈ M) -> M = Nt.
Proof.
  intros. apply AxiomI; split; intros.
  - apply H in H2. auto.
  - appA2H H2. destruct H3 as [n[]]. subst.
    apply MathInd with (n:=n); intros; auto.
    rewrite <- zsucp; auto.
Qed.

Fact NattorC : ∀ n, n ∈ Nat -> ∃ r, r ∈ rC /\ Ntor n = r.
Proof.
  intros. exists (Ntor n). apply N2rT in H. split; auto.
Qed.

Fact minr1 : ∀ n1 n2, n1 ∈ Nat -> n2 ∈ Nat -> (n1 > n2)%Nat
  -> Ntor (n1 - n2)%Nat = (Ntor n1) - (Ntor n2).
Proof.
  intros. apply AxiomI. split; intros.
  - appA2H H2. destruct H3. appA2G. split; auto.
    exists [n1 , One], [n2 , One]. repeat split.
    + appA2G. split; auto. t37.
    + appA2G. split; auto. t37.
    + unfold minF. repeat Ge. repeat rewrite FAT28a; auto.
  - appA2H H2. appA2G. destruct H3 as [?[f1[f2[?[]]]]].
    split; auto. appA2H H4. appA2H H5. destruct H7,H8.
    assert (f1 > f2)%FC.
    { apply FAT38 in H9,H10. eapply FAT44; eauto. red.
      repeat Ge. repeat rewrite FAT28a; auto. }
    apply @ FAT39 with (f1 - f2)%FC; auto.
    apply FAT38. apply MinFUn; auto.
    apply @ FAT39 with [n1, One]; try t38; auto.
    assert (([(n1 - n2)%Nat, One] + f2 ~ [n1, One])%FC).
    { apply MinFT; auto. red. repeat Ge.
      repeat rewrite FAT28a; auto. apply FAT20a with n2; auto.
      rewrite FAT6 with (n1 - n2)%Nat n2; auto.
      rewrite MinNEx; auto. apply FAT18; auto.
      assert (([n1, One] > [(n1 - n2)%Nat, One])%FC).
      { red. repeat Ge. repeat rewrite FAT28a; auto.
        apply FAT20a with n2; auto.
        rewrite FAT6 with (n1 - n2)%Nat n2; auto.
        rewrite MinNEx; auto. apply FAT18; auto. }
      apply @ FAT39 with [n2, One]; auto. apply MinFUn; auto.
      unfold addF. repeat Ge. repeat rewrite FAT28a; auto.
      rewrite FAT6; auto. rewrite MinNEx; auto. t37. } 
    apply @ FAT39 with ([(n1 - n2)%Nat, One] + f2)%FC; auto.
    apply FAT58; auto.
Qed.

Fact addr1 : ∀ n1 n2, n1 ∈ Nat -> n2 ∈ Nat
  -> Ntor (n1 + n2)%Nat = (Ntor n1) + (Ntor n2).
Proof.
  intros. assert (n1 + n2 > n2)%Nat.
  { rewrite FAT6; auto. apply FAT18; auto. }
  assert (Ntor (n1 + n2)%Nat > Ntor n2).
  { apply Ntor1; auto. }
  assert (Ntor (n1 + n2 - n2)%Nat = Ntor (n1 + n2)%Nat - Ntor n2).
  { apply minr1; auto. }
  apply (FAT96b _ _ (Ntor n2)) in H3; auto.
  rewrite FAT92 with (Ntor (n1 + n2)%Nat - Ntor n2)
  (Ntor n2) in H3; auto. rewrite MinrEx in H3; auto.
  rewrite <- H3. apply FAT96b; auto.
  apply Ntor2b; auto. apply FAT20b with n2; auto.
  rewrite FAT6 with (n1 + n2 - n2)%Nat n2; auto.
  rewrite MinNEx; auto.
Qed.

Fact mulr1 : ∀ r, r ∈ rC -> (Ntor One) · r = r.
Proof.
  intros. apply AxiomI. split; intros.
  - appA2H H0. destruct H1 as [?[f1[f2[?[]]]]]. appA2H H2.
    destruct H5. red in H6. Ge. rewrite FAT28a in H6; auto.
    rewrite FAT28ai in H6; auto. unfold mulF in H4. red in H4.
    Ge; eauto. rewrite H6 in H4.
    rewrite FAT29 with (f1)²%FC (f2)¹%FC in H4; eauto.
    rewrite FAT31 in H4; eauto.
    rewrite FAT29 with (f1)²%FC (f2)²%FC in H4; eauto.
    rewrite FAT29 with (f1)²%FC (z)²%FC in H4; auto.
    rewrite <- FAT31 in H4; eauto. rewrite <- FAT31 in H4; eauto.
    apply FAT33b in H4; eauto. apply RF6 with f2; auto. red; auto.
  - appA2G. appA2H H. destruct H1 as [f[]]. subst. appA2H H0.
    destruct H2. split; auto. exists [One,One], z. repeat split.
    + apply AxiomII. repeat split; rxo.
    + appA2G.
    + unfold mulF. red. repeat Ge. repeat rewrite FAT28ai; auto.
Qed.

Theorem FAT114 : ∀ x y r, x ∈ Nat -> y ∈ Nat -> r ∈ rC
  -> r = (eqf ([x, y])) -> ((Ntor y) · r) = (Ntor x).
Proof.
  intros. rewrite H2. clear H2. unfold eqf. unfold Ntor.
  unfold mulr. apply AxiomI. split; intros.
  - appA2H H2. destruct H3 as [H3[f1[f2[H5[]]]]]. appA2H H5.
    appA2H H4. destruct H7,H8. appA2G. split; auto.
    eapply FAT39; eauto. unfold mulF. red. repeat Ge.
    red in H9. red in H10. rewrite fra2 in H9,H10; auto.
    rewrite fra1 in H9,H10; auto. rewrite FAT28a; auto.
    rewrite FAT28a in H9; auto.
    rewrite H9. rewrite FAT29 with (f1)²%FC (f2)²%FC; auto.
    rewrite <- FAT31; auto. rewrite <- H10.
    rewrite FAT29 with (f2)¹%FC y; auto.
    repeat rewrite FAT31; auto.
    rewrite FAT29 with (f1)²%FC (f2)¹%FC; auto.
  - appA2H H2. destruct H3. appA2G. split; auto.
    exists [y, One], [x, y].
    repeat split; try appA2G; try split; try auto; try t37.
    eapply FAT39; eauto. unfold mulF. repeat Ge. red. repeat Ge.
    rewrite FAT29 with One y; auto. rewrite <- FAT31; auto. 
    rewrite FAT29 with x y; auto.
Qed.

Definition divr r1 r2 := \{ λ f, f ∈ FC
  /\ ∃ f1 f2, f1 ∈ r1 /\ f2 ∈ r2 /\  f ~ (divF f1 f2) \}%FC.

Fact divr1 : ∀ r1 r2, 
  r1 ∈ rC -> r2 ∈ rC -> r1 < r2 -> divr r1 r2 < Ntor One.
Proof.
  red. intros. appA2H H2. appA2H H3.
  destruct H5,H4 as [?[f3[f4[?[]]]]].
  red in H1. pose proof (H1 _ _ H7 H8). unfold divF in H9.
  RF. rewrite H14 in H7. rewrite H12 in H8. apply RF0b in H7,H8.
  assert (f3 · [(f4)², (f4)¹] < [One, One])%FC.
  { unfold mulF. red. repeat Ge; eauto. rewrite FAT28a; auto. 
    rewrite FAT28ai; auto. red in H10. 
    rewrite FAT29 with (f3)²%FC (f4)¹%FC; auto. }
  eapply FAT45; auto. apply H15. t38. t38. auto. auto.
Qed.

Fact Divrp : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> (divr r2 r1) ∈ rC.
Proof with auto.
  intros. apply AxiomII; split.
  - apply MKT33 with (x:=FC); [apply EnFC|].
    red; intros. apply AxiomII in H1. tauto.
  - gef H f1. gef H0 f2. pose proof (finr H1 H).
    pose proof (finr H2 H0). exists (divF f2 f1). split...
    apply AxiomI; split; intros.
    + apply AxiomII in H5 as [? [f3 [f4 [? [? []]]]]].
      apply AxiomII; repeat split... apply DivFT...
      pose proof (finr H7 H). pose proof (finr H6 H0).
      apply DivFT in H8... rewrite (finF H0 H2) in H6.
      apply AxiomII in H6 as [_ []]. rewrite (finF H H7) in H1.
      apply AxiomII in H1 as [_ []]. eapply FAT39; eauto.
      eapply FAT39; eauto. apply FAT68... apply FAT37.
    + apply AxiomII in H5 as [? []].
      apply AxiomII; repeat split... eauto.
Qed.

Global Hint Resolve Divrp : core.

Fact DivrEx : ∀ {r1 r2}, r1 ∈ rC -> r2 ∈ rC -> r1 · (divr r2 r1) = r2.
Proof with auto.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H1 as [? [? [f1 [f2 [? []]]]]].
    apply AxiomII in H4 as [? [? [f3 [f4 [? []]]]]].
    rewrite (finF H0 H7). apply AxiomII; repeat split...
    apply DivFT in H9; auto; try eapply finr; eauto.
    rewrite (finF H H3) in H8. apply AxiomII in H8 as [_ []].
    apply finr in H3; apply finr in H7; auto. apply FAT38 in H10.
    eapply FAT39; eauto... eapply FAT39; eauto...
    apply FAT68... apply FAT37.
  - gef H f1. pose proof (finr H2 H). pose proof (finr H1 H0).
    apply AxiomII; repeat split; rxo.
    exists f1, (divF z f1). repeat split...
    apply AxiomII; repeat split; rxo. exists z, f1. repeat split...
    apply FAT38, DivFT... apply FAT37.
Qed.

Fact DivrUn : ∀ {r1 r2 r3}, r1 ∈ rC -> r2 ∈ rC -> r3 ∈ rC
  -> r1 · r2 = r3 -> r2 = (divr r3 r1).
Proof with auto.
  intros. destruct (FAT81 H0 (Divrp H H1)) as [?|[?|?]]; auto.
  - apply FAT105a with (z:=r1) in H3...
    rewrite (@ FAT102 _ r1), (@ FAT102 _ r1), DivrEx in H3...
    rordF.
  - apply FAT105a with (z:=r1) in H3...
    rewrite (@ FAT102 _ r1), (@ FAT102 _ r1), DivrEx in H3...
    symmetry in H2. rordF.
Qed.

Fact Ntor3 : ∀ r, r ∈ rC
  -> ∃ n1 n2, n1 ∈ Nat /\ n2 ∈ Nat /\ r = divr (Ntor n1) (Ntor n2).
Proof.
  intros. New H. apply RF4 in H. destruct H as [f[?[]]].
  appA2H H1. destruct H3 as [x[y[?[]]]]. rewrite H3 in H2.
  pose proof (FAT114 x y r). MP.
  exists x, y. repeat split; auto. apply DivrUn; auto.
Qed.

Theorem FAT115 : ∀ r1 r2 , r1 ∈ rC -> r2 ∈ rC
  -> ∃ n, n ∈ Nat /\ (Ntor n) · r1 > r2.
Proof.
  intros. pose proof (FAT89 (divr r2 r1)).
  assert (divr r2 r1 ∈ rC). auto. MP.
  destruct H3 as [r []]. pose proof (Ntor3 r H1).
  destruct H4 as [n[v[?[]]]].
  rewrite H6 in H3. exists n. split; auto.
  apply (@ FAT105a _ _ r1) in H3; auto.
  rewrite (@ FAT102 (divr r2 r1) r1) in H3; auto.
  rewrite DivrEx in H3; auto.
  assert ((Ntor v) ≥ (Ntor One)).
  { destruct (@ FAT24 v H5). left. apply Ntor1; auto. right.
  rewrite H7; auto. }
  destruct H7.
  - apply FAT86 with (divr (Ntor n) (Ntor v) · r1); auto.
    apply FAT105c; auto. apply FAT106c with (Ntor v); auto.
    rewrite FAT102; auto. rewrite DivrEx; auto.
    rewrite FAT102; auto. pattern (Ntor n) at 1;
    rewrite <- (mulr1 (Ntor n)); auto. apply FAT105c; auto.
  - apply FAT87 with (divr (Ntor n) (Ntor v) · r1); auto.
    right. split; auto. right. rewrite <- H7. apply FAT105b; auto.
    symmetry. apply DivrUn; auto. rewrite mulr1; auto.
Qed.

Close Scope rC_scope.

(* CUTS *)

(* SECTION I Definition *)

Declare Scope CC_scope.

Delimit Scope CC_scope with CC.

Open Scope CC_scope.

(*分割*)
Definition CC := \{λ S, S ⊂ rC /\ 
  (S <> Φ /\ ∃ r, r ∈ rC /\ ~ r ∈ S) /\
  (∀ r1 r2, r1 ∈ S -> r2 ∈ rC -> r2 < r1 -> r2 ∈ S) /\
  (∀ r1, r1 ∈ S -> ∃ r2, r2 ∈ S /\ r1 < r2) \}%rC.
(*分割： 有理数的子集 （1）包含一有理数但不包含每一有理数 （2）每一有理数小于不包含于该集合的每一有理数 （3）集合中无最大有理数*)
(*分割： 有理数的子集 （1）非空，有一有理数不在集合中 （2）随着集合里的每一数，每一较小的数也在集合中 （3）对于集合中的每一数，必有一较大的数在集合中*)

Fact EnCC : Ensemble CC.
Proof.
  apply MKT33 with (x:=pow(rC)).
  - apply MKT38a; apply EnrC. 
  - red; intros. apply AxiomII in H as [? []].
    apply AxiomII; auto.
Qed.

Fact ccp1 : ∀ {S}, S ⊂ rC -> (S <> Φ /\ ∃ r, r ∈ rC /\ ~ r ∈ S)
  <-> (∃ r, r ∈ S) /\ ~ (∀ r, r ∈ rC -> r ∈ S).
Proof.
  split; intros; destruct H0; split; try apply NEexE; auto.
  - intro. destruct H1 as [r []]; auto.
  - destruct (classic (∃ r, r ∈ rC /\ ~ r ∈ S)); auto.
    elim H1; intros. destruct (classic (r ∈ S)); auto.
    elim H2; eauto.
Qed.

Fact ccp2 : ∀ {S}, S ⊂ rC
  -> (∀ r1 r2, r1 ∈ S -> r2 ∈ rC -> r2 < r1 -> r2 ∈ S)%rC
    <-> (∀ r1 r2, r1 ∈ S -> r2 ∈ rC -> ~ r2 ∈ S -> r1 < r2)%rC.
Proof.
  split; intros.
  - destruct (FAT81 (H _ H1) H2) as [? |[?|?]]; auto.
    + subst; tauto.
    + eapply H0 in H4; eauto. tauto.
 - destruct (classic (r2 ∈ S)); auto.
   pose proof (H0 _ _ H1 H2 H4). rordF.
Qed.

Fact ccp3 : ∀ {S}, S ⊂ rC
  -> (∀ r1, r1 ∈ S -> ∃ r2, r2 ∈ S /\ r1 < r2)%rC
    <-> ~ (∃ r, r ∈ S /\ (∀ r1, r1 ∈ S -> ~ r1 > r)%rC).
Proof.
  split; intros.
  - intro. destruct H1 as [r [ ]]. apply H0 in H1 as [r1 []].
    eapply H2; eauto.
  - destruct (classic (∃ r2, r2 ∈ S /\ ltr r1 r2)); auto.
    elim H0. exists r1; split; auto; intros. intro.
    apply H2; eauto.
Qed.

(*下类S的上类*)
Definition upper_class S := \{λ r, r ∈ rC
  /\ ∀ r0, r0 ∈ S -> r0 < r \}%rC.
  
(*下类数(当r为有理数c为分割)*)
Definition Num_L r c := r ∈ c.

(*上类数(同上)*)
Definition Num_U r c := ~ r ∈ c.

Fact nup : ∀ c r, c ∈ CC -> r ∈ rC -> r ∈ (upper_class c) <-> Num_U r c.
Proof.
  split; intros.
  - apply AxiomII in H1 as [? []]. red; intro.
    apply H3 in H4. rordF.
  - apply AxiomII in H as [_ [? [? []]]].
    apply AxiomII; repeat split; rxo. intros. eapply ccp2; eauto.
Qed.

Theorem FAT116 : ∀ c, c ∈ CC -> c = c.
Proof.
  auto.
Qed.

Theorem FAT117 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 = c2 -> c2 = c1.
Proof.
  auto.
Qed.

Theorem FAT118 : ∀ c1 c2 c3, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> c1 = c2 -> c2 = c3 -> c1 = c3.
Proof.
  intros. rewrite H2. auto.
Qed.

Lemma Lemma_FAT119 : ∀ {c} r1 r2, c ∈ CC -> r1 ∈ c -> r2 ∈ rC -> ~ r2 ∈ c
  -> (r1 < r2)%rC.
Proof.
  intros. apply AxiomII in H as [_ [? [? []]]]. eapply ccp2; eauto.
Qed.

Theorem FAT119 : ∀ c r1 r2, c ∈ CC -> r1 ∈ rC -> Num_U r1 c -> r2 ∈ rC
  -> (r2 > r1)%rC -> ~ r2 ∈ c.
Proof.
  intros. intro. eapply Lemma_FAT119 in H1; eauto. rordF.
Qed.

Theorem FAT120 : ∀ r r1 c, c ∈ CC -> r ∈ rC -> Num_L r c -> r1 ∈ rC
  -> (r1 < r)%rC -> r1 ∈ c.
Proof.
  intros. apply AxiomII in H as [_ [? [? []]]]. eapply H5; eauto.
Qed.

(* SECTION II Ordering *)

Definition gtc c1 c2 := ∃ r, Num_L r c1 /\ Num_U r c2.

Notation " x > y " := (gtc x y) : CC_scope.

Definition ltc c1 c2 := ∃ r, Num_L r c2 /\ Num_U r c1.

Notation " x < y " := (ltc x y) : CC_scope.

Theorem FAT121 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 > c2 -> c2 < c1.
Proof.
  auto.
Qed.

Theorem FAT122 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 < c2 -> c2 > c1.
Proof.
  auto.
Qed.

Theorem FAT123 : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC
  -> c1 = c2 \/ c1 > c2 \/ c1 < c2.
Proof.
  intros. destruct (classic (c1=c2)); auto.
  assert (~ (∀ z, z ∈ c1 <-> z ∈ c2)).
  { intro. apply H1, AxiomI; auto. }
  assert (~ (∀ z, ~ ~(z ∈ c1 <-> z ∈ c2))).
  { intro. elim H2; intros. apply NNPP; auto. }
  apply not_all_not_ex in H3 as [n ]. apply notandor in H3 as [].
  - right. left. red. destruct (imply_to_and _ _ H3); eauto.
  - right. right. red. destruct (imply_to_and _ _ H3); eauto.
Qed.

Definition gec c1 c2 := (c1 > c2) \/ (c2 = c1).

Notation " x ≥ y " := (gec x y)(at level 77) : CC_scope.

Definition lec c1 c2 := (c1 < c2) \/ (c1 = c2).

Notation " x ≤ y " := (lec x y)(at level 77) : CC_scope.

Fact elCf : ∀ {x y}, x < y -> x = y -> x ∈ CC -> y ∈ CC -> False.
Proof.
  intros. subst. destruct H as [z []]. red in H, H0. auto.
Qed.

Fact egCf : ∀ {x y}, x > y -> x = y -> x ∈ CC -> y ∈ CC -> False.
Proof.
  intros. subst. destruct H as [z []]. red in H, H0. auto.
Qed.

Fact lgCf : ∀ {x y}, x < y -> x > y -> x ∈ CC -> y ∈ CC -> False.
Proof.
  intros. destruct H as [z []], H0 as [w []].
  pose proof H1. pose proof H2. pose proof H.
  apply AxiomII in H1 as [_ [? _]].
  apply AxiomII in H2 as [_ [? _]].
  apply nup in H4; auto. apply AxiomII in H4 as [_ []].
  apply H8 in H. apply nup in H3; auto.
  apply AxiomII in H3 as [_ []]. apply H9 in H0. rordF.
Qed.

Fact legCf : ∀ {x y}, x ≤ y -> x > y -> x ∈ CC -> y ∈ CC -> False.
Proof.
  intros. destruct H; [eapply lgCf|eapply egCf]; eauto.
Qed.

Ltac ELC :=
  match goal with
    H: ltc ?n1 ?n2
    |- _ => destruct (elCf H); auto
  end.

Ltac EGC :=
  match goal with
    H: gtc ?n1 ?n2
    |- _ => destruct (egCf H); auto
  end.

Ltac LGC :=
  match goal with
    H: ltc ?n1 ?n2
    |- _ => destruct (lgCf H); auto
  end.

Ltac LEGC :=
  match goal with
    H: lec ?n1 ?n2
    |- _ => destruct (legCf H); auto
  end.

Ltac GELC :=
  match goal with
    H: gec ?n1 ?n2
    |- _ => destruct (legCf H); auto
  end.

Ltac CordF := try ELC; try EGC; try LGC; try LEGC; try GELC.

Theorem FAT124 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 ≥ c2 -> c2 ≤ c1.
Proof.
  auto.
Qed.

Theorem FAT125 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 ≤ c2 -> c2 ≥ c1.
Proof.
  auto.
Qed.

Fact rinC : ∀ c r, c ∈ CC -> r ∈ c -> r ∈ rC.
Proof.
  intros. appA2H H. destruct H1 as [? _]. red in H1. auto.
Qed.

Ltac rC r c:=
  match goal with
  H : r ∈ c,
  H1 : c ∈ CC
  |- _ => pose proof (rinC c r); MP
  end.

Theorem FAT126 : ∀ c1 c2 c3, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> c1 < c2 -> c2 < c3 -> c1 < c3.
Proof.
  intros. red in H2,H3. destruct H2 as [r1[]].
  destruct H3 as [r2[]]. red in H2,H3,H5. New H0.
  appA2H H0. destruct H7 as [?[?[]]]. apply ccp2 in H7.
  assert (∀r1 r2,r1 ∈ c2 -> r2 ∈ rC -> ~ r2 ∈ c2 -> (r1 < r2)%rC).
  { apply H7; auto. } rC r2 c3. 
  pose proof (H11 _ _ H2 H12 H5). rC r1 c2.
  apply FAT83 in H13; auto. pose proof (FAT119 c1 r1 r2). MP. red.
  exists r2. split; auto.
Qed.

Theorem FAT127 : ∀ c1 c2 c3, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> (c1 ≤ c2 /\ c2 < c3) \/ (c1 < c2 /\ c2 ≤ c3) -> c1 < c3.
Proof.
  intros. destruct H2 as [[[|]H3]|[H3[|]]].
  - apply FAT126 with c2; auto.
  - rewrite H2; auto.
  - apply FAT126 with c2; auto.
  - rewrite H2 in H3; auto.
Qed.

Theorem FAT128 : ∀ c1 c2 c3, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> c1 ≤ c2 -> c2 ≤ c3 -> c1 ≤ c3.
Proof.
  intros. red. destruct H2,H3.
  - left; apply FAT126 with c2; auto.
  - rewrite H3 in H2; tauto.
  - rewrite H2; tauto.
  - rewrite H2; tauto.
Qed.

(* SECTION III Addition *)

Definition addc c1 c2 := \{λ c, ∃ r1 r2, Num_L r1 c1
  /\ Num_L r2 c2 /\ c = (r1 + r2) \}%rC.

Notation "c1 + c2" := (addc c1 c2) : CC_scope.

Theorem FAT129a : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC -> c1 + c2 ∈ CC.
Proof.
  intros. pose proof H as G1. pose proof H0 as G2.
  apply AxiomII in H as [_ [? [[? [r3 []]] []]]]. 
  apply AxiomII in H0 as [_ [? [[? [r4 []]] []]]].
  apply NEexE in H1 as [r1]. apply NEexE in H6 as [r2].
  assert (addc c1 c2 ⊂ rC).
  { red; intros. apply AxiomII in H11 as [_ [? [? [? []]]]].
  subst; auto. }
  apply AxiomII; repeat split; auto; intros.
  - apply MKT33 with (x:=rC); [apply EnrC|auto].
  - apply NEexE. exists (addr r1 r2). apply AxiomII. split.
    unfold Ensemble; eauto. eauto.
  - exists (addr r3 r4); split; auto. intro.
    apply AxiomII in H12 as [_ [r5 [r6 [? []]]]].
    apply (Lemma_FAT119 r5) in H3;
    apply (Lemma_FAT119 r6) in H8; auto.
    apply FAT96c with (z:=r6) in H3;
    apply FAT96c with (z:=r3) in H8;
    auto. rewrite FAT92, (FAT92 r4) in H8; auto. CordF.
    rewrite H14 in H8. rordF.
  - apply AxiomII; split; unfold Ensemble; eauto.
    apply AxiomII in H12 as [_ [r6 [r7 [? []]]]].
    exists (mulr r6 (divr r5 r0)), (mulr r7 (divr r5 r0)). 
    subst. repeat split.
    + apply (H4 _ _ H12); auto. red in H12. rC r6 c1.
      pose proof (mulr1 r6). MP. pattern r6 at 3; rewrite <- H18.
      rewrite FAT102; auto.
      apply FAT105c; auto. apply divr1; auto.
    + apply (H9 _ _ H15); auto. red in H15. rC r7 c2.
      pose proof (mulr1 r7). MP. pattern r7 at 3; rewrite <- H18.
      rewrite FAT102; auto. apply FAT105c; auto.
      apply divr1; auto.
    + rewrite FAT102; auto.
      rewrite @ FAT102 with r7 (divr r5 (r6 + r7))%rC; auto.
      rewrite <- FAT104a; auto. rewrite FAT102; auto.
      rewrite DivrEx; auto.
  - apply AxiomII in H12 as [_ [r5 [r6 [? []]]]]. subst.
    destruct (H5 _ H12) as [r7 []]. exists (addr r7 r6). split.
    + apply AxiomII; split; unfold Ensemble; eauto.
    + apply FAT96c; auto.
Qed.

Global Hint Resolve FAT129a : core.

Theorem FAT129b : ∀ {c1 c2} r1 r2, c1 ∈ CC -> c2 ∈ CC -> r1 ∈ rC -> r2 ∈ rC
  -> Num_U r1 c1 -> Num_U r2 c2 -> ∀ r, r ∈ c1 + c2 -> ~(r = r1 + r2)%rC.
Proof.
  intros. intro. appA2H H5.
  destruct H7 as [r1'[r2'[?[?]]]]. red in H3,H4,H7,H8.
  assert (r1' < r1)%rC. { apply @ Lemma_FAT119 with c1; eauto. }
  assert (r2' < r2)%rC. { apply @ Lemma_FAT119 with c2; eauto. }
  rC r1' c1. rC r2' c2.
  assert ((r1' + r2') < (r1 + r2))%rC. 
  { apply FAT98; auto. }
  rewrite H9 in H6. rordF.
Qed.

Theorem FAT130 : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC -> c1 + c2 = c2 + c1.
Proof.
  intros. apply AxiomII in H as [_ [H _]].
  apply AxiomII in H0 as [_ [H0 _]]. apply AxiomI; split; intros.
  - apply AxiomII in H1 as [? [r1 [r2 [? []]]]]; subst.
    apply AxiomII. split; auto. exists r2, r1. repeat split; auto.
    apply FAT92; auto.
  - apply AxiomII in H1 as [? [r1 [r2 [? []]]]]; subst.
    apply AxiomII. split; auto. exists r2, r1. repeat split; auto.
    apply FAT92; auto.
Qed.

Theorem FAT131 : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> (c1 + c2) + c3 = c1 + (c2 + c3).
Proof.
  intros. apply AxiomII in H as [_ [? _]].
  apply AxiomII in H0 as [_ [? _]].
  apply AxiomII in H1 as [_ [? _]].
  apply AxiomI; split; intros.
  - appA2H H2. destruct H3 as [r12[r3[?[]]]]. red in H3,H4. subst.
    appA2G. appA2H H3. destruct H5 as [r1[r2[?[]]]]. red in H5,H6.
    exists r1,(r2 + r3)%rC. pose proof (H _ H5).
    pose proof (H0 _ H6). pose proof (H1 _ H4). repeat split.
    + red; auto.
    + red. appA2G.
    + subst. rewrite FAT93; auto.
  - appA2H H2. destruct H3 as [r1[r23[?[]]]]. red in H3,H4. subst.
    appA2G. appA2H H4. destruct H5 as [r2[r3[?[]]]]. red in H5,H6.
    exists (r1 + r2)%rC,r3. pose proof (H _ H3).
    pose proof (H0 _ H5). pose proof (H1 _ H6). repeat split.
    + red. appA2G.
    + red; auto.
    + subst. rewrite FAT93; auto.
Qed.

Theorem FAT132 : ∀ r c, r ∈ rC -> c ∈ CC -> ∃ r1 r2, r1 ∈ rC /\ r2 ∈ rC
  /\ Num_L r1 c /\ Num_U r2 c /\ (r2 - r1 = r)%rC.
Proof.
  intros. New H0. apply AxiomII in H0 as [_ [_ [[] _]]].
  apply NEexE in H0. destruct H0 as [x1]. destruct H2 as [y[]].
  rC x1 c. assert (y > x1)%rC.
  { eapply Lemma_FAT119; eauto. } 
  assert ((y - x1)%rC ∈ rC). auto.
  pose proof (FAT115 r (y - x1)%rC). MP. destruct H7 as [n[]].
  assert (Ntor n ∈ rC). { apply N2rT; auto. }
  apply (@ FAT96a _ _ x1) in H8; auto. rewrite FAT92 in H8; auto.
  rewrite (@ FAT92 (y - x1)%rC x1) in H8; auto.
  rewrite MinrEx in H8; auto.
  assert (~ ((x1 + Ntor n · r)%rC ∈ c)).
  { apply FAT119 with y; eauto. }
  set \{ λ n, n ∈ Nat /\ ~ ((x1 + Ntor n · r)%rC ∈ c) \}.
  pose proof FAT27 c0. assert (c0 ⊂ Nat).
  { red. intros. appA2H H12. tauto. }
  assert (c0 ≠ Φ). { apply NEexE. exists n. appA2G. } MP.
  destruct H11 as [u[]]. destruct (@ FAT24 u); auto.
  - exists (x1 + ((Ntor (u - One)%Nat) · r))%rC,
    (x1 + (Ntor u) · r)%rC.
    assert (Ntor u ∈ rC). { apply N2rT; auto. }
    assert (u ∈ Nat). { appA2H H11. tauto. }
    assert ((u - One)%Nat ∈ Nat). { pose proof FAA1. auto. }
    assert (Ntor (u - One)%Nat ∈ rC). { apply N2rT; auto. }
    repeat split; auto.
    + red. destruct
      (classic ((x1 + Ntor (u - One)%Nat · r)%rC ∈ c)); auto.
      assert (~((u - One)%Nat ∈ c0)).
      { intro. apply H14 in H21. destruct H21. pose proof FAA1.
      apply FAT19c with One in H21; auto.
      rewrite FAT6 with (u - One)%Nat One in H21; auto. 
      rewrite MinNEx in H21; auto.
      pose proof (@ FAT18 u One). MP. NordF.
      apply MinNT in H21; auto. pose proof (@ FAT7 One u); auto.
      pose proof FAA1. MP. rewrite H21 in H22. contradiction. }
      assert ((u - One)%Nat ∈ c0). { appA2G. } contradiction.
    + appA2H H11. tauto.
    + assert ((x1 + Ntor u · r) > (x1 + Ntor (u - One)%Nat · r))%rC.
      { rewrite FAT92; auto.
      rewrite FAT92 with x1 (Ntor (u - One)%Nat · r)%rC; auto.
      apply FAT96a; auto. apply FAT105a; auto. apply Ntor1; auto.
      apply FAT20a with One; auto.
      rewrite FAT6 with (u - One)%Nat One; auto.
      rewrite MinNEx; auto. apply FAT18; auto. }
      symmetry. apply MinrUn; auto. rewrite FAT93; auto.
      rewrite FAT92; auto. rewrite FAT92 with x1 (Ntor u · r)%rC;
      auto. apply FAT96b; auto. pose proof (mulr1 r). MP.
      pattern r at 2; rewrite <- H22. rewrite FAT102; auto.
      rewrite @ FAT102 with (Ntor One) r; auto.
      rewrite <- FAT104a; auto. rewrite FAT102; auto.
      apply FAT105b; auto. rewrite minr1; auto.
      assert ((Ntor u > Ntor One)%rC). { apply Ntor1; auto. }
      rewrite FAT92; auto. rewrite MinrEx; auto.
  - exists x1, (x1 + r)%rC. repeat split; auto.
    + red. appA2H H11. destruct H16. rewrite <- H15 in H17. 
      rewrite mulr1 in H17; auto.
    + assert ((x1 + r) > x1)%rC. { apply FAT94; auto. }
      symmetry. apply MinrUn; auto.
Qed.

Theorem FAT133 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 + c2 > c1.
Proof.
  intros. New H. apply AxiomII in H as [_ [? [[? _] _]]].
  apply AxiomII in H0 as [_ [? [[? _] _]]]. apply NEexE in H3.
  destruct H3 as [r2]. pose proof (H0 _ H3).
  pose proof (FAT132 r2 c1). MP. destruct H5 as [r1[r1'[?[?[?[]]]]]].
  red. exists r1'. split; red; auto. appA2G. exists r1,r2.
  repeat split; auto. subst. rewrite MinrEx; auto.
  apply @ Lemma_FAT119 with c1; auto.
Qed.

Theorem FAT134 : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c1 > c2
  -> c1 + c3 > c2 + c3.
Proof.
  intros. red in H2. destruct H2 as [r1[]]. New H.
  apply AxiomII in H as [_ [_ [_ [_ ?]]]]. pose proof (H _ H2).
  destruct H5 as [r1'[]]. red in H2,H3. rC r1 c1. rC r1' c1.
  assert ((r1' - r1)%rC ∈ rC). auto.
  pose proof (FAT132 (r1'-r1)%rC c3). MP.
  destruct H10 as [r3[r3'[?[?[?[]]]]]].
  red in H12,H13. rC r3 c3. assert (r3 < r3')%rC.
  { apply @ Lemma_FAT119 with c3; auto. }
  assert (r3' = (r1' - r1) + r3)%rC.
  { rewrite <- H14. rewrite FAT92; auto. rewrite MinrEx; auto. }
  assert (r1 + r3' = r1' + r3)%rC.
  { rewrite H17. rewrite <- FAT93; auto. rewrite MinrEx; auto. }
  red. exists (r1' + r3)%rC. split.
  - appA2G.
  - rewrite <- H18. red. intro.
    pose proof (@ FAT129b c2 c3 r1 r3').
    MP. apply H20 in H19. contradiction.
Qed.

Theorem FAT135a : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> x > y
  -> (x + z) > (y + z).
Proof.
  intros. apply FAT134; auto.
Qed.

Theorem FAT135b : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> x = y
  -> (x + z) = (y + z).
Proof.
  intros. subst; auto.
Qed.

Theorem FAT135c : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> x < y
  -> (x + z) < (y + z).
Proof.
  intros. apply FAT135a; auto.
Qed.

Theorem FAT136a : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x + z) > (y + z)
  -> x > y.
Proof.
  intros. destruct (FAT123 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT135b with (z:=z) in H3; auto. CordF.
  - apply FAT135c with (z:=z) in H3; auto. CordF.
Qed.

Theorem FAT136b : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x + z) = (y + z)
  -> x = y .
Proof.
  intros. destruct (FAT123 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT135a with (z:=z) in H3; auto. CordF.
  - apply FAT135c with (z:=z) in H3; auto. CordF.
Qed.

Theorem FAT136c : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x + z) < (y + z)
  -> x < y.
Proof.
  intros. eapply FAT136a; eauto.
Qed.

Theorem FAT137 : ∀ {c1 c2 c3 c4}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> c1 > c2 -> c3 > c4 -> (c1 + c3) > (c2 + c4).
Proof.
  intros. pose proof (@ FAT134 c1 c2 c3). MP.
  pose proof (@ FAT134 c3 c4 c2). MP. rewrite FAT130 in H6; auto.
  rewrite @ FAT130 with c4 c2 in H6; auto.
  eapply FAT126 with (c2 + c3); auto.
Qed.

Theorem FAT138 : ∀ c1 c2 c3 c4, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> (c1 ≥ c2 /\ c3 > c4) \/ (c1 > c2 /\ c3 ≥ c4) -> (c1 + c3) > (c2 + c4).
Proof.
  intros. destruct H3 as [[[|]?]|[?[|]]].
  - apply FAT137; auto.
  - rewrite H3. rewrite FAT130; auto.
    rewrite @ FAT130 with c1 c4; auto. apply FAT134; auto.
  - apply FAT137; auto.
  - rewrite H4. apply FAT134; auto.
Qed.

Theorem FAT139 : ∀ c1 c2 c3 c4, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> c1 ≥ c2 -> c3 ≥ c4 -> (c1 + c3) ≥ (c2 + c4).
Proof.
  intros. destruct H3,H4.
  - left. apply FAT137; auto.
  - left. rewrite H4. apply FAT134; auto.
  - left. apply FAT138; auto. left. split; auto. right. auto.
  - right. rewrite H3,H4. auto.
Qed.

Definition minc c1 c2 := \{λ r, ∃ r1 r2, Num_L r1 c1 /\ r2 ∈ rC
  /\ Num_U r2 c2 /\ r2 < r1 /\ r = (r1 - r2) \}%rC.

Notation " x - y " := (minc x y) : CC_scope.

Fact Le_T140 : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC -> c2 < c1 -> c1 - c2 ∈ CC.
Proof.
  intros. New H. New H0. apply AxiomII in H,H0. 
  destruct H as [_[_[[? [r1'[]]][_ ?]]]].
  destruct H0 as [_[_[[? [r2'[]]]_]]].
  apply NEexE in H as [r1]. apply NEexE in H0 as [r2].
  assert (c1 - c2 ⊂ rC).
  { red; intros. apply AxiomII in H9 as [_ [? [? [? [? [? []]]]]]].
  red in H9. rC x c1. subst; auto. }
  apply AxiomII. repeat split; auto; intros.
  - apply MKT33 with (x:=rC); [apply EnrC|auto].
  - apply NEexE. red in H1. destruct H1 as [r []]. red in H1,H10.
    destruct (H6 _ H1) as [r' []]. rC r' c1. rC r c1.
    exists (r' - r)%rC. assert ((r' - r)%rC ∈ rC). auto.
    apply AxiomII; split; unfold Ensemble; eauto.
    exists r', r. repeat split; auto.
  - exists r1'. split; auto. intro. appA2H H10. 
    destruct H11 as [x[y[?[?[?[]]]]]]. red in H11,H13. rC x c1.
    assert ((x - y) + y > (x - y))%rC.
    { apply FAT94; auto. } rewrite FAT92 in H17; auto.
    rewrite MinrEx in H17; auto.
    assert (r1' > (x - y))%rC. { apply FAT86 with x; auto. 
    apply @ Lemma_FAT119 with c1; auto. } rordF.
  - appA2H H10. destruct H13 as [x[y[?[?[?[]]]]]].
    subst. red in H13,H15. rC x c1. assert (r3 + y < x)%rC.
    { apply (FAT96c _ _ y) in H12; auto. 
    rewrite @ FAT92 with (x - y)%rC y in H12; auto.
    rewrite MinrEx in H12; auto. } appA2G.
    exists (r3 + y)%rC,y. repeat split; auto.
    + red. apply FAT120 with x; auto.
    + rewrite FAT92; auto. apply FAT94; auto.
    + rewrite FAT92; auto.
      assert ((y + r3 > y)%rC). { apply FAT94; auto. }
      apply FAT97b with y; auto.
      rewrite @ FAT92 with (y + r3 - y )%rC y; auto.
      rewrite MinrEx; auto. apply FAT92; auto.
  - appA2H H10. destruct H11 as [x[y[?[?[?[]]]]]].
    red in H11,H13. pose proof (H6 _ H11).
    destruct H16 as [x3[]]. exists (x3 - y)%rC. rC x3 c1. rC x c1.
    assert (y < x3)%rC. { apply FAT86 with x; auto. }
    assert (x3 - y > x - y)%rC.
    { apply FAT97a with y; auto.
      rewrite @ FAT92 with (x - y)%rC y; auto.
      rewrite MinrEx; auto. rewrite FAT92; auto.
      rewrite MinrEx; auto. }
    subst; split; auto. appA2G. exists x3,y. repeat split; auto.
Qed.

Global Hint Resolve Le_T140 : core.

Fact MinCEx_aux : ∀ c1 c2 z, c1 < c2 -> c1 ∈ CC -> Ensemble c2
  -> (∀ r1, r1 ∈ c2 -> ∃ r2, r2 ∈ c2 /\ (r1 < r2)%rC)
  -> z ∈ c2 -> c2 ∈ CC -> ~ (z ∈ c1) -> z ∈ c1 + (c2 - c1).
Proof.
  intros c1 c2 z H H0 H1 H4 H2 H3 H5.
  pose proof (H4 _ H2). destruct H6 as [x[]]. rC x c2. rC z c2.
  assert ((x - z)%rC ∈ rC). auto.
  pose proof (FAT132 (x - z)%rC c1). MP.
  destruct H11 as [y1[y2[?[?[?[]]]]]].
  red in H13,H14. appA2G. exists y1, (x - y2)%rC.
  assert (z > y1)%rC. { apply @ Lemma_FAT119 with c1; auto. }
  assert (y2 > y1)%rC. { apply @ Lemma_FAT119 with c1; auto. }
  assert (x > y2)%rC.
  { apply (FAT96b _ _ z) in H15; auto.
    rewrite @ FAT92 with (x - z)%rC z in H15; auto.
    rewrite MinrEx in H15; auto. rewrite <- H15.
    apply FAT97a with y1; auto. rewrite FAT92; auto.
    rewrite <- FAT93; auto. rewrite MinrEx; auto.
    rewrite FAT92; auto. rewrite @ FAT92 with y2 y1; auto.
    apply FAT96a; auto. }
  repeat split; auto.
  * red. appA2G. exists x, y2. repeat split; auto.
  * apply (FAT96b _ _ z) in H15; auto.
    rewrite @ FAT92 with (x - z)%rC z in H15; auto. 
    rewrite MinrEx in H15; auto. apply FAT97b with y2; auto.
    rewrite FAT93; auto. rewrite @ FAT92 with (x - y2)%rC y2;
    auto. rewrite MinrEx; auto.
    apply (FAT96b _ _ y1) in H15; auto.
    rewrite @ FAT92 in H15; auto. rewrite <- FAT93 in H15; auto.
    rewrite MinrEx in H15; auto. rewrite FAT92; auto.
    rewrite @ FAT92 with y1 x; auto.
Qed.

Fact MinCEx : ∀ {c1 c2}, c1 < c2 -> c1 ∈ CC -> c2 ∈ CC -> c1 + (c2 - c1) = c2.
Proof.
  intros; apply AxiomI; split; intros.
  - apply AxiomII in H2 as [? [r1 [r2 [? []]]]]. subst.
    red in H3,H4. apply AxiomII in H4 as [?[r3[r4[?[?[?[]]]]]]].
    subst. red in H5,H7. rC r3 c2. rC r1 c1.
    eapply FAT120; try apply H5; eauto.
    assert (r4 + (r3 - r4) = r3)%rC. { apply MinrEx; auto. } 
    pattern r3 at 2; rewrite <- H11. apply FAT96c; auto.
    apply @ Lemma_FAT119 with c1; auto.
  - New H1. appA2H H1. destruct H4 as [_[_[_ ?]]].
    destruct (classic (~ (z ∈ c1))).
    + apply MinCEx_aux; auto.
    + apply -> NNPP in H5. pose proof H as [r [? ?]].
      assert (r ∈ c1 + (c2 - c1)). { apply MinCEx_aux; auto. }
      red in H6. rC z c2; rC r c2. apply @ FAT120 with r; auto.
      apply @ Lemma_FAT119 with c1; auto.
Qed.

Theorem FAT140a : ∀ c1 c2 c c', c1 ∈ CC -> c2 ∈ CC ->c ∈ CC -> c' ∈ CC
  -> c1 + c = c2 -> c1 + c' = c2 -> c = c'.
Proof.
  intros. rewrite <- H3 in H4.
  destruct (@ FAT123 c c') as [H5|[H5|H5]]; auto.
  - apply (FAT135a _ _ c1) in H5; auto.
    rewrite FAT130 in H5; auto.
    rewrite @ FAT130 with c' c1 in H5; auto. CordF.
  - apply (FAT135c _ _ c1) in H5; auto.
    rewrite FAT130 in H5; auto.
    rewrite @ FAT130 with c' c1 in H5; auto. CordF.
Qed.

Theorem FAT140b : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 > c2
  -> ∃ c, c ∈ CC /\ (c2 + c) = c1.
Proof.
  intros. exists (c1 - c2). split; auto. apply MinCEx; auto.
Qed.

(* SECTION IV Multiplication *)

Definition mulc c1 c2 := \{λ c, ∃ r1 r2, Num_L r1 c1 /\ Num_L r2 c2
  /\ c = (r1 · r2)%rC \}.

Notation " x · y " := (mulc x y)(at level 40) : CC_scope.

Theorem FAT141a : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC -> c1 · c2 ∈ CC.
Proof.
  intros. pose proof H as C1. pose proof H0 as C2.
  apply AxiomII in H as [_ [? [[? [r3 []]] []]]]. 
  apply AxiomII in H0 as [_ [? [[? [r4 []]] []]]].
  apply NEexE in H1 as [r1]. apply NEexE in H6 as [r2].
  assert (mulc c1 c2 ⊂ rC).
  { red; intros. apply AxiomII in H11 as [_ [? [? [? []]]]].
    subst; auto. }
  apply AxiomII; repeat split; auto; intros.
  - apply MKT33 with (x:=rC); [apply EnrC|auto].
  - apply NEexE. exists (mulr r1 r2).
    apply AxiomII; split; unfold Ensemble; eauto.
  - exists (mulr r3 r4); split; auto. intro. appA2H H12.
    destruct H13 as [r1'[r2'[?[]]]]. red in H13,H14.
    assert (r3 > r1')%rC.
    { apply @ Lemma_FAT119 with c1; auto. }
    assert (r4 > r2')%rC.
    { apply @ Lemma_FAT119 with c2; auto. }
    assert ((r3 · r4) > (r1' · r2'))%rC.
    { apply FAT107; auto. } rordF.
  - apply AxiomII; split; unfold Ensemble; eauto. 
    apply AxiomII in H12 as [_ [r6 [r7 [? []]]]].
    exists r6, (divr r5 r6). 
    subst. repeat split; auto.
    + red. apply (H9 _ _ H15); auto. apply FAT106c with r6; auto.
      rewrite FAT102; auto. rewrite DivrEx; auto.
      rewrite FAT102; auto.
    + rewrite DivrEx; auto.
  - apply AxiomII in H12 as [_ [r5 [r6 [? []]]]]. subst.
    destruct (H5 _ H12) as [r7 []]. exists (mulr r7 r6). split.
    + apply AxiomII; split; unfold Ensemble; eauto.
    + apply FAT105c; auto.
Qed.

Global Hint Resolve FAT141a : core.

Theorem FAT141b : ∀ c1 c2 r1 r2 r, c1 ∈ CC -> c2 ∈ CC -> r1 ∈ rC -> r2 ∈ rC
  -> r ∈ c1 · c2 -> Num_U r1 c1 -> Num_U r2 c2 -> ~ r = (r1 · r2)%rC.
Proof.
  intros. red in H4,H5. intro. subst. appA2H H3. 
  destruct H6 as [r3[r4[?[]]]].
  red in H6,H7. rC r3 c1; rC r4 c2.
  assert (r1 > r3)%rC.
  { apply @ Lemma_FAT119 with c1; auto. }
  assert (r2 > r4)%rC.
  { apply @ Lemma_FAT119 with c2; auto. }
  assert ((r1 · r2) > (r3 · r4))%rC.
  { apply FAT107; auto. } rordF.
Qed.

Theorem FAT142 : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC -> c1 · c2 = c2 · c1.
Proof.
  intros. apply AxiomII in H as [_ [H _]].
  apply AxiomII in H0 as [_ [H0 _]]. 
  apply AxiomI; split; intros.
  - apply AxiomII in H1 as [? [r1 [r2 [? []]]]]; subst.
    apply AxiomII. split; auto. exists r2, r1. repeat split; auto.
    apply FAT102; auto.
  - apply AxiomII in H1 as [? [r1 [r2 [? []]]]]; subst.
    apply AxiomII. split; auto. exists r2, r1. repeat split; auto.
    apply FAT102; auto.
Qed.

Theorem FAT143 : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> (c1 · c2) · c3 = c1 · (c2 · c3).
Proof.
  intros. apply AxiomI. split; intros.
  - appA2H H2. destruct H3 as [r12[r3[?[]]]]. red in H3,H4. subst.
    appA2H H3. destruct H5 as [r1[r2[?[]]]]. subst. appA2G.
    exists r1, (r2 · r3)%rC. red in H5,H6.
    rC r1 c1. rC r2 c2. rC r3 c3. repeat split; auto.
    + red. appA2G.
    + rewrite FAT103; auto.
  - appA2H H2. destruct H3 as [r1[r23[?[?]]]]. red in H3,H4. subst.
    appA2H H4. destruct H5 as [r2[r3[?[]]]]. subst. appA2G.
    exists (r1 · r2)%rC, r3. red in H5,H6.
    rC r1 c1. rC r2 c2. rC r3 c3. repeat split; auto.
    + red. appA2G.
    + rewrite <- FAT103; auto.
Qed.

Theorem FAT144a : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> c1 · (c2 + c3) = (c1 · c2) + (c1 · c3).
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H2. destruct H3 as [r1[r23[?[]]]]. appA2G. red in H3,H4.
    subst. appA2H H4. destruct H5 as [r2[r3[?[]]]]. subst.
    red in H5,H6. exists (r1 · r2)%rC, (r1 · r3)%rC. 
    rC r1 c1. rC r2 c2. rC r3 c3.
    repeat split; try red; try appA2G. apply FAT104a; auto.
  - appA2H H2. destruct H3 as [r12[r13[?[]]]]. red in H3,H4.
    appA2H H3. appA2H H4. destruct H6 as [r1[r2[?[]]]].
    destruct H7 as [r1'[r3[?[]]]]. subst. red in H6,H8,H7,H10.
    rC r1 c1. rC r2 c2. rC r3 c3. rC r1' c1.
    destruct @ FAT81 with r1 r1' as [|[|]]; auto. 
    + appA2G. rewrite <- H13. exists r1, (r2 + r3)%rC. 
      repeat split; try red; try appA2G; auto.
      rewrite FAT104a; auto.
    + assert ((r1 · r2 + r1' · r3) < r1 · (r2 + r3))%rC.
      { rewrite FAT104a; auto. rewrite FAT92; auto. 
      rewrite @ FAT92 with (r1 · r2)%rC (r1 · r3)%rC; auto.
      apply FAT96c; auto. apply FAT105c; auto. }
      apply FAT120 with (r1 · (r2 + r3))%rC; auto. red.
      appA2G. exists r1, (r2 + r3)%rC.
      repeat split; try red; try appA2G; auto.
    + assert ((r1 · r2 + r1' · r3) < r1' · (r2 + r3))%rC.
      { rewrite FAT104a; auto. apply FAT96c; auto.
        apply FAT105c; auto. } 
      apply FAT120 with (r1' · (r2 + r3))%rC; auto. red. appA2G. 
      exists r1', (r2 + r3)%rC.
      repeat split; try red; try appA2G; auto.
Qed.

Theorem FAT144b : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> (c2 + c3) · c1 = (c2 · c1) + (c3 · c1).
Proof.
  intros. rewrite FAT142; auto. rewrite @ FAT142 with c2 c1; auto.
  rewrite @ FAT142 with c3 c1; auto. apply FAT144a; auto.
Qed.

Theorem FAT145a : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> x > y
  -> (x · z) > (y · z).
Proof.
  intros. apply FAT140b in H2; auto. destruct H2 as [c[]].
  rewrite <- H3. rewrite FAT142; auto. rewrite FAT144a; auto.
  rewrite FAT142; auto. eapply FAT133; auto.
Qed.

Theorem FAT145b : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> x = y
  -> (x · z) = (y · z).
Proof.
  intros. subst; auto.
Qed.

Theorem FAT145c : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> x < y
  -> (x · z) < (y · z).
Proof.
  intros. apply FAT145a; auto.
Qed.

Corollary FAT144c : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> c2 > c3 -> c1 · (c2 - c3) = (c1 · c2) - (c1 · c3).
Proof.
  intros. New H2. apply (FAT145a _ _ c1) in H2; auto.
  rewrite FAT142 in H2; auto.
  rewrite (@ FAT142 c3 c1) in H2; auto.
  apply FAT136b with (c1 · c3); auto.
  rewrite @ FAT130 with (c1 · c2 - c1 · c3) (c1 · c3); auto.
  rewrite MinCEx; auto. rewrite <- FAT144a; auto.
  rewrite @ FAT130 with (c2 - c3) c3; auto.
  rewrite MinCEx; auto.
Qed.

Corollary FAT144d : ∀ {c1 c2 c3}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC
  -> c2 > c3 -> (c2 - c3) · c1 = (c2 · c1) - (c3 · c1).
Proof.
  intros. rewrite FAT142; auto. rewrite @ FAT142 with c2 c1; auto.
  rewrite @ FAT142 with c3 c1; auto. apply FAT144c; auto.
Qed.

Theorem FAT146a : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x · z) > (y · z)
  -> x > y.
Proof.
  intros. destruct (FAT123 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT145b with (z:=z) in H3; auto. CordF.
  - apply FAT145c with (z:=z) in H3; auto. CordF.
Qed.

Theorem FAT146b : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x · z) = (y · z)
  -> x = y .
Proof.
  intros. destruct (FAT123 H H0) as [H3 | [H3 | H3]]; auto.
  - apply FAT145a with (z:=z) in H3; auto. CordF.
  - apply FAT145c with (z:=z) in H3; auto. CordF.
Qed.

Theorem FAT146c : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x · z) < (y · z)
  -> x < y.
Proof.
  intros. eapply FAT146a; eauto.
Qed.

Theorem FAT147 : ∀ {c1 c2 c3 c4}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> c1 > c2 -> c3 > c4 -> (c1 · c3) > (c2 · c4).
Proof.
  intros. apply (FAT145a _ _ c3) in H3; auto.
  apply (FAT145a _ _ c2) in H4; auto. rewrite FAT142 in H4; auto.
  rewrite (@ FAT142 c4 c2) in H4; auto.
  apply FAT126 with (c2 · c3); auto.
Qed.

Theorem FAT148 : ∀ {c1 c2 c3 c4}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> (c1 ≥ c2 /\ c3 > c4) \/ (c1 > c2 /\ c3 ≥ c4) -> (c1 · c3) > (c2 · c4).
Proof.
  intros. destruct H3 as [[[|]?]|[?[|]]].
  - apply FAT147; auto.
  - subst. rewrite FAT142; auto. rewrite @ FAT142 with c1 c4; auto. 
    apply FAT145a; auto.
  - apply FAT147; auto.
  - subst. apply FAT145a; auto.
Qed.

Theorem FAT149 : ∀ {c1 c2 c3 c4}, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> c1 ≥ c2 -> c3 ≥ c4 -> (c1 · c3) ≥ (c2 · c4).
Proof.
  intros. destruct H3,H4.
  - left. apply FAT147; auto.
  - left. subst. apply FAT145a; auto.
  - left; subst. rewrite FAT142; auto.
    rewrite @ FAT142 with c1 c4; auto. apply FAT145a; auto.
  - subst. right. auto.
Qed.

(*R* 有理分割（当r是有理数时）*)
Definition rtoC r := \{ λ r0, r0 ∈ rC /\ r0 < r \}%rC.

Fact r2CT : ∀ r, r ∈ rC -> rtoC r ∈ CC.
Proof.
  intros. assert (rtoC r ⊂ rC). 
  { red; intros. apply AxiomII in H0; tauto. }
  apply AxiomII. repeat split; auto; intros.
  - apply MKT33 with (x:=rC); [apply EnrC| auto].
  - apply NEexE. pose proof (FAT90 r). MP.
    destruct H2 as [r0 []]. exists r0. appA2G.
  - exists r. split; auto. intro.
    apply AxiomII in H1 as [_ []]. rordF.
  - apply AxiomII in H1 as [_ []].
    apply AxiomII; repeat split; unfold Ensemble; eauto.
    apply FAT86 with r1; auto.
  - appA2H H1. destruct H2. pose proof (FAT91 r1 r). MP.
    destruct H5 as [r0[?[]]]. exists r0. split; auto. appA2G.
Qed.

Theorem FAT150 : ∀ r, r ∈ rC -> rtoC r ∈ CC.
Proof.
  apply r2CT.
Qed.

Theorem FAT151 : ∀ c, c ∈ CC -> c · (rtoC (Ntor One)) = c.
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H0. destruct H1 as [r[r1[?[]]]]. red in H1,H2.
    appA2H H2. destruct H4. subst. rC r c.
    assert (r · r1 < r)%rC.
    { pose proof (mulr1 r). MP. pattern r at 2; rewrite <- H7.
    rewrite FAT102; auto. apply FAT105c; auto. }
    apply FAT120 with r; auto.
  - appA2G. New H. appA2H H. destruct H2 as [_[_[_ ?]]].
    pose proof (H2 _ H0). destruct H3 as [x1[]].
    exists x1, ((divr (Ntor One) x1) · z)%rC.
    rC z c; rC x1 c. pose proof (N2rT One FAA1).
    repeat split; auto. 
    + red. appA2G. split; auto.
      assert ((divr (Ntor One) x1) · x1 = Ntor One)%rC.
      { rewrite FAT102; auto. apply DivrEx; auto. }
      pattern (Ntor One) at 2; rewrite <- H8. rewrite FAT102; auto.
      rewrite @ FAT102 with (divr (Ntor One) x1) x1; auto.
      apply FAT105c; auto.
    + rewrite <- FAT103; auto. rewrite DivrEx; auto.
      rewrite mulr1; auto.
Qed.

(*最小上类数（当r是有理数c是分割）*)
Definition LNU r c := Num_U r c
  /\ (∀ r0, r0 ∈ rC /\ Num_U r0 c -> ~ r0 < r)%rC.

Definition recC c := \{ λ r, r ∈ rC /\ ∃ r0, r0 ∈ rC
  /\ Num_U r0 c /\ (~ LNU r0 c) /\ r = (divr (Ntor One) r0) \}.

Fact LNU1 : ∀ r c, Num_U r c -> ~ LNU r c
  -> ∃ r0, r0 ∈ rC /\ Num_U r0 c /\ (r0 < r)%rC.
Proof.
  intros. unfold LNU in H0. apply notandor in H0. destruct H0.
  - contradiction.
  - assert (~ (∀ r0, ~ ~(r0 ∈ rC /\ Num_U r0 c -> ~ (r0 < r)%rC))).
    { intro. elim H0. intros r0. apply NNPP; auto. }
    apply not_all_not_ex in H1 as [r1].
    apply imply_to_and in H1 as [[]].
    apply -> NNPP in H3. eauto.
Qed.

Fact RecCp : ∀ c, c ∈ CC -> recC c ∈ CC.
Proof.
  intros. assert (recC c ⊂ rC). { red. intros. appA2H H0. tauto. }
  apply AxiomII. repeat split; auto; intros.
  - apply MKT33 with (x:=rC); [apply EnrC| auto].
  - apply NEexE. New H. appA2H H. destruct H2 as [_[[_ ?]_]].
    destruct H2 as [r[]]. exists (divr (Ntor One) (r + r)%rC).
    pose proof (N2rT One FAA1).
    assert (divr (Ntor One) (r + r)%rC ∈ rC). auto.
    appA2G. split; auto. exists (r + r)%rC. repeat split; auto.
    + red. assert ((r + r) > r)%rC. { apply FAT94; auto. }
      apply FAT119 with r; auto.
    + intro. red in H6. destruct H6. pose proof (H7 r).
      elim H8. tauto. apply FAT94; auto.
  - New H. appA2H H. destruct H2 as [_[[? _]_]]. apply NEexE in H2.
    destruct H2 as [x1]. exists (divr (Ntor One) x1).
    pose proof (N2rT One FAA1). rC x1 c. split; auto. intro.
    appA2H H5. destruct H6 as [?[x[?[?[]]]]]. red in H8.
    apply (FAT105b _ _ x1) in H10; auto.
    rewrite FAT102 in H10; auto. rewrite DivrEx in H10; auto.
    apply (FAT105b _ _ x) in H10; auto.
    rewrite @ FAT102 with (divr (Ntor One) x · x1)%rC x in H10;
    auto. rewrite <- FAT103 in H10; auto.
    rewrite DivrEx in H10; auto. rewrite mulr1 in H10; auto.
    rewrite mulr1 in H10; auto. rewrite H10 in H8. contradiction.
  - appA2H H1. destruct H4 as [?[x[?[?[]]]]]. appA2G. split; auto.
    exists (divr (Ntor One) r2). pose proof (N2rT One FAA1).
    assert ((divr (Ntor One) r2 > x)%rC).
    { apply (FAT106a _ _ r2); auto.
    rewrite FAT102; auto. rewrite DivrEx; auto.
    rewrite H8 in H3. apply (FAT105c _ _ x) in H3; auto.
    rewrite @ FAT102 with (divr (Ntor One) x) x in H3; auto.
    rewrite DivrEx in H3; auto.
    rewrite FAT102; auto. }  repeat split; auto.
    + red. rewrite H8 in H3. apply FAT119 with x; auto.
    + intro. red in H11. destruct H11. pose proof (H12 x).
      elim H13; tauto.
    + apply DivrUn; auto. rewrite FAT102; auto.
      rewrite DivrEx; auto.
  - appA2H H1. destruct H2 as [?[x[?[?[]]]]].
    pose proof (LNU1 x c). MP. destruct H7 as [x1[?[]]].
    pose proof (FAT91 x1 x). MP. destruct H11 as [x2[?[]]].
    exists (divr (Ntor One) x2). split.
    + appA2G. pose proof (N2rT One FAA1). split; auto.
      exists x2. repeat split; auto.
      * apply FAT119 with x1; auto.
      * intro. red in H14. destruct H14.
        pose proof (H15 x1). apply H16; tauto.
    + rewrite H6. apply FAT106c with x; auto. rewrite FAT102; auto.
      rewrite DivrEx; auto. apply FAT106c with x2; auto.
      rewrite @ FAT102 with (divr (Ntor One) x2 · x)%rC x2; auto.
      rewrite <- FAT103; auto. rewrite DivrEx; auto.
      rewrite mulr1; auto. rewrite mulr1; auto.
Qed.

Global Hint Resolve r2CT RecCp : core.

Lemma Lemma_FAT152: ∀ c, c ∈ CC -> c · (recC c) = (rtoC (Ntor One)).
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H0. destruct H1 as [r[r'[?[]]]]. appA2G. subst.
    red in H1,H2. pose proof (RecCp c H). rC r c; rC r' (recC c).
    split; auto. appA2H H2. destruct H6 as [?[r0[?[?[]]]]].
    subst. apply FAT106c with r0; auto. rewrite FAT103; auto.
    rewrite @ FAT102 with (divr (Ntor One) r0) r0; auto.
    rewrite DivrEx; auto. rewrite mulr1; auto. rewrite FAT102; auto.
    rewrite mulr1; auto. apply @ Lemma_FAT119 with c; auto.
  - appA2H H0. destruct H1. New H. appA2H H3.
    destruct H4 as [_ [[? _] _]]. apply NEexE in H4.
    destruct H4 as [x].
    pose proof (FAT132 ((Ntor One - z) · x)%rC c).
    rC x c. assert (((Ntor One - z) · x)%rC ∈ rC). auto. MP.
    destruct H5 as [x1[x2[?[?[?[]]]]]]. appA2G.
    exists x1, (divr (Ntor One) (divr x1 z)). repeat split; auto.
    + red. assert (divr (Ntor One) (divr x1 z) ∈ rC). auto.
      appA2G. split; auto. exists (divr x1 z).
      assert (divr x1 z > x2)%rC.
      { pose proof (@ Lemma_FAT119 c x1 x2). MP. 
      assert ((x2 - x1) < ((Ntor One) - z) · x2)%rC.
      { rewrite H11. rewrite FAT102; auto.
      rewrite @ FAT102 with (Ntor One - z)%rC x2; auto.
      apply FAT105c; auto. apply @ Lemma_FAT119 with c; auto. }
      assert (z · x2 < x1)%rC.
      { apply FAT97c with (x2 - x1)%rC; auto. rewrite MinrEx; auto.
      assert (x2 = ((Ntor One) - z) · x2 + z · x2)%rC.
      { rewrite FAT102; auto. rewrite @ FAT102 with z x2; auto.
      rewrite <- FAT104a; auto. rewrite FAT92; auto.
      rewrite MinrEx; auto. rewrite FAT102; auto.
      rewrite mulr1; auto. } pattern x2 at 3; rewrite H15.
      rewrite FAT92; auto. apply FAT96c; auto. }
      assert (x2 = ((divr (Ntor One) z) · (z · x2)))%rC.
      { rewrite <- FAT103; auto.
      rewrite @ FAT102 with (divr (Ntor One) z) z; auto.
      rewrite DivrEx; auto. rewrite mulr1; auto. }
      assert ((divr (Ntor One) z · x1) = (divr x1 z))%rC.
      { apply FAT106b with z; auto. rewrite FAT102; auto. 
      rewrite @ FAT102 with (divr x1 z) z; auto.
      rewrite DivrEx; auto. rewrite <- FAT103; auto.
      rewrite DivrEx; auto. rewrite mulr1; auto. }
      rewrite H16, <- H17. rewrite FAT102; auto. 
      rewrite @ FAT102 with (divr (Ntor One) z) (z · x2)%rC; auto.
      apply FAT105c; auto. }
      repeat split; auto.
      * red. apply FAT119 with x2; auto.
      * intro. red in H14. destruct H14.
        pose proof (H15 x2). apply H16; tauto.
    + apply FAT106b with (divr x1 z); auto. rewrite FAT103; auto.
      rewrite @ FAT102 with (divr (Ntor One) (divr x1 z))
      ( divr x1 z); auto. rewrite DivrEx; auto.
      rewrite DivrEx; auto. rewrite FAT102; auto.
      rewrite mulr1; auto.
Qed.

Theorem FAT152 : ∀ c, c ∈ CC -> ∃ c1, c1 ∈ CC /\ c · c1 = (rtoC (Ntor One)).
Proof.
  intros. exists (recC c). split; auto. apply Lemma_FAT152; auto.
Qed.

Definition divC c1 c2 := c1 · (recC c2).

Fact DivCp : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> (divC c1 c2) ∈ CC.
Proof.
  intros. unfold divC. auto.
Qed.

Global Hint Resolve DivCp : core.

Fact DivCEx :  ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c2 · (divC c1 c2) = c1.
Proof.
  intros. unfold divC. rewrite FAT142; auto.
  rewrite FAT143; auto. rewrite @ FAT142 with (recC c2) c2; auto.
  rewrite Lemma_FAT152; auto. apply FAT151; auto.
Qed.

Theorem FAT153a : ∀ c1 c2 c3 c4, c1 ∈ CC -> c2 ∈ CC -> c3 ∈ CC -> c4 ∈ CC
  -> c2 · c3 = c1 ->  c2 · c4 = c1 -> c3 = c4.
Proof.
  intros. rewrite <- H3 in H4. rewrite FAT142 in H4; auto.
  rewrite @ FAT142 with c2 c3 in H4; auto.
  apply FAT146b in H4; auto.
Qed.

Fact mulc1 : ∀ c, c ∈ CC -> rtoC (Ntor One) · c = c.
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H0. destruct H1 as [r1[r[?[]]]]. red in H1,H2.
    appA2H H1. destruct H4. subst. rC r c.
    apply @ FAT120 with r; auto.
    apply (FAT105c _ _ r) in H5; auto. rewrite mulr1 in H5; auto.
  - appA2G. New H. appA2H H1. destruct H2 as [_[_[_ ?]]].
    pose proof (H2 z H0). destruct H3 as [r[]].
    exists (divr z r),r. rC z c. rC r c. repeat split; auto.
    + red. appA2G. split; auto. apply divr1; auto.
    + rewrite FAT102; auto. rewrite DivrEx; auto.
Qed.

Fact mulc2 : ∀ x y z, x ∈ CC -> y ∈ CC -> z ∈ CC -> (x · y) · z = (x · z) · y.
Proof.
  intros. rewrite @ FAT142 with x y; auto.
  rewrite FAT143; auto. rewrite FAT142; auto.
Qed.

Theorem FAT153b : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC
  -> ∃ c3, c3 ∈ CC /\ c2 · c3 = c1.
Proof.
  intros. pose proof (FAT152 c2 H0). destruct H1 as [c[]].
  exists (c · c1). split; auto. rewrite <- FAT143; auto.
  rewrite H2. apply mulc1; auto.
Qed.

(* SECTION V Rational Cuts and Integral Cuts *)

(*有理分割（当r是有理数）*)
Definition Cut_R r := rtoC r.

Fact CutRp : ∀ r, r ∈ rC -> Cut_R r ∈ CC.
Proof.
  intros. auto.
Qed.

(*有理分割集*)
Definition RCC := \{ λ c, ∃ r, r ∈ rC /\ c = Cut_R r \}.

(*整分割（当n是自然数）*)
Definition Cut_I n := rtoC (Ntor n).

Fact CutIp : ∀ n, n ∈ Nat -> Cut_I n ∈ CC.
Proof.
  intros. unfold Cut_I. assert (Ntor n ∈ rC). auto. auto.
Qed.

Global Hint Resolve CutRp CutIp : core.

(*整分割集*)
Definition NCC := \{ λ c, ∃ n, n ∈ Nat /\ c = Cut_I n \}.

Theorem FAT154a1 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (r1 > r2)%rC
  -> (Cut_R r1) > (Cut_R r2).
Proof.
  intros. unfold Cut_R. red. exists r2. split; red.
  - appA2G.
  - intro. appA2H H2. destruct H3. rordF.
Qed.

Theorem FAT154a2 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (r1 = r2)%rC
  -> (Cut_R r1) = (Cut_R r2).
Proof.
  intros. rewrite H1; auto.
Qed.

Theorem FAT154a3 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (r1 < r2)%rC
  -> (Cut_R r1) < (Cut_R r2).
Proof.
  intros. apply FAT154a1; auto.
Qed.

Theorem FAT154b1 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (Cut_R r1) > (Cut_R r2)
  -> (r1 > r2)%rC.
Proof.
  intros. unfold Cut_R in H1. red in H1. destruct H1 as [r[]].
  red in H1,H2. appA2H H1. destruct H3. assert (r ≥ r2)%rC.
  { destruct @ FAT81 with r r2; auto. right. auto.
  destruct H5. left; auto.
  assert (r ∈ rtoC r2). { appA2G. } contradiction. }
  destruct H5.
  - eapply FAT86; eauto.
  - rewrite H5; auto.
Qed.

Theorem FAT154b2 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (Cut_R r1) = (Cut_R r2)
  -> (r1 = r2)%rC.
Proof.
  intros. destruct @ FAT81 with r1 r2; auto. destruct H2.
  - apply FAT154a1 in H2; auto. CordF.
  - apply FAT154a3 in H2; auto. CordF.
Qed.

Theorem FAT154b3 : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (Cut_R r1) < (Cut_R r2)
  -> (r1 < r2)%rC.
Proof.
  intros. apply FAT154b1; auto.
Qed.

Theorem FAT155a : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC
  -> Cut_R (r1 + r2)%rC = (Cut_R r1) + (Cut_R r2).
Proof.
  intros. unfold Cut_R. apply AxiomI; split; intros.
  - appA2H H1. destruct H2. appA2G. 
    exists (r1 · (divr z (r1 + r2)))%rC,
    (r2 · (divr z (r1 + r2)))%rC. repeat split; auto.
    + red. assert ((r1 · divr z (r1 + r2))%rC ∈ rC). auto. appA2G.
      split; auto. apply FAT106c with (r1 + r2)%rC; auto.
      rewrite FAT103; auto.
      rewrite @ FAT102 with (divr z (r1 + r2))%rC (r1 + r2)%rC;
      auto. rewrite DivrEx; auto. rewrite FAT102; auto.
      rewrite @ FAT102 with r1 (r1 + r2)%rC; auto.
      apply FAT105c; auto.
    + red. assert ((r2 · divr z (r1 + r2))%rC ∈ rC). auto. appA2G.
      split; auto. apply FAT106c with (r1 + r2)%rC; auto.
      rewrite FAT103; auto.
      rewrite @ FAT102 with (divr z (r1 + r2))%rC (r1 + r2)%rC; auto.
      rewrite DivrEx; auto. rewrite FAT102; auto.
      rewrite @ FAT102 with r2 (r1 + r2)%rC; auto.
      apply FAT105c; auto.
    + rewrite <- FAT104b; auto. rewrite DivrEx; auto.
  - appA2H H1. destruct H2 as [r1'[r2'[?[]]]].
    subst. appA2G. red in H2,H3.
    assert ((rtoC r1) ∈ CC). auto. assert ((rtoC r2) ∈ CC). auto. 
    rC r1' (rtoC r1); rC r2' (rtoC r2). split; auto.
    appA2H H2. appA2H H3. destruct H8,H9. eapply FAT98; auto.
Qed.

Theorem FAT155b : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC -> (r1 > r2)%rC
  -> Cut_R (r1 - r2)%rC = (Cut_R r1) - (Cut_R r2).
Proof.
  intros. assert (r1 = (r1 - r2) + r2)%rC.
  { rewrite FAT92; auto. rewrite MinrEx; auto. }
  apply FAT154a2 in H2; auto. rewrite FAT155a in H2; auto.
  assert (Cut_R r1 ∈ CC). auto. assert (Cut_R r2 ∈ CC). auto.
  pose proof (FAT154a1 r1 r2). MP.
  apply FAT136b with (Cut_R r2); auto.
  rewrite @ FAT130 with (Cut_R r1 - Cut_R r2) (Cut_R r2); auto.
  rewrite MinCEx; auto.
Qed.

Theorem FAT155c : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC
  -> Cut_R (r1 · r2)%rC = (Cut_R r1) · (Cut_R r2).
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H1. destruct H2. appA2G.
    apply FAT91 in H3; auto. destruct H3 as [r[?[]]].
    exists (divr r r2), (r2 · (divr z r))%rC. repeat split; auto.
    + red. appA2G. split; auto. apply FAT106c with r2; auto.
      rewrite FAT102; auto. rewrite DivrEx; auto.
    + red. assert (r2 · divr z r ∈ rC)%rC. auto.
      appA2G. split; auto. pattern r2 at 2; rewrite <- mulr1; auto.
      rewrite FAT102; auto. apply FAT105c; auto. apply divr1; auto.
    + rewrite <- FAT103; auto.
      rewrite @ FAT102 with (divr r r2) r2; auto.
      rewrite DivrEx; auto. rewrite DivrEx; auto.
  - appA2H H1. destruct H2 as [r1'[r2'[?[]]]]. subst.
    appA2G. red in H2,H3. appA2H H2. appA2H H3.
    destruct H4,H5. split; auto. eapply FAT107; auto.
Qed.

Theorem FAT155d : ∀ r1 r2, r1 ∈ rC -> r2 ∈ rC
  -> Cut_R (divr r1 r2) = divC (Cut_R r1) (Cut_R r2).
Proof.
  intros. assert (r1 = (divr r1 r2) · r2)%rC.
  { rewrite FAT102; auto. rewrite DivrEx; auto. }
  apply FAT154a2 in H1; auto. rewrite FAT155c in H1; auto.
  assert ((Cut_R r1) ∈ CC). auto. assert ((Cut_R r2) ∈ CC). auto.
  apply FAT146b with (Cut_R r2); auto.
  rewrite @ FAT142 with (divC (Cut_R r1) (Cut_R r2)) (Cut_R r2);
  auto. rewrite DivCEx; auto.
Qed.

Definition Csuc := \{\ λ u v, ∃ n, n ∈ Nat
  /\ u = (Cut_I n) /\ v = (Cut_I n⁺)\}\.

Fact csucp : ∀ n, n ∈ Nat -> Csuc [Cut_I n] = Cut_I n⁺.
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H0. apply H1. appA2G. apply AxiomII'; repeat split; rxo.
  - appA2G. intros. appA2H H1. apply AxiomII' in H2.
    destruct H2 as [?[n0[?[]]]]. unfold Cut_I in H4.
    apply FAT154b2 in H4; auto. apply Ntor2a in H4; auto.
    subst; auto.
Qed.

Theorem FAT156a : Cut_I One ∈ NCC.
Proof.
  appA2G.
Qed.

Theorem FAT156b : ∀ n, n ∈ Nat -> (Cut_I n) ∈ NCC
  -> Csuc [Cut_I n] ∈ NCC.
Proof.
  intros. rewrite csucp; auto. appA2H H0. appA2G.
Qed.

Theorem FAT156c : ∀ n, n ∈ Nat -> Csuc [Cut_I n] <> Cut_I One.
Proof.
  intros. intro. rewrite csucp in H0; auto.
  unfold Cut_I in H0. apply FAT154b2 in H0; auto.
  apply Ntor2a in H0; auto. pose proof (FAA3 n H). contradiction.
Qed.

Theorem FAT156d : ∀ n1 n2, n1 ∈ Nat -> n2 ∈ Nat
  -> Csuc [Cut_I n1] = Csuc [Cut_I n2] -> (Cut_I n1) = (Cut_I n2).
Proof.
  intros. rewrite csucp in H1; auto. rewrite csucp in H1; auto.
  unfold Cut_I in H1. apply FAT154b2 in H1; auto.
  apply Ntor2a in H1; auto. apply FAA4 in H1; auto. subst; auto.
Qed.

Theorem FAT156e : ∀ M, M ⊂ NCC -> (Cut_I One) ∈ M
  -> (∀ n, (Cut_I n) ∈ M -> Csuc [Cut_I n] ∈ M) -> M = NCC.
Proof.
  intros. apply AxiomI; split; intros.
  - red in H. apply H in H2; auto.
  - appA2H H2. destruct H3 as [n[]]. subst.
    apply MathInd with (n:=n); intros; auto.
    rewrite <- csucp; auto.
Qed.

Theorem FAT157 : ∀ r c, r ∈ rC -> c ∈ CC -> LNU r c -> Cut_R r = c.
Proof.
  intros. red in H1. destruct H1. apply AxiomI; split; intros.
  - appA2H H3. destruct H4. apply NNPP. intro.
    assert (~ (z < r)%rC). { apply H2. tauto. } contradiction.
  - appA2G. rC z c. split; auto. apply @ Lemma_FAT119 with c; auto.
Qed.

Theorem FAT158a : ∀ r c, r ∈ rC -> c ∈ CC -> Num_L r c <-> Cut_R r < c.
Proof.
  intros. split; intros.
  - red in H1. unfold Cut_R. red. exists r. split; auto. red.
    intro. appA2H H2. destruct H3. rordF.
  - unfold Cut_R in H1. red. red in H1. destruct H1 as [r0[]].
    red in H1,H2. rC r0 c. destruct (@ FAT81 r r0 H H3); auto.
    + rewrite H4; auto.
    + destruct H4. 
      * assert (r0 ∈ rtoC r). { appA2G. } contradiction.
      * apply FAT120 with r0; auto.
Qed.

Theorem FAT158b : ∀ r c, r ∈ rC -> c ∈ CC -> Num_U r c <-> Cut_R r ≥ c.
Proof.
  intros. split; intros.
  - red in H1. unfold Cut_R. destruct (classic (LNU r c)).
    + right. pose proof (FAT157 r c). MP. auto.
    + left. red. pose proof (LNU1 r c). MP.
      destruct H3 as [r0[?[]]]. exists r0.
      split; auto. red. appA2G.
  - unfold Cut_R in H1. red. destruct H1.
    + red in H1. destruct H1 as [r0[]]. red in H1,H2. appA2H H1.
      destruct H3. apply FAT119 with r0; auto.
    + rewrite H1. intro. appA2H H2. destruct H3. rordF.
Qed.

Theorem FAT159 : ∀ c1 c2, c1 ∈ CC -> c2 ∈ CC -> c1 < c2
  -> ∃ r, r ∈ rC /\ c1 < Cut_R r /\ Cut_R r < c2.
Proof.
  intros. red in H1. destruct H1 as [x[]]. red in H1,H2.
  New H0. appA2H H3. destruct H4 as [_[_[_ ?]]].
  pose proof (H4 x H1). destruct H5 as [r[]].
  exists r. rC r c2. rC x c2. pose proof (@ FAT119 c1 x r). MP.
  repeat split; auto.
  - apply FAT154a3 in H6; auto. apply FAT127 with (Cut_R x); auto.
    left. split; auto. apply FAT158b; auto.
  - apply FAT158a; auto.
Qed.

Lemma Lemma_FAT160 : ∀ {c1 c2}, c1 ∈ CC -> c2 ∈ CC -> c1 ≤ c2 \/ c2 < c1.
Proof.
  intros. destruct (@ FAT123 c1 c2 H H0) as [H1|[H1|H1]].
  - left. right. auto.
  - right. auto.
  - left; left; auto.
Qed.

Theorem FAT160 : ∀ r c1 c2, r ∈ rC -> c1 ∈ CC -> c2 ∈ CC
  -> Cut_R r > (c1 · c2) -> ∃ r1 r2 , r1 ∈ rC /\ r2 ∈ rC
    /\ r = (r1 · r2)%rC /\ Cut_R r1 ≥ c1 /\ Cut_R r2 ≥ c2.
Proof.
  intros. destruct (@ Lemma_FAT160
  ((c1 + c2) + (rtoC (Ntor One))) ((rtoC r) - (c1 · c2))); auto.
  - assert (rtoC (Ntor One) ∈ CC). auto.
    pose proof (FAT133 c1 (rtoC (Ntor One))). MP.
    pose proof (FAT133 c2 (rtoC (Ntor One))). MP.
    apply FAT159 in H5,H6; auto.
    destruct H5 as [z1[?[]]]. destruct H6 as [z2[?[]]].
    exists (divr r z2), z2. repeat split; auto.
    + rewrite FAT102; auto. rewrite DivrEx; auto.
    + left. apply FAT126 with (Cut_R z1); auto.
      apply FAT154a3; auto. apply FAT106c with z2; auto.
      rewrite @ FAT102 with (divr r z2) z2; auto.
      rewrite DivrEx; auto. apply FAT154b3; auto.
      rewrite FAT155c; auto. assert (Cut_R z1 · Cut_R z2 <
      (c1 + rtoC (Ntor One)) · (c2 + rtoC (Ntor One))).
      { apply FAT147; auto. } rewrite FAT144a in H11; auto.
      rewrite (@ FAT142 (c1 + rtoC (Ntor One)) c2) in H11; auto.
      rewrite FAT144a in H11; auto. rewrite FAT151 in H11; auto.
      rewrite FAT151 in H11; auto. apply FAT127
      with ( c2 · c1 + c2 + (c1 + rtoC (Ntor One))); auto.
      right. split; auto.
      rewrite <- (@ MinCEx (c1 · c2) (Cut_R r) H2); auto.
      rewrite FAT142; auto. rewrite FAT131; auto.
      rewrite FAT130; auto.
      rewrite @ FAT130 with (c1 · c2) (Cut_R r - c1 · c2); auto.
      destruct H3.
      * left. apply FAT135c; auto. rewrite <- FAT131; auto.
        rewrite @ FAT130 with c2 c1; auto.
      * right. apply FAT135b; auto. rewrite <- FAT131; auto.
        rewrite @ FAT130 with c2 c1; auto.
    + left. auto.
  - assert (divC (rtoC r - c1 · c2)
    (c1 + c2 + rtoC (Ntor One)) ∈ CC). auto.
    pose proof (FAT133 c1 (divC ((rtoC r) - c1 · c2)
    ((c1 + c2) + (rtoC (Ntor One))))). MP.
    pose proof (FAT133 c2 (divC ((rtoC r) - c1 · c2)
    ((c1 + c2) + (rtoC (Ntor One))))). MP.
    apply FAT159 in H5,H6; auto. destruct H5 as [z1[?[]]].
    destruct H6 as [z2[?[]]]. exists (divr r z2), z2.
    repeat split; auto.
    + rewrite FAT102; auto. rewrite DivrEx; auto.
    + left. apply FAT126 with (Cut_R z1); auto.
      apply FAT154a3; auto. apply FAT106c with z2; auto.
      rewrite @ FAT102 with (divr r z2) z2; auto.
      rewrite DivrEx; auto. apply FAT154b3; auto.
      rewrite FAT155c; auto.
      assert (Cut_R z1 · Cut_R z2 <
      (c1 + (divC ((rtoC r) - c1 · c2)
      ((c1 + c2) + (rtoC (Ntor One))))) ·
      (c2 + (divC ((rtoC r) - c1 · c2)
      ((c1 + c2) + (rtoC (Ntor One)))))).
      { apply FAT147; auto. } rewrite FAT144a in H11; auto.
      assert (rtoC (Ntor One) ∈ CC). auto.
      assert (Cut_R z1 · Cut_R z2 < 
      (c1 + divC (rtoC r - c1 · c2) 
      (c1 + c2 + rtoC (Ntor One))) ·
      c2 + (c1 + (rtoC (Ntor One))) ·
      divC (rtoC r - c1 · c2) (c1 + c2 + rtoC (Ntor One))).
      { apply FAT127 with ((c1 + divC (rtoC r - c1 · c2)
      (c1 + c2 + rtoC (Ntor One))) · c2 +
      (c1 + divC (rtoC r - c1 · c2) (c1 + c2 + rtoC (Ntor One))) · 
      divC (rtoC r - c1 · c2) (c1 + c2 + rtoC (Ntor One))); auto.
      right. split; auto. left. rewrite FAT130; auto. 
      rewrite @ FAT130 with ((c1 + divC (rtoC r - c1 · c2)
      (c1 + c2 + rtoC (Ntor One))) · c2) ((c1 + rtoC (Ntor One)) ·
      divC (rtoC r - c1 · c2) (c1 + c2 + rtoC (Ntor One))); auto.
      apply FAT135c; auto. apply FAT145c; auto.
      rewrite FAT130; auto.
      rewrite @ FAT130 with c1 (rtoC (Ntor One)); auto.
      apply FAT135c; auto.
      apply FAT146c with (c1 + c2 + rtoC (Ntor One)); auto.
      rewrite FAT142; auto. rewrite DivCEx; auto.
      rewrite mulc1; auto. }
      rewrite @ FAT142 with (c1 + divC (rtoC r - c1 · c2)
      (c1 + c2 + rtoC (Ntor One))) c2 in H13; auto.
      rewrite FAT144a in H13; auto. apply FAT127 with
      (c2 · c1 + c2 · divC (rtoC r - c1 · c2)
      (c1 + c2 + rtoC (Ntor One)) + (c1 + rtoC (Ntor One)) ·
      divC (rtoC r - c1 · c2) (c1 + c2 + rtoC (Ntor One))); auto.
      right. split; auto. right.
      rewrite <- (@ MinCEx (c1 · c2) (Cut_R r) H2); auto.
      rewrite FAT142; auto. rewrite FAT131; auto.
      rewrite FAT130; auto. 
      rewrite @ FAT130 with (c1 · c2) (Cut_R r - c1 · c2); auto.
      apply FAT135b; auto. rewrite FAT142; auto.
      rewrite @ FAT142 with (c1 + rtoC (Ntor One))
      (divC (rtoC r - c1 · c2) (c1 + c2 + rtoC (Ntor One))); auto.
      rewrite <- FAT144a; auto. rewrite FAT142; auto.
      rewrite <- FAT131; auto. rewrite @ FAT130 with c2 c1; auto. 
      rewrite DivCEx; auto.
    + left. auto.
Qed.

Theorem FAT161a : ∀ c1 c2 c, c1 ∈ CC -> c2 ∈ CC -> c ∈ CC
  -> c1 · c1 = c -> ~ c2 = c1 -> ~ c2 · c2 = c.
Proof.
  intros. intro. rewrite <- H2 in H4.
  destruct (@ FAT123 c1 c2) as [H5|[H5|H5]]; auto.
  - pose proof (@ FAT147 c1 c2 c1 c2). MP. CordF.
  - pose proof (@ FAT147 c2 c1 c2 c1). MP. CordF.
Qed.

Definition Sqrt_C c := \{ λ r, r ∈ rC /\ (rtoC r) · (rtoC r) < c \}.

Notation " √ c " := (Sqrt_C c)(at level 0) : CC_scope.

Fact SqrtCp : ∀ c, c ∈ CC -> Sqrt_C c ∈ CC.
Proof.
  intros. assert (√ (c) ⊂ rC). { red. intros. appA2H H0. tauto. }
  apply AxiomII. repeat split; auto; intros.
  - apply MKT33 with (x:=rC); [apply EnrC| auto].
  - apply NEexE. assert (rtoC (Ntor One) ∈ CC). auto.
    destruct (@ FAT123 c (rtoC (Ntor One))) as [H2|[H2|H2]]; auto.
    + New H. appA2H H. destruct H4 as [_[[? _]_]].
      apply NEexE in H4. destruct H4 as [r]. rC r c.
      apply FAT158a in H4; auto. exists r. subst. appA2G.
      split; auto. apply @ FAT126 with (Cut_R r); auto.
      rewrite <- mulc1 with (Cut_R r); auto. apply FAT145c; auto.
    + New H1. appA2H H1. destruct H4 as [_[[? _]_]].
      apply NEexE in H4. destruct H4 as [r].
      rC r (rtoC (Ntor One)). apply FAT158a in H4; auto.
      exists r. appA2G. split; auto. assert (Cut_R r < c). 
      { apply FAT126 with (rtoC (Ntor One)); auto. } 
      apply @ FAT126 with (Cut_R r); auto.
      rewrite <- mulc1 with (Cut_R r); auto. apply FAT145c; auto.
    + New H. appA2H H. destruct H4 as [_[[? _]_]].
      apply NEexE in H4. destruct H4 as [r]. rC r c.
      apply FAT158a in H4; auto. exists r. appA2G. split; auto.
      assert (Cut_R r < (rtoC (Ntor One))). 
      { apply FAT126 with c; auto. } 
      apply @ FAT126 with (Cut_R r); auto.
      rewrite <- mulc1 with (Cut_R r); auto. apply FAT145c; auto.
  - assert (rtoC (Ntor One) ∈ CC). auto.
    destruct (@ FAT123 c (rtoC (Ntor One))) as [H2|[H2|H2]]; auto.
    + subst. appA2H H. destruct H2 as [_[[_ ?]_]].
      destruct H2 as [r[]]. apply FAT158b in H3; auto.
      exists r. split; auto. intro. appA2H H4.
      destruct H5. assert (rtoC r · rtoC r < Cut_R r).
      { apply FAT127 with (rtoC (Ntor One)); auto. }
      rewrite <- mulc1 with (Cut_R r) in H7; auto.
      apply FAT146c in H7; auto. CordF.
    + New H. appA2H H. destruct H4 as [_[[_ ?]_]].
      destruct H4 as [r[]]. apply FAT158b in H5; auto.
      exists r. split; auto. intro. appA2H H6.
      destruct H7. assert (rtoC r · rtoC r < Cut_R r).
      { apply FAT127 with c; auto. }
      rewrite <- mulc1 with (Cut_R r) in H9; auto.
      apply FAT146c in H9; auto.
      assert (rtoC r > rtoC (Ntor One)).
      { apply FAT127 with c; auto. } CordF.
    + New H1. appA2H H1. destruct H4 as [_[[_ ?]_]].
      destruct H4 as [r[]]. apply FAT158b in H5; auto.
      exists r. split; auto. intro. appA2H H6.
      destruct H7. assert (rtoC r · rtoC r < rtoC (Ntor One)).
      { apply FAT126 with c; auto. }
      assert (rtoC r · rtoC r < Cut_R r).
      { apply FAT127 with (rtoC (Ntor One)); auto. }
      rewrite <- mulc1 with (Cut_R r) in H10; auto.
      apply FAT146c in H10; auto. CordF.
  - appA2H H1. destruct H4. appA2G.
    split; auto. apply FAT154a3 in H3; auto.
    apply FAT126 with (rtoC r1 · rtoC r1); auto.
    apply FAT147; auto.
  - appA2H H1. destruct H2. 
    destruct (@ Lemma_FAT160 ((rtoC r1) + ((rtoC r1) +
    (rtoC (Ntor One)))) (c - ((rtoC r1) · (rtoC r1)))); auto.
    + assert (rtoC (Ntor One) ∈ CC). auto. New H5. appA2H H5.
      destruct H7 as [_[[? _]_]]. apply NEexE in H7.
      destruct H7 as [r]. rC r (rtoC (Ntor One)).
      apply FAT158a in H7; auto.
      assert (rtoC r1 + rtoC r > rtoC r1). { apply FAT133; auto. }
      exists (r1 + r)%rC. rewrite <- FAT155a in H9; auto.
      apply FAT154b1 in H9; auto. split; auto. appA2G. split; auto.
      rewrite <- (@ MinCEx (rtoC r1 · rtoC r1) c H3); auto.
      rewrite FAT155a; auto. unfold Cut_R. rewrite FAT144a; auto.
      apply FAT126 with ((rtoC r1 · rtoC r1) + (rtoC r · rtoC r1) + 
      (rtoC r1 + (rtoC (Ntor One))) · rtoC r); auto.
      * rewrite FAT142; auto. rewrite FAT144a; auto. 
        rewrite @ FAT142 with (rtoC r) (rtoC r1); auto.
        rewrite FAT130; auto.
        rewrite @ FAT130 with (rtoC r1 · rtoC r1 + rtoC r1 · rtoC r) 
        ((rtoC r1 + rtoC (Ntor One)) · rtoC r); auto.
        apply FAT135c; auto. apply FAT145c; auto.
        rewrite FAT130; auto. 
        rewrite @ FAT130 with (rtoC r1) (rtoC (Ntor One)); auto.
        apply FAT135c; auto.
      * rewrite FAT131; auto. rewrite FAT130; auto.
        rewrite @ FAT130 with (rtoC r1 · rtoC r1)
        (c - rtoC r1 · rtoC r1); auto. apply FAT135c; auto. 
        rewrite @ FAT142 with (rtoC r1 + rtoC (Ntor One)) (rtoC r);
        auto. rewrite <- FAT144a; auto. 
        apply FAT127 with (rtoC r1 + (rtoC r1 + rtoC (Ntor One)));
        auto. right. split; auto.
        pattern (rtoC r1 + (rtoC r1 + rtoC (Ntor One))) at 2;
        rewrite <- mulc1; auto. apply FAT145c; auto.
    + assert ((divC (c - rtoC r1 · rtoC r1)
      (rtoC r1 + (rtoC r1 + rtoC (Ntor One)))) ∈ CC).
      { assert (rtoC (Ntor One) ∈ CC). auto. auto. }
      New H5. appA2H H5. destruct H7 as [_[[? _]_]].
      apply NEexE in H7. destruct H7 as [r].
      rC r (divC (c - rtoC r1 · rtoC r1)
      (rtoC r1 + (rtoC r1 + rtoC (Ntor One)))).
      apply FAT158a in H7; auto.
      assert (rtoC r1 + rtoC r > rtoC r1). { apply FAT133; auto. }
      exists (r1 + r)%rC. rewrite <- FAT155a in H9; auto.
      apply FAT154b1 in H9; auto. split; auto. appA2G. split; auto.
      rewrite <- (@ MinCEx (rtoC r1 · rtoC r1) c H3); auto.
      rewrite FAT155a; auto. unfold Cut_R. rewrite FAT144a; auto.
      apply FAT126 with ((rtoC r1 · rtoC r1) + (rtoC r · rtoC r1) +
      (rtoC r1 + (rtoC (Ntor One))) · rtoC r); auto.
      assert (rtoC (Ntor One) ∈ CC). auto. auto.
      * rewrite FAT142; auto. rewrite FAT144a; auto. 
        rewrite @ FAT142 with (rtoC r) (rtoC r1); auto.
        rewrite FAT130; auto.
        rewrite @ FAT130 with (rtoC r1 · rtoC r1 + rtoC r1 · rtoC r) 
        ((rtoC r1 + rtoC (Ntor One)) · rtoC r); auto.
        apply FAT135c; auto. apply FAT145c; auto.
        rewrite FAT130; auto. 
        rewrite @ FAT130 with (rtoC r1) (rtoC (Ntor One)); auto.
        apply FAT135c; auto. apply FAT126 with (divC (c - rtoC r1 ·
        rtoC r1) (rtoC r1 + (rtoC r1 + rtoC (Ntor One)))); auto.
        apply FAT146c with (rtoC r1 + (rtoC r1 + rtoC (Ntor One)));
        auto. rewrite FAT142; auto. rewrite DivCEx; auto.
        rewrite mulc1; auto.
      * assert (rtoC (Ntor One) ∈ CC). auto. rewrite FAT131; auto.
        rewrite FAT130; auto. rewrite @ FAT130 with (rtoC r1 · rtoC r1)
        (c - rtoC r1 · rtoC r1); auto. apply FAT135c; auto.
        rewrite @ FAT142 with (rtoC r1 + rtoC (Ntor One)) (rtoC r);
        auto. rewrite <- FAT144a; auto.
        apply (FAT145c _ _ (rtoC r1 + (rtoC r1 + rtoC (Ntor One))))
        in H7; auto.
        rewrite @ FAT142 with (divC (c - rtoC r1 · rtoC r1)
        (rtoC r1 + (rtoC r1 + rtoC (Ntor One))))
        (rtoC r1 + (rtoC r1 + rtoC (Ntor One))) in H7; auto.
        rewrite DivCEx in H7; auto.
Qed.

Global Hint Resolve SqrtCp : core.

Fact SqrtCp2 : ∀ c, c ∈ CC -> √ (c · c) = c.
Proof.
  intros.
  apply AxiomI. split; intros.
  - apply AxiomII in H0. destruct H0 as [?[]].
    apply FAT158a; auto. unfold Cut_R.
    destruct (@ FAT123 (rtoC z) c) as [?|[?|?]]; auto.
    + rewrite H3 in H2. assert (c · c = c · c); auto. CordF.
    + assert (rtoC z · rtoC z > c · rtoC z).
      { apply FAT145a; auto. } assert (rtoC z · c > c · c).
      { apply FAT145a; auto. } rewrite FAT142 in H5; auto.
      assert (rtoC z · rtoC z > c · c).
      { apply FAT126 with (c · rtoC z); auto. } CordF.
  - apply AxiomII. rC z c. repeat split; auto. exists rC; auto.
    apply FAT158a in H0; auto. unfold Cut_R in H0.
    apply FAT147; auto.
Qed.

Lemma Lemma_FAT161 : ∀ c, c ∈ CC -> (Sqrt_C c) · (Sqrt_C c) = c.
Proof.
  intros. destruct (@ FAT123 (√ (c) · √ (c)) c) as [H0|[H0|H0]]; auto.
  - apply FAT159 in H0; auto. destruct H0 as [r[?[]]].
    apply FAT158a in H2; auto. red in H2. appA2H H2.
    destruct H3 as [r1[r2[?[]]]]. red in H3,H4.
    assert (√ (c) ∈ CC). auto. rC r1 √ (c). rC r2 √ (c).
    destruct (@ FAT81 r1 r2) as [H9|[H9|H9]]; auto.
    + rewrite H9 in H5. rewrite H5 in H1. appA2H H4.
      destruct H10. rewrite <- FAT155c in H11; auto. CordF.
    + assert (r > (r1 · r1))%rC.
      { appA2H H3. destruct H10. apply FAT154b3; auto.
      rewrite FAT155c; auto. apply FAT126 with c; auto. }
      assert (r > (r1 · r2))%rC.
      { apply FAT86 with ((r1 · r1)%rC); auto.
        rewrite FAT102; auto. apply FAT105c; auto. } rordF.
    + assert (r > (r2 · r2))%rC.
      { appA2H H4. destruct H10. apply FAT154b3; auto.
      rewrite FAT155c; auto. apply FAT126 with c; auto. }
      assert (r > (r1 · r2))%rC.
      { apply FAT86 with ((r2 · r2)%rC); auto.
      apply FAT105c; auto. } rordF.
  - apply FAT159 in H0; auto. destruct H0 as [r[?[]]].
    apply FAT160 in H1; auto. destruct H1 as [r1[r2[?[?[?[]]]]]].
    destruct (@ FAT81 r1 r2) as [H7|[H7|H7]]; auto.
    + assert (Cut_R r2 < √ (c)).
      { rewrite H7 in H4. rewrite H4 in H2. apply FAT158a; auto. red.
      appA2G. split; auto. rewrite <- FAT155c; auto. } CordF.
    + assert (Cut_R r2 < √ (c)).
      { apply FAT158a; auto. red. appA2G. split; auto.
        apply FAT126 with (rtoC r); auto.
        rewrite H4. rewrite FAT155c; auto.
        apply FAT145c; auto. apply FAT154a3; auto. } CordF.
    + assert (Cut_R r1 < √ (c)).
      { apply FAT158a; auto. red. appA2G. split; auto.
        apply FAT126 with (rtoC r); auto.
        rewrite H4. rewrite FAT155c; auto. 
        rewrite @ FAT142 with (Cut_R r1) (Cut_R r2); auto.
        apply FAT145c; auto. apply FAT154a3; auto. }
      destruct H5; CordF.
Qed.

Theorem FAT161b : ∀ c, c ∈ CC -> ∃ c1, c1 ∈ CC /\ c1 · c1 = c.
Proof.
  intros. exists (Sqrt_C c). split; auto. apply Lemma_FAT161; auto.
Qed.

(*无理数集*)

Definition IrratC := CC ~ RCC.

Fact Irrat1 : ∀ E, E ∈ IrratC <-> E ∈ CC /\ ~ (∃ r, r ∈ rC /\ E = Cut_R r).
Proof.
  split; intros.
  - split. appA2H H. tauto. intro. appA2H H.
    destruct H1. appA2H H2. elim H3. appA2G.
  - destruct H. appA2G. split; auto. appA2G. intro. elim H0.
    appA2H H1. auto.
Qed.

Fact Eqf : ∀ f1 f2, f1 ∈ FC -> f2 ∈ FC
  -> ((eqf f1) · (eqf f2))%rC = eqf (f1 · f2)%FC.
Proof.
  intros. apply AxiomI; split; intros.
  - appA2H H1. destruct H2 as [?[f3[f4[?[]]]]].
    appA2G. split; auto. appA2H H3. appA2H H4.
    destruct H6,H7. eapply FAT39; eauto. eapply FAT68; eauto.
  - appA2H H1. destruct H2. appA2G. split; auto. exists f1,f2.
    repeat split; auto; appA2G; split; auto; t37.
Qed.

Fact ffe : ∀ f1 f2 , f1 ∈ FC -> eqf f1 = eqf f2 -> (f1 ~ f2)%FC.
Proof.
  intros. apply RF0a in H. rewrite H0 in H. appA2H H. tauto.
Qed.

Fact mul2a : ∀ n, n ∈ Nat -> (((One) ⁺ · n) > n)%Nat.
Proof.
  intros. rewrite FAT29; auto. rewrite FAT28b; auto.
  rewrite FAT6; auto. apply FAT18; auto.
Qed.

Fact mul2b : ∀ n, n ∈ Nat -> (((One) ⁺ · n) = n + n)%Nat.
Proof.
  intros. rewrite FAT29; auto. rewrite FAT28b; auto.
  rewrite FAT28a; auto.
Qed.

Fact nmulna : ∀ x y, x ∈ Nat -> y ∈ Nat -> (x · x > y · y)%Nat
  -> (x > y)%Nat.
Proof.
  intros. destruct (@ FAT10 x y H H0) as [H2|[H2|H2]]; auto.
  - assert (x · x = y · y)%Nat. rewrite H2; auto. NordF.
  - assert ((x · x < y · y)%Nat). apply FAT34; auto. NordF.
Qed. 

Fact nmulnb : ∀ x y, x ∈ Nat -> y ∈ Nat -> (x · x = y · y)%Nat
  -> (x = y)%Nat.
Proof.
  intros. destruct (@ FAT10 x y H H0) as [H2|[H2|H2]]; auto.
  - assert (x · x > y · y)%Nat. apply FAT35; auto. NordF.
  - assert ((x · x < y · y)%Nat). apply FAT34; auto. NordF.
Qed.

Theorem FAT162 : ∃ c, c ∈ IrratC.
Proof.
  exists (Sqrt_C (rtoC (Ntor (Nsuc [One])))).
  apply Irrat1. split; auto. intro. destruct H as [r[]].
  assert ((rtoC (Ntor (One)⁺) ∈ CC)). auto.
  pose proof (Lemma_FAT161 _ H1). rewrite H0 in H2.
  rewrite <- FAT155c in H2; auto.
  assert ((Ntor (One)⁺) ∈ rC). auto.
  apply (FAT154b2 (r · r)%rC (Ntor (One) ⁺)) in H2; auto.
  pose proof (RF4 _ H). destruct H4 as [f[?[]]]. appA2H H5.
  destruct H7 as [x1[y1[?[]]]].
  set \{ λ y, exists x, x ∈ Nat /\ y ∈ Nat /\ [x, y] ∈ r \}.
  assert (c ⊂ Nat).
  { red. intros. appA2H H10. destruct H11. tauto. }
  assert (c ≠ Φ).
  { apply NEexE. exists y1. appA2G. exists x1.
  repeat split; auto. congruence. }
  pose proof (FAT27 c). MP. destruct H12 as [y[]].
  apply AxiomII in H12 as [_[x[?[]]]]. assert ([x, y] ∈ FC). auto.
  assert (((eqf ([x, y])) · (eqf ([x, y])))%rC =
  (eqf ([One⁺, One]))).
  { pose proof (RF3 _ _ H H16 H15). rewrite <- H17. auto. }
  rewrite Eqf in H17; auto. apply ffe in H17; auto.
  unfold mulF in H17. Ge. unfold eqv in H17. repeat Ge.
  rewrite FAT28a in H17; auto.
  assert (x > y)%Nat.
  { rewrite FAT29 with ((One)⁺) (y · y)%Nat in H17; auto.
  rewrite FAT28b in H17; auto. rewrite FAT28a in H17; auto.
  assert ((x · x) > (y · y))%Nat.
  { red. exists (y · y)%Nat. repeat split; auto. } 
  apply nmulna in H18; auto. }
  assert (x < ((One)⁺ · y))%Nat.
  { assert (((x · x) < (((One)⁺ · y) · ((One)⁺ · y)))%Nat).
  { rewrite H17. rewrite <- FAT31; auto. rewrite FAT29; auto.
  apply FAT32c; auto. apply mul2a; auto. }
  apply nmulna in H19; auto. } set (x - y)%Nat as u.
  assert ((x - y) < y)%Nat.
  { apply FAT20c with y; auto. rewrite FAT6; auto.
  rewrite MinNEx; auto. rewrite FAT29 in H19; auto.
  rewrite FAT28b in H19; auto. rewrite FAT28a in H19; auto. }
  set (y - u)%Nat as t.
  assert (u ∈ Nat). unfold u. auto.
  assert (t ∈ Nat). unfold t. auto.
  assert (x · x + t · t = x · x + (One)⁺ · (u · u))%Nat.
  { assert (x = y + u)%Nat. unfold u. rewrite MinNEx; auto.
  pattern x at 1 2; rewrite H23. rewrite H17.
  rewrite FAT30a; auto. repeat rewrite FAT30b; auto.
  rewrite FAT29 with u y; auto.
  rewrite <- FAT5; auto.
  rewrite FAT5 with (y · y)%Nat (y · u)%Nat (y · u)%Nat; auto.
  rewrite <- mul2b with (y · u)%Nat; auto. rewrite FAT5; auto.
  rewrite FAT29 with y u; auto. rewrite <- FAT31; auto.
  assert (y = u + t)%Nat. unfold t. rewrite MinNEx; auto.
  pattern y at 3; rewrite H24.
  rewrite FAT30a; auto. rewrite FAT5; auto.
  rewrite FAT31 with (One)⁺ u t; auto.
  rewrite mul2b with (u · t)%Nat; auto.
  rewrite mul2b with (y · y)%Nat; auto.
  assert ((One)⁺ ∈ Nat). auto. rewrite FAT6; auto. 
  rewrite FAT5 with (y · y)%Nat (y · y)%Nat
  ((One)⁺ · (u · u))%Nat; auto.
  rewrite FAT6 with (y · y)%Nat
  ((y · y + (One)⁺ · (u · u)))%Nat; auto.
  apply FAT19b; auto. rewrite FAT31; auto.
  rewrite FAT5 with ((One)⁺ · (u · u))%Nat
  (u · t + u · t)%Nat (u · u + t · t)%Nat; auto.
  rewrite FAT6; auto. apply FAT19b; auto. rewrite H24.
  rewrite FAT30a; auto. repeat rewrite FAT30b; auto.
  rewrite FAT29 with t u; auto.
  repeat rewrite <- FAT5; auto. apply FAT19b; auto.
  rewrite FAT6; auto. rewrite FAT5; auto. }
  rewrite FAT6 in H23; auto. 
  rewrite FAT6 with (x · x)%Nat ((One)⁺ · (u · u))%Nat in H23; auto.
  apply FAT20b in H23; auto.
  assert ([t, u] ∈ r).
  { apply RF6 with [x, y]; auto. red. repeat Ge.
  assert ((x · x) · ((One)⁺ · (u · u)) =
  (t · t)%Nat · ((One)⁺ · (y · y))%Nat)%Nat.
  rewrite H17,H23. rewrite FAT29; auto.
  rewrite (FAT29 (One)⁺ (u · u)%Nat) in H24; auto.
  rewrite (FAT29 (One)⁺ (y · y)%Nat) in H24; auto.
  rewrite <- FAT31 in H24; auto. 
  rewrite <- (FAT31 (t · t)%Nat (y · y)%Nat (One)⁺) in H24; auto.
  apply FAT33b in H24; auto. rewrite FAT31 in H24; auto.
  rewrite <- (FAT31 x u u) in H24; auto. rewrite FAT29 in H24; auto.
  rewrite FAT31 in H24; auto. rewrite FAT29 with u x in H24; auto.
  rewrite FAT31 with t t (y · y)%Nat in H24; auto.
  rewrite <- FAT31 with t y y in H24; auto. 
  rewrite FAT29 with (t · y)%Nat y in H24; auto.
  rewrite <- FAT31 with t y (t · y)%Nat in H24; auto.
  apply nmulnb in H24; auto. }
  assert (u ∈ c). { appA2G. } apply H13 in H25. unfold u in H25.
  destruct H25; NordF.
Qed.

Close Scope CC_scope.

(* REALS NUMBERS *)

(* SECTION I Definition *)

Declare Scope RC_scope.

Delimit Scope RC_scope with RC.

Open Scope RC_scope.

Definition zero := Φ.

Notation " 0 " := zero : RC_scope.

Fact zeroENs : ∃ x, zero ∈ x.
Proof.
  exists ω; apply MKT135.
Qed.

Global Hint Resolve zeroENs : core.

Fact ZeroP : ∀ {a} b, Ensemble a -> [a] ∈ [a,b].
Proof.
  intros. apply MKT42 in H.
  apply AxiomII; split; auto.
Qed.

Fact zeroNINat : ~ zero ∈ Nat.
Proof.
  intro. apply AxiomII in H as [H []]. apply AxiomII in H1 as [].
  apply H2. unfold One. unfold PlusOne. rewrite MKT17.
  apply MKT41; auto.
Qed.

Fact zeroNIFra : ~ zero ∈ FC.
Proof.
  intro. PP H a b. destruct H1.
  assert (Ensemble a); unfold Ensemble; eauto.
  apply (ZeroP b) in H3. rewrite <- H0 in H3.
  destruct (@ MKT16 _ H3).
Qed.

Fact zeroNIRat : ~ zero ∈ rC.
Proof.
  intro. apply AxiomII in H as [_ [f []]].
  assert (f ∈ zero).
  { rewrite H0. apply AxiomII; repeat split;
  unfold Ensemble; eauto. }
  eapply MKT16; eauto.
Qed.

Fact zeroNICut : ~ zero ∈ CC.
Proof.
  intro. apply AxiomII in H as [_ [f []]]. elim H; eauto.
Qed.

(*正数集*)
Definition PRC := \{\ λ u v, u ∈ CC /\ v = zero \}\.

(*负数集*)
Definition NRC := \{\ λ u v, u = zero /\ v ∈ CC \}\.

Fact zeroNIPR : ~ zero ∈ PRC.
Proof.
  intro. PP H a b. destruct H1.
  assert (Ensemble a); unfold Ensemble; eauto.
  apply (ZeroP b) in H3. rewrite <- H0 in H3.
  destruct (@ MKT16 _ H3).
Qed.

Fact zeroNINR : ~ zero ∈ NRC.
Proof.
  intro. PP H a b. destruct H1.
  pose proof EnEm. unfold zero in H1,H0. rewrite <- H1 in H3.
  apply (ZeroP b) in H3. rewrite <- H0 in H3.
  destruct (@ MKT16 _ H3).
Qed.

Fact PRNINR : ∀ {x}, x ∈ PRC -> x ∈ NRC -> False.
Proof.
  intros. apply AxiomII in H as [_ [y [z [? []]]]].
  apply AxiomII in H0 as [_ [u [v [? []]]]]. subst.
  apply MKT55 in H0 as []; unfold Ensemble; eauto.
  subst. apply zeroNICut; auto.
Qed.

Fact zeroNePR : ∀ {x}, [x,zero] = zero -> x ∈ CC -> False.
Proof. 
  intros. apply zeroNIPR. rewrite <- H. apply AxiomII'.
  repeat split; rxo.
Qed.

Fact zeroNeNR : ∀ {x}, [zero,x] = zero -> x ∈ CC -> False.
Proof. 
  intros. apply zeroNINR. rewrite <- H. apply AxiomII'.
  repeat split; rxo.
Qed.

Ltac find_rwd :=
  match goal with
    H1: ?r ∈ PRC,
    H2: ?r ∈ NRC
    |- _ => destruct (PRNINR H1 H2)
  end.

Ltac find_rwe :=
  match goal with
    H: zero ∈ PRC
    |- _ => destruct (zeroNIPR H)
  end.

Ltac find_rwf :=
  match goal with
    H: zero ∈ NRC
    |- _ => destruct (zeroNINR H)
  end.

Ltac npz := try find_rwd; try find_rwe; try find_rwf.

Ltac find_rwg :=
  match goal with
    H: [?x,zero] = zero 
    |- _ => destruct (zeroNePR H); auto
  end.

Ltac find_rwh :=
  match goal with
    H: [zero,?x] = zero
    |- _ => destruct (zeroNeNR H); auto
  end.

Ltac npZ := try find_rwg; try find_rwh.

(*实数集*)
Definition RC := PRC ∪ [zero] ∪ NRC.

Fact EnRC : Ensemble RC.
Proof.
  apply AxiomIV.
  - apply MKT33 with (x:=CC×[zero]).
    + apply MKT74. apply EnCC. apply MKT42, EnEm.
    + red; intros. PP H a b. destruct H1.
      apply AxiomII'; repeat split; auto. subst.
      apply MKT41; unfold Ensemble; eauto.
  - apply AxiomIV.
  + apply MKT42, EnEm.
  + apply MKT33 with (x:=[zero]×CC).
    * apply MKT74. apply MKT42, EnEm. apply EnCC.
    * red; intros. PP H a b. destruct H1.
      apply AxiomII'; repeat split; auto. subst.
      apply MKT41; unfold Ensemble; eauto.
Qed.

Notation " p ¹ " := (First p)(at level 0) : RC_scope.

Notation " p ² " := (Second p)(at level 0) : RC_scope.

Fact pr1 : ∀ x, x ∈ CC -> [x,zero]¹ = x.
Proof.
  intros. apply MKT54a; unfold Ensemble; eauto.
Qed.

Fact pr2 : ∀ x, x ∈ CC -> [x,zero]² = zero.
Proof.
  intros. apply MKT54b; unfold Ensemble; eauto.
Qed.

Fact nr1 : ∀ x, x ∈ CC -> [zero,x]¹ = zero.
Proof.
  intros. apply MKT54a; unfold Ensemble; eauto.
Qed.

Fact nr2 : ∀ x, x ∈ CC -> [zero,x]² = x.
Proof.
  intros. apply MKT54b; unfold Ensemble; eauto.
Qed.

Ltac GE := try rewrite pr1 in *; try rewrite pr2 in *; 
  try rewrite nr1 in *; try rewrite nr2 in *; auto.

Fact PR1INC : ∀ {x}, x ∈ PRC -> x¹ ∈ CC.
Proof.
  intros. apply AxiomII in H as [? [? [? [? [?]]]]]. subst. GE.
Qed.

Fact NR2INC : ∀ {x}, x ∈ NRC -> x² ∈ CC.
Proof.
  intros. apply AxiomII in H as [? [? [? [? [?]]]]]. subst. GE.
Qed.

Global Hint Resolve PR1INC NR2INC : core.

Fact Peq : ∀ r1 r2, r1 ∈ PRC -> r2 ∈ PRC -> r1¹ = r2¹ -> r1 = r2.
Proof.
  intros. apply AxiomII in H as [_ [x [? [? []]]]]; subst.
  apply AxiomII in H0 as [_ [y [? [? []]]]]; subst. do 2 GE.
  subst. auto.
Qed.

Fact Neq : ∀ r1 r2, r1 ∈ NRC -> r2 ∈ NRC -> r1² = r2² -> r1 = r2.
Proof.
  intros. apply AxiomII in H as [_ [? [x [? []]]]]; subst.
  apply AxiomII in H0 as [_ [? [y [? []]]]]; subst. do 2 GE.
  subst. auto.
Qed.

Global Hint Resolve Peq Neq : core.

Fact Pr : ∀ r, r ∈ PRC -> r = [r¹, 0].
Proof.
  intros. appA2H H. destruct H0 as [x[y[?[]]]]. subst. GE.
Qed.

Fact Nr : ∀ r, r ∈ NRC -> r = [0, r²].
Proof.
  intros. appA2H H. destruct H0 as [x[y[?[]]]]. subst. GE.
Qed.

Global Hint Resolve Pr Nr : core.

Fact funv : ∀ f u v, Function f -> [u,v] ∈ f -> f[u] = v.
Proof.
  intros. rewrite MKT70 in H0; auto.
  apply AxiomII' in H0 as []; auto.
Qed.

Fact zinr : zero ∈ RC.
Proof.
  apply MKT4. right. apply MKT4. left.
  apply MKT41; unfold Ensemble; eauto.
Qed.

Fact pinr : ∀ a, a ∈ PRC -> a ∈ RC.
Proof.
  intros. apply AxiomII; split; unfold Ensemble; eauto.
Qed.

Fact ninr : ∀ a, a ∈ NRC -> a ∈ RC.
Proof.
  intros. apply AxiomII; split; [|right; apply AxiomII];
  unfold Ensemble; eauto.
Qed.

Fact czinpr : ∀ a, a ∈ CC -> [a,zero] ∈ PRC.
Proof.
  intros. apply AxiomII'; split; rxo.
Qed.

Fact zcinnr : ∀ a, a ∈ CC -> [zero,a] ∈ NRC.
Proof.
  intros. apply AxiomII'; split; rxo.
Qed.

Global Hint Resolve zinr pinr ninr czinpr zcinnr : core.

Ltac RC X :=
  match goal with
  | H : X ∈ PRC
    |- _ => pose proof (pinr X H)
  | H : X ∈ NRC
    |- _ => pose proof (ninr X H)
  | H : X = zero
    |- _ => pose proof zinr
  end.

Fact inRC : ∀ {r}, r ∈ RC -> r ∈ PRC \/ r = zero \/ r ∈ NRC.
Proof.
  intros. apply MKT4 in H as []; auto.
  apply MKT4 in H as []; auto.
  apply MKT41 in H; unfold Ensemble; eauto.
Qed.

Ltac rewF1 :=
  match goal with
    H1: ?a ∈ ?A,
    H2: ?b ∈ ?B,
    H3: ?a ∈ ?A -> ?b ∈ ?B -> ?c = ?d
    |- _ => rewrite (H3 H1 H2); auto
  end.

Ltac rewF2 :=
  match goal with
    H1: ?P -> ?b = ?c,
    H2: ?P
    |- _ => rewrite (H1 H2); auto
  end.

Ltac ReF := repeat rewF1; repeat rewF2; auto.

Fact poisre : ∀ P, Relation \{\ λ a b, P a b \}\.
Proof.
  red; intros. apply AxiomII in H as [?[?[?[]]]]; subst; eauto.
Qed.

Theorem FAT163 : ∀ X, X ∈ RC -> X = X.
Proof.
  auto.
Qed.

Theorem FAT164 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X = Y -> Y = X.
Proof.
  auto.
Qed.

Theorem FAT165 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X = Y -> Y = Z -> X = Z.
Proof.
  intros. rewrite <- H3; auto.
Qed.

(* SECTION II Ordering *)

(*绝对值*)
Definition AbsR := \{\ λ r z, r ∈ RC /\ (r ∈ NRC -> z = [r²,zero])
  /\ (r ∈ PRC -> z = r) /\ (r = zero -> z = zero) \}\.

Notation " | X | " := (AbsR[X])(at level 10) : RC_scope.

Fact abrf : Function AbsR.
Proof.
  split; intros. apply poisre.
  apply AxiomII' in H; apply AxiomII' in H0; deand.
  destruct (inRC H1) as [?|[?|?]]; ReF.
Qed.

Global Hint Resolve abrf : core.

Local Ltac ltacr1 := intros; apply funv; auto; apply AxiomII';
  repeat split; intros; subst; npz; auto; rxo; unfold Ensemble;
  eauto.

Fact Nabs : ∀ {r}, r ∈ NRC -> AbsR[r] = [r²,zero].
Proof.
  ltacr1.
Qed.

Fact Pabs : ∀ {r}, r ∈ PRC -> AbsR[r] = r.
Proof.
  ltacr1.
Qed.

Fact Neabs : ∀ {r}, r ∈ CC -> AbsR[[zero,r]] = [r,zero].
Proof.
  intros. rewrite Nabs; GE.
Qed.

Fact Peabs : ∀ {r}, r ∈ CC -> AbsR[[r,zero]] = [r,zero].
Proof.
  intros. rewrite Pabs; GE.
Qed.

Fact Zabs : AbsR[zero] = zero.
Proof.
  ltacr1.
Qed.

Ltac reAb1 :=
  match goal with
    H: ?r ∈ NRC
    |- _ => rewrite (Nabs H) in *
  end.

Ltac reAb2 :=
  match goal with
    H: ?r ∈ PRC
    |- _ => rewrite (Pabs H) in *
  end.

Ltac reAb3 :=
  match goal with
    |- _ => rewrite Zabs in *
  end.

Ltac reAb4 :=
  match goal with
    |- _ => rewrite Neabs in *
  end.

Ltac reAb5 :=
  match goal with
    |- _ => rewrite Peabs in *
  end.

Ltac reqb1 := try reAb1; try reAb2; try reAb3; try reAb4;
  try reAb5.

Fact adsRC1 :  ∀ r, r ∈ PRC -> AbsR[r] ∈ RC.
Proof.
  intros. reqb1. auto.
Qed.

Fact adsRC2 :  ∀ r, r ∈ NRC -> AbsR[r] ∈ RC.
Proof.
  intros. reqb1. auto.
Qed.

Global Hint Resolve adsRC1 adsRC2 : core.

Fact adsRC : ∀ r, r ∈ RC -> AbsR[r] ∈ RC.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; auto.
  rewrite H0. reqb1. auto.
Qed.

Theorem FAT166 : ∀ X, X ∈ RC -> X <> zero -> AbsR [X] ∈ PRC.
Proof.
  intros. destruct (inRC H) as [H2|[H2|H2]].
  - reqb1. auto.
  - contradiction.
  - reqb1; auto.
Qed.

Definition gtR r1 r2 := (r2 ∈ PRC /\ r1 ∈ PRC /\ (r2¹ < r1¹)%CC)
  \/ (r2 = zero /\ r1 ∈ PRC) \/ (r2 ∈ NRC /\ r1 ∈ PRC)
  \/ (r2 ∈ NRC /\ r1 = zero) \/ (r2 ∈ NRC /\ r1 ∈ NRC /\ (r1² < r2²)%CC).

Notation " x > y " := (gtR x y) : RC_scope.

Definition ltR r1 r2 := (r1 ∈ PRC /\ r2 ∈ PRC /\ (r1¹ < r2¹)%CC)
  \/ (r1 = zero /\ r2 ∈ PRC) \/ (r1 ∈ NRC /\ r2 ∈ PRC)
  \/ (r1 ∈ NRC /\ r2 = zero) \/ (r1 ∈ NRC /\ r2 ∈ NRC /\ (r2² < r1²)%CC).

Notation " x < y " := (ltR x y) : RC_scope.

Theorem FAT167: ∀ {r1 r2}, r1 ∈ RC -> r2 ∈ RC
  -> r1 = r2 \/ r1 > r2 \/ r1 < r2.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; 
  destruct (inRC H0) as [?|[?|?]]; unfold gtR, ltR; subst; auto 8.
  - destruct (@ FAT123 r1¹ r2¹) as [?|[?|?]]; subst; auto; tauto.
  - destruct (@ FAT123 r1² r2²) as [?|[?|?]]; subst; auto; tauto.
Qed.

Definition geR r1 r2 := r1 > r2 \/ r2 = r1.

Notation " x ≥ y " := (geR x y)(at level 77) : RC_scope.

Definition leR r1 r2 := r1 < r2 \/ r1 = r2.

Notation " x ≤ y " := (leR x y)(at level 77) : RC_scope.

Fact elRf : ∀ {x y}, x < y -> x = y -> x ∈ RC -> y ∈ RC -> False.
Proof.
  intros. subst. red in H. deor; deand; subst; CordF; npz.
Qed.

Fact egRf : ∀ {x y}, x > y -> x = y -> x ∈ RC -> y ∈ RC -> False.
Proof.
  intros. subst. eapply elRf; eauto.
Qed.

Fact lgRf : ∀ {x y}, x < y -> x > y -> x ∈ RC -> y ∈ RC -> False.
Proof.
  intros. red in H, H0. deor; deand; subst; CordF; npz.
Qed.

Fact legRf : ∀ {x y}, x ≤ y -> x > y -> x ∈ RC -> y ∈ RC -> False.
Proof.
  intros. destruct H; [eapply lgRf|eapply egRf]; eauto.
Qed.

Ltac ELR :=
  match goal with
    H: ltR ?n1 ?n2
    |- _ => destruct (elRf H); auto
  end.

Ltac EGR :=
  match goal with
    H: gtR ?n1 ?n2
    |- _ => destruct (egRf H); auto
  end.

Ltac LGR :=
  match goal with
    H: ltR ?n1 ?n2
    |- _ => destruct (lgRf H); auto
  end.

Ltac LEGR :=
  match goal with
    H: lec ?n1 ?n2
    |- _ => destruct (legRf H); auto
  end.

Ltac GELR :=
  match goal with
    H: geR ?n1 ?n2
    |- _ => destruct (legRf H); auto
  end.

Ltac CordR := try ELR; try EGR; try LGR; try LEGR; try GELR.

Theorem FAT168a : ∀ X Y, X ∈ RC -> Y ∈ RC -> X ≥ Y -> Y ≤ X.
Proof.
  intros. destruct H1. left; auto. right; auto.
Qed.

Theorem FAT168b : ∀ X Y, X ∈ RC -> Y ∈ RC -> X ≤ Y -> Y ≥ X.
Proof.
  intros. destruct H1. left; auto. right; auto.
Qed.

Theorem FAT169a : ∀ X, X ∈ PRC -> X > 0.
Proof.
  intros; red; tauto.
Qed.

Theorem FAT169b : ∀ X, X ∈ NRC -> X < 0.
Proof.
  intros; red; tauto.
Qed.

Global Hint Resolve FAT169a FAT169b : core.

Fact inRC' : ∀ r, r ∈ RC -> r > zero \/ r = zero \/ r < zero.
Proof.
  intros. destruct (@inRC r H) as [?|[?|?]].
  - left; auto.
  - tauto.
  - right; right; auto.
Qed.

Fact FAT169a' : ∀ X, X ∈ RC -> X > 0 -> X ∈ PRC.
Proof.
  intros. destruct (@inRC X H) as [?|[?|?]]; auto.
  - CordR.
  - apply FAT169b in H1. CordR.
Qed.

Fact FAT169b' : ∀ X, X ∈ RC -> X < 0 -> X ∈ NRC.
Proof.
  intros. destruct (@inRC X H) as [?|[?|?]]; auto; CordR.
Qed.

Global Hint Resolve FAT169a' FAT169b' : core.

Theorem FAT170 : ∀ X, X ∈ RC -> AbsR [X] ≥ 0.
Proof.
  intros. destruct (@inRC X H) as [H0|[H0|H0]].
  - left. apply FAT169a; auto. apply FAT166; auto. intro.
    subst; npz.
  - right. subst. reqb1. auto.
  - left. apply FAT169a; auto. apply FAT166; auto. intro.
    subst; npz.
Qed.

Ltac Order :=
  match goal with
  | H : ?X < ?Y
    |- _ => red in H; destruct H as [[?[]]|[[]|[[]|[[]|[?[]]]]]];
            subst; try npz; Order
  | |- _ => idtac
  end.

Fact NltP : ∀ X Y, X ∈ NRC -> Y ∈ PRC -> X < Y.
Proof.
  intros. red. tauto.
Qed.

Global Hint Resolve NltP : core.

Theorem FAT171: ∀ {X Y Z}, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X < Y -> Y < Z -> X < Z.
Proof.
  intros. destruct (@ inRC Z H1) as [?|[?|?]].
  - destruct (@ inRC X H) as [?|[?|?]].
    + red. left. repeat split; auto. Order.
      apply FAT126 with ((Y)¹); auto.
    + subst. apply FAT169a; auto.
    + auto.
  - subst. apply FAT169b' in H3; auto. apply FAT169b. Order; auto.
  - Order. red. repeat right. repeat split; auto.
    apply FAT126 with ((Y)²); auto.
Qed.

Theorem FAT172 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> (X ≤ Y /\ Y < Z) \/ (X < Y /\ Y ≤ Z) -> X < Z.
Proof.
  intros. destruct H2 as [[[?|?]?]|[?[?|?]]].
  - apply @ FAT171 with Y; auto.
  - subst; auto.
  - apply @ FAT171 with Y; auto.
  - subst; auto.
Qed.

Theorem T173 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X ≤ Y -> Y ≤ Z -> X ≤ Z.
Proof.
  intros. destruct H2,H3.
  - left. apply @ FAT171 with Y; auto.
  - subst. left; auto.
  - subst. left; auto.
  - subst; right; auto.
Qed.

(*正有理数集*)
Definition PrC := \{\ λ u v, u ∈ RCC /\ v = zero \}\.
(*负有理数集*)
Definition NrC := \{\ λ u v, u = zero /\ v ∈ RCC \}\.
(*有理数集*)
Definition rC' := PrC ∪ [zero] ∪ NrC.

(* Definition PiC := \{\ λ u v, u ∈ IrratC /\ v = zero \}\. *)
(*正无理数集*)
Definition PiC := PRC ~ PrC.
(*负无理数集*)
Definition NiC := NRC ~ NrC.
(*无理数集*)
Definition IrratC' := RC ~ rC'.

(*正整数集*)
Definition PNC := \{\ λ u v, u ∈ NCC /\ v = zero \}\.
(*负整数集*)
Definition NNC := \{\ λ u v, u = zero /\ v ∈ NCC \}\.
(*整数集*)
Definition NC' := PNC ∪ [zero] ∪ NNC.

Theorem FAT174 : ∀ X, X ∈ NC' -> X ∈ rC'.
Proof.
  intros. unfold NC' in H. unfold rC'. deGun. deHun.
  - left. appA2H H. destruct H0 as [x[y[?[]]]]. appA2G.
    exists x, y. repeat split; auto. appA2H H1. appA2G.
    destruct H3 as [n[]]. exists (Ntor n). split; auto.
  - right. deGun. tauto.
  - right. deGun. right. appA2H H. destruct H0 as [x[y[?[]]]].
    appA2G. exists x, y. repeat split; auto. appA2H H2.
    appA2G. destruct H3 as [n[]]. exists (Ntor n). split; auto.
Qed.

(* SECTION III Addition *)

Definition addR a := 
  \{\ λ b c, b ∈ RC /\
  (a ∈ PRC -> b ∈ PRC -> c = [addc a¹ b¹,zero]) /\ 
  (a ∈ NRC -> b ∈ NRC -> c = [zero,addc a² b²]) /\ 
  (a = zero -> c = b) /\ (b = zero -> c = a) /\ 
  (a ∈ PRC -> b ∈ NRC -> (a¹ = b² -> c = zero) /\ 
  (gtc a¹ b² -> c = [minc a¹ b²,zero]) /\
  (ltc a¹ b² -> c = [zero,minc b² a¹]))  /\
  (a ∈ NRC -> b ∈ PRC -> (a² = b¹ -> c = zero) /\ 
  (gtc a² b¹ -> c = [zero,minc a² b¹]) /\
  (ltc a² b¹ -> c = [minc b¹ a²,zero])) \}\.

Notation "x + y" := ((addR x) [y]) : RC_scope.

Fact adrf : ∀ a, a ∈ RC -> Function (addR a).
Proof.
  intros. split; intros. apply poisre.
  apply AxiomII' in H1; apply AxiomII' in H0; deand.
  destruct (inRC H) as [?|[?|?]];
  destruct (inRC H2) as [?|[?|?]]; ReF.
  + pose proof (H7 H16 H17). pose proof (H14 H16 H17). deand.
    destruct (@ FAT123 a¹ x²) as [?|[?|?]]; ReF.
  + pose proof (H8 H16 H17). pose proof (H15 H16 H17). deand.
    destruct (@ FAT123 a² x¹) as [?|[?|?]]; ReF.
Qed.

Global Hint Resolve adrf : core.

Fact AddRpa : ∀ {b}, b ∈ RC -> (addR zero)[b] = b.
Proof.
  ltacr1.
Qed.

Fact AddRpb : ∀ {a}, a ∈ RC -> (addR a)[zero] = a.
Proof.
  ltacr1.
Qed.

Fact AddRpc : ∀ {a b}, a ∈ PRC -> b ∈ PRC -> (addR a)[b] = [addc a¹ b¹,zero].
Proof.
  ltacr1.
Qed.

Fact AddRpd : ∀ {a b}, a ∈ NRC -> b ∈ NRC -> (addR a)[b] = [zero,addc a² b²].
Proof.
  ltacr1.
Qed.

Fact AddRpe : ∀ {a b}, a ∈ PRC -> b ∈ NRC -> a¹ = b² -> (addR a)[b] = zero.
Proof.
  ltacr1; CordF.
Qed.

Fact AddRpf : ∀ {a b}, a ∈ NRC -> b ∈ PRC -> a² = b¹ -> (addR a)[b] = zero.
Proof.
  ltacr1; CordF.
Qed.

Fact AddRpg : ∀ {a b}, a ∈ PRC -> b ∈ NRC -> gtc a¹ b²
  -> (addR a)[b] = [minc a¹ b²,zero].
Proof.
  ltacr1; CordF.
Qed.

Fact AddRph : ∀ {a b}, a ∈ NRC -> b ∈ PRC -> gtc a² b¹
  -> (addR a)[b] = [zero,minc a² b¹].
Proof.
  ltacr1; CordF.
Qed.

Fact AddRpi : ∀ {a b}, a ∈ PRC -> b ∈ NRC -> ltc a¹ b²
  -> (addR a)[b] = [zero,minc b² a¹].
Proof.
  ltacr1; CordF.
Qed.

Fact AddRpj : ∀ {a b}, a ∈ NRC -> b ∈ PRC -> ltc a² b¹
  -> (addR a)[b] = [minc b¹ a²,zero].
Proof.
  ltacr1; CordF.
Qed.

Fact sym : ∀ {a b :Class}, a = b -> b = a.
Proof.
  intros. auto.
Qed.

Ltac find_eqa :=
  match goal with
    H: ?a ∈ RC
    |- _ => rewrite (AddRpa H) in *
  end.

Ltac find_eqb :=
  match goal with
    H: ?a ∈ RC
    |- _ => rewrite (AddRpb H) in *
  end.

Ltac find_eqc :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ PRC
    |- _ => rewrite (AddRpc H1 H2) in *
  end.

Ltac find_eqd :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ NRC
    |- _ => rewrite (AddRpd H1 H2) in *
  end.

Ltac req1 := try find_eqa; try find_eqb; try find_eqc;
  try find_eqd.

Ltac find_eqe :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC,
    H3: ?a¹ = ?b²
    |- _ => rewrite (AddRpe H1 H2 H3) in *
  end.

Ltac find_eqf :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC,
    H3: ?a² = ?b¹
    |- _ => rewrite (AddRpf H1 H2 H3) in *
  end.

Ltac find_eqg :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC,
    H3: gtc ?a¹ ?b²
    |- _ => rewrite (AddRpg H1 H2 H3) in *
  end.

Ltac find_eqh :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC,
    H3: gtc ?a² ?b¹
    |- _ => rewrite (AddRph H1 H2 H3) in *
  end.

Ltac find_eqi :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC,
    H3: ltc ?a¹ ?b²
    |- _ => rewrite (AddRpi H1 H2 H3) in *
  end.

Ltac find_eqj :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC,
    H3: ltc ?a² ?b¹
    |- _ => rewrite (AddRpj H1 H2 H3) in *
  end.

Ltac find_eqE :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC,
    H3: ?b² = ?a¹
    |- _ => rewrite (AddRpe H1 H2 (sym H3)) in *
  end.

Ltac find_eqF :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC,
    H3: ?b¹ = ?a²
    |- _ => rewrite (AddRpf H1 H2 (sym H3)) in *
  end.

Ltac find_eqG :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC,
    H3: ltc ?b² ?a¹
    |- _ => rewrite (AddRpg H1 H2 H3) in *
  end.

Ltac find_eqH :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC,
    H3: ltc ?b¹ ?a²
    |- _ => rewrite (AddRph H1 H2 H3) in *
  end.

Ltac find_eqI :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC,
    H3: gtc ?b² ?a¹
    |- _ => rewrite (AddRpi H1 H2 H3) in *
  end.

Ltac find_eqJ :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC,
    H3: gtc ?b¹ ?a²
    |- _ => rewrite (AddRpj H1 H2 H3) in *
  end.

Ltac req2 := try find_eqe; try find_eqf; try find_eqg; 
  try find_eqh; try find_eqi; try find_eqj; 
  try find_eqE; try find_eqF; try find_eqG; 
  try find_eqH; try find_eqI; try find_eqJ.

Theorem FAT175 : ∀ {a b}, a ∈ RC -> b ∈ RC -> a + b = b + a.
Proof with auto.
  intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]];
  subst; repeat req1; try rewrite FAT130...
  - destruct (@ FAT123 a¹ b²) as [?|[?|?]]; repeat req2...
  - destruct (@ FAT123 a² b¹) as [?|[?|?]]; repeat req2...
Qed.

Fact padd : ∀ a b, a ∈ PRC -> b ∈ PRC -> a + b ∈ PRC.
Proof.
  intros. req1; auto.
Qed.

Fact nadd : ∀ a b, a ∈ NRC -> b ∈ NRC -> a + b ∈ NRC.
Proof.
  intros. req1; auto.
Qed.

Global Hint Resolve padd nadd : core.

(*负*)
Definition minR := \{\ λ a b, a ∈ RC /\ (a ∈ PRC -> b = [zero,a¹])
  /\ (a ∈ NRC -> b = [a²,zero]) /\ (a = zero -> b= zero) \}\.

Notation "- x" := (minR[x]) : RC_scope.

Fact mirf : Function minR.
Proof.
  split; intros. apply poisre.
  apply AxiomII' in H; apply AxiomII' in H0; deand.
  destruct (inRC H1) as [?|[?|?]]; ReF.
Qed.

Global Hint Resolve mirf : core.

Fact Pmin : ∀ r, r ∈ PRC -> minR[r] = [zero,r¹].
Proof.
  ltacr1.
Qed.

Fact Nmin : ∀ r, r ∈ NRC -> minR[r] = [r²,zero].
Proof.
  ltacr1.
Qed.

Fact Zmin : minR[zero] = zero.
Proof.
  ltacr1.
Qed.

Fact gzr : ∀ r, zero < r -> r ∈ PRC.
Proof.
  intros. red in H. deor; deand; npz; auto.
Qed.

Fact lzr : ∀ r, r < zero -> r ∈ NRC.
Proof.
  intros. red in H. deor; deand; npz; auto.
Qed.

Global Hint Resolve lzr gzr : core.

Fact czo : ∀ x, x ∈ CC -> [x,zero] ∈ PRC.
Proof.
  intros. apply AxiomII'; repeat split; rxo.
Qed.

Fact zco : ∀ x, x ∈ CC -> [zero,x] ∈ NRC.
Proof.
  intros. apply AxiomII'; repeat split; rxo.
Qed.

Global Hint Resolve czo zco : core.

Theorem FAT176a1 : ∀ r, zero < r -> -r < zero.
Proof.
  intros. red. right. right. right. left. rewrite Pmin; auto.
Qed.

Theorem FAT176b1 : ∀ r, r = zero -> -r = zero.
Proof.
  intros. subst; apply Zmin.
Qed.

Theorem FAT176c1 : ∀ r, r < zero -> zero < (- r).
Proof.
  intros. red. right. left. rewrite Nmin; auto.
Qed.

Theorem FAT176a2 : ∀ r, r ∈ RC -> -r < zero -> zero < r.
Proof.
  intros. destruct (inRC' r H) as [H1|[H1|H1]]; auto.
  - apply FAT176b1 in H1. CordR.
  - apply FAT176c1 in H1; CordR.
Qed.

Theorem FAT176b2 : ∀ r, r ∈ RC -> -r = zero -> r = zero.
Proof.
  intros. destruct (inRC' r H) as [H1|[H1|H1]]; auto.
  - apply FAT176a1 in H1. CordR.
  - apply FAT176c1 in H1; CordR.
Qed.

Theorem FAT176c2 : ∀ r, r ∈ RC -> zero < (- r) -> r < zero.
Proof.
  intros. destruct (inRC' r H) as [H1|[H1|H1]]; auto.
  - apply FAT176a1 in H1. CordR.
  - apply FAT176b1 in H1; CordR.
Qed.

Fact minRC : ∀ X, X ∈ RC -> (-X) ∈ RC.
Proof.
  intros. destruct (@ inRC X H) as [H0|[H0|H0]].
  - rewrite Pmin; auto.
  - subst. rewrite Zmin; auto.
  - rewrite Nmin; auto.
Qed.

Global Hint Resolve minRC : core.

Theorem FAT177 : ∀ X, X ∈ RC -> -(-X) = X.
Proof.
  intros. apply funv; auto. apply AxiomII'.
  pose proof (minRC _ H). repeat split; intros; rxo; auto.
  - apply FAT169a in H1; auto. apply FAT176c2 in H1; auto.
    apply FAT169b' in H1; auto. rewrite Nmin; auto. GE.
  - apply FAT169b in H1; auto. apply FAT176a2 in H1; auto.
    apply FAT169a' in H1; auto. rewrite Pmin; auto. GE.
  - apply FAT176b2; auto.
Qed.

Theorem FAT178 : ∀ X, X ∈ RC -> |(-X)| = |X|.
Proof.
  intros. destruct (@inRC X H) as [H0|[H0|H0]].
  - rewrite Pmin; auto. reqb1; auto. symmetry; auto.
  - subst; rewrite Zmin; auto.
  - rewrite Nmin; auto. reqb1; auto.
Qed.

Theorem FAT179a : ∀ X, X ∈ RC -> (X + (-X)) = 0.
Proof.
  intros. destruct (@inRC X H) as [H0|[H0|H0]].
  - New H0. apply FAT169a in H1. apply FAT176a1 in H1.
    apply FAT169b' in H1; auto. rewrite Pmin in *; auto.
    New H0. rewrite Pr with X in H0; auto. rewrite Pr with X; auto.
    GE. apply AddRpe; auto. GE.
  - subst. rewrite Zmin; auto. apply AddRpa; auto.
  - New H0. apply FAT169b in H1. apply FAT176c1 in H1.
    apply FAT169a' in H1; auto. rewrite Nmin in *; auto.
    New H0. rewrite Nr with X in H0; auto. rewrite Nr with X; auto.
    GE. apply AddRpf; auto. GE.
Qed.

Theorem FAT179b : ∀ X, X ∈ RC -> ((-X) + X) = 0.
Proof.
  intros; rewrite FAT175; auto. apply (FAT179a _ H).
Qed.

Fact si1 : ∀ u, u ∈ PRC -> (- u) ∈ NRC.
Proof.
  intros. apply FAT169b'; auto. apply FAT176a1; auto.
  apply FAT169a; auto.
Qed.

Fact si1' : ∀ u, u ∈ NRC -> (- u) ∈ PRC.
Proof.
  intros. apply FAT169a'; auto. apply FAT176c1; auto.
Qed.

Fact si2 : ∀ X Y, Y < X -> X > Y.
Proof.
  auto.
Qed.

Fact si2' : ∀ X Y, Y > X -> X < Y.
Proof.
  auto.
Qed.

Fact si3 : 0 < 0 -> False.
Proof.
  intros. assert (0 = 0). auto. CordR.
Qed.

Ltac simplogic :=
  match goal with
  | H: ?u ∈ PRC,
    H0: ?u ∈ NRC
    |- _ => npz
  | H: ?u∈ PRC
    |- - ?u∈ NRC => apply si1; apply H
  | H: ?u∈ NRC
    |- - ?u∈ PRC => apply si1'; apply H
  | H: ?X ∈ NRC,
    H0: ?Y ∈ PRC
    |- ?G => match G with
            | ?X<?Y =>  apply (@ NltP _ _ H H0)
            | ?Y>?X =>  apply (@ si2 _ _ (@ NltP _ _ H H0))
            end
  | H: ?X ∈ PRC,
    H0: ?Y ∈ PRC
    |- ?Y > -?X => apply (@ si2 _ _ (@ NltP _ _ (@ si1 _ H) H0))
  | H : ?X ∈ PRC
    |- 0 > - ?X => apply FAT176a1; apply FAT169a; auto
  | H : 0 < 0
    |- _ => destruct si3; auto
  | H : 0 > 0
    |- _ => destruct si3; auto
  | H : ?X ∈ PRC,
    H1 : ?Y ∈ PRC
    |- ?X + ?Y ∈ PRC => req1; auto
  | H : ?X ∈ NRC,
    H1 : ?Y ∈ NRC
    |- ?X + ?Y ∈ NRC => req1; auto
  | |- _ => idtac
  end.

Theorem FAT180 : ∀ X Y, X ∈ RC -> Y ∈ RC -> -(X + Y) = (-X) + (-Y).
Proof.
  intros. destruct (FAT167 H H0) as [?|[?|?]].
  - subst. destruct (inRC H) as [?|[?|?]].
    + pose proof (si1 _ H1). rewrite Pmin; auto.
      rewrite (AddRpd H2 H2). apply MKT55; rxo. split; auto.
      rewrite AddRpc; auto. rewrite Pmin; auto. GE.
    + subst. req1. rewrite Zmin. req1; auto.
    + pose proof (si1' _ H1). rewrite Nmin; auto.
      rewrite (AddRpc H2 H2). apply MKT55; rxo. split; auto.
      rewrite AddRpd; auto. rewrite Nmin; auto. GE.
  - apply si2' in H1. Order.
    + rewrite Pmin; auto. pose proof (si1 _ H1).
      pose proof (si1 _ H2). repeat req1. 
      repeat rewrite Pmin; auto. repeat GE.
    + rewrite Zmin. pose proof (si1 _ H2). req1.
      rewrite AddRpb; auto.
    + destruct (@ FAT123 X¹ Y²) as [?|[?|?]]; auto.
      * assert (X = -Y). { rewrite Nmin; auto. rewrite <- H3.
        auto. } subst. rewrite FAT179b; auto. rewrite FAT177; auto.
        rewrite FAT179a; auto. rewrite Zmin; auto.
      * req2. rewrite Pmin; auto. assert (((-X)² > (-Y)¹)%CC).
        { rewrite Pmin; auto. rewrite Nmin; auto. GE. }
        rewrite AddRph; auto; simplogic.
        rewrite Pmin; auto. rewrite Nmin; auto. repeat GE.
      * req2. rewrite Nmin; auto. assert (((-X)² < (-Y)¹)%CC).
        { rewrite Pmin; auto. rewrite Nmin; auto. GE. }
        rewrite AddRpj; auto; simplogic.
        rewrite Nmin; auto. rewrite Pmin; auto. repeat GE.
    + rewrite Zmin. repeat rewrite AddRpa; auto.
    + rewrite Nmin; auto. pose proof (si1' _ H1).
      pose proof (si1' _ H2). repeat req1. 
      repeat rewrite Nmin; auto. repeat GE.
  - Order.
    + rewrite Pmin; auto. pose proof (si1 _ H1).
      pose proof (si1 _ H2). repeat req1. 
      repeat rewrite Pmin; auto. repeat GE.
    + rewrite Zmin. pose proof (si1 _ H2). req1.
      rewrite AddRpa; auto.
    + destruct (@ FAT123 Y¹ X²) as [?|[?|?]]; auto.
      * assert (Y = -X).
        { rewrite Nmin; auto. rewrite <- H3. auto. }
        subst. rewrite FAT179a; auto. rewrite FAT177; auto.
        rewrite FAT179b; auto. rewrite Zmin; auto.
      * req2. rewrite Pmin; auto. assert (((-Y)² > (-X)¹)%CC).
        { rewrite Pmin; auto. rewrite Nmin; auto. GE. }
        rewrite AddRpi; auto; simplogic.
        rewrite Pmin; auto. rewrite Nmin; auto. repeat GE.
      * req2. rewrite Nmin; auto. assert (((-Y)² < (-X)¹)%CC).
        { rewrite Pmin; auto. rewrite Nmin; auto. GE. }
        rewrite AddRpg; auto; simplogic.
        rewrite Nmin; auto. rewrite Pmin; auto. repeat GE.
    + rewrite Zmin. repeat rewrite AddRpb; auto.
    + rewrite Nmin; auto. pose proof (si1' _ H1).
      pose proof (si1' _ H2). repeat req1. 
      repeat rewrite Nmin; auto. repeat GE.
Qed.

Fact minRp1 : ∀ X, X ∈ RC -> X = (- X) -> X = 0.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; auto.
  - assert (- X ∈ NRC). simplogic. rewrite H0 in H1. npz.
  - assert (- X ∈ PRC). simplogic. rewrite H0 in H1. npz.
Qed.

Global Hint Resolve minRp1 : core.

Definition MinR a b := (addR a)[minR[b]].

Notation "x - y" := ((addR x) [minR [y]]) : RC_scope.

Theorem FAT181 : ∀ X Y, X ∈ RC -> Y ∈ RC -> -(X - Y) = Y - X.
Proof.
  intros. rewrite FAT180; auto. rewrite FAT177; auto.
  rewrite FAT175; auto.
Qed.

Theorem FAT182a1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> (X - Y) > 0 -> X > Y.
Proof.
  intros. set (- Y) as u. assert (Y = (- u)).
  { unfold u. rewrite FAT177; auto. }
  assert (u ∈ RC).
  { unfold u; auto. } rewrite H2 in *. rewrite FAT177 in H1; auto.
  destruct (@ inRC X H) as [H4|[H4|H4]];
  destruct (@ inRC u H3) as [H5|[H5|H5]].
  - simplogic.
  - rewrite H5. rewrite Zmin; auto.
  - destruct (FAT167 H H0) as [H6|[H6|H6]]; auto.
    + rewrite H6 in H1. rewrite FAT179b in H1; auto. simplogic.
    + red in H6; destruct H6 as [[?[]]|[[]|[[]|[[]|[?[]]]]]];
      try npz.
      * assert ((- u)¹ = (u)²). { rewrite Nmin; auto. GE. }
        rewrite H9 in H8. pose proof (AddRpi H4 H5). MP.
        assert (X + u ∈ NRC).
        { appA2G. exists 0, ((u)² - (X)¹)%CC.
        repeat split; auto. }
        apply FAT169b in H10; auto. CordR.
      * rewrite H6 in H4; npz.
  - rewrite H4. simplogic.
  - rewrite H4,H5 in H1. rewrite AddRpa in H1; auto. simplogic.
  - rewrite H4 in H1. rewrite AddRpa in H1; auto.
    apply FAT169b in H5. CordR.
  - destruct (FAT167 H H0) as [H6|[H6|H6]]; auto.
    + rewrite H6 in H1. rewrite FAT179b in H1; auto. simplogic.
    + red in H6; destruct H6 as [[?[]]|[[]|[[]|[[]|[?[]]]]]]; 
      try rewrite H6 in H4; try npz.
      * assert (- u ∈ NRC). simplogic. npz.
      * assert (- u ∈ NRC). simplogic. rewrite H7 in H8; npz.
      * assert ((- u)² = (u)¹). { rewrite Pmin; auto. GE. }
        rewrite H9 in H8. pose proof (AddRpi H5 H4). MP.
        assert (X + u ∈ NRC).
        { appA2G. exists 0,((X)² - (u)¹)%CC. repeat split; auto.
        rewrite FAT175; auto. }
        apply FAT169b in H10; auto. CordR.
  - rewrite H5 in *. rewrite AddRpb in H1; auto. rewrite Zmin; auto.
  - assert (X + u < 0). { apply FAT169b; auto. } CordR.
Qed.

Fact FAT182a1_aux : ∀ X Y, X ∈ RC -> Y ∈ RC -> (X + Y) > 0 -> X > - Y.
Proof.
  intros. apply FAT182a1; auto. rewrite FAT177; auto.
Qed.

Fact FAT182b1_aux : ∀ X Y, X ∈ RC -> Y ∈ RC -> (X + Y) = 0 -> X = - Y.
Proof.
  intros. destruct (@ inRC X H) as [H2|[H2|H2]];
  destruct (@ inRC Y H0) as [H3|[H3|H3]].
  - assert ((X + Y) ∈ PRC). auto. rewrite H1 in H4. npz.
  - rewrite H3 in *. rewrite Zmin; auto. rewrite <- H1. req1; auto.
  - destruct (@ FAT123 X¹ Y²) as [?|[?|?]]; auto.
    + rewrite Nmin; auto. rewrite <- H4; auto.
    + assert ((X + Y) > 0). { req2. auto. } CordR.
    + assert ((X + Y) < 0). { req2. auto. } CordR.
  - rewrite H2 in *. req1. rewrite H1. rewrite Zmin; auto.
  - subst. rewrite Zmin; auto.
  - rewrite H2 in *. req1. rewrite H1. rewrite Zmin; auto.
  - destruct (@ FAT123 Y¹ X²) as [?|[?|?]]; auto.
    + rewrite Pmin; auto. rewrite H4; auto.
    + assert ((X + Y) > 0). { req2. auto. } CordR.
    + assert ((X + Y) < 0). { req2. auto. } CordR.
  - rewrite H3 in *. req1. rewrite H1. rewrite Zmin; auto.
  - assert ((X + Y) ∈ NRC). auto. rewrite H1 in H4. npz.
Qed.

Fact FAT182c1_aux : ∀ X Y, X ∈ RC -> Y ∈ RC -> (X + Y) < 0 -> X < -Y.
Proof.
  intros. destruct (@ inRC X H) as [H2|[H2|H2]];
  destruct (@ inRC Y H0) as [H3|[H3|H3]].
  - assert ((X + Y) ∈ PRC). auto. apply FAT169a in H4. CordR.
  - rewrite H3 in *. req1. rewrite Zmin; auto.
  - destruct (@ FAT123 X¹ Y²) as [?|[?|?]]; auto.
    + assert ((X + Y) = 0). { req2. auto. } CordR.
    + assert ((X + Y) > 0). { req2. auto. } CordR.
    + red. left. repeat split; auto. simplogic.
      rewrite Nmin; auto. GE.
  - rewrite H2 in *. req1. Order.
  - subst. req1. CordR.
  - rewrite H2 in *. req1. rewrite Nmin; auto.
    apply FAT169a; auto.
  - destruct (@ FAT123 Y¹ X²) as [?|[?|?]]; auto.
    + assert ((X + Y) = 0). { req2. auto. } CordR.
    + assert ((X + Y) > 0). { req2. auto. } CordR.
    + red. repeat right. repeat split; auto. simplogic.
      rewrite Pmin; auto. GE.
  - rewrite H3 in *. req1. rewrite Zmin; auto.
  - assert (-Y ∈ PRC). simplogic. auto.
Qed.

Theorem FAT182b1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X - Y = 0 -> X = Y.
Proof.
  intros. rewrite <- FAT177 with Y; auto. apply FAT182b1_aux; auto.
Qed.

Theorem FAT182c1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> (X - Y) < 0 -> X < Y.
Proof.
  intros. rewrite <- FAT177 with Y; auto. apply FAT182c1_aux; auto.
Qed.

Fact addRC : ∀ X Y, X ∈ RC -> Y ∈ RC -> (X + Y) ∈ RC.
Proof.
  intros. destruct (@ inRC X H) as [H1|[H1|H1]];
  destruct (@ inRC Y H0) as [H2|[H2|H2]]; try subst; try req1; auto.
  - destruct (@ FAT123 (X)¹ (Y)²) as [?|[?|?]]; auto; req2; auto.
  - destruct (@ FAT123 (X)² (Y)¹) as [?|[?|?]]; auto; req2; auto.
Qed.

Global Hint Resolve addRC : core.

Theorem FAT182a2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X > Y -> (X - Y) > 0.
Proof.
  intros. assert ((X - Y) ∈ RC). auto.
  destruct (inRC' _ H2) as [?|[?|?]]; auto.
  - apply FAT182b1 in H3; auto. CordR.
  - apply FAT182c1 in H3; auto; CordR.
Qed.

Theorem FAT182b2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X = Y -> X - Y = 0.
Proof.
  intros. assert ((X - Y) ∈ RC). auto.
  destruct (inRC' _ H2) as [?|[?|?]]; auto.
  - apply FAT182a1 in H3; auto. CordR.
  - apply FAT182c1 in H3; auto; CordR.
Qed.

Theorem FAT182c2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X < Y -> (X - Y) < 0.
Proof.
  intros. assert ((X - Y) ∈ RC). auto.
  destruct (inRC' _ H2) as [?|[?|?]]; auto.
  - apply FAT182a1 in H3; auto. CordR.
  - apply FAT182b1 in H3; auto; CordR.
Qed.

Theorem FAT183a1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X > Y -> -X < -Y.
Proof.
  intros. apply FAT182c1; auto. rewrite FAT177; auto.
  rewrite FAT175; auto. apply FAT182c2; auto.
Qed.

Theorem FAT183b1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X = Y -> -X = -Y.
Proof.
  intros. apply FAT182b1; auto. rewrite FAT177; auto.
  rewrite FAT175; auto. apply FAT182b2; auto.
Qed.

Theorem FAT183c1 : ∀ X Y, X ∈ RC -> Y ∈ RC -> X < Y -> -X > -Y.
Proof.
  intros. apply FAT182a1; auto. rewrite FAT177; auto.
  rewrite FAT175; auto. apply FAT182a2; auto.
Qed.

Theorem FAT183a2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> -X < -Y -> X > Y.
Proof.
  intros. destruct (FAT167 H H0) as [?|[?|?]]; auto.
  - apply FAT183b1 in H2; auto; CordR.
  - apply FAT183c1 in H2; auto; CordR.
Qed.

Theorem FAT183b2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> -X = -Y -> X = Y.
Proof.
  intros. destruct (FAT167 H H0) as [?|[?|?]]; auto.
  - apply FAT183a1 in H2; auto; CordR.
  - apply FAT183c1 in H2; auto; CordR.
Qed.

Theorem FAT183c2 : ∀ X Y, X ∈ RC -> Y ∈ RC -> -X > -Y -> X < Y.
Proof.
  intros. destruct (FAT167 H H0) as [?|[?|?]]; auto.
  - apply FAT183b1 in H2; auto; CordR.
  - apply FAT183a1 in H2; auto; CordR.
Qed.

(* 将自然数嵌入实数 *)
Definition NtoR x := [rtoC (Ntor x), 0%RC].

Fact NtoRRC : ∀ x , x ∈ Nat -> (NtoR x) ∈ RC.
Proof.
  intros. unfold NtoR; auto.
Qed.

Global Hint Resolve NtoRRC : core.

Fact NtoR1 : ∀ x y, x ∈ Nat -> y ∈ Nat -> x = y -> NtoR x = NtoR y.
Proof.
  intros. rewrite H1; auto.
Qed.

Fact NtoR1' : ∀ x y, x ∈ Nat -> y ∈ Nat -> NtoR x = NtoR y -> x = y.
Proof.
  intros. unfold NtoR in H1. apply MKT55 in H1; rxo.
  destruct H1. apply FAT154b2 in H1; auto.
  apply Ntor2a; auto.
Qed.

Fact NtoRP : ∀ {x}, x ∈ Nat -> (NtoR x) ∈ PRC.
Proof.
  intros. unfold NtoR. auto.
Qed.

Global Hint Resolve NtoRP : core.

Fact NtoR2 : ∀ x y, x ∈ Nat -> y ∈ Nat
  -> (NtoR x) + (NtoR y) = NtoR (x + y)%Nat.
Proof.
  intros. pose proof (NtoRP H). pose proof (NtoRP H0).
  req1. unfold NtoR. repeat GE. apply MKT55; rxo.
  exists CC; auto. split; auto. rewrite <- FAT155a; auto.
  apply FAT154a2; auto. rewrite addr1; auto.
Qed.

Fact NtoR3 : ∀ x y, x ∈ Nat -> y ∈ Nat -> (x < y)%Nat -> NtoR x < NtoR y.
Proof.
  intros. red. left. repeat split; auto. unfold NtoR. repeat GE.
  apply FAT154a3; auto. apply Ntor1; auto.
Qed.

Fact NtoR3' : ∀ x y, x ∈ Nat -> y ∈ Nat -> NtoR x < NtoR y -> (x < y)%Nat.
Proof.
  intros. destruct (FAT10 H H0) as [?|[?|?]]; auto.
  - apply NtoR1 in H2; auto. CordR.
  - apply NtoR3 in H2; auto. CordR.
Qed.

Notation " 1 " := [(rtoC (Ntor One)), 0] : RC_scope.

Fact NtoROne: NtoR One = 1.
Proof.
  unfold NtoR; auto.
Qed.

Fact Onep : 1 ∈ PRC.
Proof.
  apply AxiomII'. repeat split; rxo.
Qed.

Global Hint Resolve Onep : core.

Fact add1gt : ∀ X, X ∈ PRC -> X + 1 > 1.
Proof.
  intros. pose proof Onep. req1. red. left. repeat split; auto.
  repeat GE. rewrite FAT130; auto. apply FAT133; auto.
Qed.

Fact add2gt : ∀ X, X ∈ NRC -> 1 - X > 1.
Proof.
  intros. pose proof Onep.
  assert (- X ∈ PRC). rewrite Nmin; auto.
  req1. red. left. repeat split; auto.
  repeat GE. apply FAT133; auto.
Qed.

Fact add3gt : ∀ X, X ∈ NRC -> X - 1 < 1.
Proof.
  intros. pose proof Onep. assert (- (1) ∈ NRC). simplogic. 
  assert ((X - 1) ∈ NRC). simplogic. auto.
Qed.

Fact add4gt : ∀ X, X ∈ NRC -> X - 1 < - (1).
Proof.
  intros. apply FAT183a2; auto. rewrite FAT180; auto.
  rewrite FAT177; auto. rewrite FAT175; auto. apply add2gt; auto.
Qed.

Ltac sl :=
  match goal with
  | H : ?X ∈ PRC
    |- ?X + 1 > 1 => apply (add1gt _ H)
  | H : ?X ∈ PRC
    |- (- ?X)² = (?X)¹ => rewrite Pmin; auto; GE
  | H : ?X ∈ NRC
    |- (- ?X)¹ = (?X)² => rewrite Nmin; auto; GE
  | |- | ?X | ∈ PRC => apply FAT166; auto; intro; subst; npz
  | |- _ => simplogic
  end.

Theorem FAT184 : ∀ X, X ∈ RC -> ∃ a b, a ∈ PRC /\ b ∈ PRC /\ X = a - b.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - exists (X + 1), 1. pose proof Onep. repeat split; auto. 
    assert (- (1) ∈ NRC). simplogic.
    assert ((X + 1) ∈ PRC). simplogic. assert (1 < X + 1).
    apply add1gt; auto. Order. assert ((- (1))² = (1)¹). sl.
    rewrite <- H7 in H6. req2. rewrite Pmin; auto. req1.
    repeat GE. pattern X at 1; rewrite Pr; auto.
    assert ((X)¹ ∈ CC). auto.
    assert (rtoC (Ntor One) ∈ CC). auto.
    apply MKT55; auto. unfold Ensemble; eauto.
    assert ((X)¹ + rtoC (Ntor One) > rtoC (Ntor One))%CC.
    rewrite FAT130; auto. apply FAT133; auto.
    split; auto. apply FAT136b with (rtoC (Ntor One)); auto.
    rewrite @ FAT130 with ((X)¹ + rtoC (Ntor One) -
    rtoC (Ntor One))%CC (rtoC (Ntor One)); auto.
    rewrite MinCEx; auto. rewrite H4. rewrite Zmin.
    repeat req1; auto.
  - exists 1, 1. repeat split; auto. rewrite FAT179a; auto.
  - exists 1, (| X | + 1). assert (| X | ∈ PRC). sl.
    pose proof Onep. repeat split; auto. sl. reqb1.
    rewrite <- Nmin; auto. rewrite FAT180; auto. rewrite FAT177; auto.
    assert (- (1) ∈ NRC). simplogic.
    assert ((X - 1) ∈ NRC). simplogic. assert (X - 1 < - (1)).
    apply add4gt; auto. Order. rewrite H6 in H3; npz.
    assert ((- (1))² = (1)¹). sl. rewrite H8 in H7. req1.
    req2. pattern X at 1; rewrite (Nr X); auto. 
    apply MKT55; auto. unfold Ensemble; eauto. repeat split; auto.
    repeat GE. rewrite H8. 
    assert ((X)² ∈ CC). auto.
    assert (rtoC (Ntor One) ∈ CC). auto.
    assert ((X)² + rtoC (Ntor One) > rtoC (Ntor One))%CC.
    rewrite FAT130; auto. apply FAT133; auto.
    apply FAT136b with (rtoC (Ntor One)); auto.
    rewrite @ FAT130 with ((X)² + rtoC (Ntor One) -
    rtoC (Ntor One))%CC (rtoC (Ntor One)); auto.
    rewrite MinCEx; auto.
Qed.

Lemma Lemma_FAT185a : ∀ X Y Z, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC
  -> X + Y + Z = X + (Y + Z).
Proof.
  intros. pose proof (padd X Y). MP. pose proof (padd Y Z); MP.
  repeat req1. repeat GE. apply MKT55; rxo. exists CC; auto.
  split; auto. apply FAT131; auto.
Qed.

Lemma Lemma_FAT185b : ∀ X Y Z U, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC -> U ∈ PRC
  -> (X + Y) + (Z + U) = (Z + X) + (U + Y).
Proof.
  intros. rewrite @ FAT175 with Z U; auto.
  rewrite <- Lemma_FAT185a; auto.
  rewrite @ FAT175 with (X + Y + U) Z; auto.
  rewrite Lemma_FAT185a; auto. rewrite <- Lemma_FAT185a; auto.
  rewrite @ FAT175 with Y U; auto.
Qed.

Lemma Lemma_FAT185c : ∀ X Y, X ∈ PRC -> Y ∈ PRC -> Y > X -> X + (Y - X) = Y.
Proof.
  intros. 
  assert ((Y - X) ∈ PRC). { apply FAT182a2 in H1; auto. }
  req1. apply si2' in H1. Order. assert (-X ∈ NRC). sl.
  assert (((-X)² < (Y)¹)%CC). { rewrite Pmin; auto. GE. }
  req2. GE. rewrite Pr; auto. apply MKT55; rxo.
  exists CC; auto. split; auto. rewrite Pmin; auto. GE.
  rewrite MinCEx; auto.
Qed.

Lemma Lemma_FAT185d : ∀ X Y Z, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC
  -> X + Z = Y + Z -> X = Y.
Proof.
  intros. repeat req1. apply MKT55 in H2; auto.
  destruct H2. apply FAT136b in H2; auto. exists CC; auto.
Qed.

Lemma Lemma_FAT185e : ∀ X Y Z U, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC -> U ∈ PRC
  -> X > Z -> Y > U -> X + Y > Z + U.
Proof.
  intros. apply si2' in H3. apply si2' in H4.
  Order. red. left. repeat split; auto. repeat req1.
  repeat GE. apply FAT137; auto.
Qed.

Lemma Lemma_FAT185f : ∀ X Y Z, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC
  -> X > Y -> X + Z > Y + Z.
Proof.
  intros. apply si2' in H2.
  Order. red. left. repeat split; auto. repeat req1.
  repeat GE. apply FAT135c; auto.
Qed.

Lemma Lemma_FAT185g : ∀ X Y Z, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC
  -> X = Y -> X + Z = Y + Z.
Proof.
  intros. subst; auto.
Qed.

Lemma FAT185_aux1 : ∀ X Y {a b c d}, X ∈ PRC -> Y ∈ PRC
  -> a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC
  -> X = a - b -> Y = c - d -> X + Y = (a + c) - (b + d).
Proof.
  intros.
  assert (a > b).
  { rewrite H5 in H; apply FAT182a1; auto. }
  assert (c > d).
  { rewrite H6 in H0; apply FAT182a1; auto. }
  assert ((a + c) > (b + d)).
  { apply Lemma_FAT185e; auto. }
  assert ((a + c - (b + d)) > 0).
  { apply FAT182a2; auto. }
  apply Lemma_FAT185d with (b + d); auto.
  rewrite @ FAT175 with (a + c - (b + d)) (b + d); auto.
  rewrite Lemma_FAT185c; auto.
  rewrite Lemma_FAT185b; auto. rewrite H5,H6.
  repeat rewrite Lemma_FAT185c; auto.
Qed.

Lemma FAT185_aux2 : ∀ X Y {a b c d}, X ∈ PRC -> Y ∈ NRC
  -> a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC -> X > (-Y)
  -> X = a - b -> Y = c - d -> X + Y = (a + c) - (b + d).
Proof.
  intros.
  assert ((X + Y) ∈ PRC).
  { apply FAT182a2 in H5; auto. rewrite FAT177 in H5; auto. }
  assert (a - b ∈ PRC).
  { rewrite H6 in H; auto. }
  assert (a > b).
  { apply FAT182a1; auto. }
  assert (d > c).
  { rewrite H7 in H0; apply FAT182c1; auto. }
  assert (d - c ∈ PRC).
  { apply FAT182a2 in H11; auto. } New H5.
  rewrite H6,H7 in H5. rewrite FAT181 in H5; auto.
  apply (Lemma_FAT185f _ _ b) in H5; auto.
  rewrite (@ FAT175 (a - b) b) in H5; auto.
  rewrite Lemma_FAT185c in H5; auto.
  apply (Lemma_FAT185f _ _ c) in H5; auto.
  rewrite (@ FAT175 (d - c + b) c) in H5; auto.
  rewrite <- Lemma_FAT185a in H5; auto.
  rewrite Lemma_FAT185c in H5; auto.
  rewrite (@ FAT175 d b) in H5; auto. New H5. 
  apply FAT182a2 in H14; auto.
  apply Lemma_FAT185d with (b + d); auto.
  rewrite @ FAT175 with (a + c - (b + d)) (b + d); auto.
  rewrite Lemma_FAT185c; auto.
  symmetry. pattern a at 1; rewrite <- (Lemma_FAT185c b a); auto.
  rewrite @ FAT175 with b (a - b); auto.
  rewrite Lemma_FAT185a; auto. rewrite FAT175; auto.
  rewrite H6,H7 in H13. rewrite FAT181 in H13; auto.
  New H13. apply FAT182a2 in H15; auto. pattern (a - b) at 1;
  rewrite <- (Lemma_FAT185c (d - c) (a - b)); auto.
  rewrite <- Lemma_FAT185a; auto. 
  rewrite (Lemma_FAT185a b c (d - c)); auto.
  rewrite Lemma_FAT185c; auto. rewrite FAT175,H6,H7; auto.
  rewrite FAT181; auto.
Qed.

Lemma FAT185_aux3 : ∀ X Y {a b c d}, X ∈ PRC -> Y ∈ NRC
  -> a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC
  -> X = a - b -> Y = c - d -> X + Y = (a + c) - (b + d).
Proof.
  intros. destruct (@ FAT167 X (-Y)) as [?|[?|?]]; auto.
  - rewrite H7. rewrite H5,H6 in H7. rewrite FAT181 in H7; auto.
    assert ((a - b) > 0).
    { rewrite H5 in H. auto. }
    assert ((d - c) > 0).
    { rewrite <- H7. auto. }
    apply (Lemma_FAT185g _ _ b) in H7; auto. New H9.
    apply FAT182a1 in H8, H9; auto.
    rewrite FAT175 in H7; auto. rewrite Lemma_FAT185c in H7; auto.
    apply (Lemma_FAT185g _ _ c) in H7; auto.
    rewrite (@ FAT175 (d - c + b) c) in H7; auto.
    rewrite <- Lemma_FAT185a in H7; auto.
    rewrite Lemma_FAT185c in H7; auto.
    rewrite (@ FAT175 b d); auto. rewrite FAT175; auto.
    rewrite FAT179a; auto. symmetry. apply FAT182b2; auto.
  - apply FAT185_aux2; auto.
  - rewrite <- FAT177 with (X + Y); auto. rewrite FAT180; auto.
    rewrite @ FAT175 with (-X) (-Y); auto.
    apply FAT183b1 in H5,H6; auto. rewrite FAT181 in H5,H6; auto.
    assert (- Y - X = (d + b) - (c + a)).
    { apply FAT185_aux2; auto; sl. rewrite FAT177; auto. }
    rewrite H8. rewrite FAT181; auto.
    rewrite @ FAT175 with c a; auto.
    rewrite @ FAT175 with d b; auto.
Qed.

Lemma FAT185_aux4 : ∀ X Y {a b c d}, X = 0 -> Y ∈ PRC
  -> a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC
  -> X = a - b -> Y = c - d -> X + Y = (a + c) - (b + d).
Proof.
  intros. rewrite H in H5. symmetry in H5.
  apply FAT182b1 in H5; auto.
  assert (c - d ∈ PRC). { rewrite H6 in H0; auto. }
  assert (c > d). { apply FAT182a1; auto. }
  assert (a + c = (c - d) + (a + d)).
  { rewrite @ FAT175 with a d; auto.
    rewrite <- Lemma_FAT185a; auto.
    rewrite @ FAT175 with (c - d) d; auto.
    rewrite Lemma_FAT185c; auto. rewrite FAT175; auto. }
  rewrite H. rewrite AddRpa; auto.
  assert (a + c > (b + d)).
  { rewrite H5. rewrite FAT175; auto.
    rewrite @ FAT175 with b d; auto. apply Lemma_FAT185f; auto. }
  New H10. apply FAT182a2 in H10; auto.
  apply Lemma_FAT185d with (b + d); auto.
  rewrite @ FAT175 with (a + c - (b + d)) (b + d); auto.
  rewrite Lemma_FAT185c; auto.
  rewrite H6,H9,H5; auto.
Qed.

Lemma FAT185_aux5 : ∀ X Y {a b c d}, X = 0 -> Y ∈ RC
  -> a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC
  -> X = a - b -> Y = c - d -> X + Y = (a + c) - (b + d).
Proof.
  intros. destruct (inRC H0) as [?|[?|?]].
  - apply FAT185_aux4; auto.
  - rewrite H, H7 in *. symmetry in H5,H6.
    apply FAT182b1 in H5,H6; auto.
    subst. rewrite FAT179a; auto. req1; auto.
  - New H5. rewrite H in H5. rewrite H. rewrite AddRpa; auto. 
    symmetry in H5; apply FAT182b1 in H5; auto.
    rewrite <- FAT177 with Y; auto. apply FAT183b1 in H6; auto.
    rewrite FAT181 in H6; auto.
    assert (-Y = ((a + d) - (b + c))).
    { rewrite <- AddRpa; auto. rewrite <- H. 
    apply FAT185_aux4; auto; sl. }
    rewrite H9. rewrite FAT181,H5; auto.
Qed.

Theorem FAT185 : ∀ X Y {a b c d}, X ∈ RC -> Y ∈ RC
  -> a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC
  -> X = a - b -> Y = c - d -> X + Y = (a + c) - (b + d).
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - destruct (inRC H0) as [?|[?|?]].
    + apply FAT185_aux1; auto.
    + rewrite FAT175; auto. rewrite @ FAT175 with a c; auto.
      rewrite @ FAT175 with b d; auto. apply FAT185_aux4; auto.
    + apply FAT185_aux3; auto.
  - apply FAT185_aux5; auto.
  - destruct (inRC H0) as [?|[?|?]].
    + rewrite FAT175; auto. rewrite @ FAT175 with a c; auto.
      rewrite @ FAT175 with b d; auto. apply FAT185_aux3; auto.
    + rewrite FAT175; auto. rewrite @ FAT175 with a c; auto.
      rewrite @ FAT175 with b d; auto. apply FAT185_aux5; auto.
    + rewrite <- FAT177 with (X + Y); auto.
      rewrite FAT180; auto. apply FAT183b1 in H5,H6; auto.
      rewrite FAT181 in H5,H6; auto.
      assert (- X - Y = ((b + d) - (a + c))).
      { apply FAT185_aux1; auto; sl. } rewrite H9.
      rewrite FAT181; auto.
Qed.

Fact FAT185' : ∀ a b c d, a ∈ PRC -> b ∈ PRC -> c ∈ PRC -> d ∈ PRC
  -> (a - b) + (c - d) = (a + c) - (b + d).
Proof.
  intros. set (a - b) as X. set (c - d) as Y.
  apply FAT185; auto. unfold X. auto. unfold Y; auto.
Qed.

Theorem FAT186 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> (X + Y) + Z = X + (Y + Z).
Proof.
  intros. pose proof (FAT184 _ H).
  pose proof (FAT184 _ H0). pose proof (FAT184 _ H1).
  destruct H2 as [x1[x2[?[]]]]. destruct H3 as [y1[y2[?[]]]].
  destruct H4 as [z1[z2[?[]]]]. subst. rewrite FAT185'; auto.
  rewrite FAT185'; auto. rewrite (Lemma_FAT185a x1 y1 z1); auto.
  rewrite (Lemma_FAT185a x2 y2 z2); auto. rewrite <- FAT185'; auto.
  rewrite <- FAT185'; auto.
Qed.

Fact add5gt : ∀ X, X ∈ RC -> X < X + 1.
Proof.
  intros. apply FAT182c1; auto. rewrite FAT180; auto.
  rewrite <- FAT186; auto. rewrite FAT179a; auto.
  rewrite AddRpa; auto. apply FAT176a1; auto.
  apply FAT169a; auto.
Qed.

Global Hint Resolve add5gt : core.

Fact addRp1 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X + Y + Z = Y + Z + X.
Proof.
  intros. rewrite FAT186; auto. rewrite FAT175; auto.
Qed.

Fact addRp2 : ∀ X Y Z U, X ∈ RC -> Y ∈ RC -> Z ∈ RC -> U ∈ RC
  -> (X + Y) + (Z + U) = (X + Z) + (Y + U).
Proof.
  intros. rewrite <- FAT186; auto.
  rewrite (@ FAT175 X Y); auto. rewrite (FAT186 Y X Z); auto.
  rewrite (@ FAT175 Y (X + Z)); auto. rewrite FAT186; auto.
Qed.

Fact MincEx : ∀ X Y, X ∈ RC -> Y ∈ RC -> X + (Y - X) = Y.
Proof.
  intros. rewrite @ FAT175 with Y (- X); auto.
  rewrite <- FAT186; auto. rewrite FAT179a; auto. req1. auto.
Qed.

Theorem FAT187a : ∀ X Y, X ∈ RC -> Y ∈ RC -> ∃ Z, Z ∈ RC /\ Y + Z = X.
Proof.
  intros. exists (X - Y). split; auto. apply MincEx; auto.
Qed.

Theorem FAT187b : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> Y + Z = X -> X - Y = Z.
Proof.
  intros. rewrite <- H2. rewrite FAT175; auto.
  rewrite <- FAT186; auto. rewrite @ FAT175 with (-Y) Y; auto.
  rewrite FAT179a; auto. req1; auto.
Qed.

Theorem FAT188a1 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X + Z > Y + Z -> X > Y.
Proof.
  intros. apply FAT182a2 in H2; auto. apply FAT182a1; auto.
  rewrite FAT180 in H2; auto.
  rewrite (@ FAT175 (-Y) (-Z)) in H2; auto.
  rewrite FAT186 in H2; auto.
  rewrite <- (FAT186 Z (-Z) (-Y)) in H2;
  auto. rewrite FAT179a in H2; auto. rewrite AddRpa in H2; auto.
Qed.

Theorem FAT188b1 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X + Z = Y + Z -> X = Y.
Proof.
  intros. apply FAT182b2 in H2; auto. apply FAT182b1; auto.
  rewrite FAT180 in H2; auto.
  rewrite (@ FAT175 (-Y) (-Z)) in H2; auto. 
  rewrite FAT186 in H2; auto.
  rewrite <- (FAT186 Z (-Z) (-Y)) in H2; auto.
  rewrite FAT179a in H2; auto. rewrite AddRpa in H2; auto.
Qed.

Theorem FAT188c1 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X + Z < Y + Z -> X < Y.
Proof.
  intros; eapply FAT188a1; eauto.
Qed.

Theorem FAT188a2 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X > Y -> X + Z > Y + Z.
Proof.
  intros. assert ((X + Z) ∈ RC). auto.
  assert ((Y + Z) ∈ RC). auto.
  destruct (FAT167 H3 H4) as [?|[?|?]]; auto.
  - apply FAT188b1 in H5; auto. CordR.
  - apply FAT188c1 in H5; auto; CordR.
Qed.

Theorem FAT188b2 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X = Y -> X + Z = Y + Z.
Proof.
  intros; rewrite H2; auto.
Qed.

Theorem FAT188c2 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X < Y -> X + Z < Y + Z.
Proof.
  intros; eapply FAT188a2; eauto.
Qed.

Fact NtoR4 : ∀ x y, x ∈ Nat -> y ∈ Nat -> (x < y)%Nat
  -> (NtoR y) - (NtoR x) = NtoR (y - x)%Nat.
Proof.
  intros. apply FAT188b1 with (NtoR x); auto. rewrite FAT175; auto.
  rewrite MincEx; auto. rewrite NtoR2; auto. rewrite FAT6; auto.
  rewrite MinNEx; auto.
Qed.

Theorem FAT189 : ∀ {X Y Z U}, X ∈ RC -> Y ∈ RC -> Z ∈ RC -> U ∈ RC
  -> X > Y -> Z > U -> X + Z > Y + U.
Proof.
  intros. apply (FAT188a2 _ _ Z) in H3; auto.
  apply @ FAT171 with (Y + Z); auto. rewrite FAT175; auto.
  rewrite @ FAT175 with Y Z; auto. apply FAT188c2; auto.
Qed.

Theorem FAT190 : ∀ X Y Z U, X ∈ RC -> Y ∈ RC -> Z ∈ RC -> U ∈ RC
  -> (X ≥ Y /\ Z > U) \/ (X > Y /\ Z ≥ U) -> X + Z > Y + U.
Proof.
  intros. destruct H3 as [[[?|?]?]|[?[?|?]]].
  - apply FAT189; auto.
  - subst. rewrite FAT175; auto. rewrite @FAT175 with X U; auto.
    apply FAT188c2; auto.
  - apply FAT189; auto.
  - subst; apply FAT188c2; auto.
Qed.

Theorem FAT191a : ∀ {X Y Z U}, X ∈ RC -> Y ∈ RC -> Z ∈ RC -> U ∈ RC
  -> X ≥ Y -> Z ≥ U -> (X + Z) ≥ (Y + U).
Proof.
  intros. destruct H3 as [?|?]; destruct H4 as [?|?].
  - left. apply FAT189; auto.
  - subst. left. apply FAT188c2; auto.
  - subst. left. rewrite FAT175; auto.
    rewrite @ FAT175 with X U; auto. apply FAT188c2; auto.
  - right; subst; auto.
Qed.

Theorem FAT191b : ∀ {X Y Z U}, X ∈ RC -> Y ∈ RC -> Z ∈ RC -> U ∈ RC
  -> X ≤ Y -> Z ≤ U -> (X + Z) ≤ (Y + U).
Proof.
  intros. eapply FAT191a; auto.
Qed.

(* SECTION IV Multiplication *)

Definition mulR a := \{\ λ b c, b ∈ RC
  /\ (a ∈ PRC -> b ∈ PRC -> c = [mulc a¹ b¹,zero])
  /\ (a ∈ NRC -> b ∈ NRC -> c = [mulc a² b²,zero])
  /\ (a ∈ PRC -> b ∈ NRC -> c = [zero,mulc a¹ b²])
  /\ (a ∈ NRC -> b ∈ PRC -> c = [zero,mulc a² b¹])
  /\ (a = zero -> c = zero) /\ (b = zero -> c = zero) \}\.

Notation " x · y " := ((mulR x) [y])(at level 40) : RC_scope.

Fact murf : ∀ a, a ∈ RC -> Function (mulR a).
Proof.
  split; intros. apply poisre.
  apply AxiomII' in H1; apply AxiomII' in H0; deand.
  destruct (inRC H) as [?|[?|?]];
  destruct (inRC H2) as [?|[?|?]]; ReF.
Qed.

Global Hint Resolve murf : core.

Fact MulRpa : ∀ {a b}, a ∈ PRC -> b ∈ PRC -> (mulR a)[b] = [mulc a¹ b¹,zero].
Proof.
  ltacr1.
Qed.

Fact MulRpb : ∀ {a b}, a ∈ NRC -> b ∈ NRC -> (mulR a)[b] = [mulc a² b²,zero].
Proof.
  ltacr1.
Qed.

Fact MulRpc : ∀ {a b}, a ∈ PRC -> b ∈ NRC -> (mulR a)[b] = [zero,mulc a¹ b²].
Proof.
  ltacr1.
Qed.

Fact MulRpd : ∀ {a b}, a ∈ NRC -> b ∈ PRC -> (mulR a)[b] = [zero,mulc a² b¹].
Proof.
  ltacr1.
Qed.

Fact MulRpA : ∀ {a b}, a ∈ CC -> b ∈ CC
  -> (mulR ([a,zero]))[[b,zero]] = [mulc a b,zero].
Proof.
  intros. rewrite @ MulRpa; GE; GE.
Qed.

Fact MulRpB : ∀ {a b}, a ∈ CC -> b ∈ CC
  -> (mulR ([zero,a]))[[zero,b]] = [mulc a b,zero].
Proof.
  intros. rewrite @ MulRpb; GE; GE.
Qed.

Fact MulRpC : ∀ {a b}, a ∈ CC -> b ∈ CC
  -> (mulR ([a,zero]))[[zero,b]] = [zero,mulc a b].
Proof.
  intros. rewrite @ MulRpc; GE; GE.
Qed.

Fact MulRpD : ∀ {a b}, a ∈ CC -> b ∈ CC
  -> (mulR ([zero,a]))[[b,zero]] = [zero,mulc a b].
Proof.
  intros. rewrite @ MulRpd; GE; GE.
Qed.

Fact MulRpe : ∀ {b}, b ∈ RC -> (mulR zero)[b] = zero.
Proof.
  ltacr1.
Qed.

Fact MulRpf : ∀ {a}, a ∈ RC -> (mulR a)[zero] = zero.
Proof.
  ltacr1.
Qed.

Ltac find_eq1a :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ PRC
    |- _ => rewrite (MulRpa H1 H2) in *
  end.

Ltac find_eq1b :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ NRC
    |- _ => rewrite (MulRpb H1 H2) in *
  end.

Ltac find_eq1c :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC
    |- _ => rewrite (MulRpc H1 H2) in *
  end.

Ltac find_eq1d :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC
    |- _ => rewrite (MulRpd H1 H2) in *
  end.

Ltac find_eq1A :=
  match goal with
    |- _ => rewrite MulRpA in *; auto
  end.

Ltac find_eq1B :=
  match goal with
    |- _ => rewrite MulRpB in *; auto
  end.

Ltac find_eq1C :=
  match goal with
    |- _ => rewrite MulRpC in *; auto
  end.

Ltac find_eq1D :=
  match goal with
    |- _ => rewrite MulRpD in *; auto
  end.

Ltac find_eq1e :=
  match goal with
    |- _ => rewrite MulRpe in *; auto
  end.

Ltac find_eq1f :=
  match goal with
    |- _ => rewrite MulRpf in *; auto
  end.

Ltac reqa1 := try find_eq1a; try find_eq1b; try find_eq1c;
  try find_eq1d; try find_eq1e; try find_eq1f; try find_eq1A;
  try find_eq1B; try find_eq1C; try find_eq1D.

Fact mulRC : ∀ a b, a ∈ RC -> b ∈ RC -> a · b ∈ RC.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; 
  destruct (inRC H0) as [?|[?|?]]; subst; reqa1; auto.
Qed.

Global Hint Resolve mulRC : core.

Fact mulRC1 : ∀ a b, a ∈ PRC -> b ∈ PRC ->  a · b ∈ PRC.
Proof.
  intros. reqa1; auto.
Qed.

Fact mulRC2 : ∀ a b, a ∈ NRC -> b ∈ NRC ->  a · b ∈ PRC.
Proof.
  intros. reqa1; auto.
Qed.

Fact mulRC3 : ∀ a b, a ∈ PRC -> b ∈ NRC ->  a · b ∈ NRC.
Proof.
  intros. reqa1; auto.
Qed.

Fact mulRC4 : ∀ a b, a ∈ NRC -> b ∈ PRC ->  a · b ∈ NRC.
Proof.
  intros. reqa1; auto.
Qed.

Global Hint Resolve mulRC1 mulRC2 mulRC3 mulRC4 : core.

Theorem FAT192 : ∀ a b, a ∈ RC -> b ∈ RC -> a · b = zero
  -> a = zero \/ b = zero.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; 
    destruct (inRC H0) as [?|[?|?]]; auto; reqa1; npZ.
Qed.

(* Ltac reqa1; reqb1. := reqa1; reqb1. *)

Theorem FAT193 : ∀ a b, a ∈ RC -> b ∈ RC -> |a · b| = |a| · |b|.
Proof.
  intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]]; subst;
  repeat (reqa1; reqb1); auto; rewrite MulRpa; GE; auto.
Qed.

Theorem FAT194 : ∀ a b, a ∈ RC -> b ∈ RC -> a · b = b · a.
Proof.
  intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]]; 
  subst; repeat reqa1; try rewrite FAT142; auto.
Qed.

Theorem FAT195a : ∀ X, X ∈ RC -> X · 1 = X.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - pose proof Onep. reqa1. rewrite Pr; auto. GE.
    assert ((X)¹ · rtoC (Ntor One) ∈ CC)%CC. auto.
    apply MKT55; rxo. repeat split; auto. apply FAT151; auto.
  - subst. reqa1.
  - pose proof Onep. reqa1. rewrite Nr; auto. GE.
    assert ((X)² · rtoC (Ntor One) ∈ CC)%CC. auto.
    apply MKT55; rxo. repeat split; auto. apply FAT151; auto.
Qed.

Fact Onen : - (1) ∈ NRC.
Proof.
  pose proof Onep. sl.
Qed.

Theorem FAT195b : ∀ X, X ∈ RC -> X · (- (1))  = - X.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - pose proof Onen. assert (- X ∈ NRC). sl. reqa1.
    rewrite Nr; auto. assert (((X)¹ · (- (1))²)%CC ∈ CC). auto.
    apply MKT55; rxo. split; auto.
    assert ((X)¹ = (- X)²). symmetry; sl.
    assert ((- (1))² = (1)¹). pose proof Onep. sl.
    rewrite H4, H5. GE. apply FAT151; auto.
  - subst. reqa1. rewrite Zmin; auto.
  - pose proof Onen. assert (- X ∈ PRC). sl. reqa1.
    rewrite Pr; auto. assert (((X)² · (- (1))²)%CC ∈ CC). auto.
    apply MKT55; rxo. split; auto.
    assert ((- X)¹ = (X)²). sl.
    assert ((- (1))² = (1)¹). pose proof Onep. sl.
    rewrite H4, H5. GE. apply FAT151; auto.
Qed.

Theorem FAT196a : ∀ X Y, X ∈ PRC -> Y ∈ NRC -> X · Y = - (|X| · |Y|).
Proof.
  intros. repeat (reqa1; reqb1). assert ([(Y) ², 0] ∈ PRC). auto.
  assert (X · [(Y) ², 0] ∈ PRC). reqa1. auto.
  rewrite Pmin; auto. reqa1. repeat GE.
Qed.

Theorem FAT196b : ∀ X Y, X ∈ PRC -> Y ∈ PRC -> X · Y = |X| · |Y|.
Proof.
  intros. repeat (reqa1; reqb1); auto.
Qed.

Theorem FAT196c : ∀ X Y, X ∈ NRC -> Y ∈ NRC -> X · Y = |X| · |Y|.
Proof.
  intros. repeat (reqa1; reqb1); auto.
Qed.

Fact abspn : ∀ X, X ∈ RC -> |X| = |(-X)|.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - rewrite Pmin; auto. reqb1; auto.
  - rewrite H0. rewrite Zmin; auto.
  - rewrite Nmin; auto. reqb1; auto.
Qed.

Theorem FAT197a : ∀ X Y, X ∈ RC -> Y ∈ RC -> (-X) · Y = - (X · Y).
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; 
  destruct (inRC H0) as [?|[?|?]].
  - assert (-X ∈ NRC). sl. assert ((X · Y) ∈ PRC). reqa1; auto.
    rewrite Pmin with (X · Y); auto. reqa1. 
    rewrite Pmin; auto. repeat GE.
  - subst. repeat reqa1. rewrite Zmin; auto.
  - assert (-X ∈ NRC). sl. assert ((X · Y) ∈ NRC). reqa1; auto.
    rewrite Nmin with (X · Y); auto. reqa1. 
    rewrite Pmin; auto. repeat GE.
  - subst. repeat reqa1. rewrite Zmin; auto. reqa1.
  - subst. reqa1. rewrite Zmin; auto.
  - subst. repeat reqa1. rewrite Zmin; auto. reqa1.
  - assert (-X ∈ PRC). sl. assert ((X · Y) ∈ NRC). reqa1; auto.
    rewrite Nmin with (X · Y); auto. reqa1. 
    rewrite Nmin; auto. repeat GE.
  - subst. repeat reqa1. rewrite Zmin; auto.
  - assert (-X ∈ PRC). sl. assert ((X · Y) ∈ PRC). reqa1; auto.
    rewrite Pmin with (X · Y); auto. reqa1. 
    rewrite Nmin; auto. repeat GE.
Qed.

Theorem FAT197b : ∀ X Y, X ∈ RC -> Y ∈ RC -> X · (-Y) = - (X · Y).
Proof.
  intros. rewrite FAT194; auto. rewrite FAT194 with X Y; auto.
  apply FAT197a; auto.
Qed.

Theorem FAT197c : ∀ X Y, X ∈ RC -> Y ∈ RC -> (-X) · Y = X · (-Y).
Proof.
  intros. pose proof (FAT197a X Y). MP. pose proof (FAT197b _ _ H H0).
  rewrite H2,H1. auto.
Qed.

Theorem FAT198 : ∀ X Y, X ∈ RC -> Y ∈ RC -> (-X) · (-Y) = X · Y.
Proof.
  intros. rewrite FAT197c; auto. rewrite FAT177; auto.
Qed.

Lemma Lemma_FAT199 : ∀ X Y Z, X ∈ PRC -> Y ∈ PRC -> Z ∈ PRC
  -> (X · Y) · Z = X · (Y · Z).
Proof.
  intros. repeat reqa1. repeat rewrite MulRpa; auto. repeat GE.
  apply MKT55; rxo. exists CC; auto. split; auto.
  rewrite FAT143; auto.
Qed.

Theorem FAT199 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> (X · Y) · Z = X · (Y · Z).
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; 
  destruct (inRC H0) as [?|[?|?]];
  destruct (inRC H1) as [?|[?|?]];
  try subst; try repeat reqa1.
  - pattern Z at 1; rewrite (Pr Z); auto.
    pattern X at 2; rewrite (Pr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Nr Z); auto.
    pattern X at 2; rewrite (Pr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Pr Z); auto.
    pattern X at 2; rewrite (Pr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Nr Z); auto.
    pattern X at 2; rewrite (Pr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Pr Z); auto.
    pattern X at 2; rewrite (Nr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Nr Z); auto.
    pattern X at 2; rewrite (Nr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Pr Z); auto.
    pattern X at 2; rewrite (Nr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
  - pattern Z at 1; rewrite (Nr Z); auto.
    pattern X at 2; rewrite (Nr X); auto.
    repeat reqa1. apply MKT55; auto. exists CC; auto.
    split; auto. rewrite FAT143; auto.
Qed.

Fact multRp1 : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X · Y · Z = Y · Z · X.
Proof.
  intros. rewrite FAT199; auto. rewrite FAT194; auto.
Qed.

Lemma Lemma_FAT200a : ∀ a b c, a ∈ PRC -> b ∈ PRC -> c ∈ PRC
  -> a · (b + c) = (a · b) + (a · c).
Proof.
  intros. assert (a · b ∈ PRC). auto. assert (a · c ∈ PRC). auto.
  repeat req1. pattern a at 1;  rewrite (Pr a); auto.
  repeat reqa1. repeat GE.
  apply MKT55; auto. exists CC; auto. split; auto.
  rewrite FAT144a; auto.
Qed.

Lemma Lemma_FAT200b : ∀ a b c, a ∈ PRC -> b ∈ PRC -> c ∈ PRC
  -> b > c -> a · b > a · c.
Proof.
  intros. apply si2' in H2. Order. red; left. repeat split; auto.
  repeat reqa1. repeat GE. rewrite FAT142; auto.
  rewrite @ FAT142 with ((a)¹) ((b)¹); auto.
  apply FAT145c; auto.
Qed.

Lemma FAT200_aux : ∀ a b c, a ∈ PRC -> b ∈ PRC -> c ∈ PRC
  -> (b - c) ∈ PRC -> a · (b - c) = (a · b) - (a · c).
Proof.
  intros. assert (a · b > a · c ).
  { apply Lemma_FAT200b; auto. apply FAT182a1; auto. }
  New H3. apply FAT182a2 in H3; auto.
  apply (Lemma_FAT185d _ _ (a · c)); auto.
  rewrite @ FAT175 with (a · b - a · c) (a · c); auto.
  rewrite Lemma_FAT185c; auto. rewrite <- Lemma_FAT200a; auto.
  rewrite @ FAT175 with (b - c) c; auto.
  rewrite Lemma_FAT185c; auto. apply FAT182a1; auto.
Qed.

Theorem FAT200 : ∀ a b c, a ∈ PRC -> b ∈ PRC -> c ∈ PRC
  -> a · (b - c) = (a · b) - (a · c).
Proof.
  intros. assert ((b - c) ∈ RC). auto.
  destruct (inRC H2) as [?|[?|?]].
  - apply FAT200_aux; auto.
  - rewrite H3. apply FAT182b1 in H3; auto. 
    rewrite H3. rewrite FAT179a; auto. reqa1.
  - assert (c - b ∈ PRC). { rewrite <- FAT181; auto. sl. }
    rewrite <- FAT181; auto. rewrite FAT197b; auto.
    rewrite FAT200_aux; auto. rewrite FAT181; auto.
Qed.

Lemma FAT201_aux : ∀ X Y Z, X ∈ PRC -> Y ∈ RC -> Z ∈ RC
  -> X · (Y + Z) = X · Y + X · Z.
Proof.
  intros. pose proof (FAT184 Y H0). pose proof (FAT184 Z H1).
  destruct H2 as [y1[y2[?[]]]]. destruct H3 as [z1[z2[?[]]]].
  pattern Y at 1; rewrite H5. pattern Z at 1; rewrite H7.
  rewrite FAT185'; auto. rewrite FAT200; auto.
  repeat rewrite Lemma_FAT200a; auto. rewrite <- FAT185'; auto.
  repeat rewrite <- FAT200; auto. rewrite H5,H7; auto.
Qed.

Theorem FAT201a : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X · (Y + Z) = X · Y + X · Z.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - apply FAT201_aux; auto.
  - subst. repeat reqa1. req1; auto.
  - rewrite <- FAT177 with (X · (Y + Z)); auto.
    rewrite <- FAT197a; auto. assert ((-X) ∈ PRC). sl.
    rewrite FAT201_aux; auto. rewrite FAT180; auto.
    repeat rewrite FAT197a; auto. repeat rewrite FAT177; auto.
Qed.

Theorem FAT201b : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> (Y + Z) · X = Y · X + Z · X.
Proof.
  intros. rewrite FAT194; auto. rewrite FAT194 with Y X; auto.
  rewrite FAT194 with Z X; auto. apply FAT201a; auto.
Qed.

Theorem FAT202a : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X · (Y - Z) = (X · Y) - (X · Z).
Proof.
  intros. rewrite FAT201a; auto. rewrite FAT197b; auto.
Qed.

Theorem FAT202b : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> (Y - Z) · X = (Y · X) - (Z · X).
Proof.
  intros. rewrite FAT201b; auto. rewrite FAT197a; auto.
Qed.

Theorem FAT203a : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X > Y -> Z > 0 -> X · Z > Y · Z.
Proof.
  intros. apply FAT182a2 in H2; auto. 
  assert ((X - Y) · Z > 0). auto. rewrite FAT202b in H4; auto.
  apply FAT182a1; auto.
Qed.

Theorem FAT203b : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X > Y -> Z = 0 -> X · Z = Y · Z.
Proof.
  intros. subst. repeat reqa1; auto.
Qed.

Theorem FAT203c : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X > Y -> Z < 0 -> X · Z < Y · Z.
Proof.
  intros. apply FAT182a2 in H2; auto. 
  assert ((X - Y) · Z < 0). auto. rewrite FAT202b in H4; auto.
  apply FAT182c1; auto.
Qed.

Fact FAT203d : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> X < Y -> Z > 0 -> X · Z < Y · Z.
Proof.
  intros. apply FAT203a; auto.
Qed.

Fact FAT203e : ∀ X Y Z, X ∈ RC -> Y ∈ RC -> Z ∈ RC
  -> Z > 0 -> X · Z > Y · Z -> X > Y.
Proof.
  intros. destruct (FAT167 H H0) as [?|[?|?]]; auto.
  - assert (X · Z = Y · Z). rewrite H4; auto. CordR.
  - apply (FAT203d _ _ Z) in H4; auto. CordR.
Qed.

Fact mulr2: ∀n1 n2, n1 ∈ Nat -> n2 ∈ Nat
  -> Ntor (n1 · n2)%Nat = (Ntor n1 · Ntor n2)%rC.
Proof.
  intros. apply AxiomI. split; intros.
  - appA2H H1. destruct H2. appA2G. split; auto.
    exists [n1 , One], [n2 , One].
    repeat split.
    + appA2G. split; auto. t37.
    + appA2G. split; auto. t37.
    + unfold mulF. repeat Ge. repeat rewrite FAT28a; auto.
  - appA2H H1. appA2G. destruct H2 as [?[f1[f2[?[]]]]].
    split; auto. appA2H H3. appA2H H4. destruct H6,H7.
    apply @ FAT39 with (f1 · f2)%FC; auto.
    assert (f1 · f2 ~ [n1, One] · [n2, One])%FC.
    apply FAT68; auto.
    apply @ FAT39 with ([n1, One] · [n2, One])%FC; auto.
    apply FAT112b; auto.
Qed.

Fact NtoRM : ∀ x y, x ∈ Nat -> y ∈ Nat
  -> (NtoR x) · (NtoR y) = NtoR (x · y)%Nat.
Proof.
  intros. pose proof (NtoRP H). pose proof (NtoRP H0).
  reqa1. unfold NtoR. repeat GE. apply MKT55; rxo.
  exists CC; auto. split; auto. rewrite <- FAT155c; auto.
  apply FAT154a2; auto. rewrite mulr2; auto.
Qed.

Definition divR a := \{\ λ b c, b ∈ RC /\ b <> zero
  /\ (b ∈ PRC -> c = (mulR a)[[(recC b¹),zero]])
  /\ (b ∈ NRC -> c = (mulR a)[[zero,(recC b²)]]) \}\.

Notation " x / y " := ((divR x) [y]) : RC_scope.

Fact divf : ∀ a, a ∈ RC -> Function (divR a).
Proof.
  split; intros. apply poisre.
  apply AxiomII' in H0; apply AxiomII' in H1; deand.
  destruct (inRC H) as [?|[?|?]];
  destruct (inRC H2) as [?|[?|?]]; ReF; tauto.
Qed.

Global Hint Resolve divf : core.

Fact DivRp1 : ∀ {a b}, a ∈ RC -> b ∈ PRC
  -> (divR a)[b] = (mulR a)[[(recC b¹),zero]].
Proof. 
  intros. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo; exists RC; eauto. apply mulRC; auto. intro. subst; npz. 
Qed.

Fact DivRp2 : ∀ {a b}, a ∈ RC -> b ∈ NRC
  -> (divR a)[b] = (mulR a)[[zero,(recC b²)]].
Proof.
  intros. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo; exists RC; eauto. apply mulRC; auto. intro. subst; npz. 
Qed.

Ltac find_eq1a1 :=
  match goal with
    H1: ?a ∈ RC,
    H2: ?b ∈ PRC
    |- _ => rewrite (DivRp1 H1 H2) in *
  end.

Ltac find_eq1b2 :=
  match goal with
    H1: ?a ∈ RC,
    H2: ?b ∈ NRC
    |- _ => rewrite (DivRp2 H1 H2) in *
  end.

Ltac reqa2' := try find_eq1a1; try find_eq1b2.

Fact DivRpa : ∀ {a b}, a ∈ PRC -> b ∈ PRC
  -> (divR a)[b] = [(a¹ · (recC b¹))%CC,zero].
Proof.
  intros. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo. exists CC. auto. intro. subst; npz.
  rewrite (Pr a); auto. rewrite (Pr b); auto.
  repeat GE. reqa1.
Qed.

Fact DivRpb : ∀ {a b}, a ∈ PRC -> b ∈ NRC
  -> (divR a)[b] = [zero, (a¹ · (recC b²))%CC].
Proof.
  intros. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo. exists CC. auto. intro. subst; npz.
  rewrite (Pr a); auto. rewrite (Nr b); auto.
  repeat GE. reqa1.
Qed.

Fact DivRpc : ∀ {a b}, a = 0 -> b ∈ PRC -> (divR a)[b] = 0.
Proof.
  intros. subst. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo. intro. subst; npz. reqa1.
Qed.

Fact DivRpd : ∀ {a b}, a = 0 -> b ∈ NRC -> (divR a)[b] = 0.
Proof.
  intros. subst. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo. intro. subst; npz. reqa1.
Qed.

Fact DivRpe : ∀ {a b}, a ∈ NRC -> b ∈ PRC
  -> (divR a)[b] = [zero, (a² · (recC b¹))%CC].
Proof.
  intros. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo. exists CC. auto. intro. subst; npz.
  rewrite (Nr a); auto. rewrite (Pr b); auto.
  repeat GE. reqa1.
Qed.

Fact DivRpf : ∀ {a b}, a ∈ NRC -> b ∈ NRC
  -> (divR a)[b] = [(a² · (recC b²))%CC, zero].
Proof.
  intros. apply funv. auto. apply AxiomII';
  repeat split; intros; subst; npz; auto.
  rxo. exists CC. auto. intro. subst; npz.
  rewrite (Nr a); auto. rewrite (Nr b); auto.
  repeat GE. reqa1.
Qed.

Ltac find_eq1a' :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ PRC
    |- _ => rewrite (DivRpa H1 H2) in *
  end.

Ltac find_eq1b' :=
  match goal with
    H1: ?a ∈ PRC,
    H2: ?b ∈ NRC
    |- _ => rewrite (DivRpb H1 H2) in *
  end.

Ltac find_eq1c' :=
  match goal with
    H1: ?a = 0,
    H2: ?b ∈ PRC
    |- _ => rewrite (DivRpc H1 H2) in *
  end.

Ltac find_eq1d' :=
  match goal with
    H1: ?a = 0,
    H2: ?b ∈ NRC
    |- _ => rewrite (DivRpd H1 H2) in *
  end.

Ltac find_eq1e' :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ PRC
    |- _ => rewrite (DivRpe H1 H2) in *
  end.

Ltac find_eq1f' :=
  match goal with
    H1: ?a ∈ NRC,
    H2: ?b ∈ NRC
    |- _ => rewrite (DivRpf H1 H2) in *
  end.

Ltac reqa2 := try find_eq1a'; try find_eq1b'; try find_eq1c';
  try find_eq1d'; try find_eq1e'; try find_eq1f'.

Fact divRc1 : ∀ a b, a ∈ RC -> b ∈ PRC -> a / b ∈ RC.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; reqa2; auto 6.
Qed.

Fact divRc2 : ∀ a b, a ∈ RC -> b ∈ NRC -> a / b ∈ RC.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; reqa2; auto 6.
Qed.

Global Hint Resolve divRc1 divRc2 : core.

Fact divRc3 : ∀ a b, a ∈ RC -> b ∈ RC -> b <> 0 -> a / b ∈ RC.
Proof.
  intros. destruct (inRC H0) as [?|[?|?]]; auto. contradiction.
Qed.

Global Hint Resolve divRc3 : core.

Theorem FAT204 : ∀ X Y, X ∈ RC -> Y ∈ RC -> Y <> 0
  -> ∃ Z, Z ∈ RC /\ Y · Z = X.
Proof.
  intros. exists (X / Y). split; auto.
  destruct (inRC H0) as [?|[?|?]]; try contradiction.
  - destruct (inRC H) as [?|[?|?]].
    + reqa2. rewrite (Pr X); auto. rewrite (Pr Y); auto.
      repeat GE. repeat reqa1; auto. apply MKT55; rxo.
      exists CC; auto. split; auto. 
      rewrite @ FAT142 with ((X)¹) (recC (Y)¹); auto.
      rewrite <- FAT143; auto.
      rewrite Lemma_FAT152; auto. rewrite mulc1; auto.
    + reqa2. subst. reqa1.
    + reqa2. rewrite (Nr X); auto. rewrite (Pr Y); auto.
      repeat GE. repeat reqa1; auto. apply MKT55; rxo.
      exists CC; auto. split; auto. 
      rewrite @ FAT142 with ((X)²) (recC (Y)¹); auto.
      rewrite <- FAT143; auto. 
      rewrite Lemma_FAT152; auto. rewrite mulc1; auto.
  - destruct (inRC H) as [?|[?|?]].
    + reqa2. rewrite (Pr X); auto. rewrite (Nr Y); auto.
      repeat GE. repeat reqa1; auto. apply MKT55; rxo.
      exists CC; auto. split; auto. 
      rewrite @ FAT142 with ((X)¹) (recC (Y)²); auto.
      rewrite <- FAT143; auto. 
      rewrite Lemma_FAT152; auto. rewrite mulc1; auto.
    + reqa2. subst. reqa1.
    + reqa2. rewrite (Nr X); auto. rewrite (Nr Y); auto.
      repeat GE. repeat reqa1; auto. apply MKT55; rxo.
      exists CC; auto. split; auto. 
      rewrite @ FAT142 with ((X)²) (recC (Y)²); auto.
      rewrite <- FAT143; auto. 
      rewrite Lemma_FAT152; auto. rewrite mulc1; auto.
Qed.

Fact divRp1 : ∀ x , x ∈ RC -> x <> 0 -> 0 / x = 0.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - rewrite DivRp1; auto. reqa1.
  - contradiction.
  - rewrite DivRp2; auto. reqa1.
Qed.

Fact divRp2 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> y <> 0
  -> (x / y) · z = (x · z) / y.
Proof.
  intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]]; 
  destruct (inRC H1) as [?|[?|?]]; try contradiction.
  - reqa2. reqa1. rewrite DivRpa; auto.
    rewrite MulRpa; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - subst. repeat reqa1. symmetry; apply divRp1; auto.
  - reqa2. reqa1. rewrite DivRpe; auto.
    rewrite MulRpc; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - reqa2. reqa1. rewrite DivRpb; auto.
    rewrite MulRpd; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - subst. repeat reqa1. symmetry; apply divRp1; auto.
  - reqa2. reqa1. rewrite DivRpf; auto.
    rewrite MulRpb; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - subst. repeat reqa1. rewrite divRp1; auto. reqa1.
  - subst. repeat reqa1. symmetry; apply divRp1; auto.
  - subst. repeat reqa1. rewrite divRp1; auto. reqa1.
  - subst. repeat reqa1. rewrite divRp1; auto. reqa1.
  - subst. repeat reqa1. rewrite divRp1; auto.
  - subst. repeat reqa1. rewrite divRp1; auto. reqa1.
  - reqa2. reqa1. rewrite DivRpe; auto.
    rewrite MulRpd; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - subst. repeat reqa1. rewrite divRp1; auto.
  - reqa2. reqa1. rewrite DivRpa; auto.
    rewrite MulRpb; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - reqa2. reqa1. rewrite DivRpf; auto.
    rewrite MulRpa; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
  - subst. repeat reqa1. rewrite divRp1; auto.
  - reqa2. reqa1. rewrite DivRpb; auto.
    rewrite MulRpc; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto.
    rewrite mulc2; auto.
Qed.

Fact divRp3 : ∀ x y, x ∈ RC -> y ∈ RC -> y <> 0
  -> (-x) / y = - (x / y).
Proof.
  intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]]; try contradiction.
  - assert (-x ∈ NRC). sl. reqa2. repeat rewrite Pmin; auto.
    repeat GE.
  - assert (-x ∈ NRC). sl. reqa2. rewrite Pmin; auto.
    rewrite Nmin; auto. repeat GE.
  - subst. rewrite divRp1; auto. rewrite Zmin; auto.
    rewrite divRp1; auto.
  - subst. rewrite divRp1; auto. rewrite Zmin; auto.
    rewrite divRp1; auto.
  - assert (-x ∈ PRC). sl. reqa2. rewrite Nmin; auto.
    rewrite Nmin; auto. repeat GE.
  - assert (-x ∈ PRC). sl. reqa2. rewrite Nmin; auto.
    rewrite Pmin; auto. repeat GE.
Qed.

Fact divRp4 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> y <> 0
  -> (x / y) + (z / y) = (x + z) / y.
Proof.
  intros. destruct (inRC H) as [?|[?|?]];
  destruct (inRC H0) as [?|[?|?]]; 
  destruct (inRC H1) as [?|[?|?]]; try contradiction.
  - req1. repeat reqa2. rewrite DivRpa; auto.
    rewrite AddRpc; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto. rewrite FAT144b; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpb; auto.
  - destruct (@ FAT167 x (-z)) as [?|[?|?]]; auto.
    + subst. rewrite divRp3; auto. repeat rewrite FAT179b; auto.
      rewrite divRp1; auto.
    + apply si2' in H6. assert (-z ∈ PRC). sl. Order.
      * rewrite Nmin in H9; auto. GE. req2.
        reqa2. rewrite DivRpa; auto.
        assert ([((x)¹ · recC (y)¹)%CC, 0]¹ >
        [0, ((z)² · recC (y)¹)%CC]²)%CC.
        { repeat GE. apply FAT145a; auto. }
        rewrite AddRpg; auto. repeat GE. apply MKT55; auto.
        exists CC; auto. split; auto. rewrite FAT144d; auto.
      * rewrite H6 in H7. npz.
    + assert (-z ∈ PRC). sl. Order.
      rewrite Nmin in H9; auto. GE. req2.
      reqa2. rewrite DivRpe; auto.
      assert ([((x)¹ · recC (y)¹)%CC, 0]¹ <
      [0, ((z)² · recC (y)¹)%CC]²)%CC.
      { repeat GE. apply FAT145c; auto. }
      rewrite AddRpi; auto. repeat GE. apply MKT55; auto.
      exists CC; auto. split; auto. rewrite FAT144d; auto.
  - req1. repeat reqa2. rewrite DivRpb; auto.
    rewrite AddRpd; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto. rewrite FAT144b; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpb; auto.
  - destruct (@ FAT167 x (-z)) as [?|[?|?]]; auto.
    + subst. rewrite divRp3; auto. repeat rewrite FAT179b; auto.
      rewrite divRp1; auto.
    + apply si2' in H6. assert (-z ∈ PRC). sl. Order.
      * rewrite Nmin in H9; auto. GE. req2.
        reqa2. rewrite DivRpb; auto.
        assert ([0, ((x)¹ · recC (y)²)%CC]² >
        [((z)² · recC (y)²)%CC, 0]¹)%CC.
        { repeat GE. apply FAT145a; auto. }
        rewrite AddRph; auto. repeat GE. apply MKT55; auto.
        exists CC; auto. split; auto. rewrite FAT144d; auto.
      * rewrite H6 in H7. npz.
    + assert (-z ∈ PRC). sl. Order.
      rewrite Nmin in H9; auto. GE. req2.
      reqa2. rewrite DivRpf; auto.
      assert ([0, ((x)¹ · recC (y)²)%CC]² <
      [((z)² · recC (y)²)%CC, 0]¹)%CC.
      { repeat GE. apply FAT145c; auto. }
      rewrite AddRpj; auto. repeat GE. apply MKT55; auto.
      exists CC; auto. split; auto. rewrite FAT144d; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpa; auto.
  - subst. req1. repeat rewrite divRp1; auto. req1; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpa; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpa; auto.
  - subst. req1. repeat rewrite divRp1; auto. req1; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpa; auto.
  - destruct (@ FAT167 z (-x)) as [?|[?|?]]; auto.
    + subst. rewrite divRp3; auto. repeat rewrite FAT179a; auto.
      rewrite divRp1; auto.
    + apply si2' in H6. assert (-x ∈ PRC). sl. Order.
      * rewrite Nmin in H9; auto. GE. req2.
        reqa2. rewrite DivRpa; auto.
        assert ([((z)¹ · recC (y)¹)%CC, 0]¹ >
        [0, ((x)² · recC (y)¹)%CC]²)%CC.
        { repeat GE. apply FAT145a; auto. }
        rewrite AddRpj; auto. repeat GE. apply MKT55; auto.
        exists CC; auto. split; auto. rewrite FAT144d; auto.
      * rewrite H6 in H7. npz.
    + assert (-x ∈ PRC). sl. Order.
      rewrite Nmin in H9; auto. GE. req2.
      reqa2. rewrite DivRpe; auto.
      assert ([((z)¹ · recC (y)¹)%CC, 0]¹ <
      [0, ((x)² · recC (y)¹)%CC]²)%CC.
      { repeat GE. apply FAT145c; auto. }
      rewrite AddRph; auto. repeat GE. apply MKT55; auto.
      exists CC; auto. split; auto. rewrite FAT144d; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpb; auto.
  - req1. repeat reqa2. rewrite DivRpe; auto.
    rewrite AddRpd; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto. rewrite FAT144b; auto.
  - destruct (@ FAT167 z (-x)) as [?|[?|?]]; auto.
    + subst. rewrite divRp3; auto. repeat rewrite FAT179a; auto.
      rewrite divRp1; auto.
    + apply si2' in H6. assert (-x ∈ PRC). sl. Order.
      * rewrite Nmin in H9; auto. GE. req2.
        reqa2. rewrite DivRpb; auto.
        assert ([((x)² · recC (y)²)%CC, 0]¹ <
        [0, ((z)¹ · recC (y)²)%CC]²)%CC.
        { repeat GE. apply FAT145a; auto. }
        rewrite AddRpi; auto. repeat GE. apply MKT55; auto.
        exists CC; auto. split; auto. rewrite FAT144d; auto.
      * rewrite H6 in H7. npz.
    + assert (-x ∈ PRC). sl. Order.
      rewrite Nmin in H9; auto. GE. req2.
      reqa2. rewrite DivRpf; auto.
      assert ([((x)² · recC (y)²)%CC, 0]¹ >
      [0, ((z)¹ · recC (y)²)%CC]²)%CC.
      { repeat GE. apply FAT145a; auto. }
      rewrite AddRpg; auto. repeat GE. apply MKT55; auto.
      exists CC; auto. split; auto. rewrite FAT144d; auto.
  - subst; rewrite divRp1; auto; repeat req1. rewrite AddRpb; auto.
  - req1. repeat reqa2. rewrite DivRpf; auto.
    rewrite AddRpc; auto. repeat GE. apply MKT55; auto.
    exists CC; auto. split; auto. rewrite FAT144b; auto.
Qed.

Fact divRp5 : ∀ x y z, x ∈ RC -> y ∈ RC -> z ∈ RC -> y <> 0
  -> (x / y) - (z / y) = (x - z) / y.
Proof.
  intros. rewrite <- divRp3; auto. apply divRp4; auto.
Qed.

Fact divRp6 : ∀ x, x ∈ RC -> x <> 0 -> x / x = 1.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - rewrite DivRpa; auto. rewrite Lemma_FAT152; auto.
  - contradiction.
  - New H1. reqa2. rewrite Lemma_FAT152; auto.
Qed.

Fact divRp7 : ∀ x y, x ∈ RC -> y ∈ RC -> y <> 0 -> (x / y) · y = x.
Proof.
  intros. rewrite divRp2; auto. rewrite FAT194; auto.
  rewrite <- divRp2; auto. rewrite divRp6; auto.
  rewrite FAT194; auto. rewrite FAT195a; auto.
Qed.

Fact divRp8 : ∀ x y, x ∈ RC -> y ∈ RC -> y <> 0 -> x / y = 0
  -> x = 0.
Proof.
  intros. assert ((x / y) · y = 0 · y). rewrite H2; auto.
  rewrite MulRpe in H3; auto. rewrite divRp7 in H3; auto.
Qed.

Definition Sqrt_R := \{\ λ a b, a ∈ RC /\ ~ a ∈ NRC
  /\ (a ∈ PRC -> b = [(√ (a¹))%CC, 0]) /\ (a = 0 -> b= 0) \}\.

Notation " √ c " := (Sqrt_R [c])(at level 0): RC_scope.

Fact sqrtf : Function Sqrt_R.
Proof. 
  split; intros. apply poisre.
  apply AxiomII' in H; apply AxiomII' in H0; deand.
  destruct (inRC H1) as [?|[?|?]]; ReF. contradiction.
Qed.

Global Hint Resolve sqrtf : core.

Fact SqrtRpa : ∀ {a}, a ∈ PRC -> Sqrt_R [a] = [(√ (a¹))%CC, 0].
Proof.
  ltacr1. intro. npz.
Qed.

Fact SqrtRpb : ∀ {a}, a = 0 -> Sqrt_R [a] = 0.
Proof.
  ltacr1. intro; npz.
Qed.

Fact Sqrt0 : √ 0 = 0.
Proof.
  apply SqrtRpb. auto.
Qed.

Ltac find_eq1a'' :=
  match goal with
    H: ?a ∈ PRC
    |- _ => rewrite (SqrtRpa H) in *
  end.

Ltac find_eq1b'' :=
  match goal with
    H: ?a = 0
    |- _ => rewrite (SqrtRpb H) in *
  end.

Ltac reqa3 := try find_eq1a''; try find_eq1b''.

Fact SqrtPRC : ∀ x , x ∈ PRC -> √ x ∈ RC.
Proof.
  intros. reqa3; auto.
Qed.

Fact Sqrt0RC : ∀ x , x = 0 -> √ x ∈ RC.
Proof.
  intros. reqa3; auto.
Qed.

Global Hint Resolve SqrtPRC Sqrt0RC : core.

Fact SqrtRC : ∀ x , x ∈ RC -> ~ x ∈ NRC -> √ x ∈ RC.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; auto. contradiction.
Qed.

Global Hint Resolve SqrtRC : core.

Fact squRp1 : ∀ a , a ∈ RC -> a <> 0 -> a · a ∈ PRC.
Proof.
  intros. destruct (inRC H) as [?|[?|?]]; try contradiction; auto.
Qed.

Global Hint Resolve squRp1 : core.

Fact sqrt_abs : ∀ a , a ∈ RC -> √ (a · a) = | a |.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - assert (a · a ∈ PRC); auto. reqa3. rewrite MulRpa; auto. GE.
    reqb1. rewrite SqrtCp2; auto. rewrite Pr; auto.
  - rewrite H0. reqa1. reqb1. rewrite <- H0. reqa3. auto.
  - assert (a · a ∈ PRC); auto. reqa3. rewrite MulRpb; auto. GE.
    reqb1. rewrite SqrtCp2; auto.
Qed.

Fact absRp1 : ∀ a , a ∈ PRC -> √ a · √ a = a.
Proof.
  intros. reqa3. reqa1. rewrite Lemma_FAT161; auto.
  rewrite Pr; auto.
Qed.

Fact absRp2 : ∀ a , a ∈ RC -> a · a = |a| · |a|.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - reqb1. auto.
  - rewrite H0. reqb1. auto.
  - reqb1. rewrite MulRpb; auto. rewrite MulRpA; auto.
Qed.

Fact absRp3 : ∀ a , a ∈ RC -> |a| ≥ a.
Proof.
  intros. destruct (inRC H) as [?|[?|?]].
  - right. reqb1. auto.
  - right. rewrite H0. reqb1; auto.
  - left. assert (|a| ∈ PRC). apply FAT166; auto. intro.
    rewrite H1 in H0. npz. sl.
Qed.

Fact twoprc : (1 + 1) ∈ PRC.
Proof.
  auto.
Qed.

Fact twonoz : (1 + 1) <> 0.
Proof.
  intro. pose proof twoprc. rewrite H in H0; npz.
Qed.

Global Hint Resolve twonoz : core.

Fact addRp3 : ∀ x y, x ∈ PRC -> y ∈ PRC -> x + y > x.
Proof.
  intros. pattern x at 2; rewrite <- (@ AddRpa x); auto.
  rewrite FAT175; auto. apply FAT188a2; auto.
Qed.

Fact mulRp1 : ∀ x y, x ∈ PRC -> y ∈ RC -> y ≥ 1 -> x · y ≥ x.
Proof.
  intros. destruct H1.
  - left. pattern x at 2; rewrite <- (FAT195a x); auto.
    rewrite FAT194; auto. rewrite (FAT194 x 1); auto.
    apply FAT203a; auto.
  - right. rewrite <- H1. rewrite FAT195a; auto.
Qed.

Fact absRp4 : ∀ x y, x ∈ RC -> y ∈ RC -> x ≥ y -> x ≥ -y -> x ≥ |y|.
Proof.
  intros. destruct (inRC H0) as [?|[?|?]].
  - reqb1. auto.
  - rewrite H3 in *. reqb1. auto.
  - reqb1. rewrite Nmin in H2; auto.
Qed.

Fact aver2 : ∀ x y, x ∈ RC -> y ∈ RC -> x < y
  -> x < (x + y) / (1 + 1) /\ (x + y) / (1 + 1) < y.
Proof.
  intros. split; apply (FAT203e _ _ (1 + 1)); auto;
  rewrite divRp7; auto; rewrite FAT201a; auto;
  repeat rewrite FAT195a; auto; [rewrite FAT175; auto|];
  apply FAT188a2; auto.
Qed.

Fact half1 : ∀ x, x ∈ PRC -> (x / (1 + 1)) ∈ PRC.
Proof.
  intros. pose proof twoprc. reqa2. auto.
Qed.

Global Hint Resolve half1 : core.

Fact half2 : ∀ x, x ∈ PRC -> (x / (1 + 1)) < x.
Proof.
  intros. pattern x at 1; rewrite <- (@ AddRpa x); auto.
  apply aver2; auto. apply FAT169a; auto.
Qed.

(* SECTION V Dedekind's Fundamental Theorem *)

Section Dedekind.

Variable Fst Snd :Class.

Definition R_Divide := ∀ a, a ∈ RC -> a ∈ Fst \/ a ∈ Snd.

Definition ILT_FS := ∀ a b, a ∈ Fst -> b ∈ Snd -> a < b.

End Dedekind.

Definition divide x y := x ⊂ RC /\ y ⊂ RC /\ x <> Φ /\ y <> Φ
  /\ R_Divide x y /\ ILT_FS x y.

Fact Split_Pa : ∀ a b x y, x ⊂ RC -> y ⊂ RC -> R_Divide x y
  -> ILT_FS x y -> a ∈ x -> b ∈ RC -> b < a -> b ∈ x.
Proof.
  intros. destruct H1 with b; auto.
  pose proof (H2 _ _ H3 H6). CordR.
Qed.

Fact Split_Pb : ∀ a b x y, x ⊂ RC -> y ⊂ RC -> R_Divide x y
  -> ILT_FS x y -> a ∈ y -> b ∈ RC -> a < b -> b ∈ y.
Proof.
  intros. destruct H1 with b; auto.
  pose proof (H2 _ _ H6 H3). CordR.
Qed.

Fact Split_Pc : ∀ a x y, x ⊂ RC -> y ⊂ RC -> R_Divide x y
  -> ILT_FS x y -> a ∈ x -> a ∈ y -> False.
Proof.
  intros. pose proof (H2 _ _ H3 H4). CordR.
Qed.

Fact FstRC : ∀ x y, divide x y -> (∃ a, a ∈ PRC /\ a ∈ x)
  \/ ((∀ a, a ∈ NRC -> a ∈ x) /\ (∀ a, a ∈ PRC -> a ∈ y))
  \/ (∃ a, a ∈ NRC /\ a ∈ y).
Proof.
  intros. red in H. destruct H as [fstinR[sndinR[fstne[sndne[]]]]].
  unfold R_Divide in H. unfold ILT_FS in H0.
  destruct (classic (∃ a, a ∈ PRC /\ a ∈ x)); auto.
  assert (∀ a, ~ (a ∈ PRC /\ a ∈ x)).
  apply not_ex_all_not; auto. right.
  assert (∀ a, ~ (a ∈ PRC) \/ ~ (a ∈ x)).
  { intros. pose proof (H2 a). apply notandor in H3. tauto. }
  destruct (classic (∃ a, a ∈ NRC /\ a ∈ y)); auto.
  assert (∀ a, ~ (a ∈ NRC /\ a ∈ y)).
  apply not_ex_all_not; auto.
  assert (∀ a, ~ (a ∈ NRC) \/ ~ (a ∈ y)).
  { intros. pose proof (H5 a). apply notandor in H6. tauto. }
  left. clear H1 H2 H4 H5. split; intros.
  - destruct (H6 a); try tauto. assert (a ∈ RC). auto.
    apply H in H4. destruct H4; tauto.
  - destruct (H3 a); try tauto. assert (a ∈ RC). auto.
    apply H in H4. destruct H4; tauto.
Qed.

(*x中可能存在的最大有理数的集*)
Definition FstmaxrC x := \{ λ r, r ∈ rC /\ [(rtoC r), 0] ∈ x
  /\ (∀ r0, r0 ∈ rC -> [(rtoC r0), 0] ∈ x -> (r0 ≤ r)%rC) \}.

(*x中除去可能存在的最大有理数之外所有的有理数*)
Definition DedekindCC x := \{ λ r, r ∈ rC
  /\ [(rtoC r), 0] ∈ x \} ~ (FstmaxrC x).

Fact DedCC : ∀ x y, divide x y
  -> (∃ a, a ∈ PRC /\ a ∈ x) -> (DedekindCC x) ∈ CC.
Proof.
  intros x y H H1. red in H.
  destruct H as [fstinR[sndinR[fstne[sndne[]]]]].
  assert ((DedekindCC x) ⊂ rC).
  { red. intros. apply AxiomII in H2. destruct H2 as [?[]].
  apply AxiomII in H3. tauto. }
  apply AxiomII. repeat split; auto; intros.
  - apply MKT33 with rC; auto. apply EnrC.
  - destruct H1 as [a[]]. assert (a¹ ∈ CC). auto. New H4.
    apply AxiomII in H4. destruct H4 as [_[_[[? _][_ ?]]]].
    apply NEexE in H4. destruct H4 as [r]. rC r a¹.
    apply NEexE. exists r. apply AxiomII. repeat split.
    + exists rC; auto.
    + apply AxiomII. repeat split; try exists rC; auto.
      apply FAT158a in H4; auto. unfold Cut_R in H4.
      assert ([rtoC r, 0] < a).
      { red. left. repeat split; auto. GE. }
      apply Split_Pa with a y; auto.
    + apply AxiomII. split. exists rC; auto.
      intro. apply AxiomII in H8. destruct H8 as [_[_[]]].
      apply H6 in H4. destruct H4 as [r0[]]. rC r0 a¹.
      assert ([rtoC r0, 0] ∈ x).
      { apply FAT158a in H4; auto. unfold Cut_R in H4.
      assert ([rtoC r0, 0] < a).
      { red. left. repeat split; auto. GE. }
      apply Split_Pa with a y; auto. } apply H9 in H12; auto.
      destruct H12; rordF.
  - destruct H1 as [a[]]. apply NEexE in sndne.
    destruct sndne as [b]. assert (a < b).
    { unfold ILT_FS in H0. apply H0; auto. }
    assert (b ∈ PRC). { Order; auto. }
    assert (b¹ ∈ CC). auto. New H7. apply AxiomII in H7.
    destruct H7 as [_[_[[_ ?]_]]]. destruct H7 as [r0[]].
    apply FAT158b in H9; auto. unfold Cut_R in H9.
    assert ([(rtoC r0), 0] ≥ b).
    { destruct H9. left. red. left; repeat split; auto.
    GE; auto. right. rewrite <- H9. auto. }
    assert ([rtoC r0, 0] ∈ y).
    { destruct H10. apply Split_Pb with b x; auto.
    rewrite <- H10; auto. } exists r0. split; auto. intro.
    apply AxiomII in H12. destruct H12 as [?[]].
    apply AxiomII in H13. destruct H13 as [?[]].
    apply Split_Pc with [rtoC r0, 0] x y; auto.
  - apply AxiomII in H3. destruct H3 as [_[]].
    apply AxiomII in H3. destruct H3 as [_[]].
    apply AxiomII. repeat split; try exists rC; auto.
    + apply AxiomII. repeat split; try exists rC; auto.
      apply Split_Pa with ([rtoC r1, 0]) y; auto. red. left.
      repeat split; auto. repeat GE. apply FAT154a3; auto.
    + apply AxiomII. split. exists rC; auto. intro.
      apply AxiomII in H8. destruct H8 as [_[_[_ ?]]].
      apply H8 in H7; auto. destruct H7; rordF.
  - destruct (classic ((FstmaxrC x) = Φ)).
    + apply ccp3; auto. intro. destruct H5 as [r[]].
      assert (r ∈ (FstmaxrC x)).
      { apply AxiomII in H5. destruct H5 as [?[]].
      apply AxiomII in H7. destruct H7 as [_[]].
      apply AxiomII. repeat split; auto.
      intros. assert (r0 ∈ (DedekindCC x)).
      { apply AxiomII. repeat split. exists rC; auto.
      apply AxiomII; split; auto. exists rC; auto.
      apply AxiomII. split. exists rC; auto.
      rewrite H4. apply MKT16. }
      apply H6 in H12. destruct (@ FAT81 r0 r) as [?|[?|?]]; auto.
      right; auto. contradiction. left; auto. } rewrite H4 in H7.
      pose proof (@ MKT16 r). contradiction.
    + apply NEexE in H4. destruct H4 as [b].
      assert (~ b ∈ (DedekindCC x)).
      { intro. apply AxiomII in H5. destruct H5 as [_[_ ?]].
      apply AxiomII in H5. destruct H5. contradiction. } New H3.
      apply AxiomII in H3,H4. destruct H3 as [_[]].
      destruct H4 as [_[?[]]]. apply AxiomII in H3.
      destruct H3 as [_[]]. apply H9 in H10; auto. destruct H10.
      * apply FAT91 in H10; auto. destruct H10 as [r[?[]]].
        exists r. split; auto. apply AxiomII.
        repeat split.
        -- exists rC; auto.
        -- apply AxiomII. repeat split; try exists rC; auto.
           apply Split_Pa with [rtoC b, 0] y; auto.
           red. left. repeat split; try repeat GE; auto.
           apply FAT154a3; auto.
        -- apply AxiomII. split. exists rC; auto. intro.
           apply AxiomII in H13. destruct H13 as [_[_[_ ?]]].
           apply H13 in H8; auto. destruct H8; rordF.
      * rewrite H10 in H6. contradiction.
Qed.

Fact MaxLNU : ∀ r x y, divide x y -> (∃ a, a ∈ PRC /\ a ∈ x)
  -> r ∈ (FstmaxrC x) -> LNU r (DedekindCC x).
Proof.
  intros r x y H H1 H2.
  destruct H as [fstinR[sndinR[fstne[sndne[]]]]]. red. split.
  - intro. apply AxiomII in H3. destruct H3 as [_[_ ?]].
    apply AxiomII in H3. destruct H3; contradiction.
  - intros. destruct H3. red in H4. intro. elim H4.
    apply AxiomII in H2. destruct H2 as [_[?[]]].
    apply AxiomII. repeat split.
    + exists rC; auto.
    + apply AxiomII. repeat split; try exists rC; auto.
      apply Split_Pa with [rtoC r, 0] y; auto. red. left.
      repeat split; auto. repeat GE; auto. apply FAT154a3; auto.
    + apply AxiomII. split. exists rC; auto. intro.
      apply AxiomII in H8. destruct H8 as [_[_[]]].
      apply H9 in H6; auto. destruct H6; rordF.
Qed.

Definition Split x y e := (∀ a, a ∈ RC -> a < e -> a ∈ x)
  /\ (∀ a, a ∈ RC -> a > e -> a ∈ y).

Definition contra x := \{ λ a, a ∈ RC /\ (- a) ∈ x \}.

Fact newdivide : ∀ x y, divide x y -> divide (contra y) (contra x).
Proof.
  intros. destruct H as [fstinR[sndinR[fstne[sndne[]]]]].
  red. repeat split.
  - red. intros. apply AxiomII in H1. tauto.
  - red. intros. apply AxiomII in H1. tauto.
  - apply NEexE in sndne. clear H H0. destruct sndne as [a].
    apply NEexE. exists (-a). apply AxiomII.
    New H. apply sndinR in H. assert (- a ∈ RC ). auto.
    repeat split; try exists RC; auto. rewrite FAT177; auto.
  - apply NEexE in fstne. clear H H0. destruct fstne as [a].
    apply NEexE. exists (-a). apply AxiomII.
    New H. apply fstinR in H. assert (- a ∈ RC ). auto.
    repeat split; try exists RC; auto. rewrite FAT177; auto.
  - clear H0. red. intros. unfold R_Divide in H.
    assert ((-a) ∈ RC). auto. apply H in H1.
    destruct H1.
    + right. apply AxiomII. split; try exists RC; auto.
    + left. apply AxiomII. split; try exists RC; auto.
  - clear H. intros; red; intros; red in H0.
    apply AxiomII in H,H1.
    destruct H as [?[]],H1 as [?[]].
    assert ((-b) < (-a)). apply H0; auto.
    apply FAT183a2; auto.
Qed.

Fact divi12 : ∀ x y, (∃ e, e ∈ RC /\ Split (contra y) (contra x) e)
  -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros. destruct H as [e[]]. exists (-e). split; auto.
  red in H0. destruct H0. split.
  - intros. apply FAT183c1 in H3; auto. rewrite FAT177 in H3; auto.
    apply H1 in H3; auto. apply AxiomII in H3.
    destruct H3 as [?[]]. rewrite FAT177 in H5; auto.
  - intros. apply FAT183c1 in H3; auto. rewrite FAT177 in H3; auto.
    apply H0 in H3; auto. apply AxiomII in H3.
    destruct H3 as [?[]]. rewrite FAT177 in H5; auto.
Qed.

Lemma FAT205a_aux1 : ∀ x y, divide x y
  -> (∃ a, a ∈ PRC /\ a ∈ x) -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros x y H H1. pose proof (DedCC x y H H1) as H3.
  pose proof H as divide.
  destruct H as [fstinR[sndinR[fstne[sndne[]]]]].
  exists [(DedekindCC x), 0].
  split; auto. red. split; intros.
  - destruct (inRC H2).
    + Order. GE. apply FAT159 in H7; auto. destruct H7 as [r[?[]]].
      unfold Cut_R in H8,H9. apply FAT158a in H9; auto. red in H9.
      apply AxiomII in H9. destruct H9 as [?[]].
      apply AxiomII in H10. destruct H10 as [_[]].
      apply Split_Pa with [rtoC r, 0] y; auto. red. left.
      repeat split; auto. GE; auto.
    + assert (([(DedekindCC x), 0]) / (1 + 1) <
      [(DedekindCC x), 0]). { apply half2; auto. } clear H4.
      assert ([(DedekindCC x), 0] / (1 + 1) ∈ PRC). auto. Order.
      GE. apply FAT159 in H8; auto. destruct H8 as [r[?[]]].
      unfold Cut_R in H9,H10. apply FAT158a in H10; auto.
      red in H10. apply AxiomII in H10. destruct H10 as [?[]].
      apply AxiomII in H11. destruct H11 as [_[]].
      apply Split_Pa with [rtoC r, 0] y; auto. red. destruct H5.
      * right. left; auto.
      * right; right; left; auto.
      * rewrite H6 in H4. npz.
  - apply si2' in H4. assert ([(DedekindCC x), 0] ∈ PRC). auto.
    Order; try rewrite H4 in H5; try npz. clear H5. GE.
    apply FAT159 in H7; auto. destruct H7 as [r[?[]]].
    unfold Cut_R in H7,H8. assert ((rtoC r) ≥ (DedekindCC x))%CC.
    { left; auto. } apply FAT158b in H9; auto. red in H9.
    assert (~ (LNU r (DedekindCC x))).
    { intro. red in H10. destruct H10. apply FAT159 in H7; auto.
    destruct H7 as [r1[?[]]]. unfold Cut_R in H12,H13.
    assert ((rtoC r1) ≥ (DedekindCC x))%CC.
    { left; auto. } apply FAT158b in H14; auto.
    assert (~ (r1 < r)%rC). apply H11; tauto.
    elim H15. apply FAT154b3; auto. }
    assert (~ (r ∈ (FstmaxrC x))).
    { intro. elim H10. apply MaxLNU with y; auto. }
    assert (~ [(rtoC r), 0] ∈ x).
    { intro. elim H9. apply AxiomII. repeat split.
    exists rC; auto. apply AxiomII.
    repeat split; try exists rC; auto.
    apply AxiomII. split; try exists rC; auto. }
    assert ([rtoC r, 0] ∈ y).
    { unfold R_Divide in H. assert ([rtoC r, 0] ∈ RC). auto.
    apply H in H13. destruct H13; auto. contradiction. }
    apply Split_Pb with [rtoC r, 0] x; auto. red. left.
    repeat split; repeat GE; auto.
Qed.

Lemma FAT205a_aux2 : ∀ x y, divide x y
  -> (∃ a, a ∈ NRC /\ a ∈ y) -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros. assert (∃b : Class,b ∈ PRC /\ b ∈ (contra y)).
  { destruct H0 as [a[]]. exists (-a). split. sl.
  apply AxiomII. assert (- a ∈ RC). auto. repeat split;
  try exists RC; auto. rewrite FAT177; auto. }
  apply newdivide in H.
  pose proof (FAT205a_aux1 (contra y) (contra x)).
  MP. apply divi12; auto.
Qed.

(* * 4.3 exist *)
Theorem FAT205a : ∀ x y, divide x y -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros. destruct (FstRC x y H) as [?|[?|?]].
  - apply FAT205a_aux1; auto.
  - destruct H0. exists 0. split; auto. red. split; intros.
    + assert (a ∈ NRC). auto. apply H0; auto.
    + assert (a ∈ PRC). auto. apply H1; auto.
  - apply FAT205a_aux2; auto.
Qed.

(* *4.4 unique *)
Theorem FAT205b : ∀ x y e1 e2, divide x y -> e1 ∈ RC -> e2 ∈ RC
  -> Split x y e1 -> Split x y e2 -> e1 = e2.
Proof.
  intros x y e1 e2 H1 H H0 H3 H4.
  destruct H1 as [fstinR[sndinR[fstne[sndne[]]]]].
  destruct (FAT167 H H0) as [?|[?|?]]; auto;
  apply aver2 in H5; auto; unfold Split in H3,H4;
  destruct H3,H4,H5.
  - apply H7 in H5; auto. apply H3 in H8; auto.
    pose proof (Split_Pc ((e2 + e1) / (1 + 1)) x y). MP. elim H9.
  - apply H6 in H5; auto. apply H4 in H8; auto.
    pose proof (Split_Pc ((e1 + e2) / (1 + 1)) x y). MP. elim H9.
Qed.

Close Scope RC_scope.
