(***************************************************************************)
(*   This is part of Real_Completeness, it is distributed under the        *)
(*      terms of the GNU Lesser General Public License version 3           *)
(*                (see file LICENSE for more details)                      *)
(*                                                                         *)
(*            Copyright 2025-2028: Ce Zhang and Wensheng Yu.               *)
(***************************************************************************)


Require Export FA_R1.

Open Scope RC_scope.

(* 1 引理 *)

Fact SNS : ∀ x S, x ∈ S -> x ∈ ¬S -> False.
Proof.
  intros. unfold Complement in H0. appA2H H0.
  unfold NotIn in H1; destruct H1; auto.
Qed.

Fact NotleR : ∀ r1 r2, r1 ∈ RC -> r2 ∈ RC -> ~ (r2 ≤ r1) -> r1 < r2.
Proof.
  intros. 
  assert(r1 = r2 \/ r1 > r2 \/ r1 < r2). { apply (FAT167 H H0). }
  destruct H2.
  + unfold leR in H1. destruct H1; auto.
  + destruct H2; auto. unfold leR in H1. destruct H1. auto.
Qed.

Fact Notle : ∀ r1 r2, r1 ∈ RC -> r2 ∈ RC -> ~ (r2 < r1) -> r1 ≤ r2.
Proof.
  intros. 
  assert(r1 = r2 \/ r1 > r2 \/ r1 < r2). { apply (FAT167 H H0). }
  destruct H2.
  + unfold leR. right; auto.
  + unfold leR. destruct H2; auto. elim H1. apply si2'; auto.
Qed.

Fact AUnionNotA : ∀ a , a ∪ ¬ a = μ.
Proof.
  intros. eqext.
  assert(Ensemble z). { unfold Ensemble. exists (a ∪ ¬ a); auto. }
  + apply MKT19b in H0; auto.
  + unfold Union. appA2G.
    TF(z ∈ a).
    - left; auto.
    - right. unfold Complement. appA2G.
Qed.

(*
Fact si1 : ∀ u, u ∈ PRC -> (- u) ∈ NRC.
Proof.
  intros. apply FAT169b'; auto. apply FAT176a1; auto.
  apply FAT169a; auto.
Qed.

Fact si1' : ∀ u, u ∈ NRC -> (- u) ∈ PRC.
Proof.
  intros. apply FAT169a'; auto. apply FAT176c1; auto.
Qed.

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

Fact minRC : ∀ X, X ∈ RC -> (-X) ∈ RC.
Proof.
  intros. destruct (@ inRC X H) as [H0|[H0|H0]].
  - rewrite Pmin; auto.
  - subst. rewrite Zmin; auto.
  - rewrite Nmin; auto.
Qed.
*)

Fact minRdom : dom(minR) = RC.
Proof.
  apply AxiomI; split. 
  + intros. unfold minR in H. appA2H H. destruct H0. appA2H H0. destruct H1.
    destruct H1. destruct H1, H2. New H0. apply MKT49b in H4. destruct H4. 
    apply (MKT55 z x x0 x1) in H1; auto. destruct H1. subst; auto.
  + intros. unfold minR. appA2G. assert (Ensemble z); unfold Ensemble; eauto.
    New H. apply minRC in H1. assert (Ensemble (-z)); unfold Ensemble; eauto.
    exists(-z). appA2G. exists(z). exists(-z). repeat split; auto.
    - intros. apply Pmin in H3; auto.
    - intros. apply Nmin in H3; auto.
    - intros. rewrite H3. apply Zmin.
Qed.

Fact minRC' : ∀ X, (-X) ∈ RC -> X ∈ RC.
Proof.
  intros. 
  (* 怎么写比较快？ *)
  assert(dom(minR) = RC). { apply minRdom. }
  assert(Function minR). { apply mirf. }
  assert (Ensemble (-X)); unfold Ensemble; eauto.
  rewrite <- H0.
  apply NNPP. intro. apply MKT69a in H3. rewrite H3 in H. 
  assert (Ensemble μ); unfold Ensemble; eauto. 
  assert (~ Ensemble μ); apply MKT39.
  auto.
Qed.

Fact xInX : ∀ X x, X ⊂ RC -> x ∈ X -> x ∈ RC.
Proof.
  intros. unfold Included in H. apply H in H0. auto.
Qed.


(*
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
*)

(*
Fact si2 : ∀ X Y, Y < X -> X > Y.
Proof.
  auto.
Qed.

Fact si2' : ∀ X Y, Y > X -> X < Y.
Proof.
  auto.
Qed.
*)

Fact sie2 : ∀ X Y, Y ≤ X -> X ≥ Y.
Proof.
  auto.
Qed.

Fact sie2' : ∀ X Y, Y ≥ X -> X ≤ Y.
Proof.
  auto.
Qed.

Fact xlx : ∀ x, x ∈ RC -> x < x -> False.
Proof.
  intros. New H0. apply si2 in H1. apply lgRf in H0; auto.
Qed.

Fact xleRx : ∀ x, x ∈ RC -> x ≤ x.
Proof.
  intros. TF(x ≤ x); auto. apply NotleR in H0; auto. 
  apply xlx in H0; auto. contradiction.
Qed.

Fact minsie2 : ∀ x y, x ∈ RC -> y ∈ RC -> -x ≤ y -> - y ≤ x.
Proof.
  intros. assert(∃ z, z = -x). { exists (-x); auto. }
  destruct H2. rewrite <- H2 in H1. destruct H1.
  New H. apply minRC in H3. rewrite <- H2 in H3.
  + apply FAT183c1 in H1; auto. rewrite H2 in H1. rewrite FAT177 in H1; auto.
    red. left. apply si2'; auto.
  + red; right; rewrite H1 in H2. rewrite H2. apply FAT177; auto. 
Qed.

Fact minsie2' : ∀ x y, x ∈ RC -> y ∈ RC -> y ≤ -x -> x ≤ - y.
Proof.
  intros. assert(∃ z, z = -x). { exists (-x); auto. }
  destruct H2. rewrite <- H2 in H1. destruct H1.
  New H. apply minRC in H3. rewrite <- H2 in H3.
  + apply FAT183c1 in H1; auto. rewrite H2 in H1. rewrite FAT177 in H1; auto.
    red. left. apply si2'; auto.
  + red; right. rewrite <- H1 in H2. rewrite H2. rewrite FAT177; auto. 
Qed.

(* 
Fact MincEx : ∀ X Y, X ∈ RC -> Y ∈ RC -> X + (Y - X) = Y.
Proof.
  intros. rewrite @ FAT175 with Y (- X); auto.
  rewrite <- FAT186; auto. rewrite FAT179a; auto. req1. auto.
Qed.
*)

(* 2 Dedekind基本定理 <-> 确界存在定理 *)
(* 2.1 Dedekind基本定理 -> 确界存在定理 *)

(* 上界 *)
Definition Boundup_Ens S M := S ⊂ RC /\ M ∈ RC /\ (∀ x, x ∈ S -> x ≤ M).

(* 下界 *)
Definition Bounddown_Ens S L := S ⊂ RC /\ L ∈ RC /\ (∀ x, x ∈ S -> L ≤ x).

(*
(* 有界集 *)
Definition Bounded S := ∃ M L, Boundup_Ens S M /\ Bounddown_Ens S L.

(* 无界集 *)
Definition Unbounded S := ~ (Bounded S).
*)

(* 上确界 *)
Definition supremum S η := Boundup_Ens S η /\ (∀ z, Boundup_Ens S z -> η ≤ z).
(* 下确界 *)
Definition infimum S ξ := Bounddown_Ens S ξ /\ (∀ z, Bounddown_Ens S z -> z ≤ ξ).


Definition Max S c := S ⊂ RC /\ c ∈ S /\ (∀ x, x ∈ S -> x ≤ c).

Definition Min S c := S ⊂ RC /\ c ∈ S /\ (∀ x, x ∈ S -> c ≤ x).

Lemma STlemma1 :∀ X α, X ⊂ RC -> α ∈ RC -> X ≠ Φ -> 
  ~ (∀x : Class,x ∈ X -> x ≤ α) -> (∃x1 : Class,x1 ∈ X /\ α < x1).
Proof.
  intros.
  apply NNPP. intro. elim H2. intros. apply NNPP. intro. elim H3. exists x.
  split; auto. apply NotleR; auto.
Qed.

(* 上确界存在定理 *)
Theorem SupremumT : ∀ X, X ⊂ RC -> X <> Φ -> (∃ c, Boundup_Ens X c) 
  -> exists η, supremum X η.
Proof.
  intros. destruct H1. TF (∃ m, Max X m).
  - destruct H2 as [m H2]. exists m. red; split.
    + red; split; auto. split.
      ++ destruct H2, H3. unfold Included in H2. apply H2; auto.
      ++ intros. destruct H2, H4. apply H5; auto.
    + intros. destruct H2, H4. unfold Boundup_Ens in H3.
      destruct H3, H6. apply H7; auto.
  - set (upperset := \{ λ a, Boundup_Ens X a \}).
    set (other := RC ~ upperset).
    assert (∃ y, y ∈ RC /\ Split other upperset y).
    { apply FAT205a. red. repeat split.
      + red; intros. unfold upperset in H3. unfold Boundup_Ens in H3. 
        appA2H H3. destruct H4; auto.
      + red; intros. unfold other in H3. appA2H H3. destruct H4, H5; auto.
      + red; intros. unfold other in H3. apply NEexE in H0. destruct H0. 
        assert(x0 ∈ RC ~ upperset).
        { unfold Setminus. unfold Intersection. appA2G. split.
          ++ unfold Included in H; apply H; auto.
          ++ unfold upperset. appA2G. unfold NotIn. intro. appA2H H4.
             unfold Boundup_Ens in H5. destruct H5, H6. 
             unfold Max in H2. apply H2. exists x0. split; auto. }
        rewrite H3 in H4. apply MKT16 in H4; auto.
      + red; intros.
        assert(x ∈ upperset).
        { unfold upperset. appA2G. unfold Boundup_Ens in H1. destruct H1, H4.
          unfold Ensemble; eauto. }
        rewrite H3 in H4. apply MKT16 in H4; auto.
      + red; intros. unfold other. apply MKT4. rewrite MKT6. 
        unfold Setminus. rewrite MKT8'.
        assert(upperset ⊂ RC).
        { unfold Included; intros. unfold upperset in H4. 
          unfold Boundup_Ens in H4. appA2H H4. destruct H5, H6; auto. }
        New H4. apply MKT29 in H5. 
        assert(upperset ∪ ¬ upperset = μ).
        { apply AUnionNotA. }
        rewrite H5. rewrite H6. rewrite MKT20'. auto.
      + red; intros. unfold other. unfold upperset in H4. appA2H H4.
        unfold other in H3. unfold upperset in H3. appA2H H3. destruct H6.
        appA2H H7. unfold Boundup_Ens in H5. destruct H5, H9.
        assert(~ Boundup_Ens X a).
        { intro. destruct H8. appA2G. }
        unfold Boundup_Ens in H11. 
        assert(~ (∀x : Class,x ∈ X -> x ≤ a)).
          { intro. destruct H11. split; auto. }
          New H12. apply STlemma1 in H13; auto. destruct H13. destruct H13.
        New H13. apply H10 in H13. assert(a < x0 /\ x0 ≤ b). { split; auto. }
        assert((a ≤ x0 /\ x0 < b) \/ (a < x0 /\ x0 ≤ b)). { right; auto. }
        apply FAT172 in H17; auto. }
    destruct H3. exists x0. red; split.
    + assert(upperset ⊂ RC).
      { unfold Included; intros. unfold upperset in H4. 
        unfold Boundup_Ens in H4. appA2H H4. destruct H5, H6; auto. }
      assert(other ⊂ RC).
      { unfold other. unfold Setminus. unfold Included. intros. 
        apply MKT4' in H5. destruct H5; auto. }
      assert(X ⊂ other).
      { unfold other. unfold Setminus. unfold Included. intros. apply MKT4'.
        destruct H3. split; auto. unfold Complement. appA2G. unfold upperset.
        unfold NotIn. intro. appA2H H8. unfold Boundup_Ens in H9.
        destruct H9, H10.
        assert(Max X z). { red; split; auto. }
        elim H2. exists z; auto. }
      destruct H3. unfold Boundup_Ens. repeat split; auto. intros.
      unfold Included in H6. apply H6 in H8. destruct H7.
      New H5. unfold Included in H10. New H8. apply H10 in H11.
      TF (x1 ≤ x0).
      ++ auto.
      ++ assert(x1 > x0).
         { apply NotleR in H12; auto. }
         apply H9 in H13; auto.
         (* x1 ∈ other x1 ∈ upperset 矛盾 *)
         unfold other in H8. unfold Setminus in H8. unfold Intersection in H8.
         appA2H H8. destruct H14. unfold Complement in H15. appA2H H15.
         unfold NotIn in H16. destruct H16; auto.
    + intros. New H4. rename H5 into Boundup_Ens_X_z. destruct H3. 
      unfold Split in H5. destruct H5. 
      unfold Boundup_Ens in H4. destruct H4, H7.
      unfold other in H5. unfold upperset in H6.
      apply NNPP. intro. apply NotleR in H9; auto.
      apply si2' in H9. apply H5 in H9; auto.
      unfold Setminus in H9. unfold Intersection in H9.
      appA2H H9. destruct H10. unfold upperset in H11.
      assert(~ z ∈ \{ λ a, Boundup_Ens X a \}). 
      { intro. apply SNS in H11; auto. }
      elim H12. appA2G.
Qed.

(* 下确界存在定理 *)
Theorem InfimumT : ∀ X, X ⊂ RC -> X <> Φ -> (∃ c, Bounddown_Ens X c)
  -> exists ξ, infimum X ξ.
Proof.
  intros. destruct H1.
  set (X' := \{ λ r, (- r) ∈ X \}).
  assert (∃ y, supremum X' y). 
  { apply SupremumT.
    - red. intros. unfold X' in H2. appA2H H2. unfold Included in H.
      apply H in H3. apply minRC' in H3; auto.
    - apply NEexE in H0. destruct H0. unfold Included in H. New H0. 
      apply H in H2. New H2. apply minRC in H2. New H2. rename H4 into Hminx0. 
      apply minRC in H2. New H0. New H3. apply FAT177 in H5.
      apply FAT164 in H5; auto. rewrite H5 in H0.
      assert(∃ z, z = - x0). { exists (-x0); auto. } 
      destruct H6. assert(- - x0 = - x1). { rewrite H6. auto. }
      rewrite H7 in H0.
      assert(x1 ∈ X'). 
      { unfold X'. appA2G. rewrite <- H6 in Hminx0. 
      unfold Ensemble. exists RC; auto. }
      red; intros. rewrite H9 in H8. apply MKT16 in H8; auto.
    - unfold Bounddown_Ens in H1. destruct H1, H2.
      unfold Boundup_Ens.
      assert(∃ z, z = - x).
      { exists (-x); auto. } 
      destruct H4. exists x0. repeat split.
      + unfold X'. unfold Included. intros. appA2H H5. unfold Included in H1.
        apply H1 in H6. apply minRC' in H6; auto.
      + apply minRC in H2. rewrite <- H4 in H2; auto.
      + intros. unfold X' in  H5. appA2H H5. New H6. apply xInX in H7; auto.
        apply minRC' in H7. rename H7 into Hx1RC.
        rewrite H4. apply H3 in H6.
        red. destruct H6.
        ++ left. assert(x = -x0). 
           { rewrite H4. apply FAT177 in H2. rewrite H2; auto. } 
           rewrite H7 in H6. New H2; apply minRC in H8. rewrite <- H4 in H8.
           rewrite <- H4. apply FAT183a2 in H6; auto. 
        ++ right. rewrite H6. apply FAT177 in Hx1RC. auto. }
  destruct H2 as [y [H2]].
  exists (-y); split. try red; intros.
  + repeat split.
    - auto.
    - unfold Boundup_Ens in H2. destruct H2, H4. apply minRC in H4; auto.
    - intros. unfold Boundup_Ens in H2. destruct H2, H5. unfold X' in H6. New H.
      New H4. unfold Included in H7. apply H7 in H8. apply minsie2; auto. 
      clear H8. clear H7. apply H6. appA2G. New H4. apply xInX in H4; auto. 
      apply FAT177 in H4. rewrite H4; auto. 
  + intros.  New H4. rename H5 into Bounddown_Ens_X_z. 
    unfold Bounddown_Ens in H4. destruct H4, H5. unfold Boundup_Ens in H3. 
    New H2. unfold Boundup_Ens in H7. destruct H7, H8.
    apply minsie2'; auto. apply H3. New H5. apply minRC in H10. 
    repeat split; auto. intros. New H11.
    apply xInX in H12; auto. apply minRC in H12. apply minsie2'; auto.
    apply H6. unfold X' in H11. appA2H H11. auto.
Qed.

(* 确界存在定理 *)
Theorem Sup_Inf_Principle : ∀ X, X ⊂ RC -> X <> Φ
  -> ((∃ c, Boundup_Ens X c) -> exists η, supremum X η)
  /\ ((∃ c, Bounddown_Ens X c) -> exists ξ, infimum X ξ).
Proof.
  intros. split; intros.
  - apply SupremumT; auto.
  - apply InfimumT; auto.
Qed.

(* 2.2 Dedekind基本定理 <- 确界存在定理 *)
(* 存在性 *)
Theorem Dedekind_exist : ∀ x y, divide x y -> ∃ e, e ∈ RC /\ Split x y e.
Proof.
  intros. destruct H, H0, H1, H2, H3. New H3. rename H5 into HR_Divide. 
  unfold R_Divide in H3. 
  assert (∃ u, Boundup_Ens x u).
  { apply NEexE in H2. destruct H2. exists (x0). red. repeat split; auto.
    intros. left. apply H4; auto. }
  apply SupremumT in H5; auto. destruct H5 as [e [H5]]. New H5. 
  rename H7 into HBoundup_Ens_x_e. unfold Boundup_Ens in H5. 
  destruct H5, H7; auto. exists e; split; auto; intros.
  red. split.
  - intros. destruct HR_Divide with a; auto. 
    assert (Boundup_Ens x a).
    { red; intros. repeat split; auto. intros. left. apply H4; auto. }
      apply H6 in H12. apply legRf in H12; auto. contradiction.
  - intros. destruct HR_Divide with a; auto. apply HBoundup_Ens_x_e in H11. 
    apply legRf in H11; auto. contradiction.
Qed.

(*
Fact aver2 : ∀ x y, x ∈ RC -> y ∈ RC -> x < y
  -> x < (x + y) / (1 + 1) /\ (x + y) / (1 + 1) < y.
Proof.
  intros. split; apply (FAT203e _ _ (1 + 1)); auto;
  rewrite divRp7; auto; rewrite FAT201a; auto;
  repeat rewrite FAT195a; auto; [rewrite FAT175; auto|];
  apply FAT188a2; auto.
Qed.
*)

(* 唯一性 *)
Theorem Dedekind_unique : ∀ x y e1 e2, divide x y -> e1 ∈ RC -> e2 ∈ RC
  -> Split x y e1 -> Split x y e2 -> e1 = e2.
Proof.
  assert (∀ x y, divide x y -> ∀ e1 e2, e1 ∈ RC /\ Split x y e1
    -> e2 ∈ RC /\ Split x y e2 -> ~ e1 < e2).
  { intros. intro. destruct H0, H1. red in H3, H4; destruct H3, H4.
    assert(e1 < (e1 + e2) / (1 + 1) /\ (e1 + e2) / (1 + 1) < e2). 
    { apply aver2 in H2; auto. }
    destruct H7.
    apply H5 in H7; apply H4 in H8; auto.
    red in H. destruct H, H9, H10, H11, H12. 
    (*              *)
    pose proof (H13 _ _ H8 H7). apply xlx in H14; auto. }
  intros. assert(e1 = e2 \/ e1 > e2 \/ e1 < e2). { apply (FAT167 H1 H2). }
  destruct H5; auto. destruct H5.
  (*           *)
  + eapply H in H5; eauto; tauto.
  + eapply H in H5; eauto; tauto.
Qed.
