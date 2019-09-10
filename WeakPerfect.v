









Require Export LovaszExp.
Require Export GraphCovers.
Set Implicit Arguments.

Section MeetsDef.
  Context { A: ordType }.
  
  Definition meets (K I: list A):= exists a:A, In a K /\ In a I.

  End MeetsDef.


Section ExistsCliq.
  
  Context { A: ordType }.
  Variable G: (@UG A).

  
  Hypothesis Gnil: (nodes G) <> nil.
  Hypothesis GPerfect: Perfect G.

  
  Let C:= max_subs_of G (fun I => stable G I).
  Let C':= mk_disj C.

  Let N:= union_over C.
  Let N':= union_over C'.

  Let H:= (ind_at N G).
  Let E:= (edg H).

  Let g:= fun (x: A*nat) => fst x.
  
  Let E1:= fun (x y: A*nat) => match (g x == g y) with
                          | true => match (snd x == snd y) with
                                   |true => false
                                   |false => true
                                   end
                          |false => E (g x) (g y)
                          end.

  Lemma N'IsOrd: IsOrd N'.
  Proof. subst N'. auto. Qed.

  Lemma NIsOrd: IsOrd N.
  Proof. subst N. auto. Qed.

  Hint Resolve N'IsOrd NIsOrd.
  
  Lemma E1_irefl: irefl E1.
  Proof. { unfold irefl. intro p. unfold E1.
           replace (g p == g p) with true. 
           assert (h1: snd p == snd p). apply /eqP;auto.
           rewrite h1. auto. symmetry;auto. } Qed.
         
  Lemma E1_sym: sym E1.
  Proof. { unfold sym. intros x y. unfold E1.
         destruct (g x == g y) eqn: h1; destruct (snd x == snd y) eqn: h2.
         { move /eqP in h1. symmetry in h1. move /eqP in h1. rewrite h1. rewrite h2.
           move /eqP in h2. symmetry in h2. move /eqP in h2. rewrite h2. auto. }
         { rewrite h2. move /eqP in h1. symmetry in h1. move /eqP in h1. rewrite h1.
           assert (h3: (snd y == snd x) = false). 
           switch. switch_in h2. intro h3; apply h2; eauto. rewrite h3;auto. }
         { move /eqP in h2. symmetry in h2. move /eqP in h2. rewrite h2.
           assert (h3: (g y == g x) = false). 
           switch. switch_in h1. intro h3; apply h1; eauto. rewrite h3.
           unfold E. auto. }
         { assert (h3: (g y == g x) = false). 
           switch. switch_in h1. intro h3; apply h1; eauto. rewrite h3.
           unfold E. auto. } } Qed.

  (*-----Some  more properties of the new edg relation (E1 x y)------------*)
  Lemma E1_P1: forall x y, x <> y -> g x = g y -> E1 x y.
  Proof. { intros x y h1 h2. unfold E1.
           replace (g x == g y) with true. replace (snd x == snd y) with false.
           auto. symmetry;switch. move /eqP. intro h3.
           absurd (x = y). auto.
           destruct x as [x1 x2]; destruct y as [y1 y2]; simpl in h2,h3.
           subst x1; subst x2. auto. symmetry;auto. } Qed.

  Lemma E1_P2: forall x y, g x <> g y -> E1 x y = E (g x) (g y).
  Proof. { intros x y h1. unfold E1. replace ( g x == g y) with false. auto.
           symmetry;auto. } Qed.
           
  Hint Immediate E1_P1 E1_P2.


  (*------ The edge relation E1 when restricted to N' is denoted as E' --------*)

  Let E':= E1 at_ N'.
         
  Lemma E'_out: E' only_at N'.
  Proof. unfold E'. auto. Qed.

  Lemma E'_irefl: irefl E'.
  Proof. unfold E'. cut (irefl E1). auto. apply E1_irefl. Qed.

  Lemma E'_sym: sym E'.
  Proof. unfold E'. cut (sym E1). auto. apply E1_sym. Qed.

  
  Definition H' := ({| nodes:= N'; edg:= E'; nodes_IsOrd:= N'IsOrd;
                       edg_irefl:= E'_irefl; edg_sym:= E'_sym; out_edg:= E'_out |}).

  (*-------- nodes of H and H' are related via stable sets in C and C' respectievly ------*)

  Lemma N_sub_G: N [<=] G.
  Proof. subst N. cut (forall I, In I C -> I [<=] G). auto.
         intros I h1. subst C. eauto. Qed.

  Hint Resolve N_sub_G.
  
  Lemma NG_N: N [i] G = N.
  Proof. symmetry. cut (N [<=] G). all: auto. Qed.

  Hint Resolve N_sub_G NG_N.

  Lemma mem_of_C: forall I, In I C -> Max_I_in G I.
  Proof.  intros I h1. unfold C in h1. unfold Max_I_in.
          apply max_subs_of_elim; auto. Qed.

  Lemma max_I_of_H: forall I, In I C -> Max_I_in H I.
  Proof. { intros I h1.
           assert (h2: I [<=] H).
           { simpl. rewrite NG_N. unfold N.
             intros x h2. eapply union_over_intro;eauto. }
           apply mem_of_C in h1 as h3.
           apply Max_I_in_intro.
           eapply Stable_in_GH with (G0:= G).
           unfold H. auto. auto. auto.
           intros I' h4. cut (Stable_in G I'). eauto.
           eapply Stable_in_HG with (H0:= H). unfold H. all: auto. } Qed.
  

  Lemma mem_of_C': forall I, In I C -> In (I [,] (idx I C)) C'.
  Proof. subst C'. intros I h1.  apply mk_disj_intro. auto. Qed.
  

  Lemma C'_map_to_C: forall I, In I C -> I = img g (I [,] (idx I C)).
  Proof. intros I h1. unfold g. apply fix_nat_prop2.
         subst C. cut (IsOrd G). eauto. auto. Qed.

  Hint Resolve mem_of_C max_I_of_H mem_of_C' C'_map_to_C.

  Lemma C_and_C': (nodes H) = img g H'.
  Proof. simpl. rewrite NG_N. subst N. subst N'. subst C'. unfold g.  auto.  Qed.

  Lemma E'_P1: forall x y, In x H' -> In y H' -> x <> y -> g x = g y -> edg H' x y.
  Proof. intros x y hx hy h1 h2. simpl. replace ( E' x y) with (E1 x y).
         Focus 2. unfold E'. simpl in hx, hy. auto. auto. Qed.

  Lemma E'_P2:  forall x y, In x H' -> In y H' -> g x <> g y -> edg H (g x) (g y) = edg H' x y.
  Proof. intros x y hx hy h1. symmetry. simpl (edg H' x y).
         replace ( E' x y) with (E1 x y). Focus 2. unfold E'. simpl in hx, hy. auto.
         auto. Qed.
   
  Hint Resolve C_and_C'.
  Hint Immediate E'_P1 E'_P2.
  
  
  Lemma H'_exp_of_H: Exp_of H H' g.
  Proof. { unfold Exp_of.
           split.
           {(*- H = img g H' ---*)
             auto. }
           split.
           { (*- In x H' -> In y H' -> x <> y -> g x = g y -> edg H' x y -*)
             apply E'_P1. }
           { (*- In x H' -> In y H' -> g x <> g y -> edg H (g x) (g y) = edg H' x y -*)
             apply E'_P2. } } Qed.

  Hint Resolve H'_exp_of_H.

  Lemma C'_is_disj: forall I1 I2, In I1 C' -> In I2 C' -> I1 <> I2 -> I1 [i] I2 = nil.
  Proof. { intros I1' I2' h1 h2 h3.
           assert (h4:  I1' [i] I2' = nil \/  I1' [i] I2' <> nil). eauto.
           destruct h4 as [h4 |h4].
           { auto. }
           assert (h4a: exists y, In y (I1' [i] I2')). auto.
           destruct h4a as [y h4a]. 
           assert (h4b: In y I1'). eauto. assert (h4c: In y I2'). eauto.
           unfold C' in h1, h2.
           apply mk_disj_elim in h1 as h1a.
           apply mk_disj_elim in h2 as h2a.
           destruct h1a as [I1 h1a]; destruct h1a as [h1a h1b].
           destruct h2a as [I2 h2a]; destruct h2a as [h2a h2b].
           subst I1'. subst I2'. destruct y as [y1 y2].
           assert (h5: I1 <> I2).
           { intros h5. subst I1.
             absurd (I2 [,] idx I2 C = I2 [,] idx I2 C);auto. }
           assert (h6a: y2 = idx I1 C).
           eapply fix_nat_elim1. apply h4b.
           assert (h6b: y2 = idx I2 C).
           eapply fix_nat_elim1. apply h4c.
           assert (h7: I1 = I2).
           { cut (idx I1 C = idx I2 C).
             eapply same_index;auto. omega. }
           contradiction. } Qed.
           
  
  Lemma Stable_cover_C'_H': Stable_cover C' H'.
  Proof. { unfold Stable_cover.
           split.
           { simpl. unfold Set_cover. unfold N';auto. }
           { intros I' h1. unfold C' in h1.
             apply mk_disj_elim in h1 as h1a.
             destruct h1a as [I h1a]. destruct h1a as [h1a h1b].
             split. Focus 2. rewrite h1b. cut (IsOrd I). auto.
             assert (h1c: Max_I_in G I). auto. eauto.
             assert (h2: I = img g I').
             { rewrite h1b. auto. }
             assert (h3: Exp_of H H' g). auto.
             assert (h4: Stable_in H I). auto.
             assert (h5: I' [<=] H').
             { simpl. unfold N'. unfold C'.
               intros x h5. eapply union_over_intro;eauto. }
             unfold Stable. intros x y hx hy.
             destruct h4 as [h4a h4]. unfold Stable in h4.
             assert (h6: g x = g y \/ g x <> g y). eauto.
             destruct h6 as [h6a | h6b].
             { assert (h6b: x = y).
               { destruct x as [x1 x2]; destruct y as [y1 y2].
                 cut (x1 = y1). cut (x2 = y2).
                 intros h7 h8;subst x1;subst x2; auto.
                 subst I'. replace y2 with (idx I C). eapply fix_nat_elim1; apply hx.
                 symmetry; eapply fix_nat_elim1; apply hy. simpl in h6a. auto. }
               rewrite h6b. auto. }
             { replace ( edg H' x y) with ( edg H (g x) (g y)).
               apply h4; subst I;auto. apply E'_P2;auto. } } } Qed.

  Lemma C'_mem_stable: forall I, In I C' -> Stable_in H' I.
  Proof. intros I h1. specialize Stable_cover_C'_H' as h2. eauto. Qed.
             
  Hint Resolve Stable_cover_C'_H' C'_mem_stable.

  Lemma g_one_one_on_I': forall I', Stable_in H' I' -> one_one_on I' g.
  Proof. { intros I' h1. unfold one_one_on.
           destruct h1 as [h1 h2]. unfold Stable in h2.
           intros x y hx hy h3 h4.
           absurd (edg H' x y). switch. apply h2;auto.
           apply E'_P1. all: eauto. } Qed.

  Lemma img_of_I'_is_I: forall I', Stable_in H' I' -> Stable_in H (img g I').
  Proof. { intros I' h1.
           assert (H1: one_one_on I' g).
           { apply g_one_one_on_I';auto. }
           assert (h1a: I' [<=] H'). auto.
           assert (h2: (nodes H) = img g H'). auto.
           unfold Stable_in.
           assert (h3: img g I' [<=] H).
           { rewrite h2;auto. } split. auto.
           split. cut (IsOrd I'); auto. eauto.
           unfold Stable. intros gx gy h4 h5.
           assert (h4a: exists x, In x I' /\ gx = g x). auto.
           destruct h4a as [x h4a]. destruct h4a as [h4a h4b].
           assert (h5a: exists y, In y I' /\ gy = g y). auto.
           destruct h5a as [y h5a]. destruct h5a as [h5a h5b].
           subst gx; subst gy.
           destruct h1 as [h1b h1]. unfold Stable in h1.
           assert (h6: x = y \/ x <> y). eauto.
           destruct h6 as [h6a | h6b].
           { subst x. auto. }
           { replace (edg H (g x) (g y)) with (edg H' x y).
             apply h1;auto. symmetry;apply E'_P2;auto. } } Qed.
             
  
  
  Lemma Stable_in_H': forall I, In I C' -> Max_I_in H' I.
  Proof. { intros I' h1. apply Max_I_in_intro. auto.
           intros I1 h2.
           assert (h3: exists I, In I C /\ I' = I [,] (idx I C)). auto.
           destruct h3 as [I h3]. destruct h3 as [h3a h3].
           assert (h4: I = img g I'). rewrite h3. auto.
           apply max_I_of_H in h3a as h3b.
           set (I0 := img g I1).
           assert (h5: Stable_in H I0).
           { unfold I0. apply img_of_I'_is_I. auto. }
           assert (hI': Stable_in H' I'). auto.
           assert (h8: one_one_on I' g).
           { apply g_one_one_on_I'; auto. }
            assert (h9: one_one_on I1 g).
           { apply g_one_one_on_I'; auto. }
           assert (h6: |I'| = |I|).
           { subst I. cut(IsOrd I'). auto. eauto. }
           assert (h7: |I1| = |I0|).
           { subst I0. cut(IsOrd I1). auto. eauto. }
           rewrite h6; rewrite h7. eauto. } Qed.
           
  Lemma PerfectH': Perfect H'.
  Proof. cut (Perfect H). eapply LovaszExpLemma. apply H'_exp_of_H.
         cut (Ind_subgraph H G). eauto. unfold H. auto. Qed.

  Lemma K'_meets_all_in_C': (exists K', Cliq_in H' K' /\ (forall I, In I C' -> meets K' I)).
  Proof. { destruct (i_num_of G) as [n h1].
           assert (hn: n >= 1).
           { eapply i_num_gt; eauto. }
           assert (h2: i_num H n).
           { destruct h1 as [I h1]. exists I.
             split. Focus 2. apply h1.
             destruct h1 as [h1a h1].
             apply Max_I_in_intro. cut (I [<=] H). cut (Stable_in G I).
             cut (Ind_subgraph H G). eauto. unfold H. auto. auto.
             simpl. rewrite NG_N. unfold N.
             cut (In I C). intros h2 x h3. eauto. unfold C. auto.
             intros I' h2.
             assert (h3: Stable_in G I').
             { eapply Stable_in_HG with (H0:= H). unfold H. auto. auto. }
             eapply Max_I_in_elim. apply h1a. auto. }
            
           assert (h3: i_num H' n).
           { destruct h1 as [I h1].  destruct h1 as [h1a h1].
             assert (h2b: In I C).
             { unfold C. auto. }
             apply mem_of_C' in h2b as h3.
             set(I':=  (I [,] idx I C)). fold I' in h3.
             assert (h4: |I| = |I'|).
             { unfold I'. apply fix_nat_size. }
             exists I'. split. apply Stable_in_H'. auto.
             subst n. symmetry. apply h4. }
           
           assert (h4: Perfect H').
           { apply PerfectH'. }
           
           assert (h5: chrom_num H' (|C'|)).
           { assert (h6: exists f, Coloring_of H' f /\ |clrs_of f H'| = |C'|).
             { eapply disj_cover_to_color. 
               { apply Stable_cover_C'_H'. }
               { cut (IsOrd C'). auto. unfold C'. cut (IsOrd C).
                 auto. unfold C. unfold max_subs_of. auto. }
               { apply C'_is_disj. }
               { intros I h5 h6.
                 specialize (Stable_in_H' I h5) as h7.
                 destruct h3 as [I' h3]. destruct h3 as [h3a h3].
                 assert(h8: n <= |I|).
                 { rewrite <- h3. apply h7.
                   cut (I' [<=] H'). cut (IsOrd I').  eauto. eauto. auto.
                   apply /stableP. auto. }
                 subst I. simpl in h8. omega. } }
             
             destruct h6 as [f h6]. destruct h6 as [h6a h6].
             exists f. split.
             { unfold Best_coloring_of.
               split.
               auto.
               intros f1 h7. rewrite h6.
               assert (h8: (| C' |) <= (| clrs_of f1 H' |) \/ ~ (| C' |) <= (| clrs_of f1 H' |)).
               eauto. destruct h8 as [h8 |h8]. auto.
               assert (h8a: (| C' |) > (| clrs_of f1 H' |)). omega.
               specialize (color_to_cover h7) as h9.
               destruct h9 as [C1 h9]. destruct h9 as [h9a h9b].
               rewrite <- h9b. rewrite <- h9b in h8a.
               assert (h9c:  exists I1, In I1 C1 /\ (|I1| * |C1|) >= |N'|).
               { (*- proof using lemma large_set_in_cover --*)
                 apply large_set_in_cover.
                 { (*-- N' <> nil -*)
                   destruct h1 as [I h1]. destruct h1 as [h1a h1].
                   destruct I as [|a I'] eqn: HI. rewrite <- h1 in hn.
                   simpl in hn. inversion hn.
                   assert (h1b: In I C).
                   { unfold C.  apply max_subs_of_intro. auto.
                     rewrite <- HI in h1a. auto. }
                   assert (h1c: In a I).
                   { subst I. auto. }
                   set (i:= idx I C).
                   assert (h1d: In (a,i) (I [,] i)).
                   { unfold i. auto. }
                   assert (h1e: In (I [,] i) C').
                   { unfold C'. unfold i. auto. }
                   assert (h1f: In (a,i) N').
                   { unfold N'. eauto. }
                   intro h10. rewrite h10 in h1f. simpl in h1f. auto. }
                 { (*-- In x C1 -> IsOrd x -*)
                   intros I hI. cut(Stable_in H' I). eauto. eauto. }
                 { apply h9a. } }
               
               destruct h9c as [I1 h9c]. destruct h9c as [h9c h9d].
               
               assert (h9e: Stable_in H' I1).
               { eauto. }

               assert (h9f: |I1| <= n).
               { destruct h3 as [I h3]. destruct h3 as [h3a h3b].
                 rewrite <- h3b. apply h3a. cut (I1 [<=] H'). cut (IsOrd I1).
                 auto. eauto. eauto. apply /stableP. auto. }
               
               assert (h10: Stable_cover C' H').
               { apply Stable_cover_C'_H'. }
               
               assert (h10a:  |N'| = |C'| * n). 
               { (*-- proof using lemma disj_cover_card ---*)
                 apply disj_cover_card.
                 { unfold Stable_cover in h10. apply h10. }
                 { unfold C'. cut (IsOrd C). auto.
                   unfold C. unfold max_subs_of. auto. }
                 { intros I h11. apply Stable_in_H' in h11 as h12.
                   split. eauto.  symmetry. eauto. }
                 { apply C'_is_disj. } }

               rewrite h10a in h9d.
               assert(h11: (| I1 |) * (| C1 |) <= n * (| C1 |)).
               { auto with arith. }
               assert (h12:  n * (| C1 |) <  n * (| C' |)).
               { auto with arith. }
               assert (h13:  (| I1 |) * (| C1 |) < (| C' |) * n).
               { replace ((| C' |) * n) with (n*(| C' |)). omega.
                 auto with arith. } omega. }
             { auto. } }
           
           assert (h6: cliq_num H' (|C'|)).
           {  assert (h6: Nice H'). auto.
              apply nice_elim;auto. }
              

           destruct h6 as [K' h6]. destruct h6 as [h6a h6].
           exists K'. split. auto. intros I h7.
           unfold meets. eapply php_eq with (s:= C'). 
           { eauto. }
           { unfold C'. cut (IsOrd C). auto.
             unfold C. unfold max_subs_of. auto. }
           { auto. }
           { intros x h8. unfold Max_K_in in h6a.
             assert (h6b: K' [<=] H'). apply h6a.
             assert (h8a: In x H'). auto.
             unfold H' in h8a. simpl in h8a. unfold N' in h8a.
             apply union_over_elim. auto.  }
           { intros x y I1 hxk hyk h8 hxi hyi.
             assert (h9: Cliq H' K').
             { cut(Cliq_in H' K'). auto. auto. }
             assert (h9a: Stable H' I1).
             { cut (Stable_in H' I1). auto. cut (Max_I_in H' I1).
               auto. apply Stable_in_H'. auto. }
             unfold Cliq in h9. unfold Stable in h9a.
             specialize (h9 x y hxk hyk) as h9b.
             destruct h9b as [h9b | h9b].
             auto. absurd (edg H' x y). switch. all: auto. } auto. } Qed.
           
  
   Lemma K_meets_all_in_C: (exists K, Cliq_in H K /\ (forall I, In I C -> meets K I)).
  Proof. { destruct K'_meets_all_in_C' as [K' h1].
           destruct h1 as [h1 h2].
           set (K:= img g K').
           exists K.
           split.
           { (*-- Cliq_in H K --*)
             unfold Cliq_in.
             assert (h3: K [<=] H).
             { rewrite C_and_C'. subst K. cut (K' [<=] H'). auto. auto. }
             split.
             { auto. }
             split.
             { subst K. auto. }
             { unfold Cliq. intros gx gy h4 h5.
               assert (h4a: exists x, In x K' /\ gx = g x).
               { unfold K in h4. auto. }
               assert (h5a: exists y, In y K' /\ gy = g y).
               { unfold K in h5. auto. }
               destruct h4a as [x h4a]. destruct h4a as [h4a h4b].
               destruct h5a as [y h5a]. destruct h5a as [h5a h5b].
               assert (h6: gx = gy \/ gx <> gy). eauto.
               destruct h6 as [h6 | h6].
               { left. auto. }
               { right. subst gx. subst gy.
                 replace (edg H (g x) (g y)) with (edg H' x y).
                 unfold Cliq_in in h1. unfold Cliq in h1.
                 assert (h7: x = y \/ edg H' x y). apply h1;auto.
                 destruct h7 as [h7 |h7]. subst x.
                 absurd (g y = g y);auto. auto.
                 assert (h7: K' [<=] H'). apply h1.
                 symmetry. apply E'_P2. all: eauto. } } }
           { (*--- forall I : list A, In I C -> meets K I -- *)
             intros I h3.
             specialize (C'_map_to_C I h3) as h4.
             set (I':=  (I [,] idx I C)).
             assert (h5: meets K' I').
             { apply h2. unfold C'. unfold I'. auto. }
             destruct h5 as [x h5]. destruct h5 as [h5 h6].
             exists (g x). split. subst K. auto. rewrite h4. fold I'. auto. } } Qed.
  
  Lemma Cliq_meets_all_MaxI: (exists K, Cliq_in G K /\ (forall I, Max_I_in G I -> meets K I)).
  Proof. { destruct K_meets_all_in_C as [K h1].
           destruct h1 as [h1 h2].
           exists K.
           split.
           { (*-- Cliq_in H K -> Cliq_in G K --*)
             assert (h3: Ind_subgraph H G). subst H. auto. eauto. }
           { (*-- forall I : list A, Max_I_in G I -> meets K I --*)
             intros I h3. apply h2. subst C. apply max_subs_of_intro.
             auto. unfold Max_I_in in h3. auto. } } Qed.

End ExistsCliq.




Section WPerfect.
  
  Context { A: ordType }.

 
  Lemma cliq_meets_stable_once (G: @UG A)(K: list A)(I: list A)(x y: A):
    Cliq G K -> Stable G I -> In x K -> In y K -> In x I -> In y I -> x = y.
  Proof. { intros h1 h2 hxk hyk hxi hyi. unfold Cliq in h1;unfold Stable in h2.
           specialize (h1 x y hxk hyk) as h1a.
           destruct h1a as [h1a | h1b].
           { auto. }
           { absurd (edg G x y). switch;apply h2;auto. auto. } } Qed.
  
  
  Lemma i_num_cliq_cover (G: @UG A)(n: nat):
    Perfect G -> i_num G n -> (exists C, Cliq_cover C G /\ |C| = n).
  Proof. { revert G. induction n using strong_induction.
           intros G h1 h2.
           destruct h2 as [I h2]. destruct h2 as [h2a h2].
           assert (hN: nodes G = nil \/ nodes G <> nil). eauto.
           destruct hN as [hNa | hNb].
           {(*---- When the graph is empty Graph i.e nodes G = nil  ---------*)
             exists nil. split.
             { (*-- Cliq_cover nil G --*)
               unfold Cliq_cover. split.
               unfold Set_cover. rewrite hNa. simpl. auto.
               simpl. tauto. }
             { (*---  (| nil |) = n ----*)
               simpl.
               assert (hI: I = nil). 
               { destruct h2a as [h2a h2b]. rewrite hNa in h2a.
                 apply set_equal. apply h2b. constructor. split; auto. }
               subst I. simpl in h2. auto. }   } 

           {(*----- When the graph is non-empty i.e nodes G <> nil ----------*)
             specialize (Cliq_meets_all_MaxI hNb h1) as h1a. 
             destruct h1a as [K h1a]. destruct h1a as [h1a h1b]. 
             assert (hg: exists g, In g G). auto.
             destruct hg as [g hg].
             
             assert (hn: n >= 1).
             { set (I':= g::nil). 
               assert (hI': Stable_in G I').
               { unfold Stable_in. subst I'.
                 split.
                 { intros x hx. destruct hx as [hx |hx];simpl in hx. subst x;auto. tauto. }
                 split.
                 { constructor. }
                 { unfold Stable. intros x y hx hy.
                   assert (hxy: x = y).
                   { destruct hx as [hx | hx];destruct hy as [hy | hy].
                     subst x; auto. simpl in hy;tauto. all: simpl in hx;tauto. }
                    subst x. auto. } }
               assert (h3: |I'| <= |I|).
               { eauto. }
               subst I'. simpl in h3. rewrite h2 in h3.
               auto. }
             
             assert (h1c: K [<=] G). auto.
             assert (h1d: K = K [i] G). eauto.
         
             (* G_K represents the graph obtained by removing cliq K from graph G *)
             set (G_K:= ind_at (G [\] K) G).
             assert (hg_k: Ind_subgraph G_K G).
             { subst G_K. auto. }

             assert (hG_K: Perfect G_K).
             { cut (Ind_subgraph G_K G). eauto. unfold G_K; auto. }

             assert (h3: i_num G_K (n-1)). 
             { specialize (h1b I h2a) as hKI.
               destruct hKI as [k hKI].
               set (I_k:= rmv k I).
               exists I_k.
               split.
               { (*--  Max_I_in G_K I_k --*)
                 assert (h3: Stable_in G I). auto. unfold Stable_in in h3.
                 assert (h3a: Stable G I). apply h3. unfold Stable in h3a.
                 assert (h9: I_k [<=] G_K ).
                 { subst I_k; subst G_K. simpl.
                   replace ((G [\] K) [i] G) with (G [\] K).
                   Focus 2. cut (G [\] K [<=] G); auto.
                   intros x hx.
                   assert (hx1: In x I). eauto.
                   assert (hxk: x <> k).
                   { cut (NoDup I).  eauto. cut (IsOrd I). auto. apply h3. }
                   cut (In x G). cut (~ In x K). auto.
                   intro h4. absurd (x = k). auto.
                   eapply cliq_meets_stable_once with (G:= G)(K:= K)(I:= I).
                   all: auto. apply hKI. apply hKI. cut (I [<=] G ). auto.
                   apply h3. }
                 assert (h10:  (| I_k |) = n - 1).
                 { subst I_k. cut (In k I).  rewrite <- h2. eauto.
                   apply hKI. } 
                 split.
                 { (*-- I_k [<=] G_K --*)
                   apply h9. }
                 split.
                 { (*--- IsOrd I_k---*)
                   subst I_k. cut (IsOrd I). auto. apply h3. }
                 split.
                 { (*--- stable G_K I_k----*)
                   apply /stableP. unfold Stable.
                   intros x y hx hy. replace (edg G_K x y) with (edg G x y).
                   apply h3a; unfold I_k in hx, hy;eauto.
                   symmetry. cut (In x G_K). cut (In y G_K). all: auto. }
                 { (*- (forall I' :list A, In I' (pw G_K)-> stable G_K I'-> (|I'|)<=(|I_k|)) -*)
                   intros I' h11 h12. move /stableP in h12.
                   assert (h13: Stable_in G I').
                   { cut (Stable_in G_K I'). eauto. 
                     unfold Stable_in. split. auto. split;auto.
                     cut (IsOrd G_K). eauto. subst G_K;simpl. auto. }
                   cut ( ~ (| I' |) > (| I_k |)). omega.
                   intros h14.
                   assert (h15: (|I'|) <= n).
                   { rewrite <- h2. eauto. } 
                   rewrite h10 in h14.
                   assert (h16: |I'| = n). omega.
                   assert (h17: Max_I_in G I').
                   { apply Max_I_in_intro. auto.
                     rewrite h16. rewrite <- h2. intros I0' h17. eauto. }
                   specialize (h1b I' h17) as h18. destruct h18 as [k' h18].
                   assert (h19: I' [<=] G_K).
                   { cut (IsOrd G_K). eauto. subst G_K;simpl. auto. }
                   absurd (In k' K). cut (In k' G_K).
                   subst G_K. simpl.
                   replace ((G [\] K) [i] G) with (G [\] K).
                   Focus 2. cut (G [\] K [<=] G); auto.
                   intros h20. eauto. cut (In k' I'). auto. all: apply h18. } }
               
               { (*--- (| I_k |) = n - 1 --*)
                  subst I_k. cut (In k I).  rewrite <- h2. eauto.
                  apply hKI.  } } 

             assert (h4: n - 1 < n). omega.

             specialize (H (n-1) h4 G_K hG_K h3) as h5.
             destruct h5 as [C_K h5].

             exists (K::C_K).
             split.
             { (*--- Cliq_cover (K :: C_K) G -----*)
               unfold Cliq_cover.
               split.
               {(*---- Set_cover (K :: C_K) G ----*)
                 unfold Set_cover.
                 assert (h6: nodes G_K = G [\] K).
                 { unfold G_K. simpl. symmetry.
                   cut ((G [\] K) [<=] G). auto. auto. }
                 replace (nodes G) with (K [u] (G [\] K)).
                 Focus 2. symmetry;auto. simpl.
                 replace ((G [\] K)) with (union_over C_K).
                 Focus 2. symmetry. rewrite <- h6.   apply h5.
                 auto. } 
               
               {(*---- (forall I0 : list A, In I0 (K :: C_K) -> Cliq G I0 /\ IsOrd I0) ---*)
                 intros Kx h6. destruct h6 as [h6 | h6]. 
                 { rewrite <- h6. split;auto. eauto. }
                 { assert (h5c: Cliq_cover C_K G_K). apply h5.
                   split. cut (Cliq_in G Kx). auto.
                   cut (Cliq_in G_K Kx). all: eauto. }  } }
             
             { (*---- (| K :: C_K |) = n ---------*)
               destruct h5 as [h5a h5].
               simpl. rewrite h5. omega. }   } } Qed.
           
          
 
End WPerfect.



Section WPGT.

  Context { A: ordType }.


  Lemma wpgt (G G': @UG A): Perfect G -> Compl G G'-> Perfect G'.
  Proof.
    { (* We will prove the result by well founded induction on G'. 
      To use the well founded induction we first need to prove that the relation 
      lt_graph is well founded on UG. This is proved as Lemma lt_graph_is_well_founded
      in the file DecUG.v. *)
      revert G. pattern G'. revert G'.
      eapply well_founded_ind with (R:= @lt_graph A).
      apply lt_graph_is_well_founded.
      unfold lt_graph. intros G' IH G h2 h.
      
      assert (gg': nodes G = nodes G'). apply h.

      unfold Perfect. intros H' h3.

      assert (heq: nodes H' = nodes G' \/ nodes H' <> nodes G'). eauto.

      destruct heq as [heq | neq].
      { (*--- H' = G' ---*)
        (*---- In this case the proof uses the lemma i_num_cliq_cover ----*)
        cut (Nice G').
        { cut (iso  G' H'). eauto. cut (iso H' G'). auto. auto using ind_sub_eq_iso. }
        
        destruct (cliq_num_of G') as [n' hn'].
        
        assert (h4: i_num G n').
        { (* cliq_num G' n' -> i_num G n' *)
          eapply cliq_num_i_num with (G0:= G').
          apply compl_commute;auto. auto. }
        eapply nice_intro1. exact hn'.
        specialize (i_num_cliq_cover h2 h4) as h5.
        destruct h5 as [C h5]. destruct h5 as [h5 h5a].
        exists C.
        split.
        {(* Cliq_cover C G -> Stable_cover C G' *)
          unfold Cliq_cover in h5. destruct h5 as [h5 h5b].
          unfold Stable_cover.
          split.
          { rewrite <- gg'. auto. }
          { intros I h6.
            split. eapply cliq_is_stable. exact h. unfold Cliq_in.
            split. eauto. split;apply h5b;auto. apply h5b;auto. } }
        { (*--  (| C |) = n' ---*)
          auto. }  }

      { (*----  H' <> G' ----*)
        assert (hsize: | H'| < | G'|).
        { assert (h3a: H' [<=] G'). apply h3.
          apply sub_neq_lt. all: auto. }
        
        set (H:= ind_at H' G).
        assert (h4: Ind_subgraph H G).
        { subst H. auto. }
        
        assert (h5: Perfect H).
        { eauto. }
        
        assert (h6: Compl H H').
        { subst H. unfold Compl.
          split.
          { simpl. symmetry; cut (H' [<=] G). auto. rewrite gg'; auto. }
          { intros x y hx hy. replace (edg (ind_at H' G) x y) with (edg G x y).
            replace (edg H' x y) with (edg G' x y).
            apply h;simpl in hx, hy. all: auto.   eauto.  eauto.
            symmetry;apply h3; simpl in hx, hy;eauto. }  }
        
        cut (Perfect H'). auto.
        eapply IH. exact hsize. exact h5. auto. }   } Qed.

  
 End WPGT.


 

  