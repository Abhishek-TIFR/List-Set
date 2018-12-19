







Require Export Lovasz.

Set Implicit Arguments.

Section LovaszRepLemma.

  Context { A:ordType }.

  Variable G: @UG A.
  Variable a a': A.
  Hypothesis P: In a G.
  Hypothesis P': ~In a' G.

  (* Let G':= Repeat_in G a a'. *)

  Lemma H'_sub_G (H': @UG A):
    Ind_subgraph H' (Repeat_in G a a') -> ~ In a' H' -> Ind_subgraph H' G.
  Proof. { intros h1 h2. unfold Ind_subgraph.
         assert (h3: H' [<=] G).
         { intros x h3.
           assert (h4: In x (Repeat_in G a a')).
           { apply h1. auto. }
           simpl in h4. cut (x<>a').  intro h5. eauto. intro h5. subst x. contradiction. } 
         split. auto.
         { destruct h1 as [h1a h1].
           intros x y h4 h5.
           replace (edg H' x y) with (edg (Repeat_in G a a') x y).
           symmetry. cut (In x G). cut (In y G). all: auto.
           symmetry;auto. } } Qed.

  Lemma H'_iso_G' (H' G': @UG A): Ind_subgraph H' G' -> H' [=] G'-> iso G' H'.
  Proof. { intros h1 C2.
            exists id. split.
             { unfold id; auto. } split.
             { apply set_equal. auto. auto. auto. }
             { unfold id. intros x y. symmetry.
               destruct (memb2 x y H') eqn: h2.
               { cut (In x H'). cut (In y H'). auto.
                 move /memb2P in h2; apply h2. move /memb2P in h2; apply h2. }
               { assert (h3: ~ In x H' \/ ~ In y H'). auto.
                 destruct h3 as [h3a | h3b].
                 { replace (edg H' x y) with false. symmetry. switch. intro h3.
                   assert (h4: In x G').
                   eapply no_edg1. apply h3. absurd (In x H'). auto. apply C2. auto.
                   symmetry. switch. intro h3. apply h3a. eapply no_edg1;eauto. }
                 { replace (edg H' x y) with false. symmetry. switch.
                   intro h3. assert (h4: In y G').
                   eapply no_edg2. apply h3. absurd (In y H'). auto. apply C2. auto.
                   symmetry. switch. intro h3. apply h3b. eapply no_edg2;eauto. } } } } Qed.

  Lemma RepeatH_iso_H' (H' G': @UG A): G'= Repeat_in G a a'-> Ind_subgraph H' G' -> In a H' ->
                                       In a' H'-> iso (Repeat_in (Ind_at H' G) a a') H'.
  Proof. { intros HeqG' h1 C1_b h3a. remember (Ind_at H' G) as H.
         assert (h0: H' [<=] G'). apply h1.
         assert (h0a: H [<=] H').
         { subst H; simpl; auto. }
         assert (h5: Ind_subgraph H G).
         { unfold Ind_subgraph. split.
          subst H; simpl; auto.
          subst H; simpl. intros x y h5 h6. symmetry. auto. }
          { exists id.
          split.
          (* first subgoal: forall x:A, id (id x) = x *)
          { intros; unfold id; auto. } split.
          (* second subgoal:  H' = img id (Repeat_in H a a') *)
          { subst H. simpl.
            replace (img id (add a' (inter H' G))) with (add a' (inter H' G)).
            apply set_equal. auto. auto. unfold Equal.
            split.
            { intros x h6.
              assert (h7: x = a' \/ x<> a'). eapply reflect_EM;eauto.
              destruct h7 as [h7a | h7b].
              subst x. auto.
              assert (h8: In x G).
              { cut (In x G'). subst G'. simpl. intros. eauto. auto. } auto. }
            { intros x h6.
              assert (h7: x = a' \/ In x (inter H' G)). auto.
              destruct h7 as [h7 | h7].
              subst x. auto. eauto. } apply id_is_identity. auto. }
          (* third subgoal: edg (Repeat_in H a a') x y = edg H' (id x) (id y) *)
          { simpl. unfold id. intros x y.
            unfold Ind_subgraph in h1.  unfold Ind_subgraph in h5.
            destruct (memb2 x y H') eqn: h7.
            { (* when both x and y is in H' *)
              assert (h8: In x H' /\ In y H'). move /memb2P in h7. auto.
              destruct h8 as [h8a h8b].
              replace (edg H' x y) with (edg G' x y).
              Focus 2. symmetry; apply h1;auto.
              assert (hx: x = a' \/ x <> a'). eauto.
              assert (hy: y = a' \/ y <> a'). eauto.
              destruct hx as [hx | hx]; destruct hy as [hy | hy].
              { (* when x= a' and y= a' *)
                subst x. subst y.  replace (edg G' a' a') with false.
                switch. replace (ex_edg H a a') with (edg (Repeat_in H a a')).
                eapply no_self_edg1. simpl. auto. symmetry. switch; auto. }
              { (* when x= a' and y <> a'*)
                assert (h8: In y H).
                { subst H. simpl. cut (In y G). auto.
                  cut (In y G'). subst G'. simpl. eauto. auto. } 
                assert (h9: y=a \/ y<>a). eauto.
                destruct h9 as [h9 |h9].
                { subst x. subst y.  replace (edg G' a' a) with true.
                replace (ex_edg H a a') with (edg (Repeat_in H a a')).
                cut ( edg (Repeat_in H a a') a a' = true). all: auto.
                symmetry. cut (edg G' a a' = true). auto. subst G'; auto. }
                { subst x. replace (ex_edg H a a' a' y) with (edg H a y).
                  replace (edg G' a' y) with (edg G a y).
                  apply h5. subst H. simpl. auto. auto. subst G'. auto.  
                  eapply Eay_eq_E'a'y; subst H; simpl;auto. intro h10.
                  absurd (In a' G);eauto. } }
              { (* when x <> a' and y = a' *)
                assert (h8: In x H).
                { subst H. simpl. cut (In x G). auto.
                  cut (In x G'). subst G'. simpl. eauto. auto. } 
                assert (h9: x=a \/ x<>a). eauto.
                destruct h9 as [h9 |h9].
                { subst x. subst y.  replace (edg G' a a') with true.
                replace (ex_edg H a a') with (edg (Repeat_in H a a')); auto.
                symmetry;subst G'; auto. }
                { subst y. replace (ex_edg H a a' x a') with (edg H x a).
                  replace (edg G' x a') with (edg G x a).
                  apply h5; subst H; simpl; auto. subst G'; auto.  
                  eapply Exa_eq_E'xa'; subst H; simpl;auto. intro h10.
                  absurd (In a' G);eauto. } }
              { (* when x <> a' and y <> a'*)
                assert (hx1: In x H).
                { subst H. simpl. cut (In x G). auto.
                  cut (In x G'). subst G'. simpl. eauto. auto. }
                assert (hy1: In y H).
                { subst H. simpl. cut (In y G). auto.
                  cut (In y G'). subst G'. simpl. eauto. auto. }
                replace (ex_edg H a a' x y) with (edg H x y).
                replace (edg H x y) with (edg G x y).
                cut (In x G). cut (In y G). subst G';auto.
                subst H; simpl in hy1;simpl in hx1;eauto.
                subst H; simpl in hy1;simpl in hx1;eauto.
                symmetry;apply h5;auto.  apply Exy_eq_E'xy; subst H; simpl.
                auto. intro h10. absurd (In a' G). auto. eauto. all: auto. }  }
            { (* when either x or y is not in H'*)
              assert (h8: ~ In x H' \/ ~ In y H'). auto.
              destruct h8 as [h8 | h8].
              { replace (edg H' x y) with false. 
                replace (ex_edg H a a') with (edg (Repeat_in H a a')). switch.
                cut (~ In x (Repeat_in H a a')).  eauto.
                simpl. subst H. simpl. intro h9. assert (h10: x=a' \/ In x (inter H' G)).
                auto.  destruct h10 as [h10 | h10].
                subst x;contradiction. absurd (In x H'); eauto. simpl;auto.
                symmetry. switch. intro h9;apply h8. eapply no_edg1;eauto. }
               { replace (edg H' x y) with false. 
                replace (ex_edg H a a') with (edg (Repeat_in H a a')). switch.
                cut (~ In y (Repeat_in H a a')).  eauto.
                simpl. subst H. simpl. intro h9. assert (h10: y=a' \/ In y (inter H' G)).
                auto.  destruct h10 as [h10 | h10].
                subst y;contradiction. absurd (In y H'); eauto. simpl;auto.
                symmetry; switch. intro h9;apply h8. eapply no_edg1;eauto. } } } } } Qed.   
         

  Lemma cliq_in_G' (K: list A): In a K ->  Cliq_in G K ->  Cliq_in (Repeat_in G a a') (add a' K).
  Proof.  { intros h1 h2. assert (h2b: K [<=] G). auto.
          assert (h2c: IsOrd K). eauto. assert (h2d: Cliq G K). auto.
          unfold Cliq in h2d.
          unfold Cliq_in. split. simpl;auto. split. auto.
          unfold Cliq. intros x y h4 h5.
            assert (h4a: x= a' \/ In x K). auto.
            assert (h5a: y= a' \/ In y K). auto.
            destruct h4a as [h4a | h4a]; destruct h5a as [h5a | h5a].
            { subst x; subst y; left; auto. }
            { subst x;right. cut(a = y \/ edg G a y= true). 
              intro h6. destruct h6 as [h6 | h6]. subst y; apply sym_edg; eauto. auto.
              apply h2d;auto. }
             { subst y;right. cut(x = a \/ edg G x a = true). 
              intro h6. destruct h6 as [h6 | h6]. subst x;eauto. auto.
              apply h2d;auto. }
             { assert (h6: x = y \/ edg G x y). auto. destruct h6 as [h6 | h6].
               left;auto. right. cut (In x G). cut (In y G). all: auto. } } Qed.
             
  
  Lemma max_K_in_G' (K': list A)(n:nat): cliq_num G n -> Cliq_in (Repeat_in G a a') K' -> |K'| <= n+1.
  Proof. { intros h1 h2. assert (h3: In a' K' \/ ~ In a' K'). eauto.
         destruct h3 as [h3 | h3].
         { (* In this case K' \ a' is a cliq in G *)
           assert (h4: (rmv a' K') [<=] G).
           { intros x h4. destruct h2 as [h2a h2]. destruct h2 as [h2b h2].
             cut (In x (add a' G)). cut (x<>a'). eauto. cut (NoDup K'); eauto.
             cut (In x K'). auto. eauto. }
           assert (h5: Cliq_in G (rmv a' K')).
           { destruct h2 as [h2a h2];destruct h2 as [h2b h2]. split. auto. split. 
             auto. unfold Cliq in h2. unfold Cliq. intros x y h5 h6.
             replace (edg G x y) with (edg (Repeat_in G a a') x y).
             apply h2;eauto. symmetry. cut (In x G). cut (In y G). all: auto. }
           assert (h6: | rmv a' K' | <= n). 
           { destruct h1 as [K h1]. destruct h1 as [h1 h1a].
             subst n. eapply Max_K_in_elim;eauto. }
           assert (h7: (| rmv a' K' |) = |K'| - 1). auto. omega. }
         { (* In this case K' is a cliq in G *)
           assert (h4: K' [<=] G).
           { intros x h4. destruct h2 as [h2a h2];destruct h2 as [h2b h2].
             cut (In x (add a' G)). cut (x<>a'). eauto.
             intros h5;subst x. contradiction. auto. }
           assert (h5: Cliq_in G K').
           { destruct h2 as [h2a h2];destruct h2 as [h2b h2]. split. auto. split. 
             auto. unfold Cliq in h2. unfold Cliq. intros x y h5 h6.
             replace (edg G x y) with (edg (Repeat_in G a a') x y).
             apply h2;eauto. symmetry. cut (In x G). cut (In y G). all: auto. }
           assert (h6: |K'| <= n).
           { destruct h1 as [K h1]. destruct h1 as [h1 h1a].
             subst n. eapply Max_K_in_elim;eauto. } omega. } } Qed. 
  
                                            
  Lemma ReplicationLemma: Perfect G -> Perfect (Repeat_in G a a').
  Proof. {

   (* We will prove the result by well founded induction on the set of all UG. 
      To use the well founded induction we first need to prove that the relation 
      lt_graph is well founded on UG. This is proved as Lemma lt_graph_is_well_founded
      in the file DecUG.v. *) 
    revert a a' P P'. pattern G. revert G.
    apply well_founded_ind with (R:= @lt_graph A).  apply lt_graph_is_well_founded.
    intros G IH a a' P P' h.

    remember (Repeat_in G a a') as G'.
    unfold lt_graph in IH.
    
    unfold Perfect. intros H' h1.
    assert (h0: H' [<=] G'). apply h1.
    
    (* remember (Ind_at (rmv a G') G') as G'_a. *)

    (* We break the proof in two cases (C1 and C2).
       C1 is the case when  H' is not equal to G' (i.e H' <> G'). 
       C2 is the case when H' is same as G' (i.e. H' = G').  *)
    assert (HC: Equal H' G' \/ ~ Equal H' G'). eapply reflect_EM; eauto.
    destruct HC as [C2 | C1].

    (* Case C2 (H' = G'): Proof ---------------------------------------------------- *)
    { (* C2: In this case H' [=] G'.
         We further split this case into two subcases C2a and C2b.
         C2_a is the case when a is present in some largest clique K in G.
         C2_b is the case when a is not present in any largest clique of G. *)
      
      assert (h_iso: iso G' H'). apply H'_iso_G';auto.
      cut(Nice G'). eauto.
      
      set (Pb:= fun K => max_K_in G K && memb a K). 
      specialize (exists_em_forall Pb (pw G)) as HC.
      unfold Pb in HC.
      destruct HC as [C2_a | C2_b].
      { (* C2_a : when a is present in some largest clique K of G.  *)
        destruct C2_a as [K C2_a]. destruct C2_a as [C2a C2b].
        move /andP in C2b. destruct C2b as [h2 h3]. move /max_K_inP in h2.
        move /membP in h3.  assert (h2a: Cliq_in G K). auto.
        assert (h2b: K [<=] G). auto. assert (h2c: IsOrd K). eauto.
        assert (h2d: Cliq G K). auto.
        
        (* preprocessing ends and  main proof starts *)
        apply nice_intro with (n:=|K|+1). unfold cliq_num.
        exists (add a' K).
        split.
        {(* Max_K_in G' (add a' K) *)
          apply Max_K_in_intro.
          subst G'; apply cliq_in_G';auto.
          intros K' h4. replace (| add a' K|) with (|K|+1).
          eapply max_K_in_G'. exists K.
          split;auto. subst G'; auto. symmetry. replace (|K|+1) with (S(|K|)).
          apply add_card1. auto. omega. }
        { replace (|K|+1) with (S(|K|)). apply add_card1. auto. omega. }
        { (* exists f : A -> nat, Coloring_of G' f /\ (| clrs_of f G' |) = (| K |) + 1  *)
          assert (h4: Nice G). auto. unfold Nice in h4.
          specialize (h4 (|K|)). assert (h5: cliq_num G (|K|) ). exists K. split;auto.
          specialize (h4 h5) as h6. destruct h6 as [f h6]. destruct h6 as [h6a h6b].
          destruct h6a as [h6a h6c].
          (* c0 as defined below is the new color for a' *)
          set (c0 := maxin (Nat.leb) (img f G) 0 + 1).
          assert (hc0: ~ In c0 (img f G)).
          { intro h7. eapply maxin_spec with (lr:= Nat.leb )(d:=0) in h7.
            revert h7. unfold c0. move /leP. intro h7.
            remember (maxin Nat.leb (img f G) 0) as n0. omega. all: auto.  }
          (* following function f0 is the new coloring for graph G' *)
          set (f0:= fun x:A => match x == a' with
                            |true => c0
                            |false => f x
                            end ).
          exists f0.
          assert (hf0: forall x, x<> a' ->  f x = f0 x).
          { intros x h7. unfold f0. destruct (x== a') eqn: h8.
            move /eqP in h8. contradiction. auto. }
          assert (h1f0: forall x, In x G -> f x = f0 x).
          { intros x h7. cut (x <> a'). auto. intro h8; subst x; contradiction. } 
          assert (h2f0: f0 a' = c0).
          { unfold f0. replace (a'==a') with true. auto. symmetry;auto. } 
           split.  
          {(* proof that f0 is a coloring of G' *)
            unfold Coloring_of. intros x y h7 h8 h9. unfold f0.
            destruct (x==a') eqn: hxa; destruct (y == a') eqn: hya.
            { move /eqP in hxa;move /eqP in hya. subst x;subst y. absurd (edg G' a' a'); auto. }
            { move /eqP in hya. assert (h10: In y G).
              { subst G';simpl in h7;simpl in h8; eauto. }
              intro h11. absurd (In c0 (img f G)). auto. rewrite h11. auto. }
            { move /eqP in hxa. assert (h10: In x G).
              { subst G';simpl in h7;simpl in h8; eauto. }
               intro h11. absurd (In c0 (img f G)). auto. rewrite <- h11. auto. }
            { move /eqP in hxa. move /eqP in hya. cut (In x G). cut (In y G).
               intros. apply h6a. all: auto. replace (edg G x y) with (edg G' x y).
               auto. symmetry. subst G'. auto.
               all: subst G';simpl in h7;simpl in h8; eauto. } }
          {(* proof that  (| clrs_of f0 G' |) = (| K |) + 1 *)
            unfold Coloring_of in h6a.
            subst G'. simpl. unfold clrs_of.
            replace (img f0 (add a' G)) with (add (f0 a') (img f0 G)).
            replace (img f0 G) with (img f G). replace (f0 a') with c0.
            rewrite <- h6b. unfold clrs_of.
            assert (h11: (| img f G |) + 1 = S (| img f G |)). omega.
            rewrite h11. eapply add_card1. all: auto. } }
        } 

      { (* C2_b : when a is not present in any largest clique of G. *)
        assert (C2b: forall K, Cliq_in G K -> In a K -> ~ Max_K_in G K).
        { intros K h2 h3 h4.
          absurd (max_K_in G K && memb a K).
          { apply C2_b. apply pw_intro.
            assert (h4a: Cliq_in G K). auto. all: auto. eauto. }
          { split_. apply /max_K_inP; auto. apply /membP;auto. } }
        assert (h2: forall K, Max_K_in G K-> ~ In a K). 
        { intros K h2 h3. absurd (Max_K_in G K); auto. }
        destruct (cliq_num_of G) as [wG h3]. destruct (cliq_num_of G') as [wG' h4].
        (* preprocessing ends and main proof starts *) 
        
        assert (h5a: wG <= wG').
        { apply cliq_num_HG with (H:=G)(G0:=G'). subst G'. all: auto. }
        
        (* largest cliq of G and G' has same size *)
        assert (h5: wG = wG').
        { cut (wG' <= wG). omega.
          destruct h3 as [K h3]. destruct h3 as [h3a h3].
          destruct h4 as [K' h4]. destruct h4 as [h4a h4].
          assert (h6: In a' K' \/ ~ In a' K'). eauto.
          assert (h16: Cliq_in G K). auto. assert (h17: Cliq_in G' K'). auto.
          destruct h16 as [h16a h16]. destruct h16 as [h16b h16].
          destruct h17 as [h17a h17]. destruct h17 as [h17b h17].
          destruct h6 as [h6 | h6].
          { (* both a and a' are in K' *)
            assert (h6a: In a K').
            { assert (h7: In a K' \/ ~ In a K'). eauto.
              destruct h7 as [h7 | h7]. auto.
              assert (h8: Cliq_in G' (add a K')).
              { assert (h8: add a K' [<=] G'). 
                { intros x h8. cut (x=a \/ In x K'). intro h9. destruct h9 as [h9 |h9].
                  subst x. subst G'. simpl. cut (In a G); auto. auto. auto. }
                split. auto. split. auto. unfold Cliq. unfold Cliq in h17.
                intros x y h9 h10.
                assert (hx: In x K' \/ ~ In x K'). eauto.
                assert (hy: In y K' \/ ~ In y K'). eauto.
                destruct hx as [hx | hx]; destruct hy as [hy | hy].
                { auto. }
                { assert (h11: y=a). eauto. subst y.
                  assert (h12: x = a' \/ x <> a'). eauto.
                  destruct h12 as [h12 | h12].
                  { subst x. right. subst G'. apply sym_edg. apply edg_aa';auto. }
                  { assert (h13: x = a' \/ edg G' x a'). auto. destruct h13.
                    contradiction. right. subst G'. eapply E'xa'_E'xa;auto.
                    intro h13; subst x; contradiction. } }
                { assert (h11: x=a). eauto. subst x.
                  assert (h12: y = a' \/ y <> a'). eauto.
                  destruct h12 as [h12 | h12].
                  { subst y. right. subst G'. apply edg_aa';auto. }
                  { assert (h13: a'= y  \/ edg G' a' y). auto. destruct h13.
                    symmetry in H. contradiction. right.
                    subst G'. apply sym_edg. eapply E'xa'_E'xa;auto.
                    intro h13; subst y; contradiction. } }
                { assert (h11: x = a). eauto. assert (h12: y = a). eauto. left;subst x;auto. } }
              assert (h9: |(add a K')| <= |K'|). eapply Max_K_in_elim. eauto.
              apply h8. assert (h10: | add a K'|= S (|K'|)). auto. omega. } 
            
            assert (h7: Cliq_in G (rmv a' K')).
            { unfold Cliq_in.
              assert (h18: rmv a' K' [<=] G).
              { intros x h7. cut (In x (add a' G)). cut (x <> a').
                eauto. cut (NoDup K'); eauto. cut (In x K'). subst G'. auto. eauto. }
              split. auto.   split. auto.
              unfold Cliq. unfold Cliq in h17. intros x y h7 h8.
              replace (edg G x y) with (edg G' x y). apply h17;eauto.
              symmetry. subst G'. cut (In x G). cut (In y G). all: auto. } 
            assert (h8: In a (rmv a' K')).
            { cut (a<>a'). auto. intro H. subst a;contradiction. }
            
            assert (h9: |(rmv a' K')| < wG).
            { subst wG.
              cut ((| rmv a' K' |) <= (| K |)). cut ((| rmv a' K' |) <> (| K |)). omega.
              intro H1. absurd (Max_K_in G (rmv a' K')). apply C2b;auto.
              apply Max_K_in_intro. auto. rewrite H1; eauto using Max_K_in_elim.
              eauto using Max_K_in_elim. }
            
            assert (h10: |(rmv a' K')| = |K'| - 1). auto. omega. }
          
          { assert (h7: Cliq_in G K').
            { assert (h7a: K' [<=] G).
              { subst G'. intros x H1. cut (In x (add a' G)). cut (x<>a'). eauto.
                intros H2. subst x. contradiction. auto. }
              unfold Cliq_in. split. auto. split. auto.
              unfold Cliq. intros x y H1 H2. replace (edg G x y) with (edg G' x y).
              apply h17;auto. symmetry. cut (In x G). cut (In y G). subst G'. all: auto. }
            
            assert (h8: |K'| <= wG). subst wG. eapply Max_K_in_elim;eauto. omega. } } 
        
        assert(h6: Nice G); auto. unfold Nice in h6. apply h6 in h3 as h7;destruct h7 as [f h7].
        destruct h7 as [hX1 hX]. assert (hX2: Coloring_of G f). apply hX1. clear h6. clear hX1.
        (*let f be coloring of G which uses wG colors*)
        set (Ns := filter (fun x=> ( negb (f x == f a) || (x == a))) G).
       
        (* a' is not connected to any vertices outside Ns *)
        
        assert (hNs_G: forall x, In x Ns -> (In x G /\ ( (~~(f x == f a)) || (x == a))= true)).
        { intros x.  eapply filter_In. }
        remember (fun x => ( (~~(f x == f a)) || (x == a))) as Ps.
        assert (HPs: forall x, Ps x = ( (~~(f x == f a)) || (x == a)) ).
        { subst Ps. auto. } 
        assert (hG_Ns: forall x, (In x G) /\ (( ~~(f x == f a) || (x == a)) = true) -> In x Ns ).
        { intros x.  rewrite <- (HPs x). unfold Ns. eapply filter_In. }
        subst Ps.
        assert (h6a: forall x, In x Ns -> In x G).
        { intros x H1; apply hNs_G; auto. }
        assert (h6b: forall x, In x Ns -> (~~(f x == f a) || (x == a))= true ).
        { intros x H1. apply hNs_G. auto. }
        assert (h6c: forall x, In x Ns -> f x <> f a \/ x = a).
        { intros x H1. apply h6b in H1 as H2. move /orP in H2.
          destruct H2 as [H | H]. left. move /negP in H.
          intro H2. apply H. apply /eqP. auto. move /eqP in H. subst x;right;auto. }
        assert (h6d: forall x, ~ In x Ns -> ~ edg G x a).
        { unfold Coloring_of in hX2.  intros x H1 H2. apply H1.
          apply filter_In. split. eapply no_edg1. apply H2.
          left_. apply /negP. cut (f x <> f a). auto.
          apply hX2. eapply no_edg1; eauto. eapply no_edg1; eauto. auto. }
        assert (h6e: In a Ns).
        { apply filter_In. split. auto. right_. auto. } 
        assert (h6: forall x, ~ In x Ns -> ~ edg G' x a').
        { intros x H1.
          assert(H2: x<> a). intros H2; subst x; contradiction.
          cut (~ edg G x a). intros H3 H4;apply H3.
          cut(x<>a'). subst G'. eauto. intros H5. subst x. revert H4. eauto. auto. }
        clear hNs_G. clear h6b.

        set (Gs:= Ind_at Ns G). destruct (cliq_num_of Gs) as [wGs h7].
        assert(h_Gs_nice: Nice Gs).
        { cut (Ind_subgraph Gs G). auto. unfold Gs. auto. }
        unfold Nice in h_Gs_nice. apply h_Gs_nice in h7 as h8. destruct h8 as [fs h8].
        clear h_Gs_nice.
        
        (* largest cliq of G_star is smaller than that of G *)
        assert (h9: wGs < wG).
        { assert (H1: Ind_subgraph Gs G). unfold Gs. auto. 
          assert (H2: wGs <= wG). eauto.
          assert (H3: wGs = wG \/ wGs <> wG). eauto.
          destruct H3 as [H3 | H3]. Focus 2. omega.
          (* assuming H3:  wGs = wG we will show some contradiction *)
          destruct h7 as [Ks H7]. destruct H7 as [H7a H7].
          assert (H4: In a Ks).
          { assert (H4a: In a Gs).
            { unfold Gs. simpl. cut (In a Ns). auto. apply filter_In.
              split. auto. right_. auto. }
            assert (H4b: Ks [<=] Gs).
            { apply H7a. }
            assert (H4f: (img f Ks) [<=] (img f Gs)).
            { auto. }
            assert (H4: In a Ks \/ ~ In a Ks). eauto.
            destruct H4 as [H4 | H4]. auto.
            assert (H4c: forall x, In x Gs -> x <> a -> f x <> f a).
            { intros x H5 H6.
              assert (H8: f x <> f a \/ x = a). apply h6c. simpl in H5. eauto.
              destruct H8. auto. contradiction. }
            assert (H4d: ~ In (f a) (img f Ks)).
            { intro H8. assert (H9: exists x, In x Ks /\ f a = f x). eauto.
              destruct H9 as [x H9]. destruct H9 as [H9 H10].
              absurd (f x = f a). apply H4c. auto. intro Hx. subst x. contradiction.
              symmetry;auto. }
            assert (H4e: In (f a) (img f Gs)).
            { auto. }
            assert (H4g: |img f Ks| < |img f Gs|).
            { eauto. }
            
            assert (H4h: |img f Ks| = |Ks|).  admit.
            assert (H4i: | img f Gs | = wGs). admit.
            rewrite H4i in H4g. rewrite H7 in H4h. omega. }
            
          assert (H5: Max_K_in G Ks).
          { apply Max_K_in_intro. cut (Cliq_in Gs Ks). eauto.  auto.
            rewrite H7. rewrite H3.  destruct h3 as [K h3]. destruct h3 as [h3a h3].
            rewrite <- h3.  intros K' H5. eapply Max_K_in_elim. eauto. auto. }
          absurd (Max_K_in G Ks). apply C2b; auto. auto. }
          
          
        (* c0 is the color not used by fs for coloring any vertex of Gs *)
        set (c0 := maxin (Nat.leb) (img fs Gs) 0 + 1).
          assert (hc0: ~ In c0 (img fs Gs)).
          { intro h17. eapply maxin_spec with (lr:= Nat.leb )(d:=0) in h17.
            revert h17. unfold c0. move /leP. intro h17.
            remember (maxin Nat.leb (img fs Gs) 0) as n0. omega. all: auto.  }
          
        (* a new coloring scheme f' for G' *)
        set (f':= fun x:A => match (memb x Gs) with
                          |true => (fs x)
                          |false => c0
                          end ).
          assert (hfa': f' a' = c0).
          { unfold f'. replace (memb a' Gs) with false. auto.
            symmetry. apply /membP. intro H1. simpl in H1.
            absurd (In a' G). auto. eauto. }
          assert (Hf'1: forall x, In x Gs -> f' x = fs x).
          { intros x H1. unfold f'. replace (memb x Gs) with true. auto. symmetry;auto. }
          assert (Hf'2:forall x, ~ In x Gs -> f' x = c0 ).
          { intros x H1;unfold f'. replace (memb x Gs) with false. auto. symmetry;auto. }
          assert (h_clrs: (clrs_of f' G') = add c0 (clrs_of fs Gs)).
          { apply set_equal; unfold clrs_of;auto. split.
            { replace (nodes G') with (Gs [u] (G' [\] Gs)).
              { replace (img f' (Gs [u] (G' [\] Gs))) with (img f' Gs [u] img f' (G' [\] Gs)).
                Focus 2. symmetry;auto. replace (img f' Gs) with (img fs Gs).
                Focus 2. symmetry;auto. intros fx H1.
                assert (H1a: In fx (img fs Gs) \/ In fx (img f' (G' [\] Gs))). auto.
                destruct H1a as [H1a | H1b].
                { auto. }
                { assert (H2: exists x, In x (G' [\] Gs) /\ fx = f' x). auto.
                  destruct H2 as [x H2]. destruct H2 as [H2a H2b].
                  assert (H3: ~ In x Gs). eauto. replace fx with c0. auto.
                  subst fx. symmetry;auto. } }
              { symmetry. cut (Gs [<=] G'). auto. cut (Gs [<=] G). cut (G [<=] G').
                auto. subst G';simpl. intros x; auto. unfold Gs. simpl. auto. } }
            { intros fx H1. assert (H2: fx = c0 \/ In fx (img fs Gs)). auto.
              destruct H2 as [H2a | H2b].
              { subst fx. rewrite <- hfa'. cut (In a' G'); auto. subst G';simpl;auto. }
              { replace (nodes G') with (Gs [u] (G' [\] Gs)).
                Focus 2.
                symmetry. cut (Gs [<=] G'). auto. cut (Gs [<=] G). cut (G [<=] G').
                auto. subst G';simpl. intros x; auto. unfold Gs. simpl. auto.
                replace (img f' (Gs [u] (G' [\] Gs))) with (img f' Gs [u] img f' (G' [\] Gs)).
                Focus 2. symmetry;auto. replace (img f' Gs) with (img fs Gs).
                Focus 2. symmetry;auto. auto. } } } 
              
          eapply nice_intro with (n:= wG'). auto.
          exists f'.
          assert (h10: Coloring_of G' f').  
          { assert (h11: Ind_subgraph Gs G). unfold Gs. auto.
            assert (h12: Ind_subgraph G G'). subst G'. auto.
            destruct h11 as [h11a h11]. destruct h12 as [h12a h12].
            assert (H0: Coloring_of Gs fs). apply h8. 
            unfold Coloring_of. intros x y H1 H2 H3. unfold f'.
            
            destruct (memb x Gs) eqn: Hx; destruct (memb y Gs) eqn: Hy.
            { apply H0;auto. replace (edg Gs x y) with (edg G x y).
              replace (edg G x y) with (edg G' x y). auto.
              symmetry; apply h12; auto. symmetry; apply h11; auto. }
            { intro H4. absurd (In c0 (img fs Gs)). auto. rewrite <- H4. auto. }
            { intro H4. absurd (In c0 (img fs Gs)). auto. rewrite  H4. auto. }
            { move /membP in Hx. move /membP in Hy. simpl in Hx. simpl in Hy.
               assert (Hx1: x = a' \/ x <> a'). eauto.
              assert (Hy1: y = a' \/ y <> a'). eauto.
              destruct Hx1 as [Hx1 | Hx1]. 
              { subst x. absurd (edg G' y a'). apply h6. intro H4. apply Hy.
                cut (In y G); auto. auto. }
              { destruct Hy1 as [Hy1 | Hy1].
                { subst y. absurd (edg G' x a'). apply h6. intro H4. apply Hx.
                  cut (In x G); auto. auto. }
                { unfold Coloring_of in hX2. 
                  assert (H4: In x G). subst G'; simpl in H1; eauto.
                  assert (H5: In y G). subst G'; simpl in H2; eauto.
                  assert (H6: edg G x y).
                  { replace (edg G x y) with (edg G' x y). auto. symmetry;subst G';auto. }
                  absurd (f x = f y). auto.
                  replace (f x) with (f a). replace (f y) with (f a). auto.
                  { replace (Ns [i] G) with (Ns) in Hx. replace (Ns [i] G) with (Ns) in Hy.
                    symmetry.
                    assert (H7: f y = f a \/ f y <> f a). eauto.
                    destruct H7 as [H7 | H7]. auto.
                    absurd (In y Ns). auto. apply hG_Ns. split. auto.
                    left_.  apply /negP. auto.  cut (Ns [<=] G). cut (IsOrd Ns).
                    auto. unfold Ns. auto. auto. cut (Ns [<=] G). cut (IsOrd Ns).
                    auto. unfold Ns. auto. auto. }
                  { replace (Ns [i] G) with (Ns) in Hx. replace (Ns [i] G) with (Ns) in Hy.
                    symmetry.
                    assert (H7: f x = f a \/ f x <> f a). eauto.
                    destruct H7 as [H7 | H7]. auto.
                    absurd (In x Ns). auto. apply hG_Ns. split. auto.
                    left_.  apply /negP. auto.  cut (Ns [<=] G). cut (IsOrd Ns).
                    auto. unfold Ns. auto. auto. cut (Ns [<=] G). cut (IsOrd Ns).
                    auto. unfold Ns. auto. auto. } } } } } 
            
          split. auto.
          assert (h_triv: (| clrs_of f' G' |) >= wG'). auto.
          cut ((| clrs_of f' G' |) <= wG'). omega.
          rewrite h_clrs. unfold clrs_of.
          assert (H1: |add c0 (img fs Gs)| = S (|img fs Gs |)). auto.
          rewrite H1. destruct h8 as [h8a h8]. rewrite h8. omega. } 
    } (*---------- End of Case C2 -------------------------------------------------- *)

    
    (* Case C1 (H' <> G'): Proof --------------------------------------------------- *)
    { (* C1: In this case ~ H' [=] G'. This means that H' is strictly included in G'.
         We further split this case into two subcases C1a and C1b. 
         C1_a is the case when a is not present in H' (i.e. ~ In a H').
         C1_b is the case when a is present in H' (i.e. In a H').  *)
      assert (h2: exists x, In x G' /\ ~ In x H').
      { assert (h3: forall x, In x H' \/ ~ In x H'). intros x. eapply reflect_EM;auto.
        eapply forall_exists_EM with (l:= G') in h3.
        destruct h3 as [h3 | h3].
        assert (H' [=] G'). cut (G' [<=] H'). auto. auto. contradiction. auto. }
      
      destruct h2 as [x0 h2]. 
      assert (HC: In a H' \/ ~ In a H'). eapply reflect_EM; eauto.
      destruct HC as [C1_b | C1_a].
      
      (* Case C1_b ( In a H'): Proof ----------------------------- *)
      { assert (h3: In a' H' \/ ~ In a' H'). eapply reflect_EM;eauto.
        destruct h3 as [h3a | h3b].
        (* subcase In a' H': In this case we use IH *) 
        remember (Ind_at  H' G) as H.
        assert (h0a: H [<=] H').
        { subst H; simpl; auto. }
        assert ( h4: |H| < |G|).
        { apply subset_cardinal_lt with (a0:= x0). auto.
          subst H. simpl. auto.
          assert (h5: x0 <> a').
          { intro. subst x0. destruct h2. contradiction. }
          destruct h2 as [h2 h2a]. subst G'. simpl in h2. eauto.
          destruct h2 as [h2 h2a].
          subst H. simpl. intro h3. absurd (In x0 H'). auto. eauto. }
        assert (h5: Ind_subgraph H G).
        { unfold Ind_subgraph. split.
          subst H; simpl; auto.
          subst H; simpl. intros x y h5 h6. symmetry. auto. }
        assert (h6: iso (Repeat_in H a a') H').
        { subst H. apply RepeatH_iso_H' with (G':=G');auto. }
        cut (Nice (Repeat_in H a a')). eauto.
        cut (Perfect (Repeat_in H a a')). auto.
        apply IH. auto. subst H; simpl; auto. subst H; simpl; auto. eauto. eauto.
        (* subcase ~In a' H': In this case Ind_subgraph H' G *)
        assert (h3: Ind_subgraph H' G). subst G'.  eauto using H'_sub_G. auto. }
      
      remember (Ind_at (rmv a G') G') as G'_a.
      (* Case C1_a (~ In a H'): Proof ---------------------------- *)
      { assert (h3: In a' H' \/ ~ In a' H'). eapply reflect_EM;eauto.
        destruct h3 as [h3a | h3b].
        (* subcase In a' H': In this case Ind_subgraph H' G'_a  *) 
        assert (h3: Ind_subgraph H' G'_a).
        { unfold Ind_subgraph. simpl. unfold Ind_subgraph in h1.
          assert (h4: H' [<=] rmv a G').
          { intros x h4. cut(In x G'). cut (x <> a). auto.
            intro. subst x. contradiction. auto. }
          split. subst G'_a. subst G'. rewrite <- NG'_a. auto.  intros x y h5 h6.
          replace (edg H' x y) with (edg G' x y). subst G'_a.
          apply edg_equal_at_K;replace (inter (rmv a G') G') with (rmv a G');auto;
            apply set_equal. all: auto.
          cut (rmv a G' [<=] G'); auto. cut (rmv a G' [<=] G'); auto.
          symmetry; apply h1;auto. }
        assert (h4: iso G G'_a).
        { subst G'_a. subst G'. eapply G_isomorphic_G'_a with (G0:=G)(a0:=a)(a'0:=a');auto. }
        destruct h4 as [f h4].
        assert (h5: exists H, Ind_subgraph H G /\ iso_using f H' H).
        { eapply iso_subgraphs. Focus 2. apply h3. auto. }
        destruct h5 as [H h5]. destruct h5 as [h5 h6].
        cut(iso H H'). cut (Nice H). eauto. auto. eauto.
        (* subcase ~In a' H': In this case Ind_subgraph H' G *)
        assert (h3: Ind_subgraph H' G). subst G'. eauto using H'_sub_G. auto. }  }
    (*----------- End of Case C1 -------------------------------------------------- *) 

    }  Admitted.  
      
  
  End LovaszRepLemma.