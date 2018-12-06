







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

  Lemma ReplicationLemma: Perfect G -> Perfect (Repeat_in G a a').
  Proof. {

   (* We will prove the result by well founded induction on the set of all UG. 
      To use the well founded induction we first need to prove that the relation 
      lt_graph is well founded on UG. This is proved as Lemma lt_graph_is_well_founded
      in the file DecUG.v. *) 
    revert a a' P P'. pattern G. revert G.
    apply well_founded_ind with (R:= @lt_graph A).  apply lt_graph_is_well_founded.
    intros G IH a a' P P' h. remember (Repeat_in G a a') as G'.
    unfold lt_graph in IH.
    
    unfold Perfect. intros H' h1.
    assert (h0: H' [<=] G'). apply h1.
    
    remember (Ind_at (rmv a G') G') as G'_a.

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
    
      admit.
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
        { exists id.
          split.
          (* first subgoal: forall x:A, id (id x) = x *)
          { intros; unfold id; auto. } split.
          (* second subgoal:  H' = s_map id (Repeat_in H a a') *)
          { subst H. simpl.
            replace (s_map id (add a' (inter H' G))) with (add a' (inter H' G)).
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
                assert (hx1: In x H). admit.
                assert (hy1: In y H). admit.
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
                symmetry; switch. intro h9;apply h8. eapply no_edg1;eauto. } }   }  } 
        
        cut (Nice (Repeat_in H a a')). eauto.
        cut (Perfect (Repeat_in H a a')). auto.
        apply IH. auto. subst H; simpl; auto. subst H; simpl; auto. eauto. eauto.
        (* subcase ~In a' H': In this case Ind_subgraph H' G *)
        assert (h3: Ind_subgraph H' G). subst G'.  eauto using H'_sub_G. auto. }

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