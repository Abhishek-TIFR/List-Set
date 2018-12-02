







Require Export Lovasz.

Set Implicit Arguments.

Section LovaszRepLemma.

  Context { A:ordType }.

  Variable G: @UG A.
  Variable a a': A.
  Hypothesis P: In a G.
  Hypothesis P': ~In a' G.

  (* Let G':= Repeat_in G a a'. *)

  Let id:= fun (x:A)=> x.

  Lemma id_is_identity (l:list A)(hl: IsOrd l): l = s_map id l.
  Proof. Admitted.
  
  Lemma H'_sub_G (H': @UG A):
    Ind_subgraph H' (Repeat_in G a a') -> ~ In a' H' -> Ind_subgraph H' G.
  Proof. Admitted.

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
    assert (N'_a: IsOrd (rmv a G')). subst G'. simpl. auto.
    assert (N: IsOrd G). auto.

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
      assert (h2: exists x, In x G' /\ ~ In x H'). admit.
      destruct h2 as [x0 h2]. 
      assert (HC: In a H' \/ ~ In a H'). eapply reflect_EM; eauto.
      destruct HC as [C1_b | C1_a].
      
      (* Case C1_b ( In a H'): Proof ----------------------------- *)
      { assert (h3: In a' H' \/ ~ In a' H'). eapply reflect_EM;eauto.
        destruct h3 as [h3a | h3b].
        (* subcase In a' H': In this case   *)
        assert (NH: IsOrd (inter G H')). auto.
        remember (Ind_at NH H') as H.
        
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
          subst H; simpl. intros x y h5 h6.
           assert (h5a: In x G). eauto. assert (h6a: In y G). eauto.
          unfold Ind_subgraph in h1.  destruct h1 as [h1a h1].
          replace ((edg H' at_ inter G H') x y) with  (edg H' x y).
          replace (edg G x y) with (edg G' x y).
          apply h1;eauto.
          symmetry; subst G'; auto. auto. }
        
        assert (h6: iso (Repeat_in H a a') H').
        { exists id.
          split.
          { intros; unfold id; auto. } split.
          { subst H. simpl.
            replace (s_map id (add a' (inter G H'))) with (add a' (inter G H')).
            apply set_equal. auto. auto. unfold Equal.
            split.
            { intros x h6.
              assert (h7: x = a' \/ x<> a'). eapply reflect_EM;eauto.
              destruct h7 as [h7a | h7b].
              subst x. auto.
              assert (h8: In x G).
              { cut (In x G'). subst G'. simpl. intros. eauto. auto. }
              auto. }
            { intros x h6.
              assert (h7: x = a' \/ In x (inter G H')). auto.
              destruct h7 as [h7 | h7].
              subst x. auto. eauto. }
            apply id_is_identity. auto. }
          { simpl. unfold id. admit. } }
        
        cut (Nice (Repeat_in H a a')). eauto.
        cut (Perfect (Repeat_in H a a')). auto.
        apply IH. auto. subst H; simpl; auto. subst H; simpl; auto. eauto. eauto.
        (* subcase ~In a' H': In this case Ind_subgraph H' G *)
        assert (h3: Ind_subgraph H' G). subst G'.  eauto using H'_sub_G. auto. }

      (* Case C1_a (~ In a H'): Proof ---------------------------- *)
      { assert (h3: In a' H' \/ ~ In a' H'). eapply reflect_EM;eauto.
        destruct h3 as [h3a | h3b].
        (* subcase In a' H': In this case Ind_subgraph H' G'_a  *) 
        assert (h3: Ind_subgraph H' (Ind_at N'_a G')).
        { unfold Ind_subgraph. simpl. unfold Ind_subgraph in h1.
          assert (h4: H' [<=] rmv a G').
          { intros x h4. cut(In x G'). cut (x <> a). auto.
            intro. subst x. contradiction. auto. }
          split. auto. intros x y h5 h6.
          replace (edg H' x y) with (edg G' x y).
          apply edg_equal_at_K; auto.  symmetry; apply h1;auto. }
        assert (h4: iso G (Ind_at N'_a G')).
        {  subst G'. eapply G_isomorphic_G'_a with (G0:=G)(a0:=a)(a'0:=a');auto. }
        destruct h4 as [f h4].
        assert (h5: exists H, Ind_subgraph H G /\ iso_using f H' H).
        { eapply iso_subgraphs. Focus 2. apply h3. auto. }
        destruct h5 as [H h5]. destruct h5 as [h5 h6].
        cut(iso H H'). cut (Nice H). eauto. auto. eauto.
        (* subcase ~In a' H': In this case Ind_subgraph H' G *)
        assert (h3: Ind_subgraph H' G). subst G'. eauto using H'_sub_G. auto. }
      
    } (*----------- End of Case C1 -------------------------------------------------- *) 

    }  Admitted.  
      
  
  End LovaszRepLemma.