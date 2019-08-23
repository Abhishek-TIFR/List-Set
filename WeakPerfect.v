









Require Export LovaszExp.
Require Export GraphCovers.
Set Implicit Arguments.

Section WPerfect.
  
  Context { A: ordType }.

  Definition meets (K I: list A):= exists a:A, In a K /\ In a I. 

  Lemma Cliq_meets_all_MaxI (G: @UG A):
    Perfect G -> (exists K, Cliq_in G K /\ (forall I, Max_I_in G I -> meets K I)).
  Proof. Admitted.
  

  Lemma i_num_cliq_cover (G: @UG A)(n: nat):
    Perfect G -> i_num G n -> (exists C, Cliq_cover C G /\ |C| = n).
  Proof. Admitted.

  
End WPerfect.


Section WPGT.

  Context { A: ordType }.

  Lemma compl_commute (G G': @UG A): Compl G G' -> Compl G' G.
  Proof. Admitted.
  

  Lemma stable_is_cliq (G G': @UG A)(I: list A): Compl G G'-> Stable_in G I-> Cliq_in G' I.
  Proof. Admitted.

  Lemma cliq_is_stable (G G': @UG A)(K: list A): Compl G G' -> Cliq_in G K -> Stable_in G' K.
  Proof. Admitted.

  Lemma cliq_num_i_num (G G': @UG A)(n: nat): Compl G G' -> cliq_num G n -> i_num G' n.
  Proof. Admitted.

  Lemma i_num_cliq_num (G G': @UG A)(n: nat): Compl G G'-> i_num G n -> cliq_num G' n.
  Proof. Admitted.
  
  Lemma ind_sub_eq_iso (H G: @UG A): Ind_subgraph H G -> nodes H = nodes G -> iso H G.
  Proof. Admitted.

  Lemma sub_neq_exists (l s: list A):
    IsOrd l -> IsOrd s -> l [<=] s -> l <> s -> (exists x, (In x s /\ ~ In x l)).
  Proof. { intros h1 h2 h3 h4.
           assert (h5: (forall x, In x s -> In x l)\/ (exists x, In x s /\ ~ In x l)). eauto.
           destruct h5 as [h5 | h5].
           { absurd (l = s). auto.
             apply set_equal;auto. }
           { auto. } } Qed.
         
  
  Lemma sub_neq_lt (l s: list A): IsOrd l -> IsOrd s -> l [<=] s -> l <> s -> |l| < |s|.
  Proof. { intros h1 h2 h3 h4.  specialize (sub_neq_exists h1 h2 h3 h4) as h5.
           destruct h5 as [x h5]. eapply subset_cardinal_lt with (a := x).
           all: ( auto || apply h5). } Qed.
  

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
          eapply cliq_num_i_num with (G:= G').
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


 

  