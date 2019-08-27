









Require Export LovaszExp.
Require Export GraphCovers.
Set Implicit Arguments.

Section WPerfect.
  
  Context { A: ordType }.

  Definition meets (K I: list A):= exists a:A, In a K /\ In a I. 

  Lemma Cliq_meets_all_MaxI (G: @UG A):
    (nodes G)<> nil-> Perfect G -> (exists K, Cliq_in G K /\ (forall I, Max_I_in G I -> meets K I)).
  Proof. Admitted.

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


 

  