









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
  Lemma E1_irefl: irefl E1.
  Proof. unfold irefl. intro p. unfold E1.
         replace (g p == g p) with true. 
         assert (h1: snd p == snd p). apply /eqP;auto.
         rewrite h1. auto. symmetry;auto. Qed.
         
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

  Lemma N_sub_G: N [<=] G.
  Proof. Admitted.
  Lemma NG_N: N [i] G = N.
  Proof. Admitted.

  Hint Resolve N_sub_G NG_N.

  Lemma C_and_C': (nodes H) = img g H'.
  Proof. Admitted.

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

  Lemma PerfectH': Perfect H'.
  Proof. cut (Perfect H). eapply LovaszExpLemma. apply H'_exp_of_H.
         cut (Ind_subgraph H G). eauto. unfold H. auto. Qed.
  
  Lemma K'_meets_all_in_C': (exists K', Cliq_in H' K' /\ (forall I, In I C' -> meets K' I)).
  Proof. Admitted.
  
  Lemma K_meets_all_in_C: (exists K, Cliq_in H K /\ (forall I, In I C -> meets K I)).
  Proof. Admitted.
  
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


 

  