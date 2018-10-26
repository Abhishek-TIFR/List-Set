





Require Export MoreDecUG.

Set Implicit Arguments.

Section GraphIsomorphism.

  Context { A: ordType }.

   Definition iso (G G': @UG A) :=
     exists (f: A->A), (forall x, f (f x) = x) /\ (nodes G') = (s_map f G) /\
                 (forall x y, edg G x y = edg G' (f x) (f y)).

   Definition iso_using (f: A->A)(G G': @UG A) :=
     (forall x, f (f x) = x) /\ (nodes G') = (s_map f G) /\ (forall x y, edg G x y = edg G' (f x) (f y)).

   (*--------------------- properties of bijective function for isomorphism----------------*)

  Lemma fx_is_one_one (l: list A)(f: A->A): (forall x, f (f x) = x) -> one_one_on l f.
  Proof. { intros H. unfold one_one_on. intros x y Hx Hy Hxy HC. absurd (x=y).
           auto. replace y with (f (f y)). rewrite <- HC. symmetry;auto. auto. } Qed.
  
  Lemma s_map_of_s_map (l: list A)(f: A->A)(Hl: IsOrd l):
    (forall x, f (f x) = x)-> s_map f (s_map f l) = l.
  Proof. { intro H.
         assert (H1: Equal (s_map f (s_map f l)) l).
         { unfold Equal. split.
           { unfold Subset. intros a H1.
             assert (H2: exists b, In b (s_map f l) /\ a = f b); auto.
             destruct H2 as [b H2]. destruct H2 as [H2a H2b].
             assert (H3: exists x, In x l /\ b = f x ); auto.
             destruct H3 as [x H3]. destruct H3 as [H3a H3b].
             subst a. subst b. replace (f (f x)) with x. auto. symmetry;auto. }
           { unfold Subset. intros a H1.
             assert (H2: In (f a) (s_map f l)). auto.
             assert (H2a: In (f (f a)) (s_map f (s_map f l))). auto.
             replace (f (f a)) with a in H2a. auto. symmetry;auto. } } 
         auto. } Qed.

   Lemma s_map_of_s_map1 (l: list A)(f: A->A)(Hl: IsOrd l):
     (forall x, f (f x) = x)-> l= s_map f (s_map f l).
   Proof. intros. symmetry. auto using s_map_of_s_map. Qed.
   
   Hint Resolve fx_is_one_one s_map_of_s_map s_map_of_s_map1: core.   

   (* ---------------------- Isomorphism is commutative and transitive------------------*)
  Lemma iso_commutative1 (G G': @UG A)(f: A-> A): iso_using f G G' -> iso_using f G' G.
    Proof. { intro H. destruct H as [Ha H]; destruct H as [Hb H].
           split.
           { auto. }
           split.
           { rewrite Hb;  auto. }
           { intros; symmetry.
             replace (edg G' x y) with ( edg G' (f (f x)) (f (f y))).
             auto.
             replace (f (f x)) with x. replace (f (f y)) with y.
             auto. all: symmetry;auto. } } Qed.

  Lemma iso_elim1 (G G': @UG A)(f: A->A)(x:A): iso_using f G G'-> In x G-> In (f x) G'.
   Proof. intros H Hx. replace (nodes G') with (s_map f G). auto. symmetry; apply H. Qed.  

  Lemma iso_elim2 (G G': @UG A)(f: A->A)(x:A): iso_using f G G'-> In x G'-> In (f x) G.
  Proof. intros H Hx. replace (nodes G) with (s_map f G'). auto. symmetry.
         apply iso_commutative1 in H as Ha. apply Ha. Qed.
   
  Lemma iso_commutative (G G': @UG A): iso G G' -> iso G' G.
  Proof. { intro H. destruct H as [f H].  exists f. apply iso_commutative1. auto. } Qed.
  
  Hint Immediate iso_commutative1 iso_commutative iso_elim1 iso_elim2: core.

  Lemma iso_trans1 (G G1 G2: @UG A)(f1 f2: A-> A): iso_using f1 G G1 -> iso_using f2 G1 G2 ->
                                                  iso_using (fun x=> f2 (f1 x)) G G2.
  Proof. Admitted.

  Lemma iso_trans (G G1 G2: @UG A): iso G G1 -> iso G1 G2 -> iso G G2.
  Proof. Admitted.
  

  Lemma iso_one_one1 (G G': @UG A)(f: A-> A): iso_using f G G' -> one_one_on G f.
  Proof.  intro H; apply fx_is_one_one; apply H. Qed.

  Lemma iso_one_one2 (G G': @UG A)(f: A-> A): iso_using f G G' -> one_one_on G' f.
  Proof. intro H; apply fx_is_one_one; apply H. Qed. 

  Lemma iso_using_G' (G G': @UG A)(f: A-> A): iso_using f G G' -> nodes G' = (s_map f G).
  Proof.  intro H;apply H. Qed.

  Lemma iso_using_G (G G': @UG A)(f: A-> A): iso_using f G G' -> nodes G = (s_map f G').
  Proof. intro H0. cut (iso_using f G' G). intro H;apply H. auto. Qed.

  Lemma iso_one_one (G G': @UG A)(f: A-> A)(l: list A):
    iso_using f G G'-> one_one_on l f.
    Proof. intro H; apply fx_is_one_one; apply H. Qed.
  
  
    Hint Immediate iso_one_one1 iso_one_one2 iso_one_one
         iso_using_G iso_using_G': core.

  Lemma iso_cardinal (G G': @UG A)(f: A-> A): iso_using f G G' -> |G|=|G'|.
  Proof. { intro H.  apply iso_one_one1 in H as H1.
           replace (nodes G') with (s_map f G). auto. 
           symmetry; auto using iso_using_G'. } Qed.
  Lemma iso_sub_cardinal (G G': @UG A)(X: list A)(f: A->A):
    iso_using f G G' -> NoDup X -> |X|= | s_map f X |.
  Proof. { intros H H0.
         assert (H2: one_one_on G f). eauto.
         assert (H2a: one_one_on X f). eauto. auto. } Qed.

  Lemma iso_edg1  (G G': @UG A)(f: A-> A)(x y:A): iso_using f G G' ->
                                                (edg G x y = edg G' (f x) (f y)).
  Proof. intro H;apply H. Qed.

  Lemma iso_edg2  (G G': @UG A)(f: A-> A)(x y: A): iso_using f G G' ->
                                                (edg G' x y = edg G (f x) (f y)).
  Proof. intro H0. cut (iso_using f G' G). intro H;apply H. auto. Qed.

  

  Hint Immediate iso_cardinal iso_sub_cardinal iso_edg1 iso_edg2: core.

  Lemma iso_edg3  (G G': @UG A)(f: A-> A)(x y:A): iso_using f G G' ->
                                                edg G x y -> edg G' (f x) (f y).
  Proof. intro H; replace (edg G' (f x) (f y)) with (edg G x y); eauto. Qed.

  Lemma iso_edg4  (G G': @UG A)(f: A-> A)(x y: A): iso_using f G G' ->
                                                ~ edg G' x y -> ~ edg G (f x) (f y).
  Proof. intro H; replace (edg G' (f x) (f y)) with (edg G x y); eauto. Qed.

  Hint Immediate iso_edg3 iso_edg4: core.


  (* ------------- Isomorphism preserves Cliques and Cliq_num for a graph-----------------*)
  
  Lemma iso_cliq (G G': @UG A)(f: A-> A)(K: list A):
    iso_using f G G' -> Cliq G K -> Cliq G' (s_map f K).
  Proof. {  unfold Cliq. intros H H1.  intros x y Hx Hy.
          assert (H2: exists x0, In x0 K /\ x = f x0). auto.
          destruct H2 as [x0 H2]. destruct H2 as [H2a H2b].
          assert (H3: exists y0, In y0 K /\ y = f y0). auto.
          destruct H3 as [y0 H3]. destruct H3 as [H3a H3b].
          replace x with (f x0). replace y with (f y0).
          assert (H2:  x0 = y0 \/ edg G x0 y0). auto.
          destruct H2.
          { left. subst x0. auto. }
          { right. replace (edg G' (f x0) (f y0)) with (edg G x0 y0).
            auto. apply H. }  }  Qed.
  
   Lemma iso_cliq1 (G G': @UG A)(K: list A): iso G G' -> Cliq G K -> NoDup K ->
                                           (exists K', Cliq G' K' /\ |K|=|K'|).
  Proof. { intros H H1 H2. destruct H as [f H].
         exists (s_map f K). split. eauto using iso_cliq.
         assert (H3: one_one_on K f). eauto.
         auto. } Qed.

  Lemma iso_cliq_in (G G': @UG A)(f: A-> A)(K: list A):
    iso_using f G G' -> Cliq_in G K -> Cliq_in G' (s_map f K).
  Proof. { intros H H1.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c].
         split.
         { destruct H as [Ha H]. destruct H as [Hb Hc]. rewrite Hb; auto. }
         split.
         { auto. }
         { eauto using iso_cliq. }  } Qed.

  Lemma iso_cliq_in1 (G G': @UG A)(K: list A): iso G G' -> Cliq_in G K ->
                                              (exists K', Cliq_in G' K' /\ |K|=|K'|).
  Proof. { intros H H1. destruct H as [f H].
         exists (s_map f K). split. eauto using iso_cliq_in.
         assert (H3: one_one_on K f). eauto.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c]. auto. } Qed.

  Hint Immediate iso_cliq iso_cliq1 iso_cliq_in iso_cliq_in1: core.

  Lemma max_K_in_G' (G G': @UG A)(f: A-> A)(K: list A):
    iso_using f G G' -> Max_K_in G K -> Max_K_in G' (s_map f K). 
  Proof. { intros H H1. assert (H0: iso_using f G' G); auto.
         apply  Max_K_in_intro.         
         { cut (Cliq_in G K); eauto. }
         { intros Y H2.
           replace (|Y|) with (|s_map f Y|).
           replace (|s_map f K|) with (|K|).
           assert (H3: Cliq_in G (s_map f Y)); eauto.
           eauto using Max_K_in_elim. eapply iso_sub_cardinal;eauto.
           symmetry. eapply iso_sub_cardinal; eauto. } } Qed.

  Lemma cliq_num_G' (G G': @UG A)(n: nat):
    iso G G' -> cliq_num G n -> cliq_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H1 as [K H1].
         destruct H1 as [H1 H1b]. exists (s_map f K).
         split. eauto using max_K_in_G'. replace n with (|K|).
         symmetry. eapply iso_sub_cardinal;eauto. } Qed.
  
  Hint Immediate max_K_in_G' cliq_num_G': core.       


  (*---------- Isomorphism preserves Stable set and i_num ----------------------------*)

   Lemma iso_stable (G G': @UG A)(f: A-> A)(I: list A):
    iso_using f G G' -> Stable G I -> Stable G' (s_map f I).
  Proof. {  unfold Stable. intros H H1.  intros x y Hx Hy.
          assert (H2: exists x0, In x0 I /\ x = f x0). auto.
          destruct H2 as [x0 H2]. destruct H2 as [H2a H2b].
          assert (H3: exists y0, In y0 I /\ y = f y0). auto.
          destruct H3 as [y0 H3]. destruct H3 as [H3a H3b].
          replace x with (f x0). replace y with (f y0).
          assert (H2: edg G x0 y0 = false). auto. 
          replace (edg G' (f x0) (f y0)) with (edg G x0 y0).
            auto. apply H. } Qed.
  
   Lemma iso_stable1 (G G': @UG A)(I: list A): iso G G' -> Stable G I -> NoDup I ->
                                           (exists I', Stable G' I' /\ |I|=|I'|).
  Proof. { intros H H1 H2. destruct H as [f H].
         exists (s_map f I). split. eauto using iso_stable.
         assert (H3: one_one_on I f). eauto.
         auto. } Qed.

  Lemma iso_stable_in (G G': @UG A)(f: A-> A)(I: list A):
    iso_using f G G' -> Stable_in G I -> Stable_in G' (s_map f I).
  Proof. { intros H H1.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c].
         split.
         { destruct H as [Ha H]. destruct H as [Hb Hc]. rewrite Hb; auto. }
         split.
         { auto. }
         { eauto using iso_stable. }  } Qed.

  Lemma iso_stable_in1 (G G': @UG A)(I: list A): iso G G' -> Stable_in G I ->
                                              (exists I', Stable_in G' I' /\ |I|=|I'|).
  Proof. { intros H H1. destruct H as [f H].
         exists (s_map f I). split. eauto using iso_stable_in.
         assert (H3: one_one_on I f). eauto.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c]. auto. } Qed.

  Hint Immediate iso_stable iso_stable1 iso_stable_in iso_stable_in1: core.

  Lemma max_I_in_G' (G G': @UG A)(f: A-> A)(I: list A):
    iso_using f G G' -> Max_I_in G I -> Max_I_in G' (s_map f I).
  Proof. { intros H H1. assert (H0: iso_using f G' G); auto.
         apply  Max_I_in_intro.         
         { cut (Stable_in G I); eauto. }
         { intros Y H2.
           replace (|Y|) with (|s_map f Y|).
           replace (|s_map f I|) with (|I|).
           assert (H3: Stable_in G (s_map f Y)); eauto.
           eauto using Max_I_in_elim. eapply iso_sub_cardinal;eauto.
           symmetry. eapply iso_sub_cardinal; eauto. } } Qed.

  Lemma i_num_G' (G G': @UG A)(n: nat):
    iso G G' -> i_num G n -> i_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H1 as [I H1].
         destruct H1 as [H1 H1b]. exists (s_map f I).
         split. eauto using max_I_in_G'. replace n with (|I|).
         symmetry. eapply iso_sub_cardinal;eauto. } Qed.
  
  Hint Immediate max_I_in_G' i_num_G': core.

  (*----------- Isomorphism , graph coloring and chromatic number-------------------------*)
  
  
  Lemma iso_coloring (G G': @UG A)(f: A->A)(C: A->nat):
    iso_using f G G' -> Coloring_of G C -> Coloring_of G' (fun (x:A) => C (f x)).
  Proof. { intros H H1. assert (Ha: iso_using f G' G);auto. unfold Coloring_of.
           intros x y Hx Hy H2. assert (H3: edg G (f x) (f y)). eauto. apply H1; eauto. } Qed.
          
  Lemma iso_same_clrs (G G': @UG A)(f: A->A)(C: A->nat):
    iso_using f G G' -> Coloring_of G C -> (clrs_of C G) = clrs_of (fun (x:A) => C (f x)) G'.
  Proof. { intros H H1. assert (Ha: iso_using f G' G). auto.
         assert (H2: (nodes G) = s_map f G'). auto. unfold clrs_of; rewrite H2; auto. } Qed.

  Lemma best_coloring_of_G' (G G': @UG A)(f: A-> A)(C: A->nat):
    iso_using f G G' -> Best_coloring_of G C -> Best_coloring_of G' (fun (x:A) => C (f x)).
  Proof. { unfold Best_coloring_of. intros H H1.
         assert (H0: iso_using f G' G). auto.
         destruct H1 as [H1 H2].
         split. { eauto using iso_coloring. }
                { intros C' H3.
                  assert (H4: (clrs_of C G) = clrs_of (fun (x:A) => C (f x)) G').
                  auto using iso_same_clrs. rewrite <- H4.
                  assert (H5: (clrs_of C' G') = clrs_of (fun (x:A) => C' (f x)) G).
                  auto using iso_same_clrs. rewrite H5.
                  apply H2. eauto using iso_coloring. } } Qed. 
                  
  Lemma chrom_num_G' (G G': @UG A)(n:nat):
    iso G G' -> chrom_num G n -> chrom_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H1 as [C H1].
         destruct H1 as [H1 H2].
         exists (fun (x:A) => C (f x)). split. eauto using best_coloring_of_G'.
         subst n. replace (clrs_of (fun x : A => C (f x)) G') with (clrs_of C G).
         auto. destruct H1 as [H1 H2]. auto using iso_same_clrs. } Qed.

  Hint Resolve iso_coloring iso_same_clrs best_coloring_of_G': core.
  Hint Immediate chrom_num_G': core.


  (*------------Isomorphism , nice graphs and perfect graph--------------------------------*)

  Lemma nice_G' (G G': @UG A): iso G G' -> Nice G -> Nice G'.
  Proof. Admitted.

  Lemma perfect_G' (G G': @UG A): iso G G' -> Perfect G -> Perfect G'.
  Proof. Admitted.
         

End GraphIsomorphism.


Hint Resolve fx_is_one_one s_map_of_s_map s_map_of_s_map1: core.

Hint Immediate iso_commutative1 iso_commutative iso_elim1 iso_elim2: core.
Hint Immediate iso_one_one1 iso_one_one2: core.
Hint Immediate iso_one_one iso_using_G iso_using_G': core.

Hint Immediate iso_cardinal iso_sub_cardinal iso_edg1 iso_edg2: core.
Hint Immediate iso_edg3 iso_edg4: core.

Hint Immediate iso_cliq iso_cliq1 iso_cliq_in iso_cliq_in1: core.
Hint Immediate max_K_in_G' cliq_num_G': core.

Hint Immediate iso_stable iso_stable1 iso_stable_in iso_stable_in1: core.
Hint Immediate max_I_in_G' i_num_G': core.

Hint Resolve iso_coloring iso_same_clrs best_coloring_of_G': core.
Hint Immediate chrom_num_G': core.




