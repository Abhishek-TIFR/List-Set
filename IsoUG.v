

(*---------------------------------- Descriptions ---------------------------------------

In this file we define the idea of graph isomorphism. This is done by defining following
predicates:

Definition iso (G G': @UG A) :=
     exists (f: A->A), (forall x, f (f x) = x) /\ (nodes G') = (img f G) /\
                 (forall x y, In x G -> In y G-> edg G x y = edg G' (f x) (f y)).

 Definition iso_using (f: A->A)(G G': @UG A) :=
     (forall x, f (f x) = x) /\ 
     (nodes G') = (img f G) /\ 
     (forall x y, edg G x y = edg G' (f x) (f y)).

When we say (iso_using f G1 G2), we mean f is the function establishing the isomorphism
between G1 and G2. We also prove that this relation is symmetric and transitive.
Note that the self invertible nature of f makes it one_one on both G1 and G2. 
Following are some useful property of f:
 
 Lemma fx_is_one_one (l: list A)(f: A->A): (forall x, f (f x) = x) -> one_one_on l f.
 Lemma img_of_img (l: list A)(f: A->A)(Hl: IsOrd l):
    (forall x, f (f x) = x)-> img f (img f l) = l.

 Lemma iso_sym1 (G G': @UG A)(f: A-> A): iso_using f G G' -> iso_using f G' G.
 Lemma iso_sym (G G': @UG A): iso G G' -> iso G' G.

 Lemma iso_one_one1 (G G': @UG A)(f: A-> A): iso_using f G G' -> one_one_on G f.
 Lemma iso_using_G' (G G': @UG A)(f: A-> A): iso_using f G G' -> nodes G' = (img f G).
 Lemma iso_one_one (G G': @UG A)(f: A-> A)(l: list A): iso_using f G G'-> one_one_on l f.
 Lemma iso_cardinal (G G': @UG A)(f: A-> A): iso_using f G G' -> |G|=|G'|.
 Lemma iso_sub_cardinal (G G': @UG A)(X: list A)(f: A->A): iso_using f G G' ->
                                                           NoDup X -> |X|= | img f X |.
 Lemma iso_edg1  (G G': @UG A)(f: A-> A)(x y:A): iso_using f G G' ->
                                                (edg G x y = edg G' (f x) (f y)).
 Lemma iso_edg2  (G G': @UG A)(f: A-> A)(x y: A): iso_using f G G' ->
                                                (edg G' x y = edg G (f x) (f y)).
-------------------------------------------------------------------------------------

 Stable Set, Cliq and Coloring of graphs has exact counterpart in the isomorphic Graphs.
 These results of existence of counterparts are summarized below: 


 Lemma iso_cliq_in (G G': @UG A)(f: A-> A)(K: list A): iso_using f G G' -> 
                                                      Cliq_in G K -> Cliq_in G' (img f K).
 Lemma iso_cliq_in1 (G G': @UG A)(K: list A): iso G G' -> Cliq_in G K ->
                                              (exists K', Cliq_in G' K' /\ |K|=|K'|).
 Lemma max_K_in_G' (G G': @UG A)(f: A-> A)(K: list A): iso_using f G G' ->
                                                    Max_K_in G K -> Max_K_in G' (img f K).


Lemma iso_stable (G G': @UG A)(f: A-> A)(I: list A): iso_using f G G' -> 
                                                     Stable G I -> Stable G' (img f I).
Lemma iso_stable_in (G G': @UG A)(f: A-> A)(I: list A): iso_using f G G'-> 
                                                Stable_in G I -> Stable_in G' (img f I).
Lemma max_I_in_G' (G G': @UG A)(f: A-> A)(I: list A): iso_using f G G' -> 
                                                  Max_I_in G I -> Max_I_in G' (img f I).

Lemma cliq_num_G' (G G': @UG A)(n: nat): iso G G' -> cliq_num G n -> cliq_num G' n.
Lemma i_num_G' (G G': @UG A)(n: nat):  iso G G' -> i_num G n -> i_num G' n. 
Lemma chrom_num_G' (G G': @UG A)(n:nat): iso G G' -> chrom_num G n -> chrom_num G' n.

Lemma nice_G' (G G': @UG A): iso G G' -> Nice G -> Nice G'.
Lemma iso_subgraphs (G G' H: @UG A)(f: A->A):  iso_using f G G' -> Ind_subgraph H G -> 
                                      (exists H', Ind_subgraph H' G' /\ iso_using f H H').
Lemma perfect_G' (G G': @UG A): iso G G' -> Perfect G -> Perfect G'.


Following definition represents the Graph G restricted to the vertex set K:

  Definition Ind_at (K: list A)(Pk: IsOrd K)(G: @UG A): @UG A.
     refine {|nodes:= K; nodes_IsOrd := Pk;
              edg:= (G.(edg) at_ K); |}. all: auto. Defined. 

------------------------------------------------------------------------------------------*)

Require Export MoreUG.

Set Implicit Arguments.

Section GraphIsomorphism.

  Context { A: ordType }.

   Definition iso (G G': @UG A) :=
     exists (f: A->A), (forall x, f (f x) = x) /\ (nodes G') = (img f G) /\
                 (forall x y, In x G-> In y G-> edg G x y = edg G' (f x) (f y)).

   Definition iso_using (f: A->A)(G G': @UG A) :=
     (forall x, f (f x) = x) /\ (nodes G') = (img f G) /\
     (forall x y, In x G-> In y G-> edg G x y = edg G' (f x) (f y)).

   (*--------------------- properties of bijective function for isomorphism----------------*)

   Lemma f_is_one_one (f: A->A): (forall x, f (f x) = x) -> one_one f.
   Proof.  { intros H. unfold one_one. intros x y  Hxy HC. absurd (x=y).
               auto. replace y with (f (f y)). rewrite <- HC. symmetry;auto. auto. } Qed.
     
  Lemma fx_is_one_one (l: list A)(f: A->A): (forall x, f (f x) = x) -> one_one_on l f.
  Proof. { intros H. unfold one_one_on. intros x y Hx Hy Hxy HC. absurd (x=y).
           auto. replace y with (f (f y)). rewrite <- HC. symmetry;auto. auto. } Qed.
  
  Lemma img_of_img (l: list A)(f: A->A)(Hl: IsOrd l):
    (forall x, f (f x) = x)-> img f (img f l) = l.
  Proof. { intro H.
         assert (H1: Equal (img f (img f l)) l).
         { unfold Equal. split.
           { unfold Subset. intros a H1.
             assert (H2: exists b, In b (img f l) /\ a = f b); auto.
             destruct H2 as [b H2]. destruct H2 as [H2a H2b].
             assert (H3: exists x, In x l /\ b = f x ); auto.
             destruct H3 as [x H3]. destruct H3 as [H3a H3b].
             subst a. subst b. replace (f (f x)) with x. auto. symmetry;auto. }
           { unfold Subset. intros a H1.
             assert (H2: In (f a) (img f l)). auto.
             assert (H2a: In (f (f a)) (img f (img f l))). auto.
             replace (f (f a)) with a in H2a. auto. symmetry;auto. } } 
         auto. } Qed.

   Lemma img_of_img1 (l: list A)(f: A->A)(Hl: IsOrd l):
     (forall x, f (f x) = x)-> l= img f (img f l).
   Proof. intros. symmetry. auto using img_of_img. Qed.
   
   Hint Resolve f_is_one_one fx_is_one_one img_of_img img_of_img1: core.   

   (* ---------------------- Isomorphism is commutative and transitive------------------*)
   Lemma iso_sym1 (G G': @UG A)(f: A-> A): iso_using f G G' -> iso_using f G' G.
    Proof. { intro H. destruct H as [Ha H]; destruct H as [Hb H].
           split.
           { auto. }
           split.
           { rewrite Hb;  auto. }
           { intros; symmetry.
             replace (edg G' x y) with ( edg G' (f (f x)) (f (f y))).
             assert (H2: In (f x) G). 
             { rewrite Hb in H0.
               assert (h1: exists x0, In x0 G /\ x = f x0). auto.
               destruct h1 as [x0 h1]. destruct h1 as [h1 h2].
               subst x. specialize (Ha x0) as Hx0. rewrite Hx0. auto. }
             assert (H3: In (f y) G).
              { rewrite Hb in H1.
               assert (h1: exists y0, In y0 G /\ y = f y0). auto.
               destruct h1 as [y0 h1]. destruct h1 as [h1 h2].
               subst y. specialize (Ha y0) as Hy0. rewrite Hy0. auto. }
             auto. replace (f (f x)) with x. replace (f (f y)) with y.
             auto. all: symmetry;auto. } } Qed.

  Lemma iso_elim1 (G G': @UG A)(f: A->A)(x:A): iso_using f G G'-> In x G-> In (f x) G'.
   Proof. intros H Hx. replace (nodes G') with (img f G). auto. symmetry; apply H. Qed.  

  Lemma iso_elim2 (G G': @UG A)(f: A->A)(x:A): iso_using f G G'-> In x G'-> In (f x) G.
  Proof. intros H Hx. replace (nodes G) with (img f G'). auto. symmetry.
         apply iso_sym1 in H as Ha. apply Ha. Qed.
   
  Lemma iso_sym (G G': @UG A): iso G G' -> iso G' G.
  Proof. { intro H. destruct H as [f H].  exists f. apply iso_sym1. auto. } Qed.

  Lemma iso_using_iso (G G':@UG A)(f: A->A): iso_using f G G' -> iso G G'.
  Proof. intros h. exists f. auto. Qed.

  Lemma iso_using_iso1 (G G':@UG A)(f: A->A): iso_using f G G' -> iso G' G.
  Proof. intro h. apply iso_sym. eapply iso_using_iso. eauto. Qed.
  
  
  Hint Immediate iso_sym1 iso_sym iso_elim1 iso_elim2: core.

  Hint Resolve iso_using_iso iso_using_iso1: core.

  

  Lemma iso_one_one1 (G G': @UG A)(f: A-> A): iso_using f G G' -> one_one_on G f.
  Proof.  intro H; apply fx_is_one_one; apply H. Qed.

  Lemma iso_one_one2 (G G': @UG A)(f: A-> A): iso_using f G G' -> one_one_on G' f.
  Proof. intro H; apply fx_is_one_one; apply H. Qed. 

  Lemma iso_using_G' (G G': @UG A)(f: A-> A): iso_using f G G' -> nodes G' = (img f G).
  Proof.  intro H;apply H. Qed.

  Lemma iso_using_G (G G': @UG A)(f: A-> A): iso_using f G G' -> nodes G = (img f G').
  Proof. intro H0. cut (iso_using f G' G). intro H;apply H. auto. Qed.

  Lemma iso_one_one (G G': @UG A)(f: A-> A)(l: list A):
    iso_using f G G'-> one_one_on l f.
  Proof. intro H; apply fx_is_one_one; apply H. Qed.

  Lemma iso_f_one_one (G G': @UG A)(f: A-> A): iso_using f G G'-> one_one f.
    Proof. intro H; apply f_is_one_one; apply H. Qed.
  
  
    Hint Immediate iso_one_one1 iso_one_one2 iso_one_one iso_f_one_one
         iso_using_G iso_using_G': core.

  Lemma iso_cardinal (G G': @UG A)(f: A-> A): iso_using f G G' -> |G|=|G'|.
  Proof. { intro H.  apply iso_one_one1 in H as H1.
           replace (nodes G') with (img f G). auto. 
           symmetry; auto using iso_using_G'. } Qed.
  Lemma iso_sub_cardinal (G G': @UG A)(X: list A)(f: A->A):
    iso_using f G G' -> NoDup X -> |X|= | img f X |.
  Proof. { intros H H0.
         assert (H2: one_one_on G f). eauto.
         assert (H2a: one_one_on X f). eauto. auto. } Qed.
  
   Lemma iso_edg1  (G G': @UG A)(f: A-> A)(x y:A): iso_using f G G' -> In x G -> In y G->
                                                (edg G x y = edg G' (f x) (f y)).
  Proof. intro H;apply H. Qed.

  Lemma iso_edg2  (G G': @UG A)(f: A-> A)(x y: A): iso_using f G G' -> In x G'-> In y G'->
                                                (edg G' x y = edg G (f x) (f y)).
  Proof. intro H0. cut (iso_using f G' G). intro H;apply H. auto. Qed.

  

  Hint Immediate iso_cardinal iso_sub_cardinal iso_edg1 iso_edg2: core.

   Lemma iso_edg3(G G': @UG A)(f: A-> A)(x y:A): iso_using f G G' -> In x G -> In y G->
                                                edg G x y -> edg G' (f x) (f y).
  Proof.  intros; replace (edg G' (f x) (f y)) with (edg G x y); auto.  Qed.

  Lemma iso_edg4  (G G': @UG A)(f: A-> A)(x y: A): iso_using f G G' -> In x G -> In y G-> 
                                                ~ edg G x y -> ~ edg G' (f x) (f y).
  Proof. intros ; replace (edg G' (f x) (f y)) with (edg G x y); auto. Qed.

  Hint Immediate iso_edg3 iso_edg4: core.


  (* ------------- Isomorphism preserves Cliques and Cliq_num for a graph-----------------*)

   Lemma iso_cliq (G G': @UG A)(f: A-> A)(K: list A):
    iso_using f G G' -> K [<=] G-> Cliq G K -> Cliq G' (img f K).
  Proof. {  unfold Cliq. intros H H1 h1.  intros x y Hx Hy.
          assert (H2: exists x0, In x0 K /\ x = f x0). auto.
          destruct H2 as [x0 H2]. destruct H2 as [H2a H2b].
          assert (H3: exists y0, In y0 K /\ y = f y0). auto.
          destruct H3 as [y0 H3]. destruct H3 as [H3a H3b].
          replace x with (f x0). replace y with (f y0).
          assert (H2:  x0 = y0 \/ edg G x0 y0). auto.
          destruct H2.
          { left. subst x0. auto. }
          { right. replace (edg G' (f x0) (f y0)) with (edg G x0 y0).
            auto. apply H. all: auto. }  }  Qed.
  
  Lemma iso_cliq1 (G G': @UG A)(K: list A): iso G G' -> K [<=] G -> Cliq G K -> NoDup K ->
                                           (exists K', Cliq G' K' /\ |K|=|K'|).
  Proof. { intros H h1 H1 H2. destruct H as [f H].
         exists (img f K). split. eauto using iso_cliq.
         assert (H3: one_one_on K f). eauto.
         auto. } Qed.
  

  Lemma iso_cliq_in (G G': @UG A)(f: A-> A)(K: list A):
    iso_using f G G' -> Cliq_in G K -> Cliq_in G' (img f K).
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
         exists (img f K). split. eauto using iso_cliq_in.
         assert (H3: one_one_on K f). eauto.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c]. auto. } Qed.

  Hint Immediate iso_cliq iso_cliq1 iso_cliq_in iso_cliq_in1: core.

  Lemma max_K_in_G' (G G': @UG A)(f: A-> A)(K: list A):
    iso_using f G G' -> Max_K_in G K -> Max_K_in G' (img f K). 
  Proof. { intros H H1. assert (H0: iso_using f G' G); auto.
         apply  Max_K_in_intro.         
         { cut (Cliq_in G K); eauto. }
         { intros Y H2.
           replace (|Y|) with (|img f Y|).
           replace (|img f K|) with (|K|).
            assert (H3: Cliq_in G (img f Y)). eauto.
           eauto using Max_K_in_elim. eapply iso_sub_cardinal;eauto.
           symmetry. eapply iso_sub_cardinal; eauto. } } Qed.

  Lemma cliq_num_G' (G G': @UG A)(n: nat):
    iso G G' -> cliq_num G n -> cliq_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H1 as [K H1].
         destruct H1 as [H1 H1b]. exists (img f K).
         split. eauto using max_K_in_G'. replace n with (|K|).
         symmetry. eapply iso_sub_cardinal;eauto. } Qed.
  
  Hint Immediate max_K_in_G' cliq_num_G': core.       


  (*---------- Isomorphism preserves Stable set and i_num ----------------------------*)

   Lemma iso_stable (G G': @UG A)(f: A-> A)(I: list A):
    iso_using f G G' -> I [<=] G-> Stable G I -> Stable G' (img f I).
  Proof. {  unfold Stable. intros H h1 H1.  intros x y Hx Hy.
          assert (H2: exists x0, In x0 I /\ x = f x0). auto.
          destruct H2 as [x0 H2]. destruct H2 as [H2a H2b].
          assert (H3: exists y0, In y0 I /\ y = f y0). auto.
          destruct H3 as [y0 H3]. destruct H3 as [H3a H3b].
          replace x with (f x0). replace y with (f y0).
          assert (H2: edg G x0 y0 = false). auto. 
          replace (edg G' (f x0) (f y0)) with (edg G x0 y0).
            auto. apply H. all: auto. } Qed.
  
   Lemma iso_stable1 (G G': @UG A)(I: list A): iso G G' -> I [<=] G-> Stable G I -> NoDup I ->
                                           (exists I', Stable G' I' /\ |I|=|I'|).
  Proof. { intros H h1 H1 H2. destruct H as [f H].
         exists (img f I). split. eauto using iso_stable.
         assert (H3: one_one_on I f). eauto.
         auto. } Qed.

  Lemma iso_stable_in (G G': @UG A)(f: A-> A)(I: list A):
    iso_using f G G' -> Stable_in G I -> Stable_in G' (img f I).
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
         exists (img f I). split. eauto using iso_stable_in.
         assert (H3: one_one_on I f). eauto.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c]. auto. } Qed.

  Hint Immediate iso_stable iso_stable1 iso_stable_in iso_stable_in1: core.

  Lemma max_I_in_G' (G G': @UG A)(f: A-> A)(I: list A):
    iso_using f G G' -> Max_I_in G I -> Max_I_in G' (img f I).
  Proof. { intros H H1. assert (H0: iso_using f G' G); auto.
         apply  Max_I_in_intro.         
         { cut (Stable_in G I); eauto. }
         { intros Y H2.
           replace (|Y|) with (|img f Y|).
           replace (|img f I|) with (|I|).
           assert (H3: Stable_in G (img f Y)). eauto.
           eauto using Max_I_in_elim. eapply iso_sub_cardinal;eauto.
           symmetry. eapply iso_sub_cardinal; eauto. } } Qed.

  Lemma i_num_G' (G G': @UG A)(n: nat):
    iso G G' -> i_num G n -> i_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H1 as [I H1].
         destruct H1 as [H1 H1b]. exists (img f I).
         split. eauto using max_I_in_G'. replace n with (|I|).
         symmetry. eapply iso_sub_cardinal;eauto. } Qed.
  
  Hint Immediate max_I_in_G' i_num_G': core.

  (*----------- Isomorphism, graph coloring and chromatic number -------------------------*)
  
  
  Lemma iso_coloring (G G': @UG A)(f: A->A)(C: A->nat):
    iso_using f G G' -> Coloring_of G C -> Coloring_of G' (fun (x:A) => C (f x)).
  Proof. { intros H H1. assert (Ha: iso_using f G' G);auto. unfold Coloring_of.
           intros x y Hx Hy H2. assert (H3: edg G (f x) (f y)). eauto. apply H1; eauto. } Qed.
          
  Lemma iso_same_clrs (G G': @UG A)(f: A->A)(C: A->nat):
    iso_using f G G' -> Coloring_of G C -> (clrs_of C G) = clrs_of (fun (x:A) => C (f x)) G'.
  Proof. { intros H H1. assert (Ha: iso_using f G' G). auto.
         assert (H2: (nodes G) = img f G'). auto. unfold clrs_of; rewrite H2; auto. } Qed.

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


  (*------------Isomorphism, nice graphs and perfect graph--------------------------------*)

  Lemma nice_G' (G G': @UG A): iso G G' -> Nice G -> Nice G'.
  Proof. { intro H.  assert (H0: iso G' G). auto.
         unfold Nice. intros H1 n H2.
         cut (chrom_num G n). eauto. cut (cliq_num G n); eauto. } Qed.

  Lemma iso_subgraphs (G G' H: @UG A)(f: A->A):
    iso_using f G G' -> Ind_subgraph H G -> (exists H', Ind_subgraph H' G' /\ iso_using f H H').
  Proof.  { intros F1 F2.
            assert (F0: iso_using f G' G). auto. 
            assert (Nk: IsOrd (img f H)). auto.
            pose H' := (ind_at (img f H) G').
            exists H'.
            assert (h0: H' [<=] G').
            { replace (nodes G') with (img f G). simpl.
              cut (img f H [<=] img f G). auto. 
              eapply img_subset. apply F2. symmetry. auto. }
            assert (h1: img f H [<=] G').
            { replace (nodes G') with (img f G).
                cut (H [<=] G). auto. apply F2.  symmetry.
                assert(F3: iso_using f G G'). auto. apply F3. }
            assert (h2: img f H = inter (img f H) G').
            { apply set_equal; auto. }
            split.
            (* Ind_subgraph H' G' *)
            {  unfold Ind_subgraph. split.
               { auto. }
               { unfold H'. simpl. intros. symmetry. auto. } }
           
            {  (* iso_using f H H' *)
              unfold iso_using.
              split.
              { apply F1. }
              split. 
              { simpl. symmetry. auto.  }
              { (* forall x y : A, edg H x y = edg (Ind_at Nk G') (f x) (f y) *)
                simpl. intros x y Hx Hy.
                replace (edg H x y) with (edg G x y). rewrite <- h2.
                assert (H2: In (f x) (img f H)). auto.
                replace ((edg G' at_ img f H) (f x) (f y)) with (edg G' (f x)(f y)).
                destruct F2. cut(In x G). cut(In y G). all: auto. symmetry. auto. } } } Qed.
                
 
  Lemma perfect_G' (G G': @UG A): iso G G' -> Perfect G -> Perfect G'.
  Proof. { intro F.  assert (F0: iso G' G). auto.
         unfold Perfect. destruct F0 as [f F0].
         intros F1 H' F2.
         assert (F3: exists H, Ind_subgraph H G /\ iso_using f H' H).
         { eapply iso_subgraphs. apply F0. auto. }
         destruct F3 as [H F3]. destruct F3 as [F3 F4]. 
         cut (Nice H).
         { cut (iso H H'). eauto using nice_G'.
           exists f. cut (iso_using f H H'); auto. } auto.  } Qed.

  Hint Immediate nice_G' induced_fact1 iso_subgraphs perfect_G': core.

End GraphIsomorphism.


Hint Resolve f_is_one_one fx_is_one_one img_of_img img_of_img1: core.

Hint Immediate iso_sym1 iso_sym iso_elim1 iso_elim2: core.
 Hint Resolve iso_using_iso iso_using_iso1: core.
Hint Immediate iso_one_one1 iso_one_one2: core.
Hint Immediate iso_one_one iso_f_one_one iso_using_G iso_using_G': core.

Hint Immediate iso_cardinal iso_sub_cardinal iso_edg1 iso_edg2: core.
Hint Immediate iso_edg3 iso_edg4: core.

Hint Immediate iso_cliq iso_cliq1 iso_cliq_in iso_cliq_in1: core.
Hint Immediate max_K_in_G' cliq_num_G': core.

Hint Immediate iso_stable iso_stable1 iso_stable_in iso_stable_in1: core.
Hint Immediate max_I_in_G' i_num_G': core.

Hint Resolve iso_coloring iso_same_clrs best_coloring_of_G': core.
Hint Immediate chrom_num_G': core.

Hint Immediate nice_G' iso_subgraphs perfect_G': core.







