


(*---------------------------------- Descriptions ---------------------------------------

In this file we define the idea of graph isomorphism between graphs on two different domain say A and B. This is done by defining following predicates:

Definition morph_using (f: A-> B)  


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


Section GraphMorphism.

  Context { A B: ordType }.

  Definition morph_using (f: A-> B)(G: @UG A)(G': @UG B):=
    (nodes G') = (img f G) /\  (forall x y, In x G-> In y G-> edg G x y = edg G' (f x) (f y)).

   (* Definition iso (G G': @UG A) :=
     exists (f: A->A), (forall x, In x G -> f (f x) = x) /\ (nodes G') = (img f G) /\
                 (forall x y, In x G-> In y G-> edg G x y = edg G' (f x) (f y)). *)

   Definition iso_using (f: A->A)(G G': @UG A) :=
     (forall x, In x G -> f (f x) = x) /\ (nodes G') = (img f G) /\
     (forall x y, In x G-> In y G-> edg G x y = edg G' (f x) (f y)).

  
End GraphMorphism.




Section GraphIsomorphism.
  Context { A B: ordType }.

  Definition isomorph_using (f: A-> B)(g: B-> A)(G: @UG A)(G': @UG B):=
    morph_using f G G' /\ morph_using g G' G /\ (forall x, In x G -> g (f x) = x).

  Definition isomorphic (G: @UG A)(G': @UG B):=
    exists (f: A-> B)(g: B-> A), isomorph_using f g G G'.
  
End GraphIsomorphism.


Section IsoVsIsomorph.
  Context {A: ordType }.

   Lemma img_of_imgf (l: list A)(f: A->A)(Hl: IsOrd l):
    (forall x, In x l->  f (f x) = x)-> img f (img f l) = l.
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

  Lemma iso_is_isomorph (G G': @UG A)(f: A-> A): iso_using f G G' -> isomorph_using f f G G'.
  Proof. { intro h1. destruct h1 as [h1 h2]. destruct h2 as [h2 h3]. split.
         { split;auto. } split.
         { split. rewrite h2. symmetry. apply img_of_imgf. all: auto.
           intros x y h4 h5.
           assert (h6: exists x0, In x0 G /\ x = f x0).
           { rewrite h2 in h4; auto. }
           assert (h7: exists y0, In y0 G /\ y = f y0).
           { rewrite h2 in h5; auto. }
           destruct h6 as [x0 h6]. destruct h7 as [y0 h7].
           replace x with (f x0). replace y with (f y0).
           replace (f (f x0)) with x0. replace (f (f y0)) with y0.
           symmetry;apply h3. apply h6. apply h7.
           symmetry;apply h1;apply h7.
           symmetry;apply h1;apply h6.
           symmetry; apply h7.
           symmetry;apply h6. } auto.   } Qed.

  Lemma isomorph_is_iso (G G': @UG A)(f: A-> A): isomorph_using f f G G' ->  iso_using f G G'.
  Proof.  { intro h1. destruct h1 as [h1 h2]. destruct h2 as [h2 h3].
            split; (auto || split;apply h1). } Qed.
             

End IsoVsIsomorph.

Hint Immediate img_of_imgf iso_is_isomorph isomorph_is_iso: core.



Section GraphIsoProp.

  Context { A B: ordType }.

   (*---------------- properties of bijective function f and g for isomorphism ---------*)

     
  Lemma fx_is_one_one (l: list A)(f: A->B)(g: B->A):
    (forall x, In x l ->  g (f x) = x) ->  one_one_on l f.
  Proof. { intros H. unfold one_one_on. intros x y Hx Hy Hxy HC. absurd (x=y).
           auto. replace y with (g (f y)). rewrite <- HC.
           symmetry;eapply H;eauto. eauto. } Qed.

  Lemma f_gx_is_x (l: list A)(s: list B)(f: A->B)(g: B->A):
    (forall x, In x l-> g (f x) = x) -> (s = (img f l)) -> (forall y, In y s -> f (g y) = y).
  Proof. { intros h1 h2 y h3.
           assert (h4: exists x, In x l /\ y = f x).
           { subst s; eauto. }
           destruct h4 as [x h4]. destruct h4 as [h4a h4]. subst y.
           replace (g (f x)) with x. auto. symmetry;auto. } Qed. 

  Lemma gx_is_one_one (s: list B)(f: A-> B)(g: B->A):
    (forall y, In y s -> f (g y) = y) -> one_one_on s g.
  Proof. { intros H. unfold one_one_on. intros x y Hx Hy Hxy HC. absurd (x=y).
           auto. replace y with (f (g y)). rewrite <- HC. symmetry;auto. auto. } Qed.

  Lemma img_of_img (l: list A)(f: A->B)(g: B-> A)(Hl: IsOrd l):
    (forall x, In x l-> g (f x) = x) -> img g (img f l) = l.
 Proof. { intro H.
         assert (H1: Equal (img g (img f l)) l).
         { unfold Equal. split.
           { unfold Subset. intros a H1.
             assert (H2: exists b, In b (img f l) /\ a = g b); auto.
             destruct H2 as [b H2]. destruct H2 as [H2a H2b].
             assert (H3: exists x, In x l /\ b = f x ); auto.
             destruct H3 as [x H3]. destruct H3 as [H3a H3b].
             subst a. subst b. replace (g (f x)) with x. auto. symmetry;auto. }
           { unfold Subset. intros a H1.
             assert (H2: In (f a) (img f l)). auto.
             assert (H2a: In (g (f a)) (img g (img f l))). auto.
             replace (g (f a)) with a in H2a. auto. symmetry;auto. } } 
         auto. } Qed.
  

   Lemma img_of_img1 (l: list A)(f: A->B)(g: B->A)(Hl: IsOrd l):
     (forall x, In x l-> g (f x) = x) -> l = img g (img f l).
   Proof. intros. symmetry. auto using img_of_img. Qed.

    Lemma img_of_img2 (l: list B)(f: A->B)(g: B-> A)(Hl: IsOrd l):
    (forall x, In x l-> f (g x) = x) -> img f (img g l) = l.
    Proof. { intro H.
         assert (H1: Equal (img f (img g l)) l).
         { unfold Equal. split.
           { unfold Subset. intros a H1.
             assert (H2: exists b, In b (img g l) /\ a = f b); auto.
             destruct H2 as [b H2]. destruct H2 as [H2a H2b].
             assert (H3: exists x, In x l /\ b = g x ); auto.
             destruct H3 as [x H3]. destruct H3 as [H3a H3b].
             subst a. subst b. replace (f (g x)) with x. auto. symmetry;auto. }
           { unfold Subset. intros a H1.
             assert (H2: In (g a) (img g l)). auto.
             assert (H2a: In (f (g a)) (img f (img g l))). auto.
             replace (f (g a)) with a in H2a. auto. symmetry;auto. } } 
         auto. } Qed.

  Lemma img_of_img3 (l: list B)(f: A->B)(g: B-> A)(Hl: IsOrd l):
    (forall x, In x l-> f (g x) = x) -> l = img f (img g l).
    Proof. intros. symmetry. auto using img_of_img2. Qed.
    
   
    Hint Resolve  fx_is_one_one img_of_img img_of_img1: core.
    Hint Resolve img_of_img2 img_of_img3: core.

   (* ---------------------- Isomorphism is commutative -----------------------*)
    Lemma iso_sym1 (G : @UG A)(G': @UG B)(f: A-> B)(g: B-> A):
      isomorph_using f g G G' -> isomorph_using g f G' G.
    Proof. { intro H. destruct H as [Ha H]; destruct H as [Hb H].
           split.
           { auto. }
           split.
           { auto. }
           { eapply f_gx_is_x with (l:= G). auto. apply Ha. } } Qed.

    Lemma iso_sym (G: @UG A)(G': @UG B): isomorphic G G' -> isomorphic G' G.
    Proof. { intro H. destruct H as [f H]. destruct H as [g H].
             exists g. exists f. apply iso_sym1. auto. } Qed.

    Lemma iso_using_iso (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
      isomorph_using f g G G' -> isomorphic G G'.
    Proof. intros h. exists f. exists g. auto. Qed.

    Lemma iso_using_iso1 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
      isomorph_using f g G G' -> isomorphic G' G.
    Proof. intro h. apply iso_sym. eapply iso_using_iso. eauto. Qed.

    Lemma iso_elim1 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(x:A):
      isomorph_using f g G G'-> In x G-> In (f x) G'.
   Proof. intros H Hx. replace (nodes G') with (img f G). auto. symmetry; apply H. Qed.  

   Lemma iso_elim2 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(x:B):
     isomorph_using f g G G'-> In x G'-> In (g x) G.
  Proof. intros H Hx. replace (nodes G) with (img g G'). auto. symmetry.
         apply iso_sym1 in H as Ha. apply Ha. Qed.
  
  
  Hint Immediate iso_sym1 iso_sym iso_elim1 iso_elim2: core.

  Hint Resolve iso_using_iso iso_using_iso1: core.

  (*--------------- Isomorphism is a one one function --------------------------------*)

  Lemma iso_one_one1 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
    isomorph_using f g G G' -> one_one_on G f.
  Proof.  intro H; eapply fx_is_one_one; apply H. Qed.

  Lemma iso_one_one2 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
    isomorph_using f g G G' -> one_one_on G' g.
  Proof. intro H. assert (h1: isomorph_using g f G' G); auto.
         eapply gx_is_one_one; apply h1. Qed. 

  Lemma iso_using_G' (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
    isomorph_using f g G G' -> nodes G' = (img f G).
  Proof.  intro H;apply H. Qed.

  Lemma iso_using_G (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
    isomorph_using f g G G' -> nodes G = (img g G').
  Proof. intro H0. cut (isomorph_using g f G' G). intro H;apply H. auto. Qed.

  Lemma iso_one_one_on_l (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(l: list A):
    isomorph_using f g G G'-> l [<=] G -> one_one_on l f.
  Proof. intros H H1. eapply fx_is_one_one. intros x h1. eapply H. auto. Qed.

  Lemma iso_one_one_on_s (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(s: list B):
    isomorph_using f g G G'-> s [<=] G' -> one_one_on s g.
  Proof. intros H H1. eapply gx_is_one_one. intros x h1.
         assert (H2: isomorph_using g f G' G). auto.
         eapply H2. auto. Qed.

  
    Hint Immediate iso_one_one1 iso_one_one2 iso_one_one_on_l iso_one_one_on_s
         iso_using_G iso_using_G': core.

    Lemma iso_cardinal (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A) :
      isomorph_using f g G G' -> |G|=|G'|.
  Proof. { intro H.  apply iso_one_one1 in H as H1.
           replace (nodes G') with (img f G). auto. 
           symmetry; eauto using iso_using_G'. } Qed.
  
  Lemma iso_sub_cardinal (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(X: list A):
    isomorph_using f g G G' -> NoDup X -> X [<=] G -> |X|= | img f X |.
  Proof. { intros H H0 H1.
         assert (H2: one_one_on G f). eauto.
         assert (H2a: one_one_on X f). eauto. auto. } Qed.

  Lemma iso_sub_cardinal1 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(Y: list B):
    isomorph_using f g G G' -> NoDup Y -> Y [<=] G' -> |Y|= | img g Y |.
   Proof. { intros H H0 H1.
         assert (H2: one_one_on G' g). eauto.
         assert (H2a: one_one_on Y g). eauto. auto. } Qed.

   (*------------- Isomorphism between graph preserves edge relation -------------*)
  
  
   Lemma iso_edg1 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(x y:A):
     isomorph_using f g G G' -> In x G -> In y G-> (edg G x y = edg G' (f x) (f y)).
  Proof. intro H;apply H. Qed.

  Lemma iso_edg2  (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(x y: B):
    isomorph_using f g G G' -> In x G'-> In y G'-> (edg G' x y = edg G (g x) (g y)).
  Proof. intro H0. cut (isomorph_using g f G' G). intro H;apply H. auto. Qed.

 Hint Immediate iso_cardinal iso_sub_cardinal iso_sub_cardinal1 iso_edg1 iso_edg2: core.

 Lemma iso_edg3(G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(x y:A):
   isomorph_using f g G G' -> In x G -> In y G-> edg G x y -> edg G' (f x) (f y).
  Proof.  intros; replace (edg G' (f x) (f y)) with (edg G x y); eauto.  Qed.

  Lemma iso_edg4  (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(x y: A):
    isomorph_using f g G G' -> In x G -> In y G-> ~ edg G x y -> ~ edg G' (f x) (f y).
  Proof. intros ; replace (edg G' (f x) (f y)) with (edg G x y); eauto. Qed.

  Hint Immediate iso_edg3 iso_edg4: core.


  (*----- f and g when composed with each other returns the initial sets -----------*)
                                                                

  Lemma iso_image1 (G : @UG A)(G': @UG B)(f: A-> B)(g: B-> A):
    isomorph_using f g G G' -> (nodes G') = (img f G).
  Proof. intros h1. destruct h1 as [h1 h2]. apply h1. Qed. 

  Lemma iso_image2 (G : @UG A)(G': @UG B)(f: A-> B)(g: B-> A):
    isomorph_using f g G G' -> (nodes G) = (img g G').
  Proof. intros h1. destruct h1 as [h1 h2]. apply h2. Qed. 

  Lemma iso_img_of_img1 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
    isomorph_using f g G G' -> (forall x, In x G -> g (f x) = x).
  Proof. intros h1. destruct h1 as [h1 h2]. apply h2. Qed.

   Lemma iso_img_of_img2 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A):
    isomorph_using f g G G' -> (forall x, In x G' -> f (g x) = x).
   Proof. intros h1. cut (isomorph_using  g f G' G). intro h2.
          destruct h2 as [h2 h3]. apply h3. auto. Qed.

    Lemma iso_img_of_img3 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(l: list A):
    IsOrd l -> l [<=] G -> isomorph_using f g G G' -> l = img g (img f l).
    Proof. intros h1 h2 h3. eapply img_of_img1. auto. intros x h4.
           eapply iso_img_of_img1. eauto. auto. Qed.

     Lemma iso_img_of_img4 (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(l: list B):
    IsOrd l -> l [<=] G' -> isomorph_using f g G G' -> l = img f (img g l).
  Proof. intros h1 h2 h3. eapply img_of_img3. auto. intros x h4.
           eapply iso_img_of_img2. eauto. auto. Qed.
  
    
  Hint Resolve iso_image1 iso_image2: core.
  Hint Resolve iso_img_of_img1 iso_img_of_img2 iso_img_of_img3 iso_img_of_img4: core.
  

   (* ------------- Isomorphism preserves Cliques and for a graph-----------------*)

   Lemma iso_cliq (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A) (K: list A):
    isomorph_using f g G G' -> K [<=] G-> Cliq G K -> Cliq G' (img f K).
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
  
  Lemma iso_cliq1 (G: @UG A)(G':@UG B)(K: list A):
    isomorphic G G' -> K [<=] G -> Cliq G K -> NoDup K -> (exists K', Cliq G' K' /\ |K|=|K'|).
  Proof. { intros H h1 H1 H2. destruct H as [f H]. destruct H as [g H].
         exists (img f K). split. eauto using iso_cliq.
         assert (H3: one_one_on K f). eauto. auto. } Qed.
  

  Lemma iso_cliq_in (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(K: list A):
    isomorph_using f g G G' -> Cliq_in G K -> Cliq_in G' (img f K).
  Proof. { intros H H1.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c].
         split.
         { destruct H as [Ha H]. destruct H as [Hb Hc].
           destruct Ha as [Ha1 Ha]. rewrite Ha1; auto. }
         split.
         { auto. }
         { eauto using iso_cliq. }  } Qed.

  Lemma iso_cliq_in1 (G: @UG A)(G':@UG B)(K: list A):
    isomorphic G G' -> Cliq_in G K -> (exists K', Cliq_in G' K' /\ |K|=|K'|).
  Proof. { intros H H1. destruct H as [f H]. destruct H as [g H].
           exists (img f K). split. eauto using iso_cliq_in.
           assert (H3: one_one_on K f). cut (K [<=] G). eauto. apply H1.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c]. auto. } Qed.

  Hint Immediate iso_cliq iso_cliq1 iso_cliq_in iso_cliq_in1: core.

   (*---------- Isomorphism preserves Stable set for a graph ----------------------------*)

   Lemma iso_stable (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(I: list A):
    isomorph_using f g G G' -> I [<=] G -> Stable G I -> Stable G' (img f I).
  Proof. {  unfold Stable. intros H h1 H1.  intros x y Hx Hy.
          assert (H2: exists x0, In x0 I /\ x = f x0). auto.
          destruct H2 as [x0 H2]. destruct H2 as [H2a H2b].
          assert (H3: exists y0, In y0 I /\ y = f y0). auto.
          destruct H3 as [y0 H3]. destruct H3 as [H3a H3b].
          replace x with (f x0). replace y with (f y0).
          assert (H2: edg G x0 y0 = false). auto. 
          replace (edg G' (f x0) (f y0)) with (edg G x0 y0).
            auto. apply H. all: auto. } Qed.
  
  Lemma iso_stable1 (G: @UG A)(G':@UG B)(I: list A):
    isomorphic G G' -> I [<=] G-> Stable G I -> NoDup I -> (exists I', Stable G' I' /\ |I|=|I'|).
  Proof. { intros H h1 H1 H2. destruct H as [f H]. destruct H as [g H].
         exists (img f I). split. eauto using iso_stable.
         assert (H3: one_one_on I f). eauto.
         auto. } Qed.

  Lemma iso_stable_in (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(I: list A):
    isomorph_using f g G G' -> Stable_in G I -> Stable_in G' (img f I).
  Proof. { intros H H1.
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c].
         split.
         { destruct H as [Ha H]. destruct H as [Hb Hc]. destruct Ha as [Ha1 Ha].
           rewrite Ha1; auto. }
         split.
         { auto. }
         { eauto using iso_stable. }  } Qed.

  Lemma iso_stable_in1 (G: @UG A)(G':@UG B)(I: list A):
    isomorphic G G' -> Stable_in G I -> (exists I', Stable_in G' I' /\ |I|=|I'|).
  Proof. { intros H H1. destruct H as [f H]. destruct H as [g H].
           exists (img f I). split. eauto using iso_stable_in.
           assert (H3: one_one_on I f).
           { cut (I [<=] G). eauto. auto. }
         destruct H1 as [H1a H1]. destruct H1 as [H1b H1c]. auto. } Qed.

  Hint Immediate iso_stable iso_stable1 iso_stable_in iso_stable_in1: core.

  (*----------- Isomorphism, graph coloring for graphs -------------------------*)
  
  
  Lemma iso_coloring (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(C: A->nat):
    isomorph_using f g G G' -> Coloring_of G C -> Coloring_of G' (fun (x:B) => C (g x)).
  Proof. { intros H H1. assert (Ha: isomorph_using g f G' G);auto. unfold Coloring_of.
           intros x y Hx Hy H2.
           assert (H3: edg G (g x) (g y)).
           { replace  (edg G (g x) (g y)) with (edg G' x y). auto. eauto. }
            apply H1; eauto. } Qed.
          
  Lemma iso_same_clrs  (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(C: A->nat):
    isomorph_using f g G G' -> Coloring_of G C -> (clrs_of C G) = clrs_of (fun (x:B) => C (g x)) G'.
  Proof. { intros H H1. assert (Ha: isomorph_using g f G' G). auto.
           assert (H2: (nodes G) = img g G'). apply H.
           unfold clrs_of; rewrite H2; auto. } Qed.
  
  Hint Resolve iso_coloring iso_same_clrs: core.


End GraphIsoProp.




Hint Resolve fx_is_one_one img_of_img img_of_img1: core.
Hint Resolve img_of_img2 img_of_img3: core.

Hint Immediate iso_sym1 iso_sym iso_elim1 iso_elim2: core.
Hint Resolve iso_using_iso iso_using_iso1: core.

 Hint Immediate iso_one_one1 iso_one_one2 iso_one_one_on_l iso_one_one_on_s
      iso_using_G iso_using_G': core.
 
Hint Immediate iso_cardinal iso_sub_cardinal iso_sub_cardinal1 iso_edg1 iso_edg2: core.
Hint Immediate iso_edg3 iso_edg4: core.
Hint Resolve iso_image1 iso_image2: core.
Hint Resolve iso_img_of_img1 iso_img_of_img2 iso_img_of_img3 iso_img_of_img4 : core.

Hint Immediate iso_cliq iso_cliq1 iso_cliq_in iso_cliq_in1: core.

Hint Immediate iso_stable iso_stable1 iso_stable_in iso_stable_in1: core.
Hint Resolve iso_coloring iso_same_clrs: core.





Section IsoMaxIKC.

  Context {A B: ordType }.

  (*-------------------- Max_K has an isomorphic counterpart--------------------- *)

  Lemma max_K_in_G' (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(K: list A):
    isomorph_using f g G G' -> Max_K_in G K -> Max_K_in G' (img f K). 
  Proof. { intros H H1. assert (H0: isomorph_using g f G' G); auto.
         apply  Max_K_in_intro.         
         { cut (Cliq_in G K); eauto. }
         { intros Y H2.
           replace (|Y|) with (|img g Y|).
           replace (|img f K|) with (|K|).
            assert (H3: Cliq_in G (img g Y)). eauto.
           eauto using Max_K_in_elim. eapply iso_sub_cardinal;eauto.
           symmetry. eapply iso_sub_cardinal; eauto. } } Qed.

  Lemma cliq_num_G' (G: @UG A)(G':@UG B)(n: nat):isomorphic G G' -> cliq_num G n -> cliq_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H as [g H].
           destruct H1 as [K H1].
           destruct H1 as [H1 H1b]. exists (img f K).
           split. eauto using max_K_in_G'. replace n with (|K|).
           symmetry. eapply iso_sub_cardinal;eauto. } Qed.
  
  Hint Immediate max_K_in_G' cliq_num_G': core.


  (*------------------- Max_I has an isomorphic counterpart----------------------- *)

   Lemma max_I_in_G' (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(I: list A):
    isomorph_using f g G G' -> Max_I_in G I -> Max_I_in G' (img f I).
   Proof. { intros H H1. assert (H0: isomorph_using g f G' G); auto.
         apply  Max_I_in_intro.         
         { cut (Stable_in G I); eauto. }
         { intros Y H2.
           replace (|Y|) with (|img g Y|).
           replace (|img f I|) with (|I|).
           assert (H3: Stable_in G (img g Y)). eauto.
           eauto using Max_I_in_elim. eapply iso_sub_cardinal;eauto.
           symmetry. eapply iso_sub_cardinal; eauto. } } Qed.

  Lemma i_num_G' (G: @UG A)(G':@UG B)(n: nat):
    isomorphic G G' -> i_num G n -> i_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H as [g H].
           destruct H1 as [I H1].
           destruct H1 as [H1 H1b]. exists (img f I).
           split. eauto using max_I_in_G'. replace n with (|I|).
           symmetry. eapply iso_sub_cardinal;eauto. } Qed.
  
  Hint Immediate max_I_in_G' i_num_G': core.

  (*-------------------- Cliq_num and Isomorphism ---------------------------------*)

   Lemma best_coloring_of_G' (G: @UG A)(G':@UG B)(f: A->B)(g: B-> A)(C: A->nat):
    isomorph_using f g G G' -> Best_coloring_of G C -> Best_coloring_of G' (fun (x:B) => C (g x)).
  Proof. { unfold Best_coloring_of.  intros H H1.
         assert (H0: isomorph_using g f G' G). auto.
         destruct H1 as [H1 H2].
         split.
         { eauto using iso_coloring. }
         { intros C' H3.
           assert (H4: (clrs_of C G) = clrs_of (fun (x:B) => C (g x)) G').
           { eapply iso_same_clrs. apply H. auto. }
           rewrite <- H4.
           assert (H5: (clrs_of C' G') = clrs_of (fun (x:A) => C' (f x)) G).
           eapply iso_same_clrs with (f0:=g). all: auto.
           rewrite H5.
           apply H2. eauto using iso_coloring. } } Qed. 
                  
  Lemma chrom_num_G' (G: @UG A)(G':@UG B)(n: nat):
    isomorphic G G' -> chrom_num G n -> chrom_num G' n.
  Proof. { intros H H1. destruct H as [f H]. destruct H as [g H].
           destruct H1 as [C H1]. destruct H1 as [H1 H2].
           exists (fun (x:B) => C (g x)). split. eauto using best_coloring_of_G'.
           subst n. replace (clrs_of (fun x : B => C (g x)) G') with (clrs_of C G).
           auto. destruct H1 as [H1 H2].
           eapply iso_same_clrs. apply H. auto. } Qed.

  Hint Resolve best_coloring_of_G': core.
  Hint Immediate chrom_num_G': core.

End IsoMaxIKC.


Hint Immediate max_K_in_G' cliq_num_G': core.
Hint Immediate max_I_in_G' i_num_G': core.

Hint Resolve best_coloring_of_G': core.
Hint Immediate chrom_num_G': core.



Section IsomorphicNicePerfect.

  Context { A B: ordType }.
  
  (*------------Isomorphism, nice graphs and perfect graph--------------------------------*)

  Lemma nice_G' (G: @UG A)(G':@UG B) : isomorphic G G' -> Nice G -> Nice G'.
  Proof. { intro H.  assert (H0: isomorphic G' G). auto.
         unfold Nice. intros H1 n H2.
         cut (chrom_num G n). eauto. cut (cliq_num G n); eauto. } Qed.

  Lemma iso_subgraphs (G H: @UG A)(G':@UG B)(f: A->B)(g: B-> A): isomorph_using f g G G'->
        Ind_subgraph H G ->(exists H', Ind_subgraph H' G'/\ isomorph_using f g H H').
  Proof.  { intros F1 F2.
            assert (F0: isomorph_using g f G' G). auto. 
            assert (Nk: IsOrd (img f H)). auto.
            pose H' := (ind_at (img f H) G').
            exists H'.
            assert (h0: H' [<=] G').
            { replace (nodes G') with (img f G). simpl.
              cut (img f H [<=] img f G). auto. 
              eapply img_subset. apply F2. symmetry. apply F1. }
            assert (h1: img f H [<=] G').
            { replace (nodes G') with (img f G).
                cut (H [<=] G). auto. apply F2.  symmetry. apply F1. }
            assert (h2: img f H = inter (img f H) G').
            { apply set_equal; auto. }
            split.
            (* Ind_subgraph H' G' *)
            {  unfold Ind_subgraph. split.
               { auto. }
               { unfold H'. simpl. intros. symmetry. auto. } }
           
            {  (* isomorph_using f g H H' *)
              unfold isomorph_using.
              split.
              { (*--  morph_using f H H'--*)
                split.
                (*-- H' = img f H --*)
                unfold H'. simpl. auto.
                (*-- forall x y : A, In x H -> In y H -> edg H x y = edg H' (f x) (f y) --*)
                simpl. intros x y Hx Hy.
                replace (edg H x y) with (edg G x y). rewrite <- h2.
                assert (H2: In (f x) (img f H)). auto.
                replace ((edg G' at_ img f H) (f x) (f y)) with (edg G' (f x)(f y)).
                destruct F2. cut(In y G). cut(In x G). all: auto. eauto.
                symmetry. auto.  }
              split.
              {(*---  morph_using g H' H--*)
                split.
                (*--  H = img g H' ---*)
                unfold H'. simpl. rewrite <- h2.
                assert (h3: IsOrd H). auto.
                assert (h4: H [<=] G). auto. eapply iso_img_of_img3 with (G0:=G).
                all: auto. eauto.
                (* forall x y : B, In x H' -> In y H' -> edg H' x y = edg H (g x) (g y)--*)
                simpl. rewrite <- h2. intros x y Hx Hy.
                replace ((edg G' at_ img f H) x y) with (edg G' x y).
                replace (edg H (g x) (g y)) with (edg G (g x) (g y)).
                apply F1. all:auto. symmetry. apply F2.
                assert (h3: exists x0, In x0 H /\ x = f x0). auto.
                destruct h3 as [x0 h3]. destruct h3 as [h3 h4]. subst x.
                replace  (g (f x0)) with x0. auto. symmetry. apply F1. apply F2. auto.
                assert (h3: exists y0, In y0 H /\ y = f y0). auto.
                destruct h3 as [y0 h3]. destruct h3 as [h3 h4]. subst y.
                replace  (g (f y0)) with y0. auto. symmetry. apply F1. apply F2. auto. }
                intros x h3. apply F1. apply F2. auto. } } Qed.
                


End IsomorphicNicePerfect.

Hint Immediate nice_G' iso_subgraphs : core.



Section IsoPerfect.
  
  Context {A B: ordType}.

Lemma perfect_G' (G: @UG A)(G':@UG B): isomorphic G G' -> Perfect G -> Perfect G'.
  Proof. { intro F.  assert (F0: isomorphic G' G). auto.
         unfold Perfect. destruct F0 as [g F0]. destruct F0 as [f F0].
         intros F1 H' F2.
         assert (F3: exists H, Ind_subgraph H G /\ isomorph_using g f H' H).
         { eapply iso_subgraphs. apply F0. auto. }
         destruct F3 as [H F3]. destruct F3 as [F3 F4]. 
         cut (Nice H).
         { cut (isomorphic H H'). eauto using nice_G'.
           exists f. exists g. cut (isomorph_using f g H H'); auto. } auto.  } Qed.

End IsoPerfect.

Hint Immediate perfect_G': core.





Section IsomorphTrans.
  Context {A B C: ordType}.

  Lemma iso_trans (G1 :@UG A)(G2: @UG B)(G3: @UG C):
    isomorphic G1 G2 -> isomorphic G2 G3 -> isomorphic G1 G3.
  Proof. { intros h1 h2. destruct h1 as [f h1]. destruct h1 as [g h1].
           destruct h2 as [f' h2]. destruct h2 as [g' h2].
           assert (h3: nodes G2 = img f G1). eauto.
           assert (h4: nodes G1 = img g G2). eauto.
           assert (h5: nodes G3 = img f' G2). eauto.
           assert (h6: nodes G2 = img g' G3). eauto.
           
           set (F:= fun x:A => f' (f  x)). set (G:= fun z:C => g (g' z)).
           exists F. exists G. unfold isomorph_using.
           split.
           (* --- morph_using F G1 G3 ------ *)
           { unfold morph_using.
             split.
             (*--- G3 = img F G1 ----*)
             unfold F. replace (img (fun x : A => f' (f x)) G1) with (img f' (img f G1)).
             rewrite <- h3. auto. eauto. 
             (*-- (forall x y : A, In x G1 -> In y G1 -> edg G1 x y = edg G3 (F x) (F y))---*)
             unfold F.
             intros x y hx hy. replace (edg G1 x y) with (edg G2 (f x) (f y)).
             cut (In (f y) G2). cut (In (f x) G2). apply h2.
             rewrite h3;auto. rewrite h3;auto. symmetry. apply h1. all: auto. }
           split. 
           (* ---- morph_using G G3 G1 ------ *)
           { unfold morph_using.
             split.
             (*--- G1 = img G G3 ----*)
             unfold G. replace (img (fun z : C => g (g' z)) G3) with (img g (img g' G3)).
             rewrite <- h6. auto. eauto. 
             (*-- (forall x y : C, In x G3 -> In y G3 -> edg G3 x y = edg G1 (G x) (G y) ---*)
             unfold G.
             intros x y hx hy. replace (edg G3 x y) with (edg G2 (g' x) (g' y)).
             cut (In (g' y) G2). cut (In (g' x) G2). apply h1.
             rewrite h6;auto. rewrite h6;auto. symmetry. apply h2. all: auto. }
           (* -----(forall x : A, In x G1 -> G (F x) = x) -------*)
           { intros x hx. unfold F. unfold G.
             replace (g' (f' (f x))) with (f x). apply h1. auto.
             symmetry. apply h2. rewrite h3. auto. } } Qed.
  
End IsomorphTrans.

Hint Immediate iso_trans: core.

 