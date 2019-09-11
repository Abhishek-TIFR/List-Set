



(* ------------------ Descriptions--------------------------------------------------

 In this file we define the concept of Stable Set, Cliq and Coloring for an undirected
 graph.  We also define boolean functions to check these properties. We connect these 
 properties with boolean functions using the following reflection lemmas.
 
 Predicate              Boolean function       Joining Lemma
 Stable G I             stable G I             stableP
 Max_I_in G I           max_I_in G I           max_I_inP
 Cliq G K               cliq G K               cliqP
 Max_K_in G K           max_K_in G K           max_K_inP
 Coloring_of G f        coloring_of G f        coloring_ofP


 (Max_I_in G I) declares that I is a maximum size stable set in G. 
 (Max_K_in G I) declares that K is a maximum size cliq in G. 

 Definition Stable_in (G: UG)(I: list A):= I [<=] G /\ IsOrd I /\ Stable G I.
 Definition Cliq_in (G:UG)(K: list A):Prop := K [<=] G /\ IsOrd K /\ Cliq G K.

 Definition i_num (G:UG)(n:nat):= exists I, Max_I_in G I /\ |I|=n.
 Definition cliq_num (G:UG)(n:nat):= exists K, Max_K_in G K /\ |K|=n.

 Definition clrs_of (f:A->nat) (l:list A): list nat:= (img f l).
 Definition chrom_num (G: UG) (n: nat):= 
                              exists f, Best_coloring_of G f /\ | clrs_of f G | = n.

 We also define the notion of a perfect graph as follows:
 
 Definition Nice (G: UG): Prop:= forall n, cliq_num G n -> chrom_num G n.
 Definition Perfect (G: UG): Prop:= forall G1, Ind_subgraph G1 G -> Nice G1.
 
---------------------------------------------------------------------------------------*)


Require Export UG.

Set Implicit Arguments.

Section MoreOnDecidableGraphs.

  Context { A: ordType }.

  
  (*------------  Stable set and independence number in a graph G ------------*)
  Definition Stable (G: UG)(I: list A): Prop:=
    (forall x y, In x I-> In y I -> edg G x y = false).
  Definition stable (G: UG)(I: list A):=
    (forall_xyb (fun x y => edg G x y == false) I).

  Definition Stable_in (G: UG)(I: list A):= I [<=] G /\ IsOrd I /\ Stable G I.

  Lemma Stable_elim (G:UG)(I: list A)(x y:A): Stable G I -> In x I-> In y I-> edg G x y = false.
  Proof. { intros H Hx Hy.  unfold Stable in H. specialize (H x y Hx Hy) as H'. auto. } Qed.
  Lemma Stable_in_elim (G:UG)(I: list A): Stable_in G I -> Stable G I.
  Proof. intro H; apply H. Qed.
  Lemma Stable_in_elim1 (G:UG)(I: list A): Stable_in G I -> I [<=] G.
  Proof. intro H; apply H. Qed.
  Lemma Stable_in_elim2 (G:UG)(I: list A): Stable_in G I -> IsOrd I.
  Proof. intro H; apply H. Qed.
  
  Lemma stableP (G: UG)(I: list A): reflect (Stable G I) (stable G I).
  Proof. { apply reflect_intro. split;unfold stable; unfold Stable.
         {  intro H.  apply /forall_xyP; intros; apply /eqP; auto. }
         {  intro H. move /forall_xyP in H. intros x y H1 H2; apply /eqP; auto. } } Qed.
  Lemma nil_is_stable (G: UG): stable G nil.
  Proof. unfold stable. apply /forall_xyP. auto. Qed.

  Hint Resolve Stable_elim:core.
  
  Hint Resolve Stable_in_elim Stable_in_elim1 Stable_in_elim2: core.
  Hint Resolve stableP nil_is_stable: core.
  
  (*------ Largest stable set and its properties------------------------------*)
  Definition Max_I_in (G: UG)(I: list A):= Max_sub_in G I (fun I => stable G I).
  Definition max_I_in (G: UG)(I: list A):= max_sub_in G I (fun I => stable G I).

  Lemma max_I_inP (G: UG)(I:list A): reflect (Max_I_in G I)(max_I_in G I).
  Proof. apply max_sub_inP; auto. Qed.

  Lemma exists_Max_I_in (G: UG): exists I, Max_I_in G I.
  Proof. { specialize (exists_largest_in G (fun I=> stable G I)).
         intro H.
         assert (Ha: exists X : list A, In X (pw G) /\ (fun I : list A => stable G I) X).
         { exists nil. split; auto. }
         apply H in Ha as Hb. destruct Hb as [I0 Hb]. exists I0.
         unfold Max_I_in; unfold Max_sub_in;destruct Hb as [Hb Hc]; destruct Hc as [Hc Hd].
         split.
         {  auto. }
         split.
         { eauto. }
         split.
         { auto. }
         { intros. apply Hd. auto. auto. } } Qed.
  
  Definition i_num (G:UG)(n:nat):= exists I, Max_I_in G I /\ |I|=n.
  Lemma i_num_of (G: UG): exists n, i_num G n.
  Proof. { specialize (exists_Max_I_in G) as HI. destruct HI as [I H].
           exists (|I|). unfold i_num. exists I. split; auto.  } Qed.
  
  (* Use of above lemma can be:  destruct (i_num_of G) as [n H]. *)
  
 
  Lemma Max_I_in_elim1 (G: UG)(I: list A): Max_I_in G I -> Stable G I.
  Proof. intro H. apply /stableP. apply H.  Qed.
  Lemma Max_I_in_elim2 (G: UG)(I: list A): Max_I_in G I -> Stable_in G I.
  Proof. intro H. unfold Stable_in. split. eauto.  split. eauto. apply /stableP. apply H.  Qed.
  
  Lemma Max_I_in_elim3 (G: UG)(I X: list A):
    Max_I_in G I ->  IsOrd X -> X [<=] G-> Stable G X -> |X| <= |I|.
  Proof. { intros H H1 H2 H3. destruct H as [Ha H]; destruct H as [Hb H].
           apply H; auto. apply /stableP;auto.  } Qed.

  Lemma Max_I_in_elim (G: UG)(I X: list A):
    Max_I_in G I ->  Stable_in G X -> |X| <= |I|.
  Proof. intros H H1. eapply Max_I_in_elim3 with (G:=G). all:auto. eauto. Qed.
  
  Lemma Max_I_in_intro (G: UG)( I: list A):
    Stable_in G I -> (forall I', Stable_in G I' -> |I'| <= |I|) -> Max_I_in G I.
  Proof. { intros H H1. unfold Max_I_in. unfold Max_sub_in.
         split. auto. split. apply H. split. apply /stableP. apply H.
         intros I' H2 H3. apply H1. split. auto. split. eauto.
         apply /stableP;auto. } Qed.

  Hint Resolve max_I_inP exists_Max_I_in Max_I_in_elim1 Max_I_in_elim2 : core.
  Hint Resolve Max_I_in_elim: core. 
  
  Lemma i_num_same (G: UG)(n m:nat): i_num G n -> i_num G m -> n=m.
  Proof. {  intros Hn Hm.
           destruct Hn as [I1 Hn]. destruct Hm as [I2 Hm].
           cut (n<=m /\ m<=n). omega.
           destruct Hn as [Hn1 Hn2]. destruct Hm as [Hm1 Hm2].
           unfold Max_I_in in Hn1.  unfold Max_I_in in Hm1.
           split; subst n; subst m; eapply Max_I_in_elim3;eauto. } Qed.

  Hint Resolve i_num_same : core.

  Lemma i_num_max_I (G: UG)(n :nat)(I: list A): i_num G n -> Max_I_in G I ->  n = |I|.
  Proof. { intros h1 h2. destruct h1 as [I' h1]. destruct h1 as [h1 h3].
           subst n. cut ((| I' |) <= (| I |) ). cut ((| I' |) >= (| I |)).
           omega.
           { apply h1. cut (I [<=] G). cut (IsOrd I). all: auto.
             eauto. apply /stableP. auto. }
           { apply h2. cut (I' [<=] G). cut (IsOrd I'). all: auto.
             eauto. apply /stableP. auto. } } Qed.
           

  Lemma Stable_in_HG (H G:UG)(I: list A): Ind_subgraph H G-> Stable_in H I-> Stable_in G I.
  Proof. { unfold Stable_in. intros h0 h1. unfold Ind_subgraph in h0.
         destruct h0 as [h0 h]. destruct h1 as [h2 h1]. destruct h1 as [h3 h1].
         repeat try (split;auto). unfold Stable. intros x y h4 h5.
         replace (edg G x y) with (edg H x y). apply h1;auto. auto. } Qed.

  Lemma Stable_in_GH (H G:UG)(I: list A):
    Ind_subgraph H G-> Stable_in G I-> I [<=] H-> Stable_in H I.
  Proof. { unfold Stable_in. intros h0 h1 H0. unfold Ind_subgraph in h0.
         destruct h0 as [h0 h]. destruct h1 as [h2 h1]. destruct h1 as [h3 h1].
         repeat try (split;auto). unfold Stable. intros x y h4 h5.
         replace (edg H x y) with (edg G x y). apply h1;auto. symmetry;auto. } Qed.
  
  
  Lemma i_num_HG (H G: UG)(m n:nat): Ind_subgraph H G-> i_num H m -> i_num G n-> m<=n.
  Proof. { intro h. unfold i_num. intros h1 h2.
         destruct h1 as [I h1]. destruct h1 as [h1 hm].
         destruct h2 as [Ig h2]. destruct h2 as [h2 hn].
         assert (h3: Stable_in G I).
         { cut (Stable_in H I). eauto using Stable_in_HG. auto. }
         subst n. subst m.  eapply Max_I_in_elim; eauto. } Qed.
   
  Hint Immediate Stable_in_HG Stable_in_GH i_num_HG:core.
  
  Lemma i_num_gt (G: UG)(n:nat): (nodes G) <> nil -> i_num G n -> n >= 1. 
  Proof. { intros h1 h2.
           assert (h1a: exists a, In a G). auto.
           destruct h1a as [a h1a].
           set(I0:= a::nil). destruct h2 as [I h2]. destruct h2 as [h2 h3].
           subst n. assert (h3: |I0| = 1). simpl; auto. rewrite <- h3.
           apply h2. cut (I0 [<=] G). cut (IsOrd I0). auto.
           unfold I0. constructor. subst I0. intros x h4.
           destruct h4. subst x;auto. inversion H.
           apply /stableP. unfold Stable. subst I0.
           intros x y hx hy. simpl in hx;simpl in hy.
           destruct hx as [hx |hx]; destruct hy as [hy |hy].
           { subst x;subst y;auto. } all: auto. } Qed.
           

  Hint Immediate i_num_gt: core.
    
  (*-----  Cliq and the Cliq number for a given graph G ----------------------*)
  
  Definition Cliq (G:UG)(K: list A):Prop := (forall x y, In x K-> In y K -> x=y \/ edg G x y).
  Definition cliq (G:UG)(K: list A):bool:= forall_xyb (fun x y=> (x==y) || edg G x y) K.

  Definition Cliq_in (G:UG)(K: list A):Prop := K [<=] G /\ IsOrd K /\ Cliq G K.

  Lemma Cliq_elim (G:UG)(K: list A)(x y:A): Cliq G K -> In x K-> In y K-> x<>y -> edg G x y.
  Proof. { intros H Hx Hy H1.  unfold Cliq in H. specialize (H x y Hx Hy) as H'.
           destruct H'. contradiction. auto. } Qed.
  Lemma Cliq_in_elim (G:UG)(K: list A): Cliq_in G K -> Cliq G K.
  Proof. intro H; apply H. Qed.
  Lemma Cliq_in_elim1 (G:UG)(K: list A): Cliq_in G K -> K [<=] G.
  Proof. intro H; apply H. Qed.
  Lemma Cliq_in_elim2 (G:UG)(K: list A): Cliq_in G K -> IsOrd K.
  Proof. intro H; apply H. Qed.

  Lemma cliqP (G: UG)(K: list A): reflect (Cliq G K) (cliq G K).
  Proof. { apply reflect_intro. split;unfold cliq; unfold Cliq.
           {  intro H. apply /forall_xyP.  intros x y H0 H1. apply /orP.
              specialize (H x y H0 H1) as H2. destruct H2; auto. }
           {  intro H. move /forall_xyP in H. intros x  y H0 H1.
              specialize (H x y H0 H1) as H2. move /orP in H2. destruct H2; auto. } } Qed.
  
   Lemma nil_is_cliq (G: UG): cliq G nil.
   Proof. unfold cliq. apply /forall_xyP. auto. Qed.

   Hint Resolve Cliq_in_elim Cliq_in_elim1 Cliq_in_elim2: core.
   Hint Resolve Cliq_elim cliqP nil_is_cliq: core.

  Definition Max_K_in (G: UG)(K: list A):= Max_sub_in G K (fun K => cliq G K).
  Definition max_K_in (G: UG)(K: list A):= max_sub_in G K (fun K => cliq G K).

  Lemma max_K_inP (G: UG)(K:list A): reflect (Max_K_in G K)(max_K_in G K).
  Proof. apply max_sub_inP; auto. Qed.

  Lemma exists_Max_K_in (G: UG): exists K, Max_K_in G K.
  Proof. { specialize (exists_largest_in G (fun K=> cliq G K)).
         intro H.
         assert (Ha: exists X : list A, In X (pw G) /\ (fun K : list A => cliq G K) X).
         { exists nil. split; auto. }
         apply H in Ha as Hb. destruct Hb as [K0 Hb]. exists K0.
         unfold Max_K_in; unfold Max_sub_in;destruct Hb as [Hb Hc]; destruct Hc as [Hc Hd].
         split.
         {  auto. }
         split.
         { eauto. }
         split.
         { auto. }
         { intros. apply Hd. auto. auto. } } Qed.


  Definition cliq_num (G:UG)(n:nat):= exists K, Max_K_in G K /\ |K|=n.
  
  Lemma cliq_num_of (G: UG): exists n, cliq_num G n.
  Proof. { specialize (exists_Max_K_in G) as HK. destruct HK as [K H].
           exists (|K|). unfold cliq_num. exists K. split;auto.  } Qed.
  
  (* Use of above lemma can be :  destruct (cliq_num_of G) as [n H]. *)
  
  Lemma Max_K_in_elim1 (G: UG)(K: list A): Max_K_in G K -> Cliq G K.
  Proof. intro H. apply /cliqP. apply H.  Qed.
  Lemma Max_K_in_elim2 (G: UG)(K: list A): Max_K_in G K -> Cliq_in G K.
  Proof. intro H. unfold Cliq_in. split. eauto.  split. eauto. apply /cliqP. apply H.  Qed.
  Lemma Max_K_in_elim3 (G: UG)(K X: list A):
    Max_K_in G K ->  IsOrd X -> X [<=] G-> Cliq G X -> |X| <= |K|.
  Proof. { intros H H1 H2 H3. destruct H as [Ha H]; destruct H as [Hb H].
           apply H; auto. apply /cliqP;auto. } Qed.
  
  Lemma Max_K_in_elim (G: UG)(K X: list A):
    Max_K_in G K ->  Cliq_in G X -> |X| <= |K|.
  Proof. intros H H1. eapply Max_K_in_elim3 with (G:=G). all:auto. eauto. Qed.
  
  Lemma Max_K_in_intro (G: UG)( K: list A):
    Cliq_in G K -> (forall K', Cliq_in G K' -> |K'| <= |K|) -> Max_K_in G K.
  Proof. { intros H H1. unfold Max_K_in. unfold Max_sub_in.
         split. auto. split. apply H. split. apply /cliqP. apply H.
         intros K' H2 H3. apply H1. split. auto. split. eauto.
         apply /cliqP;auto. } Qed.
  
  Hint Resolve max_K_inP exists_Max_K_in Max_K_in_elim1 Max_K_in_elim2 : core.
  Hint Resolve Max_K_in_elim: core.
  
  Lemma cliq_num_same (G: UG)(n m:nat): cliq_num G n -> cliq_num G m -> n=m.
  Proof.  {  intros Hn Hm.
           destruct Hn as [K1 Hn]. destruct Hm as [K2 Hm].
           cut (n<=m /\ m<=n). omega.
           destruct Hn as [Hn1 Hn2]. destruct Hm as [Hm1 Hm2].
           unfold Max_K_in in Hn1.  unfold Max_K_in in Hm1.
           split; subst n; subst m; eapply Max_K_in_elim3;eauto. } Qed.

  Hint Resolve cliq_num_same:core.

  Lemma Cliq_in_HG (H G:UG)(K: list A): Ind_subgraph H G-> Cliq_in H K-> Cliq_in G K.
  Proof. { unfold Cliq_in. intros h0 h1. unfold Ind_subgraph in h0.
         destruct h0 as [h0 h]. destruct h1 as [h2 h1]. destruct h1 as [h3 h1].
         repeat try (split;auto). unfold Cliq. intros x y h4 h5.
         replace (edg G x y) with (edg H x y). apply h1;auto. auto. } Qed.

  Lemma Cliq_in_GH (H G:UG)(K: list A):
    Ind_subgraph H G-> Cliq_in G K -> K [<=] H-> Cliq_in H K.
  Proof. { unfold Cliq_in. intros h0 h1 H0. unfold Ind_subgraph in h0.
         destruct h0 as [h0 h]. destruct h1 as [h2 h1]. destruct h1 as [h3 h1].
         repeat try (split;auto). unfold Cliq. intros x y h4 h5.
         replace (edg H x y) with (edg G x y). apply h1;auto. symmetry;auto. } Qed.
  

  
  Lemma cliq_num_HG (H G: UG)(m n:nat): Ind_subgraph H G-> cliq_num H m -> cliq_num G n-> m<=n.
  Proof. { intro h. unfold cliq_num. intros h1 h2.
         destruct h1 as [I h1]. destruct h1 as [h1 hm].
         destruct h2 as [Ig h2]. destruct h2 as [h2 hn].
         assert (h3: Cliq_in G I).
         { cut (Cliq_in H I). eauto using Cliq_in_HG. auto. }
         subst n. subst m.  eapply Max_K_in_elim; eauto. } Qed.
   
  Hint Immediate Cliq_in_HG Cliq_in_GH cliq_num_HG:core.

   Lemma cliq_num_gt (G: UG)(n:nat): (nodes G) <> nil -> cliq_num G n -> n >= 1.
  Proof. { intros h1 h2.
           assert (h1a: exists a, In a G). auto.
           destruct h1a as [a h1a].
           set(I0:= a::nil). destruct h2 as [I h2]. destruct h2 as [h2 h3].
           subst n. assert (h3: |I0| = 1). simpl; auto. rewrite <- h3.
           apply h2. cut (I0 [<=] G). cut (IsOrd I0). auto.
           unfold I0. constructor. subst I0. intros x h4.
           destruct h4. subst x;auto. inversion H.
           apply /cliqP. unfold Cliq. subst I0.
           intros x y hx hy. simpl in hx;simpl in hy.
           destruct hx as [hx |hx]; destruct hy as [hy |hy].
           { subst x;subst y;auto. } all: auto. } Qed.

  Hint Immediate cliq_num_gt: core.
 
   
   (*------ Concepts of Coloring and the chromatic number of a graph G ------------------*)
  Definition Coloring_of (G: UG)(f: A-> nat): Prop:=
    forall x y, In x G-> In y G -> edg G x y -> f x <> f y.
  
  Definition coloring_of (G: UG)(f: A-> nat):bool:=
    forall_xyb (fun x y => negb (edg G x y)|| negb (f x == f y)) G.
  Lemma coloring_ofP (G: UG)(f: A->nat): reflect (Coloring_of G f)(coloring_of G f).
  Proof. { apply reflect_intro. unfold coloring_of;unfold Coloring_of.
         split.
         { intro H; apply /forall_xyP; intros x y Hx Hy; apply /impP.
           intro H1; apply /negP; move /eqP; apply H;auto. }
         { move /forall_xyP. intro H. intros x y Hx Hy.
           specialize (H x y Hx Hy) as H1; move /impP in H1; intro H2.
           apply H1 in H2 as H3; move /negP in H3; move /eqP; auto. } } Qed.
        
  Lemma exists_coloring (G: UG): exists f, Coloring_of G f.
  Proof. { exists ( fun x => idx x G).  unfold Coloring_of.
         intros x y Hx Hy HE. apply diff_index. all: auto.
         eapply no_self_edg;eauto. } Qed.

   
  Definition clrs_of (f:A->nat) (l:list A): list nat:= (img f l).
   
   Definition Best_coloring_of (G: UG) (f:A->nat): Prop :=
     Coloring_of G f /\ (forall f1, Coloring_of G f1 -> | clrs_of f G | <= | clrs_of f1 G|).
   
   Definition chrom_num (G: UG) (n: nat):= exists f, Best_coloring_of G f /\ | clrs_of f G | = n.

   Lemma best_clrs_same_size (G: UG)(f1 f2: A->nat):
     Best_coloring_of G f1 -> Best_coloring_of G f2 -> |clrs_of f1 G|=|clrs_of f2 G|.
   Proof.  { intros h1 h2. destruct h1 as [h1a h1];destruct h2 as [h2a h2].
           cut((| clrs_of f1 G |) <= (| clrs_of f2 G |)).
           cut ((| clrs_of f2 G |) <= (| clrs_of f1 G |)). omega. all: eauto. } Qed.
   Lemma chrom_num_same (G:UG)(n m:nat): chrom_num G n-> chrom_num G m -> n=m.
   Proof. { intros h1 h2. destruct h1 as [f1 h1]. destruct h1 as [h1a h1].
          destruct h2 as [f2 h2]. destruct h2 as [h2a h2]. subst m;subst n.
          apply best_clrs_same_size;auto. } Qed. 

   Lemma clrs_of_inc (K1: list A)(K2: list A)(f:A-> nat):
     K1 [<=] K2 -> (clrs_of f K1) [<=] (clrs_of f K2).
   Proof.  unfold clrs_of; auto. Qed.
   Lemma clrs_of_inc1 (K1: list A)(K2: list A)(f: A->nat):
     K1 [<=] K2 -> |(clrs_of f K1)| <= |(clrs_of f K2)|.
   Proof. unfold clrs_of; auto. Qed.
   
   Hint Resolve chrom_num_same clrs_of_inc clrs_of_inc1: core.

   Lemma coloring_of_HG (H G: UG)(f: A-> nat): Ind_subgraph H G-> Coloring_of G f-> Coloring_of H f.
   Proof. { unfold Coloring_of. intros h0 h1. unfold Ind_subgraph in h0.
            destruct h0 as [h0 h]. intros x y h2 h3 h4.
            apply h1. all: try auto. replace (edg G x y) with (edg H x y); auto. } Qed.
   Lemma chrom_num_HG (H G: UG)(m n: nat): Ind_subgraph H G-> chrom_num H m-> chrom_num G n-> m<=n.
   Proof. { intro h. unfold chrom_num. intros h1 h2.
           destruct h1 as [fh h1]. destruct h1 as [h1 hm].
           destruct h2 as [fg h2]. destruct h2 as [h2 hn].
           assert (h3: Coloring_of H fg).
           { cut (Coloring_of G fg). eauto using coloring_of_HG. apply h2.  }
           subst n. subst m.
           cut ( (| clrs_of fh H |) <= (| clrs_of fg H |)).
           cut ( (| clrs_of fg H |) <= (| clrs_of fg G |)). omega.
           cut (H [<=] G). auto. apply h.  apply h1; auto. } Qed.

   Hint Immediate coloring_of_HG chrom_num_HG: core.
   
   (*----- Think about the proof of existence of a best coloring----------------------------*)

   
   (*-------- Concepts of nice graph and  perfect graphs -------------------------------- *)
   Definition Nice (G: UG): Prop:= forall n, cliq_num G n -> chrom_num G n.
   Definition Perfect (G: UG): Prop:= forall G1, Ind_subgraph G1 G -> Nice G1.
      
   Lemma perfect_is_nice (G: UG): Perfect G -> Nice G.
   Proof.  unfold Perfect. intros H; apply H. auto.  Qed.

   Hint Resolve perfect_is_nice: core.

   Lemma perfect_sub_perfect (G H: UG): Perfect G-> Ind_subgraph H G-> Perfect H.
   Proof. unfold Perfect. intros. cut (Ind_subgraph G1 G). auto. eauto. Qed.
   
    
   (*---------  More colors needed than the largest cliq size --------------------------*)

   Lemma clrs_on_a_cliq  (G: UG)(K: list A)(f: A->nat):
     Cliq_in G K-> Coloring_of G f -> |K| = |clrs_of f K|.
   Proof. { intros H H1.
            unfold clrs_of. match_up (|K|) (| img f K|).
            { auto. }
            { cut (| img f K| <= |K|).
              move /ltP in H0. intro H2. omega. auto. }
            { move /ltP in H0.
              assert (H2: ~ one_one_on K f).
              { cut(NoDup K). eauto. unfold Cliq_in in H.
                cut (IsOrd K). auto. apply H. }
              unfold one_one_on in H2. unfold Coloring_of in H1.
              absurd (forall x y : A, In x K -> In y K -> x <> y -> f x <> f y).
              apply H2. intros x y Hx Hy Hxy. 
              destruct H as [Ha H]. destruct H as [Hb H].
              apply H1;auto.  eapply Cliq_elim;eauto. } }  Qed.
   
   Lemma more_clrs_than_cliq_size (G: UG)(K: list A)(f: A->nat):
     Cliq_in G K-> Coloring_of G f -> |K| <= |clrs_of f G|.
   Proof. { intros H H1.
          assert (H2: | K | = |clrs_of f K|).
          { unfold clrs_of. match_up (|K|) (| img f K|).
            { auto. }
            { cut (| img f K| <= |K|).
              move /ltP in H0. intro H2. omega. auto. }
            { move /ltP in H0.
              assert (H2: ~ one_one_on K f).
              { cut(NoDup K). eauto. unfold Cliq_in in H.
                cut (IsOrd K). auto. apply H. }
              unfold one_one_on in H2. unfold Coloring_of in H1.
              absurd (forall x y : A, In x K -> In y K -> x <> y -> f x <> f y).
              apply H2. intros x y Hx Hy Hxy. 
              destruct H as [Ha H]. destruct H as [Hb H].
              apply H1;auto.  eapply Cliq_elim;eauto. } }    
          cut (|clrs_of f K| <= | clrs_of f G|). omega. 
          destruct H as [H H']. auto. } Qed.
   
   Lemma more_clrs_than_cliq_num (G: UG)(n:nat)(f: A->nat):
     cliq_num G n-> Coloring_of G f -> n <= |clrs_of f G|.
   Proof. { intros H H1. destruct H as [K H]. destruct H as [Ha H].
          assert (H2: Cliq_in G K); auto. subst n.
          apply more_clrs_than_cliq_size;auto. } Qed.

   (*---------Some other properties of graph --------------------------*)

   Lemma nice_intro (G: UG)(n:nat):
     cliq_num G n -> (exists f, Coloring_of G f /\ |clrs_of f G|= n)-> Nice G.
   Proof. { intros H H1 m H2. assert (Hnm: n=m); eauto; subst m. clear H2.
          destruct H1 as [f H1].
          unfold chrom_num. exists f.
          destruct H1 as [H1 HR]. split. 
          { unfold Best_coloring_of. split.
            { auto. }
            rewrite HR. intro f1. apply more_clrs_than_cliq_num;auto. }
          { auto. } } Qed.
   Lemma nice_elim (G: UG)(n: nat): Nice G -> chrom_num G n -> cliq_num G n.
   Proof.  { intros h1 h2. destruct (cliq_num_of G) as [m h3].
             unfold Nice in h1. assert (h4: chrom_num G m).
             apply h1. auto. assert (h5: m = n).
             eapply chrom_num_same; eauto. subst m. auto. } Qed.
            
   Hint Immediate perfect_sub_perfect more_clrs_than_cliq_size more_clrs_than_cliq_num: core.
   Hint Immediate nice_intro: core.

   Lemma nil_is_nice (G: UG): nodes G = nil -> Nice G.
   Proof. { intros h1.
            eapply nice_intro with (n:=0).
            { unfold cliq_num. 
              exists nil.
              split.
              { apply Max_K_in_intro.
                unfold Cliq_in. split. auto. split. constructor. 
                unfold Cliq. intros x y. simpl. auto.
                intros K' h2.
                assert (h3: K' = nil).
                { cut (K' [<=] G). intro h3. rewrite h1 in h3. auto. apply h2. }
                rewrite h3. auto. }
              { simpl. auto. } } 
            set (f:= fun x: A => 0).
            exists f. split. unfold Coloring_of. rewrite h1. simpl. auto.
            rewrite h1; simpl; auto. } Qed.

   Lemma nil_is_perfect (G: UG): nodes G = nil -> Perfect G.
   Proof. { intros h1. intros H h2.
            assert (h3: nodes H = nil).
            { cut (H [<=] G). intro h3. rewrite h1 in h3. auto. apply h2. }
            auto using nil_is_nice. } Qed.

   Hint Resolve nil_is_nice nil_is_perfect: core.

   (*--------- Graph and its Complement---------------------------------*)

  Lemma stable_is_cliq (G G': @UG A)(I: list A): Compl G G'-> Stable_in G I-> Cliq_in G' I.
  Proof. { unfold Compl; unfold Stable_in; unfold Cliq_in.
           unfold Stable; unfold Cliq.
           intros h1 h2. replace (nodes G') with (nodes G).
           split. apply h2. split. apply h2.
           intros x y hx hy. right. 
           destruct (edg G' x y) eqn: hxy.
           auto.
           absurd (edg G x y).
           { switch;apply h2;auto. }
           { destruct h2 as [h2a h2].
             apply h1; auto. switch;auto. }
           apply h1. } Qed.

  Lemma cliq_is_stable (G G': @UG A)(K: list A): Compl G G' -> Cliq_in G K -> Stable_in G' K.
  Proof. { unfold Compl; unfold Stable_in; unfold Cliq_in.
           unfold Stable; unfold Cliq.
           intros h1 h2. replace (nodes G') with (nodes G).
           split. apply h2. split. apply h2.
           intros x y hx hy.
           assert (h3: x = y \/ edg G x y).
           { apply h2;auto. }
           destruct h3 as [h3 | h3].
           { subst x; auto. }
           { destruct h2 as [h2a h2]. switch;apply h1;auto. }
           apply h1. } Qed. 

  Lemma cliq_num_i_num (G G': @UG A)(n: nat): Compl G G' -> cliq_num G n -> i_num G' n.
  Proof. { intros h1 h2. 
           assert (h1a: Compl G' G). auto.
           assert (gg': nodes G = nodes G').
           { apply h1. }
           destruct h2 as [K h2].
           destruct h2 as [h2a h2].
           exists K. split.
           { apply Max_I_in_intro.
             { cut (Cliq_in G K). apply cliq_is_stable;auto. auto. }
             { intros I h3.
               assert (h4: Cliq_in G I).
               { eapply stable_is_cliq;auto. exact h1a. auto. }
               apply h2a. rewrite gg'.
               cut (I [<=] G'). cut (IsOrd I). auto. apply h4. apply h3.
               apply /cliqP. auto. } }
             auto. } Qed.

  Lemma i_num_cliq_num (G G': @UG A)(n: nat): Compl G G'-> i_num G n -> cliq_num G' n.
  Proof.  { intros h1 h2. 
           assert (h1a: Compl G' G). auto.
           assert (gg': nodes G = nodes G').
           { apply h1. }
           destruct h2 as [I h2].
           destruct h2 as [h2a h2].
           exists I. split.
           { apply Max_K_in_intro.
             { cut (Stable_in G I). apply stable_is_cliq; auto. auto. }
             { intros K h3.
               assert (h4: Stable_in G K).
               { eapply cliq_is_stable; auto. exact h1a. auto. }
               apply h2a. rewrite gg'.
               cut (K [<=] G'). cut (IsOrd K). auto. apply h4. apply h3.
               apply /stableP. auto. } }
             auto. } Qed.

  Hint Immediate stable_is_cliq cliq_is_stable cliq_num_i_num i_num_cliq_num: core.
   
End MoreOnDecidableGraphs.



 Hint Resolve Stable_elim:core.
 Hint Resolve Stable_in_elim Stable_in_elim1 Stable_in_elim2: core.
 Hint Resolve stableP nil_is_stable: core.
 Hint Resolve max_I_inP exists_Max_I_in Max_I_in_elim1 Max_I_in_elim2 : core.
 Hint Resolve Max_I_in_elim: core.
 Hint Resolve i_num_same i_num_max_I:core.
 Hint Immediate Stable_in_HG Stable_in_GH i_num_HG:core.
 Hint Immediate i_num_gt: core.

 Hint Resolve Cliq_in_elim Cliq_in_elim1 Cliq_in_elim2: core.
 Hint Resolve  Cliq_elim cliqP nil_is_cliq: core.
 Hint Resolve max_K_inP exists_Max_K_in  Max_K_in_elim1 Max_K_in_elim2: core.
 Hint Resolve Max_K_in_elim: core.
 Hint Resolve cliq_num_same:core.
 Hint Immediate Cliq_in_HG Cliq_in_GH cliq_num_HG:core.
 Hint Immediate cliq_num_gt: core.
 
 Hint Resolve chrom_num_same clrs_of_inc clrs_of_inc1: core.
 Hint Immediate coloring_of_HG chrom_num_HG: core.
 
 Hint Resolve perfect_is_nice: core.
 Hint Immediate perfect_sub_perfect more_clrs_than_cliq_size more_clrs_than_cliq_num: core.
 Hint Resolve clrs_on_a_cliq: core.
 Hint Immediate nice_intro: core.

 Hint Immediate stable_is_cliq cliq_is_stable cliq_num_i_num i_num_cliq_num: core.

  
 
