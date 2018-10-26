



(* ------------------ Descriptions--------------------------------------------------

 In this file we define the concept of Stable Set, Cliq and Coloring for an undirected
 graph.  We also define boolean functions to check these properties. We connect these 
 properties with boolean functions using reflection lemmas.
 
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

 Definition clrs_of (f:A->nat) (l:list A): list nat:= (s_map f l).
 Definition chrom_num (G: UG) (n: nat):= 
                              exists f, Best_coloring_of G f /\ | clrs_of f G | = n.

 We also define the notion of a perfect graph as follows:
 
 Definition Nice (G: UG): Prop:= forall n, cliq_num G n -> chrom_num G n.
 Definition Perfect (G: UG): Prop:= forall G1, Ind_subgraph G1 G -> Nice G1.
 
---------------------------------------------------------------------------------------*)


Require Export DecUG.

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

  
  Hint Resolve Stable_in_elim Stable_in_elim1 Stable_in_elim2: core.
  Hint Resolve stableP nil_is_stable: core.
  
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
  Proof. Admitted.
  
  Lemma Max_I_in_intro (G: UG)( I: list A):
    Stable_in G I -> (forall I', Stable_in G I' -> |I'| <= |I|) -> Max_I_in G I.
  Proof. Admitted.

   Hint Resolve max_I_inP exists_Max_I_in Max_I_in_elim1 Max_I_in_elim2 : core.
  
  Lemma i_num_same (G: UG)(n m:nat): i_num G n -> i_num G m -> n=m.
  Proof. {  intros Hn Hm.
           destruct Hn as [I1 Hn]. destruct Hm as [I2 Hm].
           cut (n<=m /\ m<=n). omega.
           destruct Hn as [Hn1 Hn2]. destruct Hm as [Hm1 Hm2].
           unfold Max_I_in in Hn1.  unfold Max_I_in in Hm1.
           split; subst n; subst m; eapply Max_I_in_elim3;eauto. } Qed.

  Hint Resolve i_num_same:core.
    
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
  Proof. Admitted.
  
  Lemma Max_K_in_intro (G: UG)( K: list A):
    Cliq_in G K -> (forall K', Cliq_in G K' -> |K'| <= |K|) -> Max_K_in G K.
  Proof. Admitted.
  
  

  Hint Resolve max_K_inP exists_Max_K_in Max_K_in_elim1 Max_K_in_elim2 : core.
  
  Lemma cliq_num_same (G: UG)(n m:nat): cliq_num G n -> cliq_num G m -> n=m.
  Proof.  {  intros Hn Hm.
           destruct Hn as [K1 Hn]. destruct Hm as [K2 Hm].
           cut (n<=m /\ m<=n). omega.
           destruct Hn as [Hn1 Hn2]. destruct Hm as [Hm1 Hm2].
           unfold Max_K_in in Hn1.  unfold Max_K_in in Hm1.
           split; subst n; subst m; eapply Max_K_in_elim3;eauto. } Qed.

  Hint Resolve cliq_num_same:core.
 
   
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

   
  Definition clrs_of (f:A->nat) (l:list A): list nat:= (s_map f l).
   
   Definition Best_coloring_of (G: UG) (f:A->nat): Prop :=
     Coloring_of G f /\ (forall f1, Coloring_of G f1 -> | clrs_of f G | <= | clrs_of f1 G|).
   
   Definition chrom_num (G: UG) (n: nat):= exists f, Best_coloring_of G f /\ | clrs_of f G | = n.

   Lemma best_clrs_same_size (G: UG)(f1 f2: A->nat):
     Best_coloring_of G f1 -> Best_coloring_of G f2 -> |clrs_of f1 G|=|clrs_of f2 G|.
   Proof.  Admitted.
   Lemma chrom_num_same (G:UG)(n m:nat): chrom_num G n-> chrom_num G m -> n=m.
   Proof. Admitted.

   Lemma clrs_of_inc (K1: list A)(K2: list A)(f:A-> nat):
     K1 [<=] K2 -> (clrs_of f K1) [<=] (clrs_of f K2).
   Proof.  unfold clrs_of; auto. Qed.
   Lemma clrs_of_inc1 (K1: list A)(K2: list A)(f: A->nat):
     K1 [<=] K2 -> |(clrs_of f K1)| <= |(clrs_of f K2)|.
   Proof. unfold clrs_of; auto. Qed.
   
   Hint Resolve chrom_num_same clrs_of_inc clrs_of_inc1: core.
   
   (*----- Think about the proof of existence of a best coloring----------------------------*)

   
   (*-------- Concepts of nice graph and  perfect graphs -------------------------------- *)
   Definition Nice (G: UG): Prop:= forall n, cliq_num G n -> chrom_num G n.
   Definition Perfect (G: UG): Prop:= forall G1, Ind_subgraph G1 G -> Nice G1.
      
   Lemma perfect_is_nice (G: UG): Perfect G -> Nice G.
   Proof.  unfold Perfect. intros H; apply H. auto.  Qed.
   
   (*---------  More colors needed than the largest cliq size --------------------------*)
   Lemma more_clrs_than_cliq_size (G: UG)(K: list A)(f: A->nat):
     Cliq_in G K-> Coloring_of G f -> |K| <= |clrs_of f G|.
   Proof. { intros H H1.
          assert (H2: | K | = |clrs_of f K|).
          { unfold clrs_of. match_up (|K|) (| s_map f K|).
            { auto. }
            { cut (| s_map f K| <= |K|).
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

   (*---------Some elimination and introduction  property of nice--------------------------*)

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
            
  Hint Resolve perfect_is_nice: core.
   
End MoreOnDecidableGraphs.




 Hint Resolve Stable_in_elim Stable_in_elim1 Stable_in_elim2: core.
 Hint Resolve stableP nil_is_stable: core.
 Hint Resolve max_I_inP exists_Max_I_in Max_I_in_elim1 Max_I_in_elim2 : core.
 Hint Resolve i_num_same:core.

 Hint Resolve Cliq_in_elim Cliq_in_elim1 Cliq_in_elim2: core.
 Hint Resolve  Cliq_elim cliqP nil_is_cliq: core.
 Hint Resolve max_K_inP exists_Max_K_in Max_K_in_elim1 Max_K_in_elim2: core.
 Hint Resolve cliq_num_same:core.
 
 Hint Resolve chrom_num_same clrs_of_inc clrs_of_inc1: core.
 Hint Resolve perfect_is_nice: core.
 
