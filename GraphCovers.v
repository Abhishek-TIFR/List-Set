



(* ------------------ Descriptions--------------------------------------------------

 In this file we define the concept of covering a graph with Stable Sets and Cliqs. We  
 also describe the relationship of chromatic number of an undirected graph and the min 
 size of stable set cover for the graph. Most of these new definitions are given using
 functions which are originally defined in the file SetCover.v. Furthermore, we also 
 prove various lemmas specifying the relationship between a graph and its complement. 


We connect these  properties with boolean functions using the following reflection lemmas.
 
 Predicate                  Boolean function       Joining Lemma
 Stable_cover C G           stable_cover C G       stable_coverP
 Cliq_cover C G             cliq_cover C G         cliq_coverP 
 


 (Stable_cover C G) states that C is a collection of stable sets that spans the whole graph G. 
 (Cliq_cover C G) states that C is a collection of cliques that spans the whole graph G. 
 

 We also prove following important results relating the size of smallest stable color and 
 chromatic number for a given graph G:

 Lemma color_to_cover (G:UG) (f: A-> nat): Coloring_of G f ->
                                         (exists C, Stable_cover C G /\ |C| = |clrs_of f G|).

Lemma cover_to_color (G:UG) (C: list (list A)):
 Stable_cover C G -> (exists f, Coloring_of G f /\ |clrs_of f G| <= |C|).

Lemma nice_intro1 (G: UG)(n:nat): cliq_num G n -> 
                                  (exists C, Stable_cover C G /\ | C | = n) -> Nice G.

 

---------------------------------------------------------------------------------------*)


Require Export MoreUG.
Require Export SetCover.

Set Implicit Arguments.

Section GraphCover.

  Context { A: ordType }.

  (*--------- Stable set cover for a graph G -------------------------------*)

  Definition stable_cover (C: list (list A))(G: UG):=
    set_cover C G && forallb (fun I => (stable G I && isOrd I)) C.

  Definition Stable_cover (C: list (list A))(G: UG):=
    Set_cover C G /\ (forall I, In I C -> (Stable G I /\ IsOrd I)).

  Lemma stable_coverP (C: list (list A))(G: UG): reflect (Stable_cover C G)(stable_cover C G).
  Proof. { apply reflect_intro. split;unfold stable_cover;unfold Stable_cover.
           { intros h1. split_. apply /set_coverP. apply h1. apply /forallbP.
             intros x h2. apply /andP;split. apply /stableP. apply h1. auto.
             apply /isOrdP. apply h1;auto. }
           { intros h1. move /andP in h1. destruct h1 as [h1 h1a].
             split. apply /set_coverP. auto.
             intros I h2. move /forallbP in h1a.
             specialize (h1a I h2) as h3. move /andP in h3.
             split. apply /stableP;apply h3. apply /isOrdP;apply h3. } } Qed.

  Lemma Stable_cover_elim (C: list (list A))(G: UG)(I: list A):
    Stable_cover C G -> In I C -> Stable_in G I.
  Proof. { unfold Stable_cover; unfold Stable_in. intros h1 h2.
           destruct h1 as [h1a h1b]. specialize (h1b I h2) as h3.
           destruct h3 as [h3a h3b]. split. eauto. split;auto. } Qed.

Hint Resolve Stable_cover_elim: core.        

  (*---------  Cliq cover for a graph G -------------------------------*)

  Definition cliq_cover (C: list (list A))(G: UG):=
    set_cover C G && forallb (fun I => (cliq G I && isOrd I)) C.

  Definition Cliq_cover (C: list (list A))(G: UG):=
    Set_cover C G /\ (forall I, In I C -> (Cliq G I /\ IsOrd I)).

  Lemma cliq_coverP (C: list (list A))(G: UG): reflect (Cliq_cover C G)(cliq_cover C G).
  Proof. { apply reflect_intro. split;unfold cliq_cover;unfold Cliq_cover.
           { intros h1. split_. apply /set_coverP. apply h1. apply /forallbP.
             intros x h2. apply /andP;split. apply /cliqP. apply h1. auto.
             apply /isOrdP. apply h1;auto. }
           { intros h1. move /andP in h1. destruct h1 as [h1 h1a].
             split. apply /set_coverP. auto.
             intros I h2. move /forallbP in h1a.
             specialize (h1a I h2) as h3. move /andP in h3.
             split. apply /cliqP;apply h3. apply /isOrdP;apply h3. } } Qed.

  Lemma Cliq_cover_elim (C: list (list A))(G: UG)(K: list A):
    Cliq_cover C G -> In K C -> Cliq_in G K.
  Proof. { unfold Cliq_cover; unfold Cliq_in. intros h1 h2.
           destruct h1 as [h1a h1b]. specialize (h1b K h2) as h3.
           destruct h3 as [h3a h3b]. split. eauto. split;auto. } Qed.

  Hint Resolve Cliq_cover_elim: core.

  (*----------- Smallest Stable_cover Vs Chromatic Number --------------- *)

  Lemma color_to_cover (G:UG) (f: A-> nat): Coloring_of G f ->
                                         (exists C, Stable_cover C G /\ |C| = |clrs_of f G|).
  Proof. { intro h1.
           (*--all colors used in G is stored in cls ------*)
           set (cl:= clrs_of f G).
           set (F:= fun c => (filter (fun v => f v == c) G)).
           set (C:= map F cl).
           exists C. split.
           { (*---Stable_cover C G----*)
             unfold Stable_cover.
             split.
             { (*----Set_cover C G----*)
               unfold Set_cover. apply set_equal. all: auto.
               split.
               { (*--  G [<=] union_over C ---*)
                 intros x h2. set (Cx := F (f x)).
                 assert (Hx: In x Cx).
                 { unfold Cx. unfold F.
                   apply filter_In. split;auto. }
                 assert (HCx: In Cx C).
                 { unfold C. unfold Cx. cut (In (f x) cl).
                   auto. unfold cl. unfold clrs_of. auto. }
                 eapply union_over_intro. apply Hx. auto. }
               { (*--- union_over C [<=] G ----*)
                 intros x h2.
                 apply union_over_elim in h2 as h3.
                 destruct h3 as [Cx h3]. destruct h3 as [h3a h3b].
                 unfold C in h3a.
                 assert (h4: exists c, In c cl /\ Cx = F c). auto.
                 destruct h4 as [c h4]. destruct h4 as [h4a h4].
                 subst Cx. unfold F in h3b. eapply filter_elim1. apply h3b. }  }
             { (*-- forall I : list A, In I C -> Stable G I /\ IsOrd I---*)
               intros I h2.
               split.
               { (*-Stable G I-*)
                 unfold Stable. intros x y hx hy.
                 assert (h3: exists c, In c cl /\ I = F c).
                 { unfold C in h2. auto. }
                 destruct h3 as [c h3]. destruct h3 as [h3a h3b].
                 subst I. unfold F in hx, hy.
                 assert (hfx: f x == c).
                 { apply filter_elim2 in hx as h4. auto. }
                 assert (hfy: f y == c).
                 { apply filter_elim2 in hy as h4. auto. }
                 assert (Hx: In x G).
                 {  apply filter_elim1 in hx as h4; auto. }
                 assert (Hy: In y G).
                 {  apply filter_elim1 in hy as h4; auto. }
                 switch. intro h4.
                 absurd (f x = f y). auto. move /eqP in hfx. move /eqP in hfy.
                 omega. }
               { (*-IsOrd I -*)
                 assert (h3: exists c, In c cl /\ I = F c).
                 { unfold C in h2. auto. }
                 destruct h3 as [c h3]. destruct h3 as [h3a h3b].
                 subst I. unfold F. cut (IsOrd G). auto. auto. }  }  }
           { (*-- (| C |) = (| cl |)--*)
             unfold C. symmetry. auto.  } } Qed.


         

  Lemma cover_to_color (G:UG) (C: list (list A)): Stable_cover C G ->
                                                  ( exists f, Coloring_of G f /\ |clrs_of f G| <= |C|).
  Proof. { intro h1.
           set (f:= fun x => idc x C).
           set (cl:= clrs_of f G).
           set (Nc:= map (fun c => idx c C) C).
           exists f. split.
           { (*-- Coloring_of G f ---*)
             unfold Coloring_of.
             destruct h1 as [h1 h1a]. unfold Set_cover in h1.
             intros x y hx hy hxy h2.
             assert (h3: exists c, In c C /\ In x c /\ In y c).
             { apply idc_eq_same_set. rewrite <- h1. auto.
               unfold f in h2. auto. }
             destruct h3 as [c h3].
             assert (h4: Stable G c).
             { apply h1a. apply h3. }
             unfold Stable in h4.
             absurd ( edg G x y). switch. apply h4;apply h3. auto. }
           
           { (*--  (| clrs_of f G |) <= (| C |) --*)
             assert (h2: clrs_of f G [<=] Nc).
             { unfold clrs_of. intros n h3.
               assert (h4: exists x, In x G /\ n = f x). auto.
               destruct h4 as [x h4]. destruct h4 as [h4a h4].
               unfold f in h4.
               assert (h5:  exists c, In c C /\  In x c /\ idc x C = idx c C).
               { apply idc_from_idx. unfold Stable_cover in h1.
                 destruct h1 as [h1 h1a]. unfold Set_cover in h1.
                 rewrite <- h1;auto. }
               destruct h5 as [c h5]. subst n.
               replace (idc x C) with (idx c C).
               unfold Nc. set (f1:= (fun c0 : list_eqType => idx c0 C)).
               replace (idx c C) with (f1 c).
               cut (In c C). auto. apply h5. unfold f1;simpl;auto.
               symmetry;apply h5. }
             assert (h3: NoDup (clrs_of f G )).
             { unfold clrs_of. auto. }
             assert (h4: |C| = |Nc|).
             { unfold Nc. auto. }
             rewrite h4. auto. } } Qed.


 Lemma nice_intro1 (G: UG)(n:nat): cliq_num G n -> (exists C, Stable_cover C G /\ | C | = n) -> Nice G.
  Proof. { intros h1 h2. eapply nice_intro with (n0:=n).
           auto. destruct h2 as [C h2]. destruct h2 as [h2a h2b].
           specialize (cover_to_color  h2a) as h3.
           destruct h3 as [f h3]. destruct h3 as [h3a h3b].
           exists f. split. auto. rewrite h2b in h3b.
           cut ((| clrs_of f G |) >= n). intros. omega. auto. } Qed.
           

End GraphCover.

Hint Resolve Stable_cover_elim: core.
Hint Resolve Cliq_cover_elim: core.






  
