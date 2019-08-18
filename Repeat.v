

(* --------------------------   Description ---------------------------------------------------  

      In this file we formally define the  relation between graphs G and G', where the graph G'
      is obtained by repeating vertex a of G  to a'. 

      Following definition captures this relationship:

      Definition Rep_in (G:UG) (a a':A) (G': UG):=
       In a G /\ ~ In a' G /\ (nodes G') = (add a' G) /\ edg G' a a' /\
       (forall x y, In x G -> In y G-> edg G x y = edg G' x y) /\ 
       (forall x, x<>a-> edg G x a = edg G' x a').

       Definition Rep G G':= exists a a', Rep_in G a a' G'.

      For a the given graphs G and G' related to each other by above relation we prove 
      many useful properties relating their edges.

      We also establish an isomorphism between the graph G and G'_a using the following 
      function f: 

       Let f:= ( fun x:A => match (x == a), (x == a') with
                            | true, true => x
                            | true, false => a'
                            | false, true => a
                            | false, false => x
                     end).

      Lemma G_iso_G'_a : iso_usg f G (ind_at N'_a G').

   ------------------------------------------------------------------------------------------*)

Require Export MoreUG GenIso.

Set Implicit Arguments.

Section Repeat_node.

  Context { A: ordType }.

  (*------ Definition and properties of the relation (Repeat G G' a a') and (Rep G G' -------*)

  Definition Rep_in (G:UG) (a a':A) (G': UG):=
    In a G /\ ~ In a' G /\ (nodes G') = (add a' G) /\ edg G' a a' /\
    (forall x y, In x G -> In y G-> edg G x y = edg G' x y) /\ (forall x, x<>a-> edg G x a = edg G' x a').

  Definition Rep G G':= exists a a', Rep_in G a a' G'.

  
  Variable G G': @UG A.
  Variable a a': A.
  
  Hypothesis Hrep: Rep_in G a a' G'.
  
  Lemma a_in_G: In a G.
  Proof. apply Hrep. Qed.

  Lemma a'_not_in_G: ~ In a' G.
  Proof. apply Hrep. Qed.

  Lemma a'_in_G': In a' G'.
  Proof. replace (nodes G') with (add a' G). auto. symmetry;apply Hrep. Qed.

  Lemma nodes_GG': (nodes G') = (add a' G).
  Proof. apply Hrep. Qed.

  Lemma a_not_a': a <> a'.
  Proof. intro h1; subst a; unfold Rep_in in Hrep; absurd (In a' G); apply Hrep.  Qed.

  Hint Resolve a_in_G a'_not_in_G a'_in_G'  nodes_GG' a_not_a': core.
  

  Lemma E'_aa': (edg G') a a'.
  Proof.  { unfold Rep_in in Hrep.
            destruct Hrep as [hr1 hr]; destruct hr as [hr2 hr]; destruct hr as [hr3 hr].
            destruct hr as [hr4 hr];destruct hr as [hr5 hr]. auto. } Qed.

  Lemma Exa_E'xa' (x: A):(edg G) x a-> (edg G') x a'.
  Proof. { unfold Rep_in in Hrep.
           destruct (x==a) eqn: Hxa.
           move /eqP in Hxa. subst x;intros;apply Hrep. move /eqP in Hxa.
           replace (edg G' x a') with (edg G x a). auto. apply Hrep. auto. } Qed.

  Lemma Eay_E'a'y (y: A): (edg G) a y -> (edg G') a' y.
  Proof. { intros h. apply sym_edg. apply sym_edg in h.  apply Exa_E'xa'; auto. } Qed.
  
  Hint Resolve E'_aa' Exa_E'xa' Eay_E'a'y : core. 

 
 
  (* --- following three results true only for x y both in G  --- *)

  Lemma In_Exy_eq_E'xy (x y:A): In x G-> In y G-> edg G x y=edg G' x y.
  Proof. { unfold Rep_in in Hrep. apply Hrep. } Qed.
  
  Lemma In_E'xy_Exy (x y:A): In x G -> In y G -> ~ edg G x y  -> ~ edg G' x y.
  Proof.  { intros h1 h2. replace (edg G' x y) with (edg G x y). auto.
            apply In_Exy_eq_E'xy;auto. } Qed.
      
  Lemma In_E'xy_Exy1 (x y:A): In x G -> In y G  -> edg G' x y -> edg G x y.
  Proof.  { intros h1 h2. replace (edg G' x y) with (edg G x y). auto.
            apply In_Exy_eq_E'xy;auto. } Qed.


Hint Immediate In_E'xy_Exy In_E'xy_Exy1 In_Exy_eq_E'xy: core.

  Lemma Exy_E'xy (x y:A): edg G x y -> edg G' x y.
  Proof. { intro h1.
           assert (h2: In x G). eauto.
           assert (h3: In y G). eauto.
           replace (edg G' x y) with (edg G x y); auto. } Qed.
  
  Hint Immediate Exy_E'xy: core.


  (* ---- if niether x nor y is a' then E' x y = E x y --------*)

  Lemma Exy_eq_E'xy (x y:A): x <> a'-> y<> a'->  edg G x y = edg G' x y.
  Proof. { intros H1 H2.
           assert (hx: In x G \/ ~ In x G). eauto.
           assert (hy: In y G \/ ~ In y G). eauto.
           destruct hx as [hx | hx].
           { (*--  In x G  -*)
             destruct hy as [hy | hy].
             { (*-- In y G---*)
               auto. }
             { (*---  ~ In y G --*)
               assert (hyG': ~ In y G' ).
               { intros h1. replace (nodes G') with (add a' G) in h1.
                 cut (y = a' \/ In y G). intro h2.
                 destruct h2; contradiction. auto. symmetry; apply Hrep.  }
               replace (edg G x y) with false.
               replace (edg G' x y) with false.
               auto. all: symmetry; switch; intros h3.
               absurd (In y G');eauto. absurd (In y G);eauto. } } 
           { (*--  ~ In x G  -*)
             assert (hyG': ~ In x G' ).
              { intros h1. replace (nodes G') with (add a' G) in h1.
                cut (x = a' \/ In x G). intro h2.
                destruct h2; contradiction. auto. symmetry; apply Hrep.  }
             replace (edg G x y) with false.
             replace (edg G' x y) with false.
             auto. all: symmetry; switch; intros h3.
             absurd (In x G');eauto. absurd (In x G);eauto. }  } Qed.

  
    Hint Immediate Exy_eq_E'xy: core.

    Lemma E'xy_Exy (x y:A): x<>a'-> y<>a'-> edg G' x y -> edg G x y.
    Proof. intros h1 h2; replace (edg G' x y) with (edg G x y); auto. Qed.
           
    Lemma Exy_E'xy1 (x y:A): x<>a'-> y<>a'-> edg G x y -> edg G' x y.
    Proof. intros h1 h2; replace (edg G' x y) with (edg G x y); auto. Qed.
    
    Hint Immediate E'xy_Exy Exy_E'xy1: core.

   (*------------- other special cases of interest------------*)

    Lemma E'xa_Exa (x:A):  x<> a'->  edg G' x a -> edg G x a.
    Proof. intros. apply E'xy_Exy; auto.  Qed.

   Lemma Exa_eq_E'xa'(x:A): x <> a ->  edg G x a = edg G' x a'.
   Proof. apply Hrep. Qed.
            
  Lemma Eay_eq_E'a'y (y:A): y<>a  -> edg G a y = edg G' a' y.
  Proof. { replace (edg G a y) with (edg G y a);
           replace (edg G' a' y) with (edg G' y a');
           (eapply Exa_eq_E'xa' || eapply edg_sym); auto. } Qed.

   
    Lemma E'xa'_Exa (x:A): x <> a->  edg G' x a' -> edg G x a.
    Proof. { intro h1. replace (edg G' x a') with (edg G x a). auto.
              auto using Exa_eq_E'xa'. } Qed.

  
  Hint Immediate E'xa_Exa E'xa'_Exa Exa_eq_E'xa' Eay_eq_E'a'y: core.

  

  (*------------------------- edge properties only in G'--------------*)
  Lemma E'xa_E'xa' (x:A):  x <> a' -> edg G' x a -> edg G' x a'.
    Proof.  auto.  Qed.

  Lemma E'xa'_E'xa (x:A): x <> a->  edg G' x a' -> edg G' x a.
  Proof. intros H1 H2.  specialize ( E'xa'_Exa H1 H2) as H3;  auto. Qed.

  Hint Immediate E'xa_E'xa' E'xa'_E'xa: core.
    
  Lemma E'xa_eq_E'xa' (x:A): x <> a-> x<> a'->  edg G' x a = edg G' x a'.
   Proof. auto. Qed.

   Lemma E'ay_eq_E'a'y (y:A): y<>a -> y<> a'-> edg G' a y = edg G' a' y.
   Proof. { intros H1 H2.
           replace (edg G' a y) with (edg G' y a);
             replace (edg G' a' y) with (edg G' y a').
           auto using E'xa_eq_E'xa'. all: apply edg_sym. } Qed.

   Hint Immediate E'xa_eq_E'xa' E'ay_eq_E'a'y: core.

   (*------------------- G is Induced subgraph of G'-----------------------*)

   Lemma Ind_sub_GG': Ind_subgraph G G'.
   Proof.  { split. replace (nodes G') with (add a' G). intros x h1; auto.
             symmetry. auto.  apply Hrep. } Qed.

   Hint Resolve Ind_sub_GG': core.

   

   (* The term G'_a is used to represent the induced subgraph of G' at G' \ {a} *)
   
   (*-------------------- G'_a is isomorphic to G  -----------------------*)

   Let N'_a:= (rmv a G').
   Let G'_a:= (ind_at (rmv a G') G').


   Lemma NG'_a: N'_a = nodes (ind_at N'_a G').
   Proof.  apply set_equal;auto. unfold N'_a. auto. 
          cut ((rmv a G') [<=] G'). simpl. auto. auto.  Qed.


   Lemma G'_a_is_ind_subgraph: Ind_subgraph (ind_at N'_a G') G'.
   Proof. split.
          { simpl. auto. }
          { intros x y H1 H2. simpl. symmetry;auto. } Qed.

   
   (*---- Following function is used to establish isomorphism between G and G'_a----*)
   
   Let f:= ( fun x:A => match (x == a), (x == a') with
                            | true, true => x
                            | true, false => a'
                            | false, true => a
                            | false, false => x
                     end).

   (* -----------  some properties of f to become an isomorphism-------------- *)
   Lemma fa_is_a':  (f a) = a'.
   Proof. { unfold f. replace (a==a) with true. replace (a==a') with false.
            auto. all: symmetry; apply /eqP; auto. } Qed.
   
   Lemma fa'_is_a :  (f a') = a.
   Proof. { unfold f. replace (a'==a') with true. replace (a'==a) with false.
            auto. all: symmetry; apply /eqP; auto.  } Qed.
   
   Lemma fx_is_x (x:A): In x G-> x<>a-> (f x) = x.
   Proof.  { intros H H1. unfold f. replace (x==a) with false. replace (x==a') with false.
             auto. all: symmetry; apply /eqP; auto. intro. subst x.
             absurd (In a' G). apply Hrep. auto.  } Qed.
   
   Lemma fx_is_x2 (x:A): x<>a'-> x<>a-> (f x) = x.
   Proof.  { intros H H1. unfold f. replace (x==a) with false. replace (x==a') with false.
             auto. all: symmetry; apply /eqP; auto.  } Qed.
   
   (* -----   fact: f (f x) = x     ------------ *)
   Lemma f_is_invertible: forall x : A, f (f x) = x.
   Proof. { assert (H0: a <> a'). auto.
            intro x. unfold f.  destruct (x==a) eqn: Hxa;destruct (x==a') eqn: Hxa'.
            {  absurd (a=a'). auto. move /eqP in Hxa; move /eqP in Hxa'.
               rewrite <- Hxa; auto.  }
            { replace (a'== a) with false.
              { replace (a'==a') with true. symmetry;auto. symmetry;auto. }
              { symmetry. switch.  move /eqP. intro H1;apply H0;auto. } }
            { replace (a==a) with true. replace (a==a') with false. all: symmetry;auto.  }
            { rewrite Hxa. rewrite Hxa'. auto. } } Qed.

   (* -----   fact:   G'_a = (img f G) -------- *)
   Lemma G'_a_is_imgG: nodes (ind_at N'_a G') = (img f G).
   Proof. { assert (H0: a <> a'). auto.
            assert (HGG': nodes G' = add a' G). apply Hrep.
          assert (H1: Equal (ind_at N'_a G') (img f G)).
          { split; unfold Subset.
            { (* -- x in G_a' implies x in img f G --*)
              intros x H1.
              assert (H1a: x <> a). rewrite <- NG'_a in H1. 
              { eapply set_rmv_elim2 with (l:= (add a' G)). auto.
                unfold N'_a in H1. rewrite <- HGG'. auto.  }
              assert (case_xa': x=a' \/ x<>a'). eauto.
              destruct case_xa'.
              { subst x. replace a' with (f a).  auto. auto using fa_is_a'. }
              { assert (H2: In x G).
                { simpl in H1.  cut (In x (add a' G)). eauto.
                  unfold N'_a in H1. rewrite <- HGG'. eauto. }
                replace x with (f x). auto. auto using fx_is_x.  } }
            { (*--- x in img f G implie x in G_a' ---*)
              intros y H1.
              assert (H1a: exists x, In x G /\ y= f x ). auto.
              destruct H1a as [x H1a]. destruct H1a as [H1a H1b].
              assert (Hxa: x=a \/ x<>a). eauto.
              destruct Hxa.
              { subst y. replace (f x) with a'. simpl.
                cut (In a' (add a' G)). cut (In a' N'_a).
                auto. unfold N'_a. cut(a'<>a). cut (In a' G').  auto.
                simpl. all: auto.  subst x; symmetry. auto using fa_is_a'. }
              { subst y. replace (f x) with x. rewrite <- NG'_a.
                unfold N'_a. cut (In x G').  auto. rewrite HGG'. auto.
                symmetry; auto using fx_is_x. } } }
              auto. } Qed. 
   
   (* -----   fact: f preserves edg relation ----- *)
   Lemma f_preserves_edg(x y:A):In x G -> In y G -> edg G x y = edg (ind_at N'_a G') (f x) (f y).
   Proof. { intros hx hy.  assert (H0: a <> a'). auto.
          assert (H0a: a == a' = false). switch. move /eqP. auto.
          assert (H0b: (rmv a G') [<=] G'). auto.
          
          assert (H0d: In a' G'). simpl;  auto. 
         
          destruct (x==y) eqn: Hxy.
          { (* when x =y : easy case*)
            assert (H1: x=y). auto. subst y.
            replace (edg G x x) with false.  all: symmetry; switch; auto. }
          { (* when x <> y : involved case*)
            assert (H1: x <> y).
            { move /eqP. switch_in Hxy. auto. }
            unfold f.
            destruct (x==a) eqn: Hxa.
            { (* when x=a*)
              assert (x=a); auto. subst x. rewrite H0a.
              assert (y == a =false).
              { switch. move /eqP. intro H2. subst y. auto. }
              rewrite H.
              destruct (y == a') eqn: Hya'.
              { (*when y=a'*)
                assert (y=a'). auto. subst y. absurd (In a' G).
                apply Hrep. auto.  }
              { (*when y <> a'*)
                assert (y<>a'). move /eqP. switch. auto. 
                replace (edg G a y) with (edg G' a' y). 
                Focus 2. symmetry. apply Eay_eq_E'a'y;auto.
                assert (H3: In a' (rmv a G')).  auto.
                assert (H3a: memb a' G' = memb a' (rmv a G')). symmetry; auto.
                assert (H4: memb y G' = memb y (rmv a G')). auto. auto. } }
            { (*when x<>a*)
              assert (x<> a). move /eqP. switch; auto.
              destruct (x==a') eqn: Hxa'.
              { (* when x =a'*)
                assert (x=a'). auto. subst x. absurd (In a' G).
                apply Hrep. auto. }
              { (* when x <> a'*)
                assert (x<> a'). switch_in Hxa'. intro H2; apply Hxa'; auto.
                destruct (y==a) eqn: Hya; destruct (y== a') eqn: Hya'.
                { move /eqP in Hya. move /eqP in Hya'. subst y. contradiction. }
                { move /eqP in Hya. subst y.
                  replace (edg G x a) with (edg G' x a').
                  Focus 2. auto.
                  assert (memb x G' = memb x (rmv a G')). auto.
                  assert (memb a' G' = memb a' (rmv a G')). auto.
                  auto. }
                { move /eqP in Hya'. subst y.  absurd (In a' G).
                  apply Hrep. auto.  } 
                { assert (y<>a). move /eqP; switch; auto.
                  assert (y<>a'). move /eqP; switch; auto.
                  replace (edg G x y) with (edg G' x y).
                  Focus 2. auto.
                  assert (memb x G' = memb x (rmv a G')). auto.
                  assert (memb y G' = memb y (rmv a G')). auto.
                  auto. } } } }  } Qed.
                  
   Lemma G_iso_G'_a : iso_usg f G (ind_at N'_a G').
   Proof. { assert (H0: a <> a'). auto.
          split.
          { (* ------------------ Proof of the fact that f (f x) = x -----------------*)
             intros x hx. apply f_is_invertible;auto. }
          split.
          { (*----------------- Proof of the fact that G'_a = img f G -------------- *)
            apply G'_a_is_imgG;auto. }
          { (*---------------  Proof that isomorphism preserves the edg relation-------*)
            intros x y. intros hx hy. apply f_preserves_edg;auto.  } } Qed.

   Lemma G_isomorphic_G'_a: exists f, iso_usg f G (ind_at N'_a G').
     Proof.  exists f. apply G_iso_G'_a;auto. Qed.
    
End Repeat_node.


Hint Resolve a_in_G a'_not_in_G a'_in_G' nodes_GG' a_not_a': core.
Hint Resolve E'_aa' Exa_E'xa' Eay_E'a'y : core.

 Hint Immediate In_E'xy_Exy In_E'xy_Exy1 In_Exy_eq_E'xy: core.
 Hint Immediate Exy_E'xy Exy_E'xy1 Exy_eq_E'xy: core.

 Hint Immediate E'xy_Exy : core.

 Hint Immediate E'xa_Exa E'xa'_Exa Exa_eq_E'xa' Eay_eq_E'a'y: core.

 Hint Immediate E'xa_E'xa' E'xa'_E'xa: core.
 Hint Immediate E'xa_eq_E'xa' E'ay_eq_E'a'y: core.

 Hint Resolve Ind_sub_GG': core.
 
 Hint Resolve G_isomorphic_G'_a: core.

 Hint Resolve no_edg1 no_edg2: core.
 Hint Resolve G_iso_G'_a: core.