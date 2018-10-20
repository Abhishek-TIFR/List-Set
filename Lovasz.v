



Require Export DecUG MoreDecUG.

Set Implicit Arguments.

Section Repeat_node.

   Context { A: ordType }.
 
   (*---------- Repeating a vertex a as a' in a graph G-----------------------------------*)
   
   Definition nw_edg (G: @UG A)(a a': A):=
     fun (x y: A) => match (x == a), (y == a') with
                  | _ , false => (edg G) x y
                  | true, true => true
                  |false, true => (edg G) x a
                  end.

   Lemma nw_edg_a_a'(G: @UG A)(a a':A): (nw_edg G a a') a a'.
   Proof.  unfold nw_edg. replace (a == a ) with true. replace (a' == a') with true.
           auto. all: symmetry; apply /eqP;auto. Qed.

   Lemma nw_edg_xa_xa' (G: @UG A)(a a' x:A): (edg G) x a ->  (nw_edg G a a') x a'.
   Proof. intro H. unfold nw_edg. replace (a' == a') with true.
          destruct (x==a); auto. symmetry; apply /eqP; auto. Qed.

   Lemma nw_edg_xy_xy (G: @UG A)(a a' x y:A)(P': ~In a' G): (edg G) x y ->  (nw_edg G a a') x y.
   Proof. { intro H. unfold nw_edg.
          destruct (x==a) eqn:Hxa.
          { case (y == a'). all: auto. }
          { destruct (y == a') eqn:Hya'.
            { move /eqP in Hya'. subst y. absurd (In a' G). auto. eauto. }
            { auto. } } } Qed.

   Lemma nw_edg_xy_xy1 (G: @UG A)(a a' x y:A)(P: In a G)(P': ~In a' G):
     In x G -> In y G  ->  (edg G) x y = (nw_edg G a a') x y.
   Proof.  { intros Gx Gy. unfold nw_edg.
           destruct (x==a) eqn: Hxa; destruct (y==a') eqn: Hya';
             move /eqP in Hxa; move /eqP in Hya'.
           { subst x. subst y. contradiction. }
           { auto. }
           { subst y. contradiction. }
           { auto. }  } Qed.
   
  Lemma nw_edg_xy_xy2 (G: @UG A)(a a' x:A)(P: In a G)(P': ~In a' G):
    (edg G) x a = (nw_edg G a a') x a.
  Proof. {  unfold nw_edg. replace (a==a') with false.
         destruct (x==a); auto. symmetry;switch.
         intro H; move /eqP in H; subst a; contradiction. } Qed.

  Lemma nw_edg_xy_xy3 (G: @UG A)(a a' y:A)(P: In a G)(P': ~In a' G):
    y <> a' -> (edg G) a y = (nw_edg G a a') a y.
  Proof. {  intro H0. unfold nw_edg. replace (y==a') with false.
         destruct (a==a); auto. symmetry;switch.
         intro H; move /eqP in H; contradiction. } Qed.
  
  Lemma nw_edg_xy_xy4 (G: @UG A)(a a' x y:A)(P: In a G)(P': ~In a' G):
    y <> a' -> (edg G) x y = (nw_edg G a a') x y.
  Proof. {  intro H0. unfold nw_edg. replace (y==a') with false.
         destruct (x==a); auto. symmetry;switch.
         intro H; move /eqP in H; contradiction. } Qed.
  
  Lemma nw_edg_xy_xy5 (G: @UG A)(a a' x:A)(P: In a G)(P': ~In a' G):
    x <> a-> (edg G) x a = (nw_edg G a a') x a'.
  Proof. { intro H0. unfold nw_edg. replace (x==a) with false.
           replace (a'== a') with true. auto. symmetry; apply /eqP;auto.
           symmetry;switch;auto. } Qed.

   
             
  Hint Resolve nw_edg_a_a' nw_edg_xa_xa' nw_edg_xy_xy nw_edg_xy_xy1: core.
  Hint Resolve nw_edg_xy_xy2 nw_edg_xy_xy3 nw_edg_xy_xy4 nw_edg_xy_xy5: core.
   
   Definition ex_edg (G: @UG A)(a a': A):= mk_sym (mk_irefl ((nw_edg G a a') at_ (add a' G))).

   Definition Repeat_in (G: @UG A)(a: A)(a':A): @UG A.
    refine({| nodes:= add a' G; edg:= (ex_edg G a a');
           |}); unfold ex_edg. all: auto. Defined.



  Variable G: @UG A.
  Variable a a': A.

  Let G':= (Repeat_in G a a').

  Lemma edge_aa': In a G-> a<>a' -> (edg G') a a'.
  Proof.  { simpl. intros H H1.  unfold ex_edg.  auto. } Qed.

  Lemma edg_aa': In a G -> ~ In a' G -> (edg G') a a'.
  Proof. { intros H H1.
         assert (H2: a <> a'). intro Heq; subst a; contradiction.
         apply edge_aa';auto. } Qed.

  Lemma edg_xa_xa' (x: A)(P: In a G)(P': ~In a' G): (edg G) x a-> (edg G') x a'.
  Proof. { simpl. intros H. unfold ex_edg. 
           assert (Ha: a <> a'). intro; subst a; contradiction. 
           assert (Hb: In x G). eauto.
           assert (Hc: x <> a'). intro; subst x; contradiction.  
           auto. } Qed.

  Lemma Exy_E'xy (x y:A)(P: In a G)(P': ~In a' G): edg G x y -> edg G' x y.
  Proof. { intro H. simpl. unfold ex_edg.
           assert (Hx: In x G). eauto.
           assert (Hy: In y G). eauto. 
           assert (Hxy: x=y \/ x<>y). eauto.
           destruct Hxy. 
           { subst x; absurd (edg G y y); auto. }
           { auto. } } Qed.

 
  Lemma E'xy_Exy (x y:A)(P: In a G)(P': ~In a' G):
    In x G -> In y G -> ~ edg G x y  -> ~ edg G' x y.
  Proof.  { intros Gx Gy H. simpl. unfold ex_edg.
          assert (Ha: ~ edg G y x); auto.
          assert (H1: ~ (nw_edg G a a') x y).
          { replace (nw_edg G a a' x y) with (edg G x y).
            auto.  auto. }
          assert (H1a: ~ (nw_edg G a a') y x).
           { replace (nw_edg G a a' y x) with (edg G y x).
             auto. auto. }
           auto. } Qed.

  Lemma E'xy_Exy1 (x y:A)(P: In a G)(P': ~In a' G):
    In x G -> In y G  -> edg G' x y -> edg G x y.
  Proof. { intros Gx Gy H. destruct (edg G x y) eqn:Exy. auto.
         switch_in Exy. absurd (edg G' x y). auto using E'xy_Exy. auto. }  Qed.
  
   Lemma In_xy_G (x y:A)(P: In a G)(P': ~In a' G): In x G-> In y G-> edg G x y=edg G' x y.
    Proof.  { intros Gx Gy.
           destruct (edg G x y) eqn: Exy; destruct (edg G' x y) eqn: E'xy.
           auto.
           absurd ( edg G' x y). switch;auto. apply Exy_E'xy;auto.
           absurd (edg G x y). switch;auto. apply E'xy_Exy1;auto.
           auto. } Qed.

    Hint Resolve edge_aa' edg_xa_xa': core.
    Hint Immediate Exy_E'xy E'xy_Exy E'xy_Exy1 In_xy_G: core.

    Lemma edg_G'G1(x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a -> edg G x a.
    Proof. { intros H1 H2. simpl.  unfold ex_edg.
           apply /impP.
           destruct (edg G x a) eqn:H3.
           { right_;auto. }
           { switch_in H3. left_. apply /negP.
             assert (H3b: ~ edg G a x); auto.
             assert (H4a: ~ (nw_edg G a a') x a ).
             { replace (nw_edg G a a' x a) with (edg G x a); auto. }
             assert (H4b: ~ (nw_edg G a a') a x ).
             { replace (nw_edg G a a' a x) with (edg G a x); auto. }
              auto. } } Qed.
    

    Lemma edg_G'G2(x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a' -> edg G x a.
    Proof.   { intros H1 H2. simpl.  unfold ex_edg.
           apply /impP.
           destruct (edg G x a) eqn:H3.
           { right_;auto. }
           { switch_in H3. left_. apply /negP.
             assert (H3b: ~ edg G a x); auto.
             assert (H4a: ~ (nw_edg G a a') x a' ).
             { replace (nw_edg G a a' x a') with (edg G x a); auto. }
             assert (H4b: ~ (nw_edg G a a') a' x ).
             { replace (nw_edg G a a' a' x) with (edg G a' x). auto. auto. }
             auto. } } Qed.

   
    
   Lemma edg_G_G'(x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G x a = edg G' x a'.
   Proof. { intros H1 H2.
          assert (H3: edg G x a -> edg G' x a'). auto.
          assert (H4: edg G' x a' -> edg G x a). auto using edg_G'G2. auto. } Qed.
          
  
  Lemma edg_G_G'1 (y:A)(P: In a G)(P': ~In a' G): y<>a -> y<> a' -> edg G a y = edg G' a' y.
  Proof. { replace (edg G a y) with (edg G y a);
           replace (edg G' a' y) with (edg G' y a');
           (eapply edg_G_G'|| eapply edg_sym); auto. } Qed. 

    Lemma edg_G'1 (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a -> edg G' x a'.
    Proof.  auto using edg_G'G1. Qed.

    Lemma edg_G'2 (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a' -> edg G' x a.
    Proof. intros H1 H2 H3. specialize ( edg_G'G2 P P' H1 H2 H3) as H4.  auto. Qed.
    
   Lemma edg_G'3 (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a = edg G' x a'.
   Proof. { intros Ha Ha'.
         destruct (edg G' x a) eqn: H1; destruct (edg G' x a') eqn:H2.
         all: auto.
         { absurd (edg G' x a'). switch;auto.  auto using edg_G'1. }
         { absurd (edg G' x a). switch;auto. auto using edg_G'2. } } Qed.

   Lemma edg_G'4 (y:A) (P: In a G)(P': ~In a' G): y<>a -> y<> a'-> edg G' a y = edg G' a' y.
  Proof. { intros H1 H2.
           replace (edg G' a y) with (edg G' y a);
             replace (edg G' a' y) with (edg G' y a').
           auto using edg_G'3. all: apply edg_sym. } Qed.

  (* Organise these lemmas as hint in core database *)

  
End Repeat_node.





Section LovaszRepLemma.

  Context { A:ordType }.

  Variable G: @UG A.
  Variable a a': A.
  Hypothesis P: In a G.
  Hypothesis P': ~In a' G.

  Let G':= Repeat_in G a a'.

  

  Lemma ReplicationLemma: Perfect G -> Perfect G'.
    Proof. Admitted.
  
  End LovaszRepLemma.