



(* --------------------------   Description ---------------------------------------------------  

      In this file we formally define the  graph G' obtained by repeating vertex a of G 
      to a'. The following definition nw_edg creates a new edge relation for graph G' obtained 
      by repeating vertex a of G to a'.

      Definition nw_edg (G: UG)(a a': A):=
      fun (x y: A) => match (x == a), (y == a') with
                  | _ , false => (edg G) x y
                  | true, true => true
                  |false, true => (edg G) x a
                  end.

      This is a lazy description which doesnot ensure the symmetric and ireflexive property of
      edge relation. Later on we give a more accurate description of edge relation which uses 
      mk_iref and mk_sym function to modify the nw_edg relation. Hence the following edge 
      relation  is irreflexive, symmetric and restricted to nodes of G'.

      Definition ex_edg (G: UG)(a a': A):= mk_sym (mk_irefl ((nw_edg G a a') at_ (add a' G))).

      Then, we use the following definition to express G'.

      Definition Repeat_in (G: @UG A)(a: A)(a':A): @UG A.
       refine({| nodes:= add a' G; edg:= (ex_edg G a a');
           |}); unfold ex_edg. all: auto. Defined. 


   ---------------------------------------------------------------------------------------------*)

Require Export MoreDecUG IsoUG.

Set Implicit Arguments.

Section Repeat_node.

  Context { A: ordType }.
 
  (*---------- Lazy description of nw_edg relation and its essential properties------------- *)
  
   Definition nw_edg (G: UG)(a a': A):=
     fun (x y: A) => match (x == a), (y == a') with
                  | _ , false => (edg G) x y
                  | true, true => true
                  |false, true => (edg G) x a
                  end.

   Lemma nw_edg_a_a'(G: UG)(a a':A): (nw_edg G a a') a a'.
   Proof.  unfold nw_edg. replace (a == a ) with true. replace (a' == a') with true.
           auto. all: symmetry; apply /eqP;auto. Qed.
   
   Lemma nw_edg_xa_xa' (G: UG)(a a' x:A): (edg G) x a ->  (nw_edg G a a') x a'.
   Proof. intro H. unfold nw_edg. replace (a' == a') with true.
          destruct (x==a); auto. symmetry; apply /eqP; auto. Qed.

   Lemma nw_edg_xy_xy (G: UG)(a a' x y:A)(P': ~In a' G): (edg G) x y ->  (nw_edg G a a') x y.
   Proof. { intro H. unfold nw_edg.
          destruct (x==a) eqn:Hxa.
          { case (y == a'). all: auto. }
          { destruct (y == a') eqn:Hya'.
            { move /eqP in Hya'. subst y. absurd (In a' G). auto. eauto. }
            { auto. } } } Qed.

   Lemma nw_edg_xy_xy1 (G: UG)(a a' x y:A)(P: In a G)(P': ~In a' G):
     In x G -> In y G  ->  (edg G) x y = (nw_edg G a a') x y.
   Proof.  { intros Gx Gy. unfold nw_edg.
           destruct (x==a) eqn: Hxa; destruct (y==a') eqn: Hya';
             move /eqP in Hxa; move /eqP in Hya'.
           { subst x. subst y. contradiction. }
           { auto. }
           { subst y. contradiction. }
           { auto. }  } Qed.
   
  Lemma nw_edg_xy_xy2 (G: UG)(a a' x:A)(P: In a G)(P': ~In a' G):
    (edg G) x a = (nw_edg G a a') x a.
  Proof. {  unfold nw_edg. replace (a==a') with false.
         destruct (x==a); auto. symmetry;switch.
         intro H; move /eqP in H; subst a; contradiction. } Qed.

  Lemma nw_edg_xy_xy3 (G: UG)(a a' y:A)(P: In a G)(P': ~In a' G):
    y <> a' -> (edg G) a y = (nw_edg G a a') a y.
  Proof. {  intro H0. unfold nw_edg. replace (y==a') with false.
         destruct (a==a); auto. symmetry;switch.
         intro H; move /eqP in H; contradiction. } Qed.
  
  Lemma nw_edg_xy_xy4 (G: UG)(a a' x y:A)(P: In a G)(P': ~In a' G):
    y <> a' -> (edg G) x y = (nw_edg G a a') x y.
  Proof. {  intro H0. unfold nw_edg. replace (y==a') with false.
         destruct (x==a); auto. symmetry;switch.
         intro H; move /eqP in H; contradiction. } Qed.
  
  Lemma nw_edg_xy_xy5 (G: UG)(a a' x:A)(P: In a G)(P': ~In a' G):
    x <> a-> (edg G) x a = (nw_edg G a a') x a'.
  Proof. { intro H0. unfold nw_edg. replace (x==a) with false.
           replace (a'== a') with true. auto. symmetry; apply /eqP;auto.
           symmetry;switch;auto. } Qed.

  Hint Resolve nw_edg_a_a' nw_edg_xa_xa' nw_edg_xy_xy nw_edg_xy_xy1: core.
  Hint Resolve nw_edg_xy_xy2 nw_edg_xy_xy3 nw_edg_xy_xy4 nw_edg_xy_xy5: core.

  (*--------------------------------------------------------------------------------------- *)
  (* ---------- Following is the exact definition of edg relation for G' ------------------ *)
   
   Definition ex_edg (G: UG)(a a': A):= mk_sym (mk_irefl ((nw_edg G a a') at_ (add a' G))).

   Definition Repeat_in (G: @UG A)(a: A)(a':A): @UG A.
    refine({| nodes:= add a' G; edg:= (ex_edg G a a');
           |}); unfold ex_edg. all: auto. Defined.

  Variable G: @UG A.
  Variable a a': A.

  Let G':= (Repeat_in G a a').

  Lemma edge_aa': In a G-> a<>a' ->(edg G') a a'.
  Proof.  { simpl. intros H H1.  unfold ex_edg.  auto. } Qed.

  Lemma edg_aa': In a G -> ~ In a' G -> (edg G') a a'.
  Proof. { intros H H1.
         assert (H2: a <> a'). intro Heq; subst a; contradiction.
         apply edge_aa';auto. } Qed.

  Lemma Exa_E'xa' (x: A)(P: In a G)(P': ~In a' G): (edg G) x a-> (edg G') x a'.
  Proof. { simpl. intros H. unfold ex_edg. 
           assert (Ha: a <> a'). intro; subst a; contradiction. 
           assert (Hb: In x G). eauto.
           assert (Hc: x <> a'). intro; subst x; contradiction.  
           auto. } Qed.

   Lemma a_not_eq_a' (P: In a G)(P': ~In a' G): a <> a'.
   Proof. intro. subst a. absurd (In a' G); auto. Qed.

  Hint Resolve edge_aa' Exa_E'xa' a_not_eq_a': core.
   
  Lemma Exy_E'xy (x y:A)(P: In a G)(P': ~In a' G): edg G x y -> edg G' x y.
  Proof. { intro H. simpl. unfold ex_edg.
           assert (Hx: In x G). eauto.
           assert (Hy: In y G). eauto. 
           assert (Hxy: x=y \/ x<>y). eauto.
           destruct Hxy. 
           { subst x; absurd (edg G y y); auto. }
           { auto. } } Qed.

  Hint Immediate Exy_E'xy: core.

 

  (* --- following three results true only for x y both in G  --- *)
  
  Lemma In_E'xy_Exy (x y:A)(P: In a G)(P': ~In a' G):
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

  Lemma In_E'xy_Exy1 (x y:A)(P: In a G)(P': ~In a' G):
    In x G -> In y G  -> edg G' x y -> edg G x y.
  Proof. { intros Gx Gy H. destruct (edg G x y) eqn:Exy. auto.
         switch_in Exy. absurd (edg G' x y). auto using In_E'xy_Exy. auto. }  Qed.
  
   Lemma In_Exy_eq_E'xy (x y:A)(P: In a G)(P': ~In a' G): In x G-> In y G-> edg G x y=edg G' x y.
    Proof. { intros Gx Gy.
           destruct (edg G x y) eqn: Exy; destruct (edg G' x y) eqn: E'xy.
           auto.
           absurd ( edg G' x y). switch;auto. apply Exy_E'xy;auto.
           absurd (edg G x y). switch;auto. apply In_E'xy_Exy1;auto.
           auto. } Qed.

    Hint Immediate In_E'xy_Exy In_E'xy_Exy1 In_Exy_eq_E'xy: core.

   (* ---- if niether x nor y is a' then E' x y = E x y --------*) 

    Lemma E'xy_Exy (x y:A)(P: In a G)(P': ~In a' G):
      x<>a'-> y<>a'-> edg G' x y -> edg G x y.
    Proof. { intros H1 H2. apply /impP.
           destruct (edg G x y) eqn: Hxy.
           { right_;auto. }
           { left_. switch_in Hxy. apply /negP.
             unfold G'. simpl. unfold ex_edg.
             assert (Hyx: ~ edg G y x). auto.
             assert (H3: ~ nw_edg G a a' x y).
             { replace (nw_edg G a a' x y) with (edg G x y).
               auto. auto. }
             assert (H3b: ~ nw_edg G a a' y x).
             { replace (nw_edg G a a' y x) with (edg G y x).
               auto. auto. }
             auto. } } Qed.
    Hint Immediate E'xy_Exy: core.

    Lemma Exy_eq_E'xy (x y:A)(P: In a G)(P': ~In a' G):
      x <> a'-> y<> a'->  edg G x y = edg G' x y.
    Proof. { intros H1 H2.
             assert (H3: edg G x y -> edg G' x y). auto.
             assert (H4: edg G' x y -> edg G x y). auto. auto. } Qed.
    Hint Immediate Exy_eq_E'xy: core.

    (*------------- other special cases of interest------------*)
   Lemma E'xa_Exa (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a -> edg G x a.
      Proof. intros. apply E'xy_Exy;auto. Qed.
   
   Lemma E'xa'_Exa (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'-> edg G' x a' -> edg G x a.
    Proof. { intros H1 H2. simpl.  unfold ex_edg.
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

   Lemma Exa_eq_E'xa'(x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G x a = edg G' x a'.
   Proof. { intros H1 H2.
          assert (H3: edg G x a -> edg G' x a'). auto.
          assert (H4: edg G' x a' -> edg G x a). auto using E'xa'_Exa. auto. } Qed.
            
  Lemma Eay_eq_E'a'y (y:A)(P: In a G)(P': ~In a' G): y<>a -> y<> a' -> edg G a y = edg G' a' y.
  Proof. { replace (edg G a y) with (edg G y a);
           replace (edg G' a' y) with (edg G' y a');
           (eapply Exa_eq_E'xa' || eapply edg_sym); auto. } Qed.

  Hint Immediate E'xa_Exa E'xa'_Exa Exa_eq_E'xa' Eay_eq_E'a'y: core.

  

  (*------------------------- edge property only in G'--------------*)
  Lemma E'xa_E'xa' (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a -> edg G' x a'.
    Proof.  auto.  Qed.

  Lemma E'xa'_E'xa (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a' -> edg G' x a.
  Proof. intros H1 H2 H3.  specialize ( E'xa'_Exa P P' H1 H2 H3) as H4;  auto. Qed.

  Hint Immediate E'xa_E'xa' E'xa'_E'xa: core.
    
  Lemma E'xa_eq_E'xa' (x:A)(P: In a G)(P': ~In a' G): x <> a-> x<> a'->  edg G' x a = edg G' x a'.
   Proof. auto. Qed.

   Lemma E'ay_eq_E'a'y (y:A) (P: In a G)(P': ~In a' G): y<>a -> y<> a'-> edg G' a y = edg G' a' y.
   Proof. { intros H1 H2.
           replace (edg G' a y) with (edg G' y a);
             replace (edg G' a' y) with (edg G' y a').
           auto using E'xa_eq_E'xa'. all: apply edg_sym. } Qed.

   Hint Immediate E'xa_eq_E'xa' E'ay_eq_E'a'y: core.

   (*------------------- G is Induced subgraph of G'-----------------------*)

   Lemma Ind_sub_GG': In a G-> ~ In a' G-> Ind_subgraph G G'.
   Proof.  intros H1 H2. split.
           { subst G'; simpl; unfold Subset; auto. }
           { intros. auto. } Qed.

   Hint Resolve Ind_sub_GG': core.

   (*---------------------------------------------------------------------*)
   (*-------------------- G'_a is isomorphic to G  -----------------------*)

   Lemma G'_a: IsOrd (rmv a G').
   Proof. auto. Qed.

   (* Definition Ind_at (K: list A)(Pk: IsOrd K)(G: UG): UG.
     refine {|nodes:= K; nodes_IsOrd := Pk;
              edg:= (G.(edg) at_ K); |}. all: auto. Defined. *)

   Lemma G'_a_is_ind_subgraph(P: In a G)(P': ~ In a' G): Ind_subgraph (Ind_at G'_a G') G'.
   Proof. split.
          { simpl. auto. }
          { intros x y H1 H2. simpl. symmetry;auto. } Qed.

   Lemma memb_G'_G'_a (P: In a G)(P': ~ In a' G)(x:A): x<>a -> memb x G' = memb x (rmv a G').
   Proof. Admitted.
   
   Let f:= ( fun x:A => match (x == a), (x == a') with
                            | true, true => x
                            | true, false => a'
                            | false, true => a
                            | false, false => x
                     end).

   (* some properties of isomorphism f *)
   Lemma fa_is_a' (P: In a G)(P': ~ In a' G):  (f a) = a'.
   Proof. Admitted.
   Lemma fa'_is_a (P: In a G)(P': ~ In a' G):  (f a') = a.
   Proof. Admitted.
   Lemma fx_is_x (P: In a G)(P': ~ In a' G)(x:A): In x G-> x<>a-> (f x) = x.
   Proof. Admitted.
   Lemma fx_is_x2 (P: In a G)(P': ~ In a' G)(x:A): x<>a'-> x<>a-> (f x) = x.
   Proof. Admitted.
   
   (* -----   fact: f (f x) = x     ------------ *)
   Lemma f_is_invertible (P: In a G)(P': ~ In a' G): forall x : A, f (f x) = x.
   Proof. { assert (H0: a <> a'). auto.
            intro x. unfold f.  destruct (x==a) eqn: Hxa;destruct (x==a') eqn: Hxa'.
            {  absurd (a=a'). auto. move /eqP in Hxa; move /eqP in Hxa'. subst a;auto. }
            { replace (a'== a) with false.
              { replace (a'==a') with true. symmetry;auto. symmetry;auto. }
              { symmetry. switch.  move /eqP. intro H1;apply H0;auto. } }
            { replace (a==a) with true. replace (a==a') with false. all: symmetry;auto.  }
            { rewrite Hxa. rewrite Hxa'. auto. } } Qed.

   (* -----   fact:   G'_a = (s_map f G) -------- *)
   Lemma G'_a_is_s_mapG (P: In a G)(P': ~ In a' G): nodes (Ind_at G'_a G') = (s_map f G).
   Proof. { assert (H0: a <> a'). auto.
          assert (H1: Equal (Ind_at G'_a G') (s_map f G)).
          { split; unfold Subset.
            { (* -- x in G_a' implies x in s_map f G --*)
              intros x H1.
              assert (H1a: x <> a). simpl in H1. 
              { eapply set_rmv_elim2 with (l:= (add a' G));auto. }
              assert (case_xa': x=a' \/ x<>a'). eauto.
              destruct case_xa'.
              { subst x. replace a' with (f a).  auto. auto using fa_is_a'. }
              { assert (H2: In x G).
                { simpl in H1. cut (In x (add a' G)); eauto. }
                replace x with (f x). auto. auto using fx_is_x.  } }
            { (*--- x in s_map f G implie x in G_a' ---*)
              intros y H1.
              assert (H1a: exists x, In x G /\ y= f x ). auto.
              destruct H1a as [x H1a]. destruct H1a as [H1a H1b].
              assert (Hxa: x=a \/ x<>a). eauto.
              destruct Hxa.
              { subst y. replace (f x) with a'. simpl.
                cut (In a' (add a' G)); auto. subst x; symmetry. auto using fa_is_a'. }
              { subst y. replace (f x) with x. simpl.
                cut (In x (add a' G)); auto. symmetry; auto using fx_is_x. } } }
              auto. } Qed. 
   
   (* -----   fact: f preserves edg relation ----- *)
   Lemma f_preserves_edg (P: In a G)(P': ~ In a' G)(x y:A):
     edg G x y = edg (Ind_at G'_a G') (f x) (f y).
   Proof. {  assert (H0: a <> a'). auto.
          assert (H0a: a == a' = false). switch. move /eqP. auto.
          assert (H0b: (rmv a G') [<=] G'). auto.
          assert (H0c: forall x, x <> a -> memb x G'= memb x (rmv a G')).
          auto using memb_G'_G'_a.
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
                assert (y=a'). auto. subst y.
                replace (edg G a a') with false.
                symmetry;switch. cut (~ In a (Ind_at G'_a G')).
                eauto. simpl. cut (NoDup (add a' G)); auto.
                symmetry. switch. cut (~ In a' G); eauto. }
              { (*when y <> a'*)
                assert (y<>a'). move /eqP. switch. auto. 
                replace (edg G a y) with (edg G' a' y). 
                Focus 2. symmetry. apply Eay_eq_E'a'y;auto.
                assert (H3: In a' (rmv a G')). simpl. auto.
                assert (H3a: memb a' G' = memb a' (rmv a G')). symmetry; auto.
                assert (H4: memb y G' = memb y (rmv a G')). auto using  memb_G'_G'_a .
                auto. } }
            { (*when x<>a*)
              assert (x<> a). move /eqP. switch; auto.
              destruct (x==a') eqn: Hxa'.
              { (* when x =a'*)
                assert (x=a'). auto. subst x.
                replace (edg G a' y) with false.
                Focus 2. symmetry; switch; eauto.
                symmetry. replace (y==a') with false.
                switch. cut (~ In a (Ind_at G'_a G')). eauto.
                simpl. cut (NoDup (add a' G)); auto. rewrite <- Hxy. auto. }
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
                { move /eqP in Hya'. subst y.
                  replace (edg G x a') with false.
                  symmetry. switch.
                  cut (~ In a (Ind_at G'_a G')). eauto.
                  simpl. cut (NoDup (add a' G)); auto.
                  symmetry;switch. eauto. }
                { assert (y<>a). move /eqP; switch; auto.
                  assert (y<>a'). move /eqP; switch; auto.
                  replace (edg G x y) with (edg G' x y).
                  Focus 2. auto.
                  assert (memb x G' = memb x (rmv a G')). auto.
                  assert (memb y G' = memb y (rmv a G')). auto.
                  auto. } } } }  } Qed.
                  
   Lemma G_iso_G'_a (P: In a G)(P': ~ In a' G): iso_using f G (Ind_at G'_a G').
   Proof. { assert (H0: a <> a'). auto.
          split.
          { (* ------------------ Proof of the fact that f (f x) = x -----------------*)
             apply f_is_invertible;auto. }
          split.
          { (*----------------- Proof of the fact that G'_a = s_map f G -------------- *)
            apply G'_a_is_s_mapG;auto. }
          { (*---------------  Proof that isomorphism preserves the edg relation-------*)
            intros x y. apply f_preserves_edg;auto.  } } Qed.
            
    
End Repeat_node.

 Hint Resolve edge_aa' Exa_E'xa' a_not_eq_a': core.
 Hint Immediate Exy_E'xy: core.
 Hint Immediate In_E'xy_Exy In_E'xy_Exy1 In_Exy_eq_E'xy: core.
 Hint Immediate E'xy_Exy: core.
 Hint Immediate Exy_eq_E'xy: core.
 Hint Immediate E'xa_Exa E'xa'_Exa Exa_eq_E'xa' Eay_eq_E'a'y: core.
 Hint Immediate E'xa_E'xa' E'xa'_E'xa: core.
 Hint Immediate E'xa_eq_E'xa' E'ay_eq_E'a'y: core.



 
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