







Require Export LovaszRep.

Set Implicit Arguments.

Section GraphExp.
  
  Context { A B:ordType }.

  Definition Exp_of (G: @UG A) (G': @UG B)(g:B-> A):=
    (nodes G = img g G') /\ (forall x y, x <>y -> g x = g y -> edg G' x y) /\
    (forall x y, g x <> g y -> edg G (g x) (g y) = edg G' x y).

End GraphExp.

Section ExpProp.
  
  Context { A B:ordType }.

  Variable G: @UG A.
  Variable G': @UG B.
  Variable g: B-> A.

  Lemma exp_elim1: Exp_of G G' g  -> (nodes G = img g G').
  Proof. intros h; apply h. Qed.

  Lemma exp_elim1a: Exp_of G G' g  -> (img g G' = nodes G).
  Proof. intros h; symmetry; apply h. Qed.

  Lemma exp_elim2 (x y: B): Exp_of G G' g -> x <> y -> g x = g y -> edg G' x y.
  Proof. intros h; apply h. Qed.

  Lemma exp_elim3 (x y: B): Exp_of G G' g -> g x <> g y -> edg G (g x) (g y) = edg G' x y.
  Proof. intros h; apply h. Qed.

  Hint Resolve exp_elim1 exp_elim1a exp_elim2 exp_elim3: core.

  Lemma exp_elim4 (x y: B):Exp_of G G' g  -> edg G' x y -> (g x = g y \/ edg G (g x)(g y)).
  Proof. { intros h1 h2.
           assert (h3: g x = g y \/ g x <> g y). eauto.
           destruct h3 as [h3 | h3].
           { left;auto. }
           { assert (h4: x <> y).
             { intro h4;subst x. absurd (edg G' y y);auto. }
             right. replace (edg G (g x) (g y)) with (edg G' x y).
             auto. symmetry;auto. } } Qed.

  Lemma exp_intro (x1 x2: A):
    Exp_of G G' g -> edg G x1 x2 -> (exists y1 y2,  ( x1 = g y1 /\ x2 = g y2) /\ edg G' y1 y2 ).
  Proof. { intros h1 h2.
           assert (gg': nodes G = img g G'); auto.
           assert (h3: x1 <> x2).
           { intro h3;subst x1. absurd (edg G x2 x2);auto. }
           assert (hx1: In x1 G); eauto.
           assert (hx2: In x2 G); eauto.
           assert (hy1: exists y1, In y1 G' /\ x1 = g y1).
           { rewrite gg' in hx1; auto. }
           assert (hy2: exists y2, In y2 G' /\ x2 = g y2).
           { rewrite gg' in hx2; auto. }
           destruct hy1 as [y1 hy1]; destruct hy2 as [y2 hy2].
           exists y1. exists y2.
           split. split; ( apply hy1 || apply hy2).
           destruct hy1;destruct hy2. subst x1;subst x2.
           replace (edg G' y1 y2) with (edg G (g y1) (g y2)); auto. } Qed.

  Hint Immediate exp_elim4 exp_intro: core.
           
  
End ExpProp.

Hint Resolve exp_elim1 exp_elim1a exp_elim2 exp_elim3: core.
Hint Immediate exp_elim4 exp_intro: core.

  
Section LovaszExp.

  Context { A B :ordType }.
  
  Variable db : B.

  Lemma LovaszExpLemma (G: @UG A)(G': @UG B)(g: B-> A): Exp_of G G' g -> Perfect G -> Perfect G'.
  Proof.
    {
     (* We will prove the result by well founded induction on G'. 
      To use the well founded induction we first need to prove that the relation 
      lt_graph is well founded on UG. This is proved as Lemma lt_graph_is_well_founded
      in the file DecUG.v. *)
      pattern G'. revert G'.
      eapply well_founded_ind with (R:= @lt_graph B).
      apply lt_graph_is_well_founded.
      unfold lt_graph. intros G' IH h1 h2.
      set (P:= fun x y => (negb (g x == g y)) || (x == y)).

      specialize (forall_xy_EM P G') as HC.

      (* The proof is split into two cases C1 and C2. 
         C1: forall x y, In x G' -> In y G' -> x<> y -> g x <> g y 
         C2: exists x y, In x G' /\ In y G' /\ x<> y /\ g x = g y   *)
      destruct HC as [C1 | C2].
      { (* C1: forall x y, In x G' -> In y G' -> x<> y -> g x <> g y *)
        assert (C1a: forall x y: B, In x G' -> In y G' -> g x = g y -> x = y).
        { intros x y hx hy. specialize (C1 x y hx hy) as hP. unfold P in hP.
          move /impP in hP. intros h3; apply /eqP; apply hP; auto. }

        (* In this case G and G' are isomorphic and hence G' is perfect *)
        assert (Hiso: iso G G').
        { apply iso_sym. apply iso_intro with (f:=g). eauto.
          { (*--- morph_using g G' G ---*)
            unfold morph_using.
            unfold Exp_of in h1.
            split. apply h1.
            intros x y hx hy.
            assert (hxy: x = y \/ x <> y). eauto.
            destruct hxy as [hxy | hxy].
            { subst x.
              replace (edg G' y y) with false. replace (edg G (g y) (g y)) with false.
              auto. all: symmetry;switch;auto. }
            { symmetry. apply h1. auto. } }
          { (*----one_one_on G' g ---*)
            unfold one_one_on; intros;auto. }   }  eauto.  }

      { (* C2: exists x y, In x G' /\ In y G' /\ x<> y /\ g x = g y  *)
        assert (C2a:exists x y : B, In x G' /\ In y G' /\ g x = g y /\ x <> y ).
        { destruct C2 as [x C2];destruct C2 as [y C2].
          exists x. exists y. destruct C2 as [C2a C2]. destruct C2 as [C2b C2].
          unfold P in C2. split. auto. split. auto. switch_in C2.
          destruct (g x == g y) eqn: h3; destruct (x == y) eqn: h4; simpl in C2.
          { inversion C2. }
          { move /eqP in h3; move /eqP in h4; split;auto. }
          all: inversion C2. }

        (* In this case we define a subgraph G'_a' := G' \ {a'}   and  prove the following two
           (Exp_of G G'_a' g) and Rep_in G'_a' x y G'. Moreover since G is perfect therefore due 
           to IH G'_a' is also perfect. Furthermore, due to LovaszRepLemma G' is also perfect. *)
        destruct C2a as [a C2a]. destruct C2a as [a' C2a].
        set (G'_a':= ind_at (rmv a' G') G').
        assert (hsize: | G'_a'| < |G' |).
        { simpl. replace (rmv a' G' [i] G') with (rmv a' G').
          replace (| rmv a' G' |) with (|G'| - 1).
          cut (|G'| > 0). omega. cut (In a G').
          case (nodes G'). simpl. tauto. intros;simpl;auto;omega. apply C2a.
          symmetry; eapply rmv_card1;apply C2a.
          apply set_inter_elim15; auto. }

        assert (h3: Exp_of G G'_a' g). admit.

        assert (h4: Perfect G'_a'). admit.

        assert (h5: Rep_in G'_a' a a' G'). admit.

        eapply ReplicationLemma. exact h4. exact h5. }    } Qed.
       
       
      
          

  
  

  
 
    
  End LovaszExp.