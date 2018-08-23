



Require Export Dec_UG.

Set Implicit Arguments.

Section Repeat_edg.


  Set Implicit Arguments.
  Variable A: Type.
  Hypothesis decA: forall x y:A, {x=y}+{x<>y}.
  Open Scope type_scope.
  
  (* ---------- Finite sets as duplicate free lists -------------------------------- *
     Record fset : Type := { set_of :> list A;
                          fset_dupP : noDup decA set_of }.                          
  
  
  (*------------ Reflexive, Symmetric Relation and Functions to construct them -------------*)
  Definition refl (E: A -> A-> bool):= forall x, E x x = true.
  Definition irefl (E: A -> A-> bool):= forall x, E x x = false.
  Definition sym (E: A -> A-> bool):= forall x y, E x y = E y x.
  
  Definition only_at (K: list A)(E: A-> A-> bool):= forall x y, E x y -> (In x K /\ In y K).
  Notation "E 'is_at' K":= (only_at K E) (at level 70).

  (* ---------- UG := finite undirected simple graph ----------------------------*)
  Record UG:Type:= { nodes :> list A;
                        nodes_dupP : noDup decA nodes;
                        edg: A-> A -> bool;
                        edg_irefl: irefl edg;
                        no_edg: edg is_at nodes;
                        edg_sym: sym edg
                   }. 
  (*-- Following declaration expresses that nodes of Graph are duplicate free sets --*)
  Canonical nodes_of (G:UG):= (@Build_fset _  decA G.(nodes) (nodes_dupP G)).

  Check nodes_of.
  Definition V := fun (G:UG) => nodes_of G.
  
  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "| s |":= (length s) (at level 70, no associativity).     

  Definition E_res_to (K: list A)(E: A-> A-> bool)(x y:A):bool:= match (set_mem2 decA x y K) with
                                                            |true => E x y
                                                            |false => false
                                                            end.
   Notation "E 'at_' K":= (E_res_to K E)(at level 70).              

  Definition compl (E: A-> A-> bool)(x y:A):= match (decA x y) with
                                                 | left _ => false
                                                 | right _ => negb (E x y)
                                                 end. 

  Definition Ind_at (K:fset  decA)(G:UG): UG.
      refine ( {|nodes:= K; nodes_dupP := K.(fset_dupP);
                 edg:= (G.(edg) at_ K); |} ).
      { cut (irefl (edg G)). eauto with hint_rel. apply edg_irefl. }
      { eauto with hint_rel. }
      { cut (sym (edg G)). eauto with hint_rel. apply edg_sym. } Defined.

   Notation "G 'res_to' K":= (Ind_at K G) (at level 70). *)

 (*---------- Repeating a vertex a as a' in a graph G-----------------------------------*)
    Definition nw_edg (E: A-> A-> bool)(a a': A)(x y: A):=
    match (decA x a), (decA y a') with
    | left _ , left _ => true
    | left _ , right _ => E a y
    | right _, left _ => E x a
    |right _, right _=> E x y
    end.
  Lemma nw_edg_irefl (E: A -> A-> bool): irefl E -> forall a a', a<>a' -> ~ E a' a -> irefl( nw_edg E a a').
  Proof. { unfold irefl. intros H a a' H1 H2 x. unfold nw_edg.
         case (decA x a).  intro H3; rewrite H3.
         case (decA a a'). intro H4; contradiction. intro H4; auto.
         intro H3. case (decA x a'). intros H4; rewrite H4.
         destruct (E a' a). absurd (true); auto. auto. intro. auto. } Qed.
  
  Lemma nw_edg_E_at_K (E: A-> A-> bool)(a a':A)(K: list A)(P: In a K)(P': ~ In a' K):
    E is_at K -> (nw_edg E a a') is_at (set_add decA a' K).
  Proof. { unfold "is_at". intro H.
         assert(H1: ~ E a a').
         { intro H1. absurd (In a' K). auto. cut (In a K /\ In a' K). tauto. eauto. }
         assert(H2: ~ E a' a).
         { intro H2. absurd (In a' K). auto. cut (In a' K /\ In a K). tauto. eauto. }
         unfold nw_edg. intros x y.
         case (decA x a); case(decA y a'); intros H3 H4.
         { rewrite H3; rewrite H4. split. eapply set_add_intro1.  auto.
           eapply set_add_intro2. auto. }
         { intro H5. split. rewrite H4. eapply set_add_intro1. auto. cut (In y K).
           eapply set_add_intro1. cut (In a K /\ In y K). tauto. eauto. }
         { intro H5. split. assert (H6: In x K /\ In a K). eauto. cut (In x K).
           eapply set_add_intro1.  apply H6. rewrite H3. eapply set_add_intro2. auto. }
         { intro H5. assert(H6: In x K /\ In y K). eauto. 
           split; eapply set_add_intro1; apply H6. } } Qed. 
         
  Definition ex_edg (E: A-> A-> bool)(a a': A):= mk_sym (nw_edg E a a').
  
  Lemma ex_edg_at_K (G: UG decA)(a a':A)(P: In a G)(P': ~ In a' G):
    (ex_edg G.(edg) a a') is_at (set_add decA a' G).
  Proof. { assert (H: a <> a').
         { intro H. absurd (In a' G). auto. rewrite <- H;auto. } 
         assert (H1: ~ edg G a' a).
         { intro H1. assert (H2: In a' G /\ In a G). apply no_edg. auto.
           absurd (In a' G). auto. apply H2. }  
         unfold ex_edg.
         cut ((nw_edg (edg G) a a') is_at set_add decA a' G).
         auto with hint_rel. eapply nw_edg_E_at_K. auto. auto.
         eapply no_edg. } Qed. 
         

  Definition Repeat_in (G: UG decA)(a: A)(a':A)(P: In a G)(P': ~ In a' G): UG decA.
    refine({| nodes:= set_add decA a' G; edg:= mk_sym ((nw_edg G.(edg) a a'));
           |}).
    { apply /nodupP. cut (NoDup G). simpl.  eauto with hint_nodup. apply /nodupP.
      Unshelve. Focus 2.  assumption. eapply nodes_dupP.  }
    { cut (irefl (nw_edg G.(edg) a a')).  eauto with hint_rel.
      eapply nw_edg_irefl. eapply edg_irefl. intro H. absurd (In a' G). auto.
      rewrite <- H; auto. intro H. cut (In a' G /\ In a G). intro H1.
      absurd (In a' G). auto.  apply H1. eapply no_edg. auto. }
    { eapply ex_edg_at_K.  auto. auto. }
    { eauto with hint_rel. } Defined.

End Repeat_edg.

Section Ex_edg_prop.
  Variable A:Type.
  Hypothesis decA:  forall x y:A, {x=y}+{x<>y}.

  Variable G: UG decA.
  Variable a a': A.
  Hypothesis P: In a G.
  Hypothesis P': ~In a' G.

  Let G_a':= Repeat_in G a a' P P'.
  
  Lemma edg_a_a': (edg G_a') a a'.
  Proof. { simpl. cut (nw_edg decA (edg G) a a' a a'=true). eauto with hint_rel.
         unfold nw_edg. case(decA a a); case(decA a' a').
         auto.  intros; absurd(a'=a');auto.
         intros;absurd(a=a);auto. intros;absurd(a=a);auto. } Qed.
  Lemma edg_a'_a: (edg G_a') a' a.
  Proof. replace (edg G_a' a' a) with (edg G_a' a a').  eapply edg_a_a'. eapply mk_symP. Qed.      

  Lemma Exy_E'xy (x y:A): edg G x y -> edg G_a' x y.
  Proof. { intro H. simpl. cut (nw_edg decA (edg G) a a' x y=true).
         eauto with hint_rel.
         unfold nw_edg. case(decA  x a);case(decA y a').
         { auto. }
         { intros H1 H2; rewrite H2 in H; eauto. }
         { intros H1 H2; rewrite H1 in H. absurd (In a' G). auto.
           cut(In x G /\ In a' G). tauto. eapply no_edg;auto. }
         { auto. } } Qed.

  Lemma In_xy_G (x y:A): In x G-> In y G-> edg G x y=edg G_a' x y.
  Proof. { intros H1 H2. simpl. unfold mk_sym.
         unfold nw_edg. case(decA x a); case (decA y a');simpl.
         { intros e. absurd (In a' G). auto. rewrite <- e;auto. }
         { simpl. case (decA y a); case (decA x a'). simpl.
           { intro e. absurd(In a' G). auto.  rewrite <- e;auto. }
           { intros H e H3 f; rewrite e; rewrite f. case (edg G a a); simpl; auto.  }
           { intro e. absurd(In a' G). auto.  rewrite <- e;auto. }
           { intros H3 H4 H5 e; rewrite e. replace (edg G y a) with (edg G a y).
             case (edg G a y);simpl;auto. eapply edg_sym. } }
         { intros e. absurd(In a' G).  auto. rewrite <- e;auto. }
         { case(decA y a); case (decA x a').
           {intros e.  absurd(In a' G). auto. rewrite <- e; auto. }
           { intros e1 e; rewrite e. replace (edg G a x) with (edg G x a).
             case(edg G x a);simpl;auto. eapply edg_sym. }
           { intro e. absurd (In a' G). auto. rewrite <-e;auto.  }
           { intros; replace (edg G y x) with (edg G x y). case (edg G x y);simpl;auto.
             eapply edg_sym.  } }   } Qed.
  

  Lemma edg_G'(x:A): x <> a-> x<> a'->  edg G_a' x a = edg G_a' x a'.
  Proof. { intros H H1.  simpl. unfold mk_sym.
         unfold nw_edg.
         case (decA x a); case(decA a a');case (decA  x a'); simpl; try(contradiction).
         { intros H2 e. absurd (In a G). rewrite e;auto. auto. }
         { case(decA a a).
           { case (decA a' a');case (decA a' a); try(contradiction).
             intro e. absurd (In a' G). auto. subst a'. auto.
             replace (edg G a x) with (edg G x a). replace (edg G a' x) with false.
             case (edg G x a);simpl; auto. case (edg G a' x) eqn:H2.
             absurd (In a' G). auto. cut(In a' G /\ In x G).
             tauto. eapply no_edg. auto. auto. eapply edg_sym. }
           { intro e; absurd (a=a);auto.  }  }   } Qed. 

  Lemma edg_G'1 (x:A): x<>a -> x<> a'-> edg G_a' a x = edg G_a' a' x.
  Proof. { intros H1 H2.
           replace (edg G_a' a x) with (edg G_a' x a);
             replace (edg G_a' a' x) with (edg G_a' x a').
         eapply edg_G';auto. apply edg_sym. apply edg_sym. apply edg_sym. } Qed. 

  Lemma edg_G_G'(x:A): x <> a-> x<> a'->  edg G x a = edg G_a' x a'.
  Proof. { intros H H1.  simpl. unfold mk_sym.
         unfold nw_edg.
         case (decA x a); case(decA a a');case (decA  x a'); simpl; try(contradiction).
         { intros H2 e. absurd (In a G). rewrite e;auto. auto. }
          { case (decA a' a');case (decA a' a); try(contradiction).
             intro e. absurd (In a' G). auto. subst a'. auto.
              replace (edg G a' x) with false.
             case (edg G x a);simpl; auto. case (edg G a' x) eqn:H2.
             absurd (In a' G). auto. cut(In a' G /\ In x G).
             tauto. eapply no_edg. auto. auto. } } Qed.
  
  Lemma edg_G_G'1 (x:A): x<>a -> x<> a' -> edg G a x = edg G_a' a' x.
  Proof. { replace (edg G a x) with (edg G x a);
           replace (edg G_a' a' x) with (edg G_a' x a');
           (eapply edg_G_G'|| eapply edg_sym).      } Qed. 


End Ex_edg_prop.


Section PowerSets.
   Variable A:Type.
   Hypothesis decA:  forall x y:A, {x=y}+{x<>y}.

   
  Check filter.
  Check map.
  Let l_dec:= (list_eq_dec decA).
  Check cons.
  Fixpoint Pw (l: list A): list (list A):=
    match l with
    | nil=> nil::nil          
    |h::tl=> set_union (l_dec) (Pw tl) (map (cons h) (Pw tl))
    end.
  
  Let L:= Pw (nil). Eval compute in (length L).
  Lemma Pow_elim(l: list A): forall l0, In l0 (Pw l)-> Subset l0 l.
  Proof. { induction l.
         { intros l0 H. destruct H.  subst l0. unfold "[<=]". tauto. inversion H. }
         { simpl.  intros l0 H.
         cut( In l0 (Pw l) \/ In l0 (map (cons a)(Pw l))).
         Focus 2. eapply set_union_elim. eauto. intro H1; destruct H1 as [H1l | H1r].
         { assert (H1:l0 [<=] l).  eauto. unfold "[<=]".  auto with hint_list. }
         { assert(H1: exists l', cons  a l' = l0 /\ In l' (Pw l)).
           eapply in_map_iff;auto.
           destruct H1 as [l' H1].  destruct H1 as [H1 H2]. subst l0.
           assert (H3: l' [<=] l). eauto. unfold "[<=]". intros a0 H4.
           assert (H5: a0=a \/ In a0 l'). eauto with hint_list.
           destruct H5 as [H5 | H6]. subst a0; eauto with hint_list.
           eauto with hint_list. } } } Qed. 
  Lemma Pow_intro(l: list A): forall l0, Subset l0 l -> In l0 (Pw l).
  Proof. induction l.
         { intros l0 H. destruct l0. simpl. left;auto.
           absurd ( In a nil). eauto with hint_list. eauto with hint_list. }
         { 
  
  End PowerSets.

Section LovaszRepLemma.

  Variable A:Type.
  Hypothesis decA:  forall x y:A, {x=y}+{x<>y}.

  Variable G: UG decA.
  Variable a a': A.
  Hypothesis P: In a G.
  Hypothesis P': ~In a' G.

  Check (edg_a_a').
  Let G_a':= Repeat_in G a a' P P'.

  

  Lemma LovaszReplicationLemma: Is_perfect G -> Is_perfect G_a'.
    Proof. Admitted.
  
  End LovaszRepLemma.