 





Require Export SetMaps.

Set Implicit Arguments.

Section DecidableGraphs.
 Set Implicit Arguments.
  Variable A: Type.
  Hypothesis decA: forall x y:A, {x=y}+{x<>y}.


 (* ---------- Finite sets as duplicate free lists -------------------------------- *
     Record fset : Type := { set_of :> list A;
                          fset_dupP : noDup decA set_of }.                          *)
  
  (*----------- Graph:= finite simple graphs----------------------------------------*)
  Record Graph:Type:={ V_of :> list A;
                       V_dupP: noDup decA V_of;
                       edge: A-> A-> bool;
                       edge_irefl: forall x, edge x x =false;
                       no_edge: forall x y, edge x y -> (In x V_of /\ In y V_of)
                     }.
  
  
  
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

  Definition mk_refl (E: A-> A-> bool)(x y:A): bool:= match (decA x y) with
                                              | left _ => true
                                              |right _ => E x y
                                              end.
  Lemma mk_reflP (E: A-> A-> bool): refl (mk_refl E).
  Proof. { unfold refl. intro x. assert (H: x=x). reflexivity. 
           unfold mk_refl. destruct (decA x x) eqn:H1. auto. contradiction. } Qed.
  

  Definition mk_irefl (E: A-> A-> bool)(x y:A): bool:= match (decA x y) with
                                              | left _ => false
                                              |right _ => E x y
                                              end.
  Lemma mk_ireflP (E: A -> A-> bool): irefl (mk_irefl E).
  Proof. { unfold irefl. intro x. assert (H: x=x). reflexivity. 
           unfold mk_irefl. destruct (decA x x) eqn:H1. auto. contradiction. } Qed.
  Lemma Exy_inv_for_mk_irefl (E:A->A-> bool)(x y:A): x<>y-> E x y = (mk_irefl E) x y.
  Proof. intros H. unfold mk_irefl. case (decA x y) eqn: H1. contradiction. tauto. Qed.
  Lemma Exy_inv_for_mk_irefl1 (E:A->A-> bool)(x y:A): x<>y-> E x y -> (mk_irefl E) x y.
   Proof. intros H. unfold mk_irefl. case (decA x y) eqn: H1. contradiction. tauto. Qed. 
  Lemma negExy_inv_for_mk_irefl(E: A->A->bool)(x y:A): ~ E x y -> ~ (mk_irefl E) x y.
  Proof. { intros H H1. apply H.  unfold mk_irefl in H1. case(decA x y) eqn: H2.
           inversion H1. auto. } Qed.
  
  
  Definition mk_sym (E: A-> A-> bool)(x y:A): bool:= E x y || E y x.
  Lemma mk_symP (E: A-> A-> bool): sym (mk_sym E).
  Proof. { unfold sym. intros x y.  unfold mk_sym.
           destruct (E x y); destruct (E y x); simpl; auto. } Qed.
  Lemma Exy_inv_for_mk_sym (E: A->A->bool)(x y:A): E x y-> (mk_sym E) x y.
  Proof. unfold mk_sym. intro H. apply /orP.  tauto. Qed.
  Lemma negExy_inv_for_mk_sym (E: A->A->bool)(x y:A): ~ E x y-> ~ E y x -> ~(mk_sym E) x y.
  Proof.  unfold mk_sym. case( E x y); case(E y x);simpl; tauto. Qed.
  
  Lemma irefl_inv_for_mk_sym (E: A-> A-> bool): irefl E -> irefl (mk_sym E).
  Proof. { unfold irefl. intro H. intro x. unfold mk_sym.
           specialize (H x). rewrite H; simpl;auto. } Qed. 
  Lemma sym_inv_for_mk_irefl (E: A->A-> bool): sym E -> sym (mk_irefl E).
  Proof. { unfold sym. intros H x y. unfold mk_irefl.
           destruct (decA x y);destruct (decA y x). auto.
           symmetry in e; contradiction. symmetry in e; contradiction. apply H. } Qed.
  
  Definition E_res_to (K: list A)(E: A-> A-> bool)(x y:A):bool:= match (set_mem2 decA x y K) with
                                                            |true => E x y
                                                            |false => false
                                                            end.
   Notation "E 'at_' K":= (E_res_to K E)(at level 70).

   Lemma edg_equal_at_K (K: list A)(E: A-> A-> bool)(x y: A):
     In x K -> In y K -> E x y = (E at_ K) x y.
   Proof. { intros H1 H2. assert (H3: set_mem2 decA x y K).
          apply /mem2P. split; auto. unfold E_res_to. rewrite H3. reflexivity. } Qed.
   
   Lemma no_edg_E_at_K (E: A-> A-> bool)(K: list A): forall x y, (E at_ K) x y-> (In x K /\ In y K).
   Proof. { intros x y. unfold E_res_to. destruct (set_mem2 decA x y K)  eqn: H.
          intro H1. assert(H2: IN x y K). apply /mem2P. eauto. auto.
          intro H1. inversion H1. } Qed. 
   Lemma is_at_inv_for_E_at_K1 (E: A-> A-> bool)(K: list A): (E at_ K) is_at K.
   Proof. unfold "is_at". eapply no_edg_E_at_K. Qed.
   Lemma is_at_inv_for_E_at_K (G: UG)(K: list A): ((edg G) at_ K) is_at K.
   Proof. simpl. apply is_at_inv_for_E_at_K1. Qed.
   
   Lemma irefl_inv_for_E_at_K (E: A-> A-> bool)(K: list A): irefl E -> irefl (E at_ K).
   Proof. unfold irefl. intros H x. unfold "at_". destruct (set_mem2 decA x x K) eqn:H1.
          auto. auto.  Qed.
   Lemma sym_inv_for_E_at_K(E: A-> A-> bool)(K: list A): sym E -> sym (E at_ K).
   Proof. { unfold sym. intros H x y. unfold "at_".
          destruct (set_mem2 decA x y K) eqn:H1. destruct (set_mem2 decA y x K) eqn: H2.
          auto. assert (H3: set_mem2 decA y x K = set_mem2 decA x y K).
          eauto with hint_set. rewrite H1 in H3; rewrite H2 in H3; discriminate H3.
          replace (set_mem2 decA y x K) with (set_mem2 decA x y K).
          rewrite H1;simpl; auto. eauto with hint_set. } Qed. 
   Lemma is_at_inv_for_mk_irefl(E:A-> A-> bool)(K:list A): E is_at K -> (mk_irefl E) is_at K.
   Proof. { unfold "is_at". intro H. intros x y. unfold mk_irefl. case (decA x y).
          intros H1 H2. inversion H2. intros H1 H2. apply H;auto. } Qed.
   Lemma is_at_inv_for_mk_sym(E: A-> A-> bool)(K:list A): E is_at K -> (mk_sym E) is_at K.
   Proof. { unfold "is_at". intros H x y. unfold mk_sym. move /orP. intro H1.
          elim H1. auto.  intro H2. cut (In y K /\ In x K). tauto. auto. } Qed.

   Definition compl (E: A-> A-> bool)(x y:A):= match (decA x y) with
                                                 | left _ => false
                                                 | right _ => negb (E x y)
                                                 end.
  Print negb. (*     negb = fun b : bool => if b then false else true     *)
  Lemma complP (E: A-> A-> bool)(x y:A): x<>y -> E x y -> (compl E x y = false).
  Proof. { intros H H1. unfold compl. case (decA x y) eqn:H2. auto.
         case (E x y) eqn:H3; simpl. auto. discriminate H1. } Qed. 
  Lemma complP1 (E: A-> A-> bool)(x y:A): x<>y -> compl E x y -> E x y =false.
  Proof. { unfold compl. case (decA x y) eqn:H2. intros H1 H3; discriminate H3.
         intro H3. case (E x y); simpl. intro H; discriminate H. auto. } Qed.
  
  Lemma irefl_inv_for_compl (E: A-> A-> bool ): irefl E -> irefl (compl E).
  Proof. { intros H x. unfold compl.  case (decA x x). auto. intro.
         absurd (x=x). auto. reflexivity. } Qed.

   Lemma sym_inv_for_compl (E: A-> A-> bool): sym E -> sym (compl E).
   Proof. {  intro H; unfold sym. intros.  specialize (H x y).
             unfold compl. replace (E x y) with (E y x).
            case (decA x y); case (decA y x).
            auto. intros H1 H2; symmetry in H2; contradiction.
            intros H1 H2; symmetry in H1;contradiction.  auto. } Qed.
  

   Hint Resolve mk_ireflP mk_symP complP complP1: hint_rel.
   Hint Resolve irefl_inv_for_mk_sym irefl_inv_for_compl irefl_inv_for_E_at_K: hint_rel.
   Hint Resolve sym_inv_for_mk_irefl sym_inv_for_compl sym_inv_for_E_at_K: hint_rel.
   Hint Resolve  is_at_inv_for_E_at_K is_at_inv_for_E_at_K1: hint_rel.
   Hint Resolve is_at_inv_for_mk_irefl is_at_inv_for_mk_sym: hint_rel.


   (*------Concepts of Subgraph and the Induced Subgraph of a given  graph G ---------- *)
   Definition Is_subgraph (G1 G2: UG): Prop := G1 [<=] G2 /\ (forall x y, edg G1 x y-> edg G2 x y).
   Definition Is_ind_subgraph ( G1 G2: UG): Prop :=
     G1 [<=] G2 /\ (forall x y, In x G1-> In y G1-> edg G1 x y = edg G2 x y).
   
   Definition Ind_at (K:fset  decA)(G:UG): UG.
      refine ( {|nodes:= K; nodes_dupP := K.(fset_dupP);
                 edg:= (G.(edg) at_ K); |} ).
      { cut (irefl (edg G)). eauto with hint_rel. apply edg_irefl. }
      { eauto with hint_rel. }
      { cut (sym (edg G)). eauto with hint_rel. apply edg_sym. } Defined.

   Notation "G 'res_to' K":= (Ind_at K G) (at level 70).
   
   Notation " G1 'is_ind_in' G2 ":= (Is_ind_subgraph G1 G2) (at level 70).
   Notation " G1 'is_sub_in' G2 ":= (Is_subgraph G1 G2) (at level 70). 

  Lemma induced_fact1: forall (K:fset decA) (G:UG),  K[<=]G -> Is_ind_subgraph (G res_to K) G.
   Proof. { intros K G H. split. assumption. simpl.
          intros. symmetry. eapply edg_equal_at_K; auto. }  Qed.

   Lemma self_is_induced (G: UG): Is_ind_subgraph G G.
   Proof. split;  auto with hint_set. Qed.
   Hint Resolve self_is_induced : hint_graph.
   Lemma induced_is_subgraph (G: UG): forall (G1: UG), Is_ind_subgraph G1 G -> Is_subgraph G1 G.
   Proof. { intros G1 H1. split. apply H1. destruct H1 as [H1 H2]. intros x y H3.
          replace (edg G x y) with (edg G1 x y). auto. Check no_edg_E_at_K.
          assert (H4: In x G1 /\ In y G1). eapply no_edg;auto. 
          apply H2; apply H4. } Qed.
   Hint Resolve induced_is_subgraph: hint_graph.

  (*------------ Concept of Stable set and independence number in a graph G ------------*)
  Definition Is_stable_in (G: UG)(I: list A): Prop:=
    I [<=] G /\ (forall x y, In x I-> In y I -> edg G x y = false).
  Definition Largest_I_in (G: UG)(I:list A): Prop:=
    Is_stable_in G I /\ (forall I', Is_stable_in G I' -> |I'| <= |I|).
  Definition i_num (G:UG)(n:nat):= exists I, Largest_I_in G I /\ |I|=n.
  
  (*----- Concepts of Cliq and the Cliq number for a given graph G ----------------------*)
   Definition Is_cliq (G:UG): Prop := forall x y, In x G -> In y G -> edg G x y.
   Definition Is_cliq_in (G:UG)(K: list A):Prop := K [<=] G /\ (forall x y, In x K-> In y K -> edg G x y).
   Definition Largest_K_in (G: UG)(K:list A): Prop:=
     Is_cliq_in G K /\ (forall K', Is_cliq_in G K'-> |K'| <= |K|).   
   Definition cliq_num (G:UG)(n:nat):= exists K, Largest_K_in G K /\ |K|=n.

   Notation " K 'is_cliq_in' G":= (Is_cliq_in G K) (at level 70).
   Notation "K 'largest_k_in' G " := (Largest_K_in G K) (at level 70). 
  
   Lemma cliq_fact1: forall (K:fset decA)(G:UG), Is_cliq_in G K  -> Is_cliq ( G res_to K).
   Proof. { intros K G H. destruct H. intros x y H1. intro H2.  simpl.
          replace ((edg G at_ K) x y) with ( edg G x y). apply H0;assumption.
          eapply edg_equal_at_K; auto. }  Qed.
   
   (*------ Concepts of Coloring and the chromatic number of a graph G ------------------*)
   Definition Is_coloring_of (G: UG)(f: A-> nat): Prop:= forall x y, In x G-> In y G -> edg G x y -> f x <> f y.
   
   Definition clrs_of (f:A->nat) (l:list A): list nat.
     refine  (s_map _ f l). decide equality. Defined.
   
   Definition Best_coloring_of (G: UG) (f:A->nat): Prop :=
     Is_coloring_of G f /\ (forall f1, Is_coloring_of G f1 -> | clrs_of f G | <= | clrs_of f1 G|).
   Definition chrom_num (G: UG) (n: nat):= exists f, Best_coloring_of G f /\ | clrs_of f G | = n.

   
   (*-------- Concepts of nice graph and  perfect graphs -------------------------------- *)
   Definition Is_nice (G: UG): Prop:= forall n, cliq_num G n -> chrom_num G n.
   Definition Is_perfect (G: UG): Prop:= forall G1, Is_ind_subgraph G1 G -> Is_nice G1.
      
   Lemma perfect_is_nice (G: UG): Is_perfect G -> Is_nice G.
   Proof.  unfold Is_perfect. intros H; apply H. auto with hint_graph. Qed.
   Hint Resolve perfect_is_nice: hint_graph.
   
   (*------------ Complement of a graph G and its edge relation--------------------- *)
  Print sumbool.
  Lemma is_at_inv_for_compl1 (E:A-> A-> bool)(K:list A): ((compl E) at_ K) is_at K.
  Proof. { unfold "is_at". intros x y. unfold compl. unfold "at_".
         case (set_mem2 decA x y K) eqn: H.
         intro H1. cut (IN x y K). unfold IN;tauto. apply /mem2P; eauto.
         intro H1; discriminate H1. } Qed.
  Lemma is_at_inv_for_compl (G:UG): ((compl (edg G)) at_ G) is_at G.
  Proof. eapply is_at_inv_for_compl1. Qed.
  Hint Resolve is_at_inv_for_compl : hint_rel.
  Hint Resolve is_at_inv_for_compl : hint_graph.
  Definition Compl (G: UG): UG.
    refine ({|nodes:= G.(nodes);
             nodes_dupP := G.(nodes_dupP);
             edg:= ((compl G.(edg)) at_ G); |}).
    { cut (irefl (edg G)). eauto with hint_rel. eapply edg_irefl. }
    { eauto with hint_graph. }
    { cut (sym (edg G)). eauto with hint_rel. eapply edg_sym. } Defined.

 (* 
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
  Lemma ex_edg_at_K (G: UG)(a a':A)(P: In a G)(P': ~ In a' G):
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
         

  Definition Add_in (G: UG)(a: A)(a':A)(P: In a G)(P': ~ In a' G): UG.
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
  
 *)  

End DecidableGraphs.

Hint Resolve mk_ireflP mk_symP complP complP1: hint_rel.
Hint Resolve irefl_inv_for_mk_sym irefl_inv_for_compl irefl_inv_for_E_at_K: hint_rel.
Hint Resolve sym_inv_for_mk_irefl sym_inv_for_compl sym_inv_for_E_at_K: hint_rel.
Hint Resolve is_at_inv_for_E_at_K is_at_inv_for_E_at_K: hint_rel.
Hint Resolve is_at_inv_for_mk_irefl is_at_inv_for_mk_sym: hint_rel.
Hint Resolve Exy_inv_for_mk_irefl Exy_inv_for_mk_irefl1 Exy_inv_for_mk_sym: hint_rel.

Hint Resolve self_is_induced induced_is_subgraph perfect_is_nice: hint_graph.

Hint Resolve is_at_inv_for_compl : hint_rel.
Hint Resolve is_at_inv_for_compl : hint_graph.




Notation "E 'is_at' K":= (only_at K E) (at level 70).

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "| s |":= (length s) (at level 70, no associativity).

 Notation "E 'at_' K":= (E_res_to K E)(at level 70).

 Notation "G 'res_to' K":= (Ind_at K G) (at level 70).
   
   Notation " G1 'is_ind_in' G2 ":= (Is_ind_subgraph G1 G2) (at level 70).
   Notation " G1 'is_sub_in' G2 ":= (Is_subgraph G1 G2) (at level 70). 

Notation " K 'is_cliq_in' G":= (Is_cliq_in G K) (at level 70).
   Notation "K 'largest_k_in' G " := (Largest_K_in G K) (at level 70). 