 

(* ------------------ Descriptions--------------------------------------------------

 This file implements the notion of finite undirected graphs representaed as UG
 
  Record UG:Type:= { nodes :> list A;
                        nodes_IsOrd : IsOrd nodes;
                        edg: A-> A -> bool;
                        edg_irefl: irefl edg;
                        no_edg: edg only_at nodes;
                        edg_sym: sym edg
                   }.

 In order to be lazy while declaring an instance for UG we provide functions such as
 mk_irefl, mk_sym and E_res_to  which can be used to convert any graph into
 the exact specifications of an undirected graph (UG). 
 Moreover, we prove that these functions work well when used together. They do not 
 disturb the properties established by each other. 

 We also define the concept of Subgraph, Ind_Subgraph and Complement of a Graph.
 
 Predicate              Boolean function       Joining Lemma
 Subgraph G1 G2         subgraph G1 G2         subgraphP
 Ind_Subgraph G1 G2     ind_subgraph G1 G2     ind_subgraphP
  

 Definition Compl (G: UG): UG.
    refine ({|nodes:= G.(nodes);
             nodes_IsOrd := G.(nodes_IsOrd);
             edg:= ((compl G.(edg)) at_ G); |}). all: auto. Defined.

---------------------------------------------------------------------------------------*)

Require Export SetMaps.
Require Export Powerset.

Set Implicit Arguments.

Section DecidableGraphs.

  Context { A: ordType }.
  
  (*------------ Reflexive, Ireflexive and Symmetric Relation --------------------------------*)
  Definition refl (E: A -> A-> bool):= forall x, E x x = true.
  Definition irefl (E: A -> A-> bool):= forall x, E x x = false.
  Definition sym (E: A -> A-> bool):= forall x y, E x y = E y x.
  
  Definition edg_only_at (K: list A)(E: A-> A-> bool):= forall x y, E x y -> (In x K /\ In y K).
  Notation "E 'only_at' K":= (edg_only_at K E) (at level 70).
  Hint Unfold edg_only_at.

  (* ---------- UG := finite undirected simple graph ----------------------------*)
  Record UG:Type:= { nodes :> list A;
                        nodes_IsOrd : IsOrd nodes;
                        edg: A-> A -> bool;
                        edg_irefl: irefl edg;
                        no_edg: edg only_at nodes;
                        edg_sym: sym edg
                   }.
  
  Hint Resolve nodes_IsOrd edg_irefl edg_sym: core.
  Hint Resolve IsOrd_S: core.
  
  (*------ Following declaration expresses that nodes of Graph are ordered sets -----------*)

  (* Record set_on : Type := { S_of :> list A;
                             IsOrd_S : IsOrd S_of }.*)

  Canonical nodes_of (G:UG):= (@Build_set_on  A G.(nodes) (nodes_IsOrd G)).

  Definition V := fun (G:UG) => nodes_of G.

  Lemma no_edg1 (G: UG)(x y:A): (edg G) x y -> In x G.
  Proof. apply no_edg. Qed.

  Lemma no_edg2 (G: UG)(x y:A): (edg G) x y -> In y G.
  Proof. apply no_edg. Qed.
  
  
  Lemma no_self_edg (G: UG)(x y:A): edg G x y -> x <>y.
  Proof. intros H Hxy; subst x; absurd (edg G y y); [ switch;apply edg_irefl | auto]. Qed.
  Lemma no_self_edg1 (G: UG)(x:A): ~ edg G x x.
  Proof. intros H. absurd (edg G x x); [ switch;apply edg_irefl | auto]. Qed.
  Lemma sym_edg (G: UG)(x y:A): edg G x y -> edg G y x.
    Proof. rewrite edg_sym; auto. Qed.

    Hint Resolve no_edg2 no_edg1 no_self_edg no_self_edg1 : core.
    Hint Immediate edg_sym sym_edg: core.
  
  (*---------- function  mk_refl to make a relation reflexive ------------------------------*)

  Definition mk_refl (E: A-> A-> bool)(x y:A): bool:= match (x == y) with
                                              |true => true
                                              |false => E x y
                                              end.
  Lemma mk_reflP (E: A-> A-> bool): refl (mk_refl E).
  Proof. { unfold refl. intro x. assert (H: x=x). reflexivity. 
           unfold mk_refl. destruct (x == x) eqn:H1. auto. by_conflict. } Qed.
  

  (*------------ function mk_irefl to make a relation ireflexive----------------------------*)
  Definition mk_irefl (E: A-> A-> bool)(x y:A): bool:= match (x == y) with
                                              |true => false
                                              |false => E x y
                                               end.
  
  Lemma mk_ireflP (E: A -> A-> bool): irefl (mk_irefl E).
  Proof. { unfold irefl. intro x. assert (H: x=x). reflexivity. 
           unfold mk_irefl. destruct (x == x) eqn:H1. auto. by_conflict. } Qed.

  (*------------- mk_irefl makes minimum changes to make a relation irreflexive -----------*)
  Lemma Exy_inv_for_mk_irefl (E:A->A-> bool)(x y:A): x<>y-> E x y = (mk_irefl E) x y.
  Proof. intros H. unfold mk_irefl. case (x == y) eqn: H1. by_conflict. auto.  Qed.
  Lemma Exy_inv_for_mk_irefl1 (E:A->A-> bool)(x y:A): x<>y-> E x y -> (mk_irefl E) x y.
   Proof. intros H. unfold mk_irefl. case (x == y) eqn: H1. by_conflict. auto. Qed. 
  Lemma negExy_inv_for_mk_irefl(E: A->A->bool)(x y:A): ~ E x y -> ~ (mk_irefl E) x y.
  Proof. { intros H H1. apply H.  unfold mk_irefl in H1. case(x == y) eqn: H2.
           inversion H1. auto. } Qed.
  

  (*--------------- mk_sym function makes a relation symmetric by making min changes--------*)
  Definition mk_sym (E: A-> A-> bool)(x y:A): bool:= E x y || E y x.
  Lemma mk_symP (E: A-> A-> bool): sym (mk_sym E).
  Proof. { unfold sym. intros x y.  unfold mk_sym.
           destruct (E x y); destruct (E y x); simpl; auto. } Qed.
  Lemma Exy_inv_for_mk_sym (E: A->A->bool)(x y:A): E x y-> (mk_sym E) x y.
  Proof. unfold mk_sym. intro H. apply /orP.  tauto. Qed.
  Lemma Exy_inv_for_mk_sym1 (E: A->A->bool)(x y:A): E x y-> (mk_sym E) y x.
  Proof. unfold mk_sym. intro H. apply /orP.  tauto. Qed.
  
  Lemma negExy_inv_for_mk_sym (E: A->A->bool)(x y:A): ~ E x y-> ~ E y x -> ~(mk_sym E) x y.
  Proof.  unfold mk_sym. case( E x y); case(E y x);simpl; tauto. Qed.

  Hint Resolve Exy_inv_for_mk_irefl1 Exy_inv_for_mk_sym Exy_inv_for_mk_sym1: core.
  
  (*--------------- mk_irefl and mk_sym are invariant over each other ---------------------*)
  Lemma irefl_inv_for_mk_sym (E: A-> A-> bool): irefl E -> irefl (mk_sym E).
  Proof. { unfold irefl. intro H. intro x. unfold mk_sym.
           specialize (H x). rewrite H; simpl;auto. } Qed. 
  Lemma sym_inv_for_mk_irefl (E: A->A-> bool): sym E -> sym (mk_irefl E).
  Proof. { unfold sym. intros H x y. unfold mk_irefl.
           destruct (x== y) eqn:H1;destruct (y == x) eqn:H2. auto.
           move /eqP in H1; subst x; by_conflict.
           move /eqP in H2; subst x; by_conflict. auto.  } Qed.
  

  (*------------------ E at_ K := relation E restricted on the set of nodes K ------------*)
  Definition E_res_to (K: list A)(E: A-> A-> bool)(x y:A):bool:= match (mem2 x y K) with
                                                            |true => E x y
                                                            |false => false
                                                            end.
   Notation "E 'at_' K":= (E_res_to K E)(at level 70).

   Lemma edg_equal_at_K (K: list A)(E: A-> A-> bool)(x y: A):
     In x K -> In y K -> E x y = (E at_ K) x y.
   Proof. { intros H1 H2. assert (H3: mem2 x y K).
            apply /mem2P. split; auto. unfold E_res_to. rewrite H3. reflexivity. } Qed.  
   
   Lemma no_edg_E_at_K (E: A-> A-> bool)(K: list A): forall x y, (E at_ K) x y-> (In x K /\ In y K).
   Proof. { intros x y. unfold E_res_to. destruct (mem2 x y K)  eqn: H.
          intro H1. assert(H2: IN x y K). apply /mem2P. eauto. auto.
          intro H1. inversion H1. } Qed.
   Lemma no_edg_E_at_K1 (E: A-> A-> bool)(K: list A): forall x y, (E at_ K) x y-> In x K.
   Proof. intros x y H; apply no_edg_E_at_K in H; tauto.  Qed.
   Lemma no_edg_E_at_K2 (E: A-> A-> bool)(K: list A): forall x y, (E at_ K) x y-> In y K.
   Proof. intros x y H; apply no_edg_E_at_K in H; tauto.  Qed.
   
   Hint Immediate no_edg_E_at_K1 no_edg_E_at_K2 : core.
   
   Lemma Exy_inv_for_at_K (K: list A)(E: A-> A-> bool)(x y: A):
     In x K -> In y K -> E x y -> (E at_ K) x y.
   Proof. Admitted.
   Lemma Exy_inv_for_at_K1 (K: list A)(E: A-> A-> bool)(x y: A): (E at_ K) x y -> E x y.
   Proof. Admitted.
   Lemma negExy_inv_for_at_K (K: list A)(E: A-> A-> bool)(x y: A): ~ E x y -> ~ (E at_ K) x y.
   Proof. Admitted.

   
   Hint Resolve Exy_inv_for_at_K edg_equal_at_K: core.

   Hint Resolve negExy_inv_for_mk_irefl negExy_inv_for_mk_sym negExy_inv_for_at_K: core.
   
   Lemma only_at_inv_for_E_at_K1 (E: A-> A-> bool)(K: list A): (E at_ K) only_at K.
   Proof. unfold "only_at". eapply no_edg_E_at_K. Qed.
   Lemma only_at_inv_for_E_at_K (G: UG)(K: list A): ((edg G) at_ K) only_at K.
   Proof. simpl. apply only_at_inv_for_E_at_K1. Qed.


   (*------  E at_ K preserves the irreflexive and symmetric property of relation----------- *)
   Lemma irefl_inv_for_E_at_K (E: A-> A-> bool)(K: list A): irefl E -> irefl (E at_ K).
   Proof. unfold irefl. intros H x. unfold "at_". destruct (mem2 x x K) eqn:H1.
          auto. auto.  Qed.
   Lemma sym_inv_for_E_at_K(E: A-> A-> bool)(K: list A): sym E -> sym (E at_ K).
   Proof. { unfold sym. intros H x y. unfold "at_".
          destruct (mem2 x y K) eqn:H1. destruct (mem2 y x K) eqn: H2.
          auto. assert (H3: mem2 y x K = mem2 x y K).
          eauto.  rewrite H1 in H3; rewrite H2 in H3; discriminate H3.
          replace (mem2 y x K) with (mem2 x y K).
          rewrite H1;simpl; auto. eauto.  } Qed.

   (*--------- mk_irefl and mk_sym preserves the " E only_at K" property of relation-----------*)
   Lemma only_at_inv_for_mk_irefl(E:A-> A-> bool)(K:list A): E only_at K -> (mk_irefl E) only_at K.
   Proof. { unfold "only_at". intro H. intros x y. unfold mk_irefl. case (x == y).
          intros H2. inversion H2. intros H1. apply H;auto. } Qed.
   Lemma only_at_inv_for_mk_sym(E: A-> A-> bool)(K:list A): E only_at K -> (mk_sym E) only_at K.
   Proof. { unfold "only_at". intros H x y. unfold mk_sym. move /orP. intro H1.
            elim H1. auto.  intro H2. cut (In y K /\ In x K). tauto. auto. } Qed.

   (*-------compl inverts a relation at every point while preserving irreflexivity-------- *)

   Definition compl (E: A-> A-> bool)(x y:A):= match (x == y) with
                                                 | true => false
                                                 | false => negb (E x y)
                                          end.
   
 
  Lemma complP (E: A-> A-> bool)(x y:A): x<>y -> E x y -> (compl E x y = false).
  Proof. { intros H H1. unfold compl. case  (x == y) eqn:H2. auto.
         case (E x y) eqn:H3; simpl. auto. discriminate H1. } Qed. 
  Lemma complP1 (E: A-> A-> bool)(x y:A): x<>y -> compl E x y -> E x y =false.
  Proof. { unfold compl. case (x == y) eqn:H2. intros H1 H3; discriminate H3.
         intro H3. case (E x y); simpl. intro H; discriminate H. auto. } Qed.

  (*------- complementing a relation preserves irreflexive and symmetric properties--------*)
  Lemma irefl_inv_for_compl (E: A-> A-> bool ): irefl E -> irefl (compl E).
  Proof. { intros H x. unfold compl.  case (x == x) eqn:H1. auto.  
         absurd (x=x). intro; by_conflict. reflexivity. } Qed.

   Lemma sym_inv_for_compl (E: A-> A-> bool): sym E -> sym (compl E).
   Proof. {  intro H; unfold sym. intros.  specialize (H x y).
             unfold compl. replace (E x y) with (E y x).
            case (x == y) eqn:H1; case (y == x) eqn:H2.
            auto. move /eqP in H1. by_conflict. move /eqP in H2. by_conflict.  auto. } Qed.
  
   Hint Resolve mk_ireflP mk_symP complP complP1: core.
   Hint Resolve irefl_inv_for_mk_sym irefl_inv_for_compl irefl_inv_for_E_at_K: core.
   Hint Resolve sym_inv_for_mk_irefl sym_inv_for_compl sym_inv_for_E_at_K: core.
   Hint Resolve  only_at_inv_for_E_at_K only_at_inv_for_E_at_K1: core.
   Hint Resolve only_at_inv_for_mk_irefl only_at_inv_for_mk_sym: core.
   Hint Resolve edg_equal_at_K: core.


   (*------Concepts of Subgraph and the Induced Subgraph of a given  graph G ---------- *)
   Definition Subgraph (G1 G2: UG): Prop := G1 [<=] G2 /\ (forall x y, edg G1 x y-> edg G2 x y).
   Definition Ind_subgraph ( G1 G2: UG): Prop :=
     G1 [<=] G2 /\ (forall x y, In x G1-> In y G1-> edg G1 x y = edg G2 x y).

   Lemma Ind_subgraph_elim1 (G1 G2:UG) (x y:A):
     Ind_subgraph G1 G2 ->  In x G1 -> In y G1 -> edg G1 x y = edg G2 x y.
   Proof. intros H Hx Hy. destruct H as [H1 H2]. auto. Qed.
   
    Lemma Ind_subgraph_elim2 (G1 G2:UG) (x y:A):
     Ind_subgraph G1 G2 -> G1 [<=] G2.
    Proof. intros H. apply H. Qed.

    Hint Immediate Ind_subgraph_elim1 Ind_subgraph_elim2: core.
    Lemma Ind_subgraph_trans (G1 G2 G3: UG): Ind_subgraph G1 G2-> Ind_subgraph G2 G3->
                                             Ind_subgraph G1 G3.
    Proof. { unfold Ind_subgraph. intros H1 H2.
             destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b].
             split. auto. intros x y Hx Hy. replace (edg G3 x y) with (edg G2 x y).
             all: auto. } Qed.
    Lemma Subgraph_trans (G1 G2 G3: UG): Subgraph G1 G2 -> Subgraph G2 G3-> Subgraph G1 G3.
    Proof. unfold Subgraph. intros H1 H2.
           destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b]. split; auto. Qed.

    Hint Immediate Ind_subgraph_trans Subgraph_trans: core.

   Lemma Subgraph_iff (G1 G2: UG):
     Subgraph G1 G2 <->  G1 [<=] G2 /\ (forall x y, In x G1 -> In y G1-> edg G1 x y-> edg G2 x y).
   Proof. { split.
          { unfold Subgraph. intros H. split. apply H.
            intros x y H1 H2. destruct H as [H H0]. auto. }
          { unfold Subgraph. intros H. destruct H as [H H0].
            split. auto. intros x y H1. apply H0; eauto. } } Qed.
   
   Definition subgraph (G1 G2: UG):=
     (subset G1 G2) && ( forall_xyb (fun x y => negb (edg G1 x y) || (edg G2 x y)) G1 ).
   Lemma subgraphP (G1 G2: UG): reflect (Subgraph G1 G2) (subgraph G1 G2).
   Proof. { eapply iffP
            with (P:= (G1 [<=] G2 /\ (forall x y, In x G1 -> In y G1-> edg G1 x y-> edg G2 x y))).
          unfold subgraph. apply reflect_intro.
          split.
          { intro H. destruct H as [H H0]. split_. apply /subsetP;auto.
            apply /forall_xyP. intros. apply /impP. auto. }
          { move /andP. intro H. destruct H as [H H0].
            split. auto. move /forall_xyP in H0. intros x y H1 H2.
            auto. apply /impP. auto. }
          all: apply Subgraph_iff. } Qed.
   
   Definition ind_subgraph (G1 G2: UG):=
     (subset G1 G2) && ( forall_xyb (fun x y => edg G1 x y == edg G2 x y) G1).
   Lemma ind_subgraphP (G1 G2: UG): reflect (Ind_subgraph G1 G2) (ind_subgraph G1 G2).
   Proof. { unfold ind_subgraph. apply reflect_intro.
          split.
           { intro H. destruct H as [H H0]. split_. apply /subsetP;auto.
             apply /forall_xyP. intros; apply /eqP; auto.  }
            { move /andP. intro H. destruct H as [H H0].
              split. auto. move /forall_xyP in H0.
              intros x y H1 H2; apply /eqP; auto. } } Qed.
           
   Lemma self_is_induced (G: UG): Ind_subgraph G G.
   Proof. split; auto. Qed.
   
   Lemma induced_is_subgraph (G: UG): forall (G1: UG), Ind_subgraph G1 G -> Subgraph G1 G.
   Proof. { intros G1 H1. split. apply H1. destruct H1 as [H1 H2]. intros x y H3.
          replace (edg G x y) with (edg G1 x y). auto. 
          assert (H4: In x G1 /\ In y G1). eapply no_edg; auto. 
          apply H2; apply H4. } Qed.
   
   Hint Resolve subgraphP ind_subgraphP: core.
   Hint Resolve self_is_induced induced_is_subgraph: core.

    (*------------ Complement of a graph G and its edge relation--------------------- *)

  Lemma only_at_inv_for_compl1 (E:A-> A-> bool)(K:list A): ((compl E) at_ K) only_at K.
  Proof. { unfold "only_at". intros x y. unfold compl. unfold "at_".
         case (mem2 x y K) eqn: H.
         intro H1. cut (IN x y K). unfold IN;tauto. apply /mem2P; eauto.
         intro H1; discriminate H1. } Qed.
  Lemma only_at_inv_for_compl (G:UG): ((compl (edg G)) at_ G) only_at G.
  Proof. eapply only_at_inv_for_compl1. Qed.
  
  
  Hint Resolve only_at_inv_for_compl only_at_inv_for_compl1: core.

  Definition Compl (G: UG): UG.
    refine ({|nodes:= G.(nodes);
             nodes_IsOrd := G.(nodes_IsOrd);
             edg:= ((compl G.(edg)) at_ G); |}). all: auto. Defined.
  
End DecidableGraphs.


Hint Resolve nodes_IsOrd edg_irefl edg_sym: core.

 Hint Resolve no_edg2 no_edg1 no_self_edg no_self_edg1 : core.
 Hint Immediate edg_sym sym_edg: core.
 
 Hint Resolve IsOrd_S: core.

 Hint Resolve Exy_inv_for_mk_irefl1 Exy_inv_for_mk_sym Exy_inv_for_mk_sym1: core.
 Hint Immediate no_edg_E_at_K1 no_edg_E_at_K2: core.
 Hint Resolve Exy_inv_for_at_K edg_equal_at_K: core.

 Hint Resolve negExy_inv_for_mk_irefl negExy_inv_for_mk_sym negExy_inv_for_at_K: core.
  
 Hint Resolve mk_ireflP mk_symP complP complP1: core.
 Hint Resolve irefl_inv_for_mk_sym irefl_inv_for_compl irefl_inv_for_E_at_K: core.
 Hint Resolve sym_inv_for_mk_irefl sym_inv_for_compl sym_inv_for_E_at_K: core.
 Hint Resolve  only_at_inv_for_E_at_K only_at_inv_for_E_at_K1: core.
 Hint Resolve only_at_inv_for_mk_irefl only_at_inv_for_mk_sym: core.
 Hint Resolve edg_equal_at_K: core.

 Hint Immediate Ind_subgraph_elim1 Ind_subgraph_elim2: core.

 Hint Immediate Ind_subgraph_trans Subgraph_trans: core.
 

 Hint Resolve subgraphP ind_subgraphP: core.
 Hint Resolve self_is_induced induced_is_subgraph: core.

 Hint Resolve only_at_inv_for_compl only_at_inv_for_compl1: core.

Notation "E 'only_at' K":= (edg_only_at K E) (at level 70).
Notation "E 'at_' K":= (E_res_to K E)(at level 70).






