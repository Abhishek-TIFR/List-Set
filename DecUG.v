 

(* ------------------ Descriptions--------------------------------------------------

 This file implements the notion of decidable finite  graphs representaed as dG
 
  Record dG:Type:= { nodes :> list A;
                        nodes_isOrd : isOrd nodes;
                        edg: A-> A -> bool;
                        edge_irefl: irefl_in nodes edg;
                        edge_sym: sym_in nodes edg
                   }.

 In order to be lazy while declaring an instance for dG we provide functions such as
 mk_irefl, mk_sym and E_res_to  which can be used to convert any graph into
 the exact specifications of an undirected graph (dG). 
 Moreover, we prove that these functions work well when used together. They do not 
 disturb the properties established by each other. 

 We also define the concept of Subgraph, Ind_Subgraph and Complement of a Graph.
 
 Predicate              Boolean function       Joining Lemma
 Subgraph G1 G2         subgraph G1 G2         subgraphP
 Ind_Subgraph G1 G2     ind_subgraph G1 G2     ind_subgraphP
  

 Definition Compl (G: dG): UG.
    refine ({|nodes:= G.(nodes);
             nodes_IsOrd := G.(nodes_IsOrd);
             edg:= (compl G.(edg)); |}). all: auto. Defined.

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
  
  Definition refl_in (l: list A) (E: A -> A-> bool):= forallb (fun x => (E x x)) l.
  Definition irefl_in (l: list A)(E: A -> A-> bool):= forallb (fun x => negb (E x x)) l.
  Definition sym_in (l: list A) (E: A -> A-> bool):= forall_xyb (fun x y => (E x y == E y x)) l.

  Lemma irefl_in_sub (l s: list A)(E: A-> A-> bool): l [<=] s -> irefl_in s E -> irefl_in l E.
  Proof. unfold irefl_in. intros h1 h2. apply /forallbP. move /forallbP in h2. auto. Qed.
  Lemma sym_in_sub (l s: list A)(E: A->A-> bool): l [<=] s -> sym_in s E -> sym_in l E.
  Proof.  unfold sym_in. intros h1 h2. apply /forall_xyP. move /forall_xyP in h2. auto. Qed.

  Lemma irefl_imp_irefl_in (l: list A)(E: A-> A-> bool): irefl E -> irefl_in l E.
  Proof.  unfold irefl_in. unfold irefl.
          intro H. apply /forallbP. intros. apply /negP. switch. auto. Qed.
  
  Lemma sym_imp_sym_in (l: list A)(E: A-> A-> bool): sym E -> sym_in l E.
  Proof. unfold sym_in. unfold sym. intro H. apply /forall_xyP. intros;auto. Qed.

  Hint Resolve irefl_imp_irefl_in sym_imp_sym_in: core.

  Hint Resolve irefl_in_sub sym_in_sub: core.
  

  (* ---------- dG := finite undirected simple graph ----------------------------*)
  Record dG:Type:= { nodes :> list A;
                        nodes_isOrd : isOrd nodes;
                        edg: A-> A -> bool;
                        edge_irefl: irefl_in nodes edg;
                        edge_sym: sym_in nodes edg
                   }.

  
  Lemma nodes_IsOrd (G: dG): IsOrd (nodes G).
  Proof. apply /isOrdP; apply nodes_isOrd. Qed.

  Lemma edg_irefl (G: dG)(x:A): In x G -> edg G x x = false.
  Proof. { destruct G as [N P1 E P2 P3]. simpl. unfold irefl_in in P2.
           move /forallbP in P2. intro h1. apply P2 in h1 as h2.
           destruct (E x x); simpl in h2; auto. } Qed.

  Lemma edg_irefl_in (G: dG): irefl_in G (edg G).
  Proof.   apply edge_irefl.  Qed.
  

  Lemma edg_sym (G: dG)(x y: A): In x G -> In y G -> edg G x y = edg G y x.
  Proof. { destruct G as [N P1 E P2 P3]. simpl. unfold sym_in in P3.
           move /forall_xyP in P3. intros. apply /eqP. auto. } Qed.

  Lemma edg_sym_in (G: dG): sym_in G (edg G).
  Proof. apply edge_sym. Qed.
  
  
  
  Hint Resolve nodes_IsOrd edg_irefl edg_sym: core.
  Hint Resolve IsOrd_S: core.

  Hint Resolve edg_irefl_in edg_sym_in: core.

 (*------------------------ Essentially Equal Graphs are Isomorphic --------------------*)
  
  
  Definition EqualG (G1 G2: dG):= (nodes G1) = (nodes G2) /\
                                 (forall x y, In x G1 -> In y G1-> edg G1 x y = edg G2 x y).

  
  (*------ Following declaration expresses that nodes of Graph are ordered sets -----------*)

  (* Record set_on : Type := { S_of :> list A;
                             IsOrd_S : IsOrd S_of }.*)

  Canonical nodes_of (G:dG):= (@Build_set_on  A G.(nodes) (nodes_IsOrd G)).

  Definition V := fun (G:dG) => nodes_of G.

 (* Lemma no_edg1 (G: UG)(x y:A): (edg G) x y -> In x G.
  Proof. apply no_edg. Qed.

  Lemma no_edg2 (G: UG)(x y:A): (edg G) x y -> In y G.
  Proof. apply no_edg. Qed. *)
  
  
  Lemma no_self_edg (G: dG)(x y:A): In x G -> In y G -> edg G x y -> x <>y. 
  Proof. intros H0 H1 H Hxy.
         subst x; absurd (edg G y y); [ switch;apply edg_irefl;auto | auto]. Qed.
  Lemma no_self_edg1 (G: dG)(x:A): In x G ->  ~ edg G x x.
  Proof. intros H0 H. absurd (edg G x x); [ switch;apply edg_irefl;auto | auto]. Qed.
  Lemma sym_edg (G: dG)(x y:A): In x G -> In y G-> edg G x y -> edg G y x.
    Proof. intros H0 H1. rewrite edg_sym; auto.  Qed.

    Hint Resolve  no_self_edg no_self_edg1 : core.
    Hint Immediate edg_sym sym_edg: core.


 (*----------Well founded induction on the size of a graph---------------------------------*)

Definition lt_graph (g1 g2: dG):= |g1| < |g2|.

Lemma lt_graph_is_well_founded: well_founded lt_graph.
Proof. { unfold well_founded. intro a.
       remember (|a|) as n. revert Heqn. revert a.
       induction n using strong_induction.
       { intros a H1. apply Acc_intro.
         intros a0 H2. apply H with (k:= |a0|).
         subst n; apply H2. auto. } } Qed.

Hint Resolve lt_graph_is_well_founded: core.
  
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

  Lemma irefl_in_inv_for_mk_sym (E: A-> A-> bool)(l:list A): irefl_in l E -> irefl_in l (mk_sym E).
  Proof. { unfold irefl_in. intro H. unfold mk_sym. move /forallbP in H.
           apply /forallbP. intros x h1.  specialize (H x h1).
           destruct (E x x);simpl; simpl in H;auto.   } Qed.
  
  Lemma sym_inv_for_mk_irefl (E: A->A-> bool): sym E -> sym (mk_irefl E).
  Proof. { unfold sym. intros H x y. unfold mk_irefl.
           destruct (x== y) eqn:H1;destruct (y == x) eqn:H2. auto.
           move /eqP in H1; subst x; by_conflict.
           move /eqP in H2; subst x; by_conflict. auto.  } Qed.

   Lemma sym_in_inv_for_mk_irefl (E: A->A-> bool)(l: list A): sym_in l E -> sym_in l (mk_irefl E).
   Proof. { unfold sym_in. intros H. apply /forall_xyP. move /forall_xyP in H.
            unfold mk_irefl. intros x y h1 h2.
            destruct (x== y) eqn:H1;destruct (y == x) eqn:H2. auto.
            move /eqP in H1; subst x; by_conflict.
            move /eqP in H2; subst x; by_conflict. auto.  } Qed.
  


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

   Lemma irefl_in_inv_for_compl (E: A-> A-> bool )(l: list A): irefl_in l E -> irefl_in l (compl E).
   Proof. { intro H. unfold compl. apply /forallbP. intros x h1.
            replace (x==x) with true. simpl. all: auto. } Qed.

   Lemma sym_inv_for_compl (E: A-> A-> bool): sym E -> sym (compl E).
   Proof. {  intro H; unfold sym. intros.  specialize (H x y).
             unfold compl. replace (E x y) with (E y x).
            case (x == y) eqn:H1; case (y == x) eqn:H2.
            auto. move /eqP in H1. by_conflict. move /eqP in H2. by_conflict.  auto. } Qed.
    Lemma sym_in_inv_for_compl (E: A-> A-> bool)(l: list A): sym_in l E -> sym_in l (compl E).
    Proof. {  unfold sym_in; intro H. apply /forall_xyP. move /forall_xyP in H.
              intros x y h1 h2.  specialize (H x y h1 h2).
              unfold compl. replace (E x y) with (E y x).
              case (x == y) eqn:H1; case (y == x) eqn:H2.
              auto. move /eqP in H1. by_conflict. move /eqP in H2.
              by_conflict. auto. symmetry; auto. } Qed.
  
   Hint Resolve mk_ireflP mk_symP complP complP1: core.

   Hint Resolve irefl_inv_for_mk_sym irefl_inv_for_compl: core.
   Hint Resolve irefl_in_inv_for_mk_sym irefl_in_inv_for_compl: core.
   
   Hint Resolve sym_inv_for_mk_irefl sym_inv_for_compl : core.
   Hint Resolve sym_in_inv_for_mk_irefl sym_in_inv_for_compl: core.



   (*------Concepts of Subgraph and the Induced Subgraph of a given  graph G ---------- *)
   
   Definition Subgraph (G1 G2: dG): Prop := G1 [<=] G2 /\
                                         (forall x y, In x G1-> In y G1-> edg G1 x y-> edg G2 x y).
   Definition Ind_subgraph ( G1 G2: dG): Prop :=
     G1 [<=] G2 /\ (forall x y, In x G1-> In y G1-> edg G1 x y = edg G2 x y).

   Lemma Ind_subgraph_elim1 (G1 G2:dG) (x y:A):
     Ind_subgraph G1 G2 ->  In x G1 -> In y G1 -> edg G1 x y = edg G2 x y.
   Proof. intros H Hx Hy. destruct H as [H1 H2]. auto. Qed.
   
    Lemma Ind_subgraph_elim2 (G1 G2:dG) (x y:A):  Ind_subgraph G1 G2 -> G1 [<=] G2.
    Proof. intros H. apply H. Qed.

    Hint Immediate Ind_subgraph_elim1 Ind_subgraph_elim2: core.
    
    Lemma Ind_subgraph_trans (G1 G2 G3: dG): Ind_subgraph G1 G2-> Ind_subgraph G2 G3->
                                             Ind_subgraph G1 G3.
    Proof. { unfold Ind_subgraph. intros H1 H2.
             destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b].
             split. auto. intros x y Hx Hy. replace (edg G3 x y) with (edg G2 x y).
             all: auto. } Qed.
    
    Lemma Subgraph_trans (G1 G2 G3: dG): Subgraph G1 G2 -> Subgraph G2 G3-> Subgraph G1 G3.
    Proof. unfold Subgraph. intros H1 H2.
           destruct H1 as [H1a H1b]; destruct H2 as [H2a H2b]. split; auto. Qed.

    Hint Immediate Ind_subgraph_trans Subgraph_trans: core.

   Lemma Subgraph_iff (G1 G2: dG):
     Subgraph G1 G2 <->  G1 [<=] G2 /\ (forall x y, In x G1 -> In y G1-> edg G1 x y-> edg G2 x y).
   Proof. { split; unfold Subgraph; auto.  } Qed.
   
   Definition subgraph (G1 G2: dG):=
     (subset G1 G2) && ( forall_xyb (fun x y => negb (edg G1 x y) || (edg G2 x y)) G1 ).
   Lemma subgraphP (G1 G2: dG): reflect (Subgraph G1 G2) (subgraph G1 G2).
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
   
   Definition ind_subgraph (G1 G2: dG):=
     (subset G1 G2) && ( forall_xyb (fun x y => edg G1 x y == edg G2 x y) G1).
   Lemma ind_subgraphP (G1 G2: dG): reflect (Ind_subgraph G1 G2) (ind_subgraph G1 G2).
   Proof. { unfold ind_subgraph. apply reflect_intro.
          split.
           { intro H. destruct H as [H H0]. split_. apply /subsetP;auto.
             apply /forall_xyP. intros; apply /eqP; auto.  }
            { move /andP. intro H. destruct H as [H H0].
              split. auto. move /forall_xyP in H0.
              intros x y H1 H2; apply /eqP; auto. } } Qed.
           
   Lemma self_is_induced (G: dG): Ind_subgraph G G.
   Proof. split; auto. Qed.
   
   Lemma induced_is_subgraph (G: dG): forall (G1: dG), Ind_subgraph G1 G -> Subgraph G1 G.
   Proof. { intros G1 H1. split. apply H1. destruct H1 as [H1 H2]. intros x y h1 h2.
          replace (edg G x y) with (edg G1 x y). auto. auto. } Qed.
   
   Hint Resolve subgraphP ind_subgraphP: core.
   Hint Resolve self_is_induced induced_is_subgraph: core.

    (*------------ Complement of a graph G and its edge relation--------------------- *)

  Definition Compl (G: dG): dG.
    refine ({|nodes:= G.(nodes);
             nodes_isOrd := G.(nodes_isOrd);
             edg:= ((compl G.(edg))); |}). all: auto. Defined.

  (* Definition Ind_at (K: list A)(Pk: IsOrd K)(G: UG): UG.
     refine {|nodes:= K; nodes_IsOrd := Pk;
              edg:= (G.(edg) at_ K); |}. all: auto. Defined. *)

   Definition Ind_at (K: list A)(G: dG): dG.
     refine {|nodes:= (inter K G); edg:= G.(edg); |}. apply /isOrdP. all: eauto. Defined.  

   Lemma induced_fact1: forall (K:list A) (G: dG),
        K[<=]G -> Ind_subgraph (Ind_at K G) G.
   Proof. { intros K G H. split. simpl. auto. simpl;intros;symmetry;auto. }  Qed.

   (*------------ description of the following lemma while explainig Ind_at ----------- *)

   Lemma induced_fact2 (K:list A) (G: dG)(x y:A): edg G x y = edg (Ind_at K G) x y.
   Proof.  simpl. auto. Qed.


   Hint Immediate induced_fact1 induced_fact2: core.
  
End DecidableGraphs.

Hint Resolve irefl_imp_irefl_in sym_imp_sym_in: core.
Hint Resolve irefl_in_sub sym_in_sub: core.

Hint Resolve nodes_IsOrd edg_irefl edg_sym: core.
Hint Resolve edg_irefl_in edg_sym_in: core.

 Hint Resolve no_self_edg no_self_edg1 : core.
 Hint Immediate edg_sym sym_edg: core.

 Hint Resolve lt_graph_is_well_founded: core.
 
 Hint Resolve IsOrd_S: core.

 Hint Resolve Exy_inv_for_mk_irefl1 Exy_inv_for_mk_sym Exy_inv_for_mk_sym1: core.


 Hint Resolve negExy_inv_for_mk_irefl negExy_inv_for_mk_sym : core.
  
 Hint Resolve mk_ireflP mk_symP complP complP1: core.
 
 Hint Resolve irefl_inv_for_mk_sym irefl_inv_for_compl : core.
 Hint Resolve irefl_in_inv_for_mk_sym irefl_in_inv_for_compl: core.
 
 Hint Resolve sym_inv_for_mk_irefl sym_inv_for_compl : core.
 Hint Resolve sym_in_inv_for_mk_irefl sym_in_inv_for_compl: core.
 

 Hint Immediate Ind_subgraph_elim1 Ind_subgraph_elim2: core.

 Hint Immediate Ind_subgraph_trans Subgraph_trans: core.
 

 Hint Resolve subgraphP ind_subgraphP: core.
 Hint Resolve self_is_induced induced_is_subgraph: core.


 Hint Immediate induced_fact1 induced_fact2: core.
 






