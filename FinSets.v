





From Coq Require Export ssreflect  ssrbool.
Require Export Lists.List Lists.ListSet.
Set Implicit Arguments.



Print Bool.reflect.

Section GeneralReflections.
Definition Prop_bool_eq (P: Prop) (b: bool):= P <-> b=true.
Check reflect. Print Bool.reflect.
(* Inductive reflect (P : Prop) : bool -> Set :=  
   ReflectT : P -> reflect P true | ReflectF : ~ P -> reflect P false *)
Lemma reflect_elim (P:Prop)(b: bool): reflect P b -> Prop_bool_eq P b.
Proof. { intro H.
       split. case H; [ auto | discriminate || contradiction ].
       case H; [ auto | discriminate || contradiction ]. } Qed. 
Lemma reflect_intro (P:Prop)(b:bool): Prop_bool_eq P b -> reflect P b.
Proof. { intros. destruct H as  [H1 H2]. destruct b; constructor;auto. } Qed.
Hint Immediate  reflect_elim reflect_intro : hint_reflect.

Lemma reflect_dec P: forall b:bool, reflect P b -> {P} + {~P}.
Proof. intros b H; destruct b; inversion H; auto.  Qed.
Lemma reflect_EM P: forall b:bool, reflect P b -> P \/ ~P.
Proof. intros b H. case H; tauto. Qed.
Lemma pbe_EM P: forall b:bool, Prop_bool_eq P b -> P \/ ~P.
Proof. { intros b H; cut( reflect P b).
         apply reflect_EM. apply reflect_intro;auto. } Qed.
Hint Immediate reflect_EM reflect_dec: hint_reflect.
About iffP.
(* iffP : forall (P Q : Prop) (b : bool), reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b *)
About idP.
(* idP : forall b1 : bool, reflect b1 b1 *)
Print NoDup.
(* Inductive NoDup (A : Type) : list A -> Prop := 
| NoDup_nil : NoDup nil 
| NoDup_cons : forall (x : A) (l : list A), ~ In x l -> NoDup l -> NoDup (x :: l) *)
End GeneralReflections.
Hint Immediate reflect_intro reflect_elim  reflect_EM reflect_dec : hint_reflect.


Ltac solve_dec := eapply reflect_dec; eauto with hint_reflect.
Ltac solve_EM  := eapply reflect_EM; eauto with hint_reflect.





Hint Resolve in_eq in_cons in_inv in_nil in_dec: hint_list.
Section BasicListFacts.
  Variable A:Type.
  Lemma in_inv1 : forall (a b:A) (l:list A), In b (a :: l) -> b = a \/ In b l.
  Proof. { intros  a b l H. cut (a=b \/ In b l).
       Focus 2. auto with hint_list. intros H1; destruct H1 as [H1 | H2].
       left; symmetry; auto. right;auto. } Qed.
  Hint Resolve in_inv1: hint_list.
  End BasicListFacts.
Hint Resolve in_inv1: hint_list.
Hint Resolve in_inv1: hint_set.
Hint Resolve in_eq in_cons in_inv in_nil in_dec: hint_set.




Section SetSpec.
  Variable A:Type.
  Definition Empty (s:list A):Prop := forall a : A, ~ In a s.
  Definition Equal (s s': list A) := forall a : A, In a s <-> In a s'.
  Definition Subset (s s': list A) := forall a : A, In a s -> In a s'.
  Print Forall.
  (* Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop := 
     | Forall_nil : Forall P nil 
     | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l)  *)
  Print Exists.
  (* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
      |Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l) 
      | Exists_cons_tl : forall (x : A) (l : list A), Exists P l -> Exists P (x :: l) *)
  Print NoDup.
  (* Inductive NoDup (A : Type) : list A -> Prop := 
      | NoDup_nil : NoDup nil 
      | NoDup_cons : forall (x : A) (l : list A), ~ In x l -> NoDup l -> NoDup (x :: l) *)
End SetSpec.


Ltac unfold_spec := try(unfold Equal);try(unfold Subset);try(unfold Empty).



Section BasicSetFacts.
  Variable A:Type.

  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "| s |":= (length s) (at level 70, no associativity).

  (* -----------------------Empty (spec) and its properties ------------------------*)
  Lemma empty_set_spec : Empty (empty_set A).
  Proof. unfold empty_set. unfold Empty.  auto with hint_list. Qed.

  (*-----------------------Subset (spec) and its properties ------------------------*)
  
  Lemma Subset_elim1 (a:A) (s s':list A): Subset (a:: s) s'-> In a s' /\ Subset s s'.
  Proof. { unfold Subset. intro H. split. apply H. auto with hint_list. intros a1 H1.
           apply H. auto with hint_list. } Qed.
  Lemma self_incl (l:list A): l [<=] l.
  Proof. Admitted.
  Hint Resolve self_incl: hint_set.

  
  (* ---------------------- Equal (spec) and their properties--------------------*)
  Lemma Eq_refl (s: list A):  s [=] s.
  Proof.  unfold Equal. tauto.  Qed. 
  Lemma Eq_sym (s s':list A): s [=] s' -> s' [=] s.
  Proof. unfold Equal. unfold iff. intros H a. specialize (H a). tauto. Qed. 
  Lemma Eq_trans ( x y z : list A) : x [=] y -> y [=] z -> x [=] z.
  Proof. { unfold Equal. unfold iff. intros H H1 a.
         specialize (H1 a). specialize (H a). tauto. } Qed. 
  Lemma Equal_intro (s s': list A): s [<=] s' -> s' [<=] s -> s [=] s'.
  Proof. unfold_spec. intros H H1 a; unfold iff. auto. Qed. 
  Lemma Equal_elim ( s s': list A): s [=] s' ->  s [<=] s' /\ s' [<=] s.
  Proof. unfold_spec; unfold iff. intros H; split; intro a;apply H. Qed. 
End BasicSetFacts.

Hint Immediate Eq_refl Eq_sym Equal_elim Equal_intro : hint_set.
Hint Immediate Subset_elim1 : hint_set.
Hint Resolve self_incl Eq_trans: hint_set. 



Section SetReflections.
Variable A:Type.
Hypothesis decA: forall x y:A, {x=y}+{x<>y}.

(*--------- set_mem (boolean function)  and its specification ---------*)
Print set_mem.
(* fix set_mem (a : A) (x : set A) {struct x} : bool :=
  match x with
  | nil => false
  | a1 :: x1 => if Aeq_dec a a1 then true else set_mem a x1
  end *)
Print In.
(* fix In (a : A) (l : list A) {struct l} : Prop :=
  match l with
  | nil => False
  | b :: m => b = a \/ In a m
  end
*)
Lemma memP a x: reflect (set_In a x) (set_mem decA a x).  
Proof. { destruct (set_mem decA a x)  eqn: H.
         constructor; apply (set_mem_correct1 decA); auto. 
         constructor; apply (set_mem_complete1 decA); auto. } Qed.
Hint Resolve memP : hint_reflect.

Lemma In_EM: forall (a:A) (x: set A), set_In a x \/ ~ set_In a x.
Proof. eauto with hint_reflect. Qed.
Check set_In_dec. (* forall (a : A) (x : set A), {set_In a x} + {~ set_In a x} *)
Check in_dec.
(* in_dec
     : forall A : Type, (forall x y : A, {x = y} + {x <> y}) ->
        forall (a : A) (l : list A), {In a l} + {~ In a l} *)

(*
End SetReflections.
Lemma decN: forall x y:nat, {x=y}+{x<>y}.
   Proof. intros. decide equality. Defined.
  Lemma TrivialN1: set_In   2 (1::3::4::2::nil).
  Proof.  apply /memP. Unshelve. intros. apply decN.  simpl; auto. Qed.
 *)

Definition IN := fun (x:A)(y:A)(l:list A) => In x l /\ In y l.
Definition set_mem2 x y l := set_mem decA x l && set_mem decA y l.

Lemma mem2P a b x : reflect (IN a b x) (set_mem2 a b x).
Proof. Admitted.

Hint Resolve mem2P: hint_reflect.
Lemma IN_EM: forall (a b:A)(x:set A), IN a b x \/ ~ IN a b x.
Proof.  eauto with hint_reflect. Qed.

(*---------- noDup  (boolean function) and its specification ---------*)

Print NoDup.
(* Inductive NoDup (A : Type) : list A -> Prop :=
    NoDup_nil : NoDup nil
  | NoDup_cons : forall (x : A) (l : list A), ~ In x l -> NoDup l -> NoDup (x :: l) *)
Fixpoint noDup (x: list A): bool:=
  match x with
    |nil => true
    |h :: x1 => if set_mem decA h x1 then false else noDup x1
  end.
Lemma NoDup_iff_noDup l: NoDup l <-> noDup l. 
Proof. { split. 
       { induction l.  auto.
       intro H; inversion H;  simpl.
       replace (set_mem decA a l) with false; auto.
       symmetry. apply /memP. auto. } 
       { induction l. constructor.
       simpl. case (set_mem decA a l) eqn: H1. discriminate.  intro H2.
       constructor. move /memP.  rewrite H1.  auto. tauto. }  } Qed. 
Lemma nodupP l: reflect (NoDup l) (noDup l).
Proof. {cut (NoDup l <-> noDup l). eauto with hint_reflect. apply NoDup_iff_noDup. } Qed. 

Hint Resolve nodupP : hint_reflect.

Lemma NoDup_EM: forall l:list A, NoDup l \/ ~ NoDup l.
Proof. eauto with hint_reflect. Qed.
Lemma NoDup_dec: forall l:list A, {NoDup l} + { ~ NoDup l}.
Proof. eauto with hint_reflect. Qed. 
Lemma nodup_spec: forall l:list A, NoDup (nodup decA l).
Proof. intros. eapply NoDup_nodup. Qed.
Lemma nodup_spec1:  forall l:list A, noDup (nodup decA l).
Proof. { intros.  apply /nodupP. apply nodup_spec. } Qed.

(*---------- is_empty (boolean function) and its specification -----------------*)
Definition is_empty (x:list A) : bool := match x with
                                 | nil => true
                                 | _ => false
                                 end.

Lemma emptyP l : reflect (Empty l) (is_empty l).
Proof. { destruct l eqn:H. simpl.  constructor. unfold Empty. auto.
       simpl. constructor. unfold Empty.  intro H1. specialize (H1 a).
       apply H1. auto with hint_list. } Qed. 
Hint Resolve emptyP : hint_reflect.
Lemma Empty_EM (l:list A): Empty l \/ ~ Empty l.
  Proof. solve_EM. Qed.  
Lemma Empty_dec (l: list A): {Empty l} + {~Empty l}.
  Proof. solve_dec. Qed.  

Lemma empty_set_spec1: is_empty (empty_set A).
  Proof. { assert (H: Empty (empty_set A)). apply empty_set_spec.
         apply /emptyP. auto. } Qed. 

(*----------- subset (boolean function) and its specification--------------------*)
Fixpoint set_subset (s s': list A): bool:=
  match s with
  |nil => true
  | a1 :: s1=> set_mem decA a1 s' && set_subset s1 s'
  end.
Print Subset.
(* Subset = 
fun (A : Type) (s s' : list A) => forall a : A, In a s -> In a s' *)

Lemma subsetP s s': reflect (Subset s s') (set_subset s s').
Proof. { induction s. simpl. constructor. intro. intros  H. absurd (In a nil); auto.
       apply reflect_intro. split.
       { intro H. cut (In a s' /\ Subset s s'). Focus 2. auto with hint_set. simpl.
         intro H1; destruct H1 as [H1 H2].
         apply /andP. split. apply /memP;auto. apply /IHs;auto.  }
       { simpl.  move /andP. intro H; destruct H as [H1 H2]. unfold Subset.
         intros a0 H3. cut (a0= a \/ In a0 s). intro H4; destruct H4 as [H4 | H5].
         rewrite H4. apply /memP;auto. cut (Subset s s'). intro H6. auto. apply /IHs;auto.
         eauto with hint_set.   }  } Qed.

Hint Resolve subsetP: hint_reflect.
Lemma Subset_EM (s s': list A): Subset s s' \/ ~ Subset s s'.
Proof. solve_EM. Qed.
Lemma Subset_dec (s s': list A): {Subset s s'} + {~ Subset s s'}.
Proof. solve_dec. Qed.
(*----------- equal (boolean function) and its specifications--------------------*)
Definition set_equal (s s':list A): bool:= set_subset s s' && set_subset s' s.
Lemma equalP s s': reflect (Equal s s') (set_equal s s').
Proof. { apply reflect_intro.  split.
       { intro H. cut (Subset s s'/\ Subset s' s).
       Focus 2. auto with hint_set. intro H1. unfold set_equal.
       apply /andP. split; apply /subsetP; tauto. }
       { unfold set_equal. move /andP. intro H. apply Equal_intro; apply /subsetP; tauto. }
       } Qed. 
Hint Resolve equalP: hint_reflect.
Lemma Equal_EM (s s': list A): Equal s s' \/ ~ Equal s s'.
Proof. solve_EM. Qed.
Lemma Equal_dec (s s': list A): {Equal s s'} + {~ Equal s s'}.
Proof. solve_dec. Qed.


(*----------- existsb (boolean function) and its specifications-------------------*)

  Print existsb.
  (* fix existsb (l : list A) : bool :=
  match l with
  | nil => false
  | a :: l0 => f a || existsb l0
  end *)
  Print Exists.
(* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
    Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l)
  | Exists_cons_tl : forall (x : A) (l : list A), Exists P l -> Exists P (x :: l) *)
  Lemma existsP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (Exists P l) (existsb f l).
  Proof.  { intro H. eapply reflect_intro.
         induction l. simpl. constructor; intro H1; inversion H1.
         split.
         { intro H1.  inversion H1. simpl. apply /orP; left; apply /H;auto.
           simpl. apply /orP; right; apply /IHl; auto. }
         { simpl. move /orP. intro H1; destruct H1 as [H1| H2]. constructor. apply /H; auto.
           eapply Exists_cons_tl. apply /IHl; auto.  } } Qed.
  Hint Resolve existsP: hint_reflect.
  Lemma Exists_EM P f l:(forall x:A, reflect (P x) (f x) )-> Exists P l \/ ~ Exists P l.
  Proof. intros; solve_EM. Qed.
  
  Lemma Exists_dec P f l: (forall x:A, reflect (P x) (f x) )-> {Exists P l} + {~ Exists P l}.
  Proof.  intros;solve_dec. Qed.
    
(*----------- forallb ( boolean function) and its specifications----------------- *)
 Print forallb.
 (* fix forallb (l : list A) : bool :=
    match l with
     | nil => true
     | a :: l0 => f a && forallb l0
    end *)
 Print Forall.
 (* Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l) *)

 Lemma forallP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (Forall P l) (forallb f l).
 Proof.   { intro H. eapply reflect_intro.
         induction l. simpl. constructor; intro H1; inversion H1; auto.
         split.
         { intro H1.  inversion H1. simpl. apply /andP. split.  apply /H;auto.
           apply /IHl; auto. }
         { simpl. move /andP. intro H1; destruct H1 as [H1 H2]. constructor. apply /H; auto.
           apply /IHl; auto. } } Qed.

 Hint Resolve forallP: hint_reflect.
 Lemma forall_EM P f l:(forall x:A, reflect (P x) (f x) )-> Forall P l \/ ~ Forall P l.
 Proof. intros; solve_EM. Qed.
 Lemma forall_dec P f l: (forall x:A, reflect (P x) (f x) )-> {Forall P l} + {~ Forall P l}.
 Proof. intros; solve_dec. Qed.

End SetReflections.

Hint Resolve memP nodupP emptyP subsetP equalP existsP forallP : hint_reflect.



Hint Immediate set_add_nodup set_remove_nodup: hint_nodup.
Hint Resolve set_union_nodup set_inter_nodup set_diff_nodup: hint_nodup.
Section Dup_free_sets.
  Variable A:Type.
  Hypothesis decA: forall x y: A, {x=y}+{x<>y}. 
  Record fset : Type := { set_of :> list A;
                          fset_dupP : noDup decA set_of }.
  Definition no_dup := noDup decA.
  Definition empty:= empty_set A.
  Definition add := set_add decA.  
  Definition mem := set_mem decA.
  Definition remove:= set_remove decA.
  Definition inter := set_inter decA.
  Definition union := set_union decA.
  Definition diff:= set_diff decA.

  Ltac unfold_all := try(unfold no_dup); try(unfold empty);try(unfold add); try(unfold mem);try(unfold remove);try(unfold inter); try(unfold union); try(unfold diff).
  
  Lemma nodup_empty: no_dup empty.
  Proof. simpl; auto. Qed.
  Canonical empty_fset := @Build_fset ( empty ) (nodup_empty).
  Lemma nodup_add a (l:list A): noDup decA l -> noDup decA (add  a l).
  Proof. move /nodupP; intro H; apply /nodupP;  unfold_all; eauto with hint_nodup. Qed.
  Canonical addF a (l:fset) := (@Build_fset (add a l) (nodup_add a l (fset_dupP l))).
End Dup_free_sets.
Check no_dup.

Section Set_maps.
  Variable A B:Type.
  Hypothesis decA:  forall x y: A, {x=y}+{x<>y}.
  Hypothesis decB:  forall x y: B, {x=y}+{x<>y}.
  Print set_map.
  Fixpoint s_map (f:A->B) (l:list A): list B:= match l with
                                        | nil => nil
                                        | a1::l1 => set_add decB (f a1) (s_map f l1)
                                              end.
  
  Lemma s_map_nodup (f:A->B) (l:list A): NoDup l -> NoDup (s_map f l).
  Proof. Admitted.
  Lemma funP (f: A->B)(x y: A): f x <> f y -> x <> y.
  Proof. intros H H1. apply H;rewrite H1; auto. Qed.
  Check map. Print map.
  Definition one_one (f: A->B): Prop:= forall x y, x <> y -> f x <> f y.
  Lemma one_oneP1 (f:A->B): one_one f -> forall x y, f x = f y -> x =y.
  Proof. Admitted.
  Definition one_one_on (l: list A) (f: A-> B):Prop:= forall x y, IN x y l ->  x<>y -> f x <> f y.
  Lemma one_one_onP1: forall (l:list A) (f: A-> B) (x y: A), one_one_on l f -> f x = f y -> x = y. 
  Proof. Admitted.
  Definition one_one_onb (l: list A) (f: A->B):bool:= noDup decB (map f l).  
  Lemma one_oneP (l:list A) (f: A->B): NoDup l ->  reflect (one_one_on l f)(one_one_onb l f).
  Proof. Admitted.
End Set_maps.

Section DecidableGraphs.

  Variable A: Type.
  Hypothesis decA: forall x y:A, {x=y}+{x<>y}.


 (* ---------- Finite sets as duplicate free lists -------------------------------- *
     Record fset : Type := { set_of :> list A;
                          fset_dupP : noDup decA set_of }.                          *)
  
  (* ---------- Graph := finite undirected simple graph ----------------------------*)
  Record Graph:Type:= { nodes :> list A;
                        nodes_dupP : noDup decA nodes;
                        edg: A-> A -> bool;
                        edg_sym: forall x y, edg x y = edg y x;
                        edg_not_refl: forall x, edg x x =false }.
  (*-- Following declaration expresses that nodes of Graph are duplicate free sets --*)
  Canonical nodes_of (G:Graph):= (@Build_fset _  decA G.(nodes) (nodes_dupP G)).

  Check nodes_of.
  Definition V := fun (G:Graph) => nodes_of G.
  
  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "| s |":= (length s) (at level 70, no associativity).


  (*----- Concepts of Cliq and the Cliq number for a given graph G ----------------------*)

   Definition Is_cliq (G:Graph): Prop := forall x y, IN x y G -> edg G x y.
   Definition Is_cliq_in (G:Graph)(K: list A):Prop := K [<=] G /\ (forall x y, IN x y K -> edg G x y).
   Definition Largest_K_in (G: Graph)(K:list A): Prop:=
     Is_cliq_in G K /\ (forall K', Is_cliq_in G K'-> |K'| <= |K|).   
   Definition cliq_num (G:Graph)(n:nat):= exists K, Largest_K_in G K /\ |K|=n.

   Notation " K 'cliq_in' G":= (Is_cliq_in G K) (at level 70).
   Notation "K 'largest_cliq_in' G " := (Largest_K_in G K) (at level 70). 
   Notation " n 'equal_omega' G ":= (cliq_num G n) (at level 70).  

   (*Variable G: Graph. Variable K: list A.
   Check (K is_cliq_in G ). *)

  (*------Concepts of Subgraph and the Induced Subgraph of a given  graph G ---------- *)
   Definition Is_subgraph (G1 G2: Graph): Prop := G1 [<=] G2 /\ (forall x y, edg G1 x y-> edg G2 x y).
   Definition Is_ind_subgraph ( G1 G2: Graph): Prop := G1 [<=] G2 /\ edg G1 = edg G2.
   Definition Ind_at (K:fset decA)(G:Graph): Graph:=
     {|nodes:= K; nodes_dupP := K.(fset_dupP);
       edg:= G.(edg); edg_sym:= G.(edg_sym); edg_not_refl:= G.(edg_not_refl) |}.

   
    Notation "G 'res_to' K":= (Ind_at K G) (at level 70).
    Notation " G1 'ind_in' G2 ":= (Is_ind_subgraph G1 G2) (at level 70).
    Notation " G1 'sub_in' G2 ":= (Is_subgraph G1 G2) (at level 70).


   Lemma cliq_fact1: forall (K:fset decA)(G:Graph),  K cliq_in G  -> Is_cliq ( G res_to K).
   Proof. intros K G H. destruct H. intros x y H1.  apply H0. assumption. Qed.
   
   Lemma induced_fact1: forall (K:fset decA) (G:Graph),  K[<=]G -> (G res_to K) sub_in G.
   Proof. intros K G H. split. assumption. simpl. tauto.  Qed.

   Lemma self_is_induced (G: Graph): Is_ind_subgraph G G.
   Proof. split;  auto with hint_set. Qed.
   Hint Resolve self_is_induced : hint_graph.
   Lemma induced_is_subgraph (G: Graph): forall (G1: Graph), Is_ind_subgraph G1 G -> Is_subgraph G1 G.
   Proof. intros G1 H1. split. apply H1. destruct H1 as [H1 H2]; rewrite H2; tauto. Qed.
   Hint Resolve induced_is_subgraph: hint_graph.

   (*------ Concepts of Coloring and the chromatic number of a graph G ------------------*)
   Definition Is_coloring_of (G: Graph)(f: A-> nat): Prop:= forall x y, IN x y G -> edg G x y -> f x <> f y.

   Lemma decN: forall (m n:nat), {m=n}+{m<>n}.
   Proof. Admitted.
   
   Definition all_clrs (f:A->nat) (l:list A):= (s_map decN f l).
   Definition Best_coloring_of (G: Graph) (f:A->nat): Prop :=
     Is_coloring_of G f /\ (forall f1, Is_coloring_of G f1 -> | all_clrs f G | <= | all_clrs f1 G|).
   Definition chrom_num (G: Graph) (n: nat):= exists f, Best_coloring_of G f /\ | all_clrs f G | = n.

   Notation " n 'equal_chi' G":= (chrom_num G n)(at level 70).

   (*-------- Some trivial facts on cliq_number and chrom_number--------------------------*)

   (*-------- Concepts of nice graph and  perfect graphs -------------------------------- *)
   Definition Is_nice (G: Graph): Prop:= forall n, cliq_num G n -> chrom_num G n.
   Definition Is_perfect (G: Graph): Prop:= forall G1, Is_ind_subgraph G1 G -> Is_nice G1.
      
   Lemma perfect_is_nice (G: Graph): Is_perfect G -> Is_nice G.
   Proof.  unfold Is_perfect. intros H; apply H. auto with hint_graph. Qed.
   Hint Resolve perfect_is_nice: hint_graph.
   

   

   

  

   
  

  

  

  End DecidableGraphs.