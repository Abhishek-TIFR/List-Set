



(* -----------------Description --------------------------------------------------
   
   This file summarises some useful results from List Module of standard Library. 
   We create a hint database to remember important results regarding lists (hint_list).

   Some new definitions:
   Definition Empty (s:list A):Prop := forall a : A, ~ In a s.
   Definition Equal (s s': list A) := forall a : A, In a s <-> In a s'.
   Definition Subset (s s': list A) := forall a : A, In a s -> In a s'.

   Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
   Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
   Notation "| s |":= (length s) (at level 70, no associativity).

  --------------------   ------------------  ------------------------------------- *)



From Coq Require Export ssreflect  ssrbool.
Require Export Lists.List.

Set Implicit Arguments.

Hint Resolve in_eq in_cons in_inv in_nil in_dec: hint_list.

Section BasicListFacts.
  Variable A:Type.
  Lemma in_inv1 : forall (a b:A) (l:list A), In b (a :: l) -> b = a \/ In b l.
  Proof. { intros  a b l H. cut (a=b \/ In b l).
       Focus 2. auto with hint_list. intros H1; destruct H1 as [H1 | H2].
       left; symmetry; auto. right;auto. } Qed.
  Lemma in_inv2: forall (x a:A) (l:list A), In x (a::l)-> x <> a -> In x l.
  Proof.  { intros x a l H. cut (x=a \/ In x l). intro H1;destruct H1 as [Hl1|Hr1].
          intro;contradiction. auto. eapply in_inv1;auto. } Qed.
  Lemma in_inv3: forall (x a:A) (l:list A), In x (a::l)-> ~ In x l -> x = a.
    Proof.  { intros x a l H. cut (x=a \/ In x l). intro H1;destruct H1 as [Hl1|Hr1].
          intro;auto. intro;contradiction.  eapply in_inv1;auto. } Qed.
  Hint Resolve in_inv1 in_inv2 in_inv3 : hint_list.
  (*---------Some facts about NoDup on a list --------------------------------*)
  Lemma nodup_intro (a:A)(l: list A): ~ In a l -> NoDup l -> NoDup (a::l).
    Proof.  intros H1 H2; eapply NoDup_cons_iff;tauto.  Qed. 
  Lemma nodup_elim1 (a:A)(l: list A): NoDup (a::l)-> NoDup (l).
  Proof. intro H. eapply NoDup_cons_iff; eauto. Qed.
  Lemma nodup_elim2 (a:A)(l: list A): NoDup (a::l) -> ~ In a l.
    Proof. intro H. eapply NoDup_cons_iff; eauto. Qed. 
  
  Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : hint_list.
  End BasicListFacts.
Hint Resolve in_inv1 in_inv2 in_inv3: hint_list.
Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : hint_list.
Hint Immediate nodup_elim1  nodup_elim2  nodup_intro : hint_nodup.



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
  


  (*-----------------------Subset (spec) and its properties ------------------------*)
  
  Lemma Subset_elim1 (a:A) (s s':list A): Subset (a:: s) s'-> In a s' /\ Subset s s'.
  Proof. { unfold Subset. intro H. split. apply H. auto with hint_list. intros a1 H1.
           apply H. auto with hint_list. } Qed.
  Lemma self_incl (l:list A): l [<=] l.
  Proof. unfold Subset; tauto.  Qed. 
  Hint Resolve self_incl: hint_set.

  Lemma Subset_nil (l: list A): nil [<=] l.
    Proof. unfold "[<=]"; simpl; intros; contradiction. Qed.

  
  (* ---------------------- Equal (spec) and their properties--------------------*)
  Lemma Eq_refl (s: list A):  s [=] s.
  Proof.  unfold Equal. tauto.  Qed. 
  Lemma Eq_sym (s s':list A): s [=] s' -> s' [=] s.
  Proof. unfold Equal. unfold iff. intros H a. specialize (H a). tauto. Qed. 
  Lemma Eq_trans1 ( x y z : list A) : x [=] y -> y [=] z -> x [=] z.
  Proof. { unfold Equal. unfold iff. intros H H1 a.
         specialize (H1 a). specialize (H a). tauto. } Qed. 
  Lemma Equal_intro (s s': list A): s [<=] s' -> s' [<=] s -> s [=] s'.
  Proof. unfold_spec. intros H H1 a; unfold iff. auto. Qed.
  Lemma Equal_intro1 (s s': list A): s = s' -> Equal s s'.
  Proof. intro; subst s; apply Eq_refl; auto. Qed.
  Lemma Equal_elim ( s s': list A): s [=] s' ->  s [<=] s' /\ s' [<=] s.
  Proof. unfold_spec; unfold iff. intros H; split; intro a;apply H. Qed.
 
End BasicSetFacts.

 Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
 Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
 Notation "| s |":= (length s) (at level 70, no associativity).

Hint Immediate Eq_refl Eq_sym Eq_trans1 Equal_elim Equal_intro Equal_intro1: hint_list.
Hint Immediate Subset_elim1 Subset_nil : hint_list.
Hint Resolve  self_incl Eq_trans1: hint_list.

