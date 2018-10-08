



(* This file contains some important results on lists of elements from an ordered type. 
   Following are some important notions formalized in this file----------------------
          
 IsOrd l           <==> l is an strictly increasing list
 isOrd l           ==> boolean function to check if the list is strictly increasing

 insert a l        => adds a to the list l (even if l is not ordered )
 
 del_all a l       => removes all occurences of a in l


 Some of the useful results in this file are:

 Lemma IsOrd_NoDup (l: list A): IsOrd l -> NoDup l.
 Lemma isOrdP (l:list A): reflect(IsOrd l)(isOrd l).
 
 Lemma head_equal (a b: A)(l s: list A): 
            IsOrd (a::l)-> IsOrd (b::s)-> Equal (a::l) (b::s)-> a=b.
 Lemma tail_equal (a b: A)(l s:list A):
            IsOrd (a::l)->IsOrd (b::s)->Equal (a::l)(b::s)-> Equal l s.
 Lemma set_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> l=s.
 Lemma length_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> |l|=|s|. 
                                                                             ------- *)


Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.

Set Implicit Arguments.

Section OrderedLists.
  Context {A: ordType}. 
  (* Variable A: ordType.  *)

  Lemma decA (x y:A): {x=y}+{x<>y}.
  Proof. eapply reflect_dec with (b:= eqb x y). apply eqP. Qed.
  
  Lemma EM_A (x y: A): x=y \/ x<>y.
  Proof. eapply reflect_EM with (b:= eqb x y). apply eqP. Qed.
   
  (* ------------IsOrd Predicate  -----------------------------------------------  *)
  Inductive IsOrd :list A -> Prop:=
  |  IsOrd_nil: IsOrd nil
  | IsOrd_singl: forall x:A, IsOrd (x::nil)
  | IsOrd_cons: forall (x y: A)(l: list A), (ltb x y)-> IsOrd (y::l) -> IsOrd (x::y::l).

  Lemma IsOrd_elim (l: list A)(x y: A): IsOrd (x::y::l)-> IsOrd (y::l).
  Proof. intro H;inversion H; auto. Qed.
  Lemma IsOrd_elim1 (l: list A)(x y: A): IsOrd (x::y::l)-> (ltb x y).
  Proof. intro H;inversion H; auto. Qed.
  Lemma IsOrd_elim0 (l:list A)(x:A): IsOrd (x::l)-> IsOrd(l).
  Proof. case l. constructor. intros s l0. apply IsOrd_elim. Qed.
  
  Lemma IsOrd_intro (a:A)(l: list A): IsOrd l-> (forall x, In x l -> ltb a x)-> IsOrd (a::l).
  Proof. intros H H1. case l eqn:H2. constructor. constructor.
         apply H1. all: auto. Qed.
  
  Hint Resolve IsOrd_elim IsOrd_elim1 IsOrd_elim0 IsOrd_intro: core.
  
  
  Lemma IsOrd_elim2(l:list A): forall a:A, IsOrd (a::l)-> (forall x:A, In x l-> ltb a x).
  Proof. { induction l.
         { intros a H x H0. inversion H0.  }
         { intros a0 H x H0.
           assert (H1: x=a \/ In x l); auto.
           destruct H1 as [H1 | H1]. rewrite H1. eauto.
           assert (H2: a <b x). apply IHl; eauto.
           assert (H3 : a0 <b a). eauto. eauto.  } } Qed.
  
   Lemma IsOrd_elim2a(l:list A)(a x:A): IsOrd (a::l)-> In x l -> ltb a x.
  Proof. { intros H H1. eapply (@IsOrd_elim2 l a) in H. exact H. auto. } Qed. 
      
  
  Lemma IsOrd_elim3 (x a: A)(l: list A): IsOrd (a::l)-> ltb x a -> ~ In x (a::l).
  Proof. { intros H H0 H1.
         assert (H2: x=a \/ In x l); eauto.
         destruct H2. eapply ltb_not_eq; eauto.
         assert (H3: a <b x). eapply IsOrd_elim2;eauto.  eapply ltb_antisym;eauto. } Qed. 
  
  Lemma IsOrd_elim4 (a:A)(l: list A): IsOrd (a::l)-> ~ In a l.
  Proof. { intros H H1. assert (H2: ltb a a). eapply IsOrd_elim2;eauto.
           absurd (a <b a); auto. } Qed.

  Lemma IsOrd_elim5 (a b:A)(l: list A): IsOrd (a::l)-> In b (a::l)-> (b=a \/ a <b b).
    Proof.  { intros H1 H2. cut (b=a \/ In b l).
           intro H0; destruct H0 as [Ha | Hb]. left;auto.
           right; eapply IsOrd_elim2;eauto.  eauto. } Qed.

  Hint Resolve IsOrd_elim2a IsOrd_elim3 IsOrd_elim4 IsOrd_elim5: core.  

  Lemma IsOrd_NoDup (l: list A): IsOrd l -> NoDup l.
  Proof. { intros. induction l. constructor.
         constructor. eapply IsOrd_elim4;auto.  eauto. } Qed. 

  Fixpoint isOrd (l: list A): bool:=
    match l with
    |nil => true
    |x ::l1=> match l1 with
             | nil => true
             | y::l2 => (ltb x y) && (isOrd l1)
             end
    end.
   Lemma isOrd_elim (l: list A)(x y: A): isOrd (x::y::l)-> isOrd (y::l).
   Proof.  simpl; move /andP; tauto.  Qed.
   Lemma isOrd_elim1 (l: list A)(x y: A): isOrd (x::y::l)-> (ltb x y).
   Proof. simpl; move /andP; tauto. Qed.
   Lemma isOrd_elim0 (l:list A)(x:A): isOrd (x::l)-> isOrd(l).
   Proof. case l. simpl;auto.  intros s l0. simpl; move /andP; tauto. Qed.

   Hint Resolve isOrd_elim isOrd_elim1 isOrd_elim0: core.

  Lemma isOrdP (l:list A): reflect(IsOrd l)(isOrd l).
  Proof. { apply reflect_intro. split.
         { intro H. induction l. 
         { simpl;auto. }
         { simpl. case l eqn:H1.  auto. apply /andP.
           split. eauto. apply IHl; eauto. } }
         {  intro H. induction l. constructor. case l eqn:H1.
            constructor. constructor. eauto.
            apply IHl. eapply isOrd_elim. apply H.  } } Qed.

  Hint Resolve isOrdP: core.

  Lemma NoDup_elim1(a:A)(l:list A): NoDup (a::l) -> ~ In a l.
  Proof. eapply NoDup_cons_iff. Qed.

  Lemma NoDup_elim2 (a: A)(l: list A): NoDup (a::l) -> NoDup l.
  Proof. eapply NoDup_cons_iff. Qed.

  Lemma NoDup_intro (a: A)(l: list A): ~ In a l -> NoDup l -> NoDup (a::l).
  Proof. intros; eapply NoDup_cons_iff;auto. Qed.

  
  Hint Resolve NoDup_elim1 NoDup_elim2 NoDup_intro: core.

  (* --------------------Equality of Ordered Lists---------------------------------------*)

  Definition empty: list A:= nil.
  
  Lemma empty_equal_nil (l: list A): l [=] empty -> l = empty.
  Proof. { case l. auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.

  Lemma head_equal (a b: A)(l s: list A): IsOrd (a::l)-> IsOrd (b::s)-> Equal (a::l) (b::s)-> a = b.
  Proof. { intros H H1 H2.
         assert(H3: In b (a::l)).
         unfold "[=]" in H2. apply H2. auto.   
         assert(H3A: b=a \/ a <b b). eauto.  
         assert(H4: In a (b::s)). unfold "[=]" in H2. apply H2. auto. 
         assert(H4A: a = b \/ b <b a). eauto.
         destruct H3A; destruct H4A.
         auto. symmetry;auto. auto. absurd (b <b a); auto. } Qed.
         

  Lemma tail_equal (a b: A)(l s:list A):IsOrd (a::l)->IsOrd (b::s)->Equal (a::l)(b::s)-> Equal l s.
  Proof. { intros H H1 H2. unfold "[=]". 
         assert(H0: a = b). eapply head_equal;eauto. subst b.
         split; intro x.
         { intro H3. assert (H3A: a <b x). eauto.
           assert (H3B: In x (a::l)). auto.
           assert (H3C: x=a \/ In x s).
           { cut (In x (a::s)). eauto. apply H2;auto. }
           destruct H3C. absurd (a <b x); eauto. auto. }
          { intro H3. assert (H3A: a <b x). eauto. 
           assert (H3B: In x (a::s)). auto.
           assert (H3C: x=a \/ In x l).
           { cut (In x (a::l)). auto.  apply H2;auto. }
           destruct H3C. absurd (a <b x); auto. auto. } } Qed.
         
  Lemma set_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> l=s.
  Proof. { revert s. induction l; induction s.
         { auto. }
         { intros; symmetry; apply empty_equal_nil; unfold empty; auto.  }
         { intros; apply empty_equal_nil; unfold empty; auto. }
         { intros H H1 H2. replace a0 with a. replace s with l.
           auto. apply IHl. all: eauto. 
           eapply tail_equal; eauto. eapply head_equal;eauto. } } Qed.  
  
  Lemma length_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> |l|=|s|.
  Proof. intros. replace s with l. auto. eapply set_equal; eauto. Qed.

  Hint Resolve head_equal tail_equal set_equal length_equal: core.

  (*----------Misc property on ordList-------------------------------*)
  Lemma nodup_Subset_elim(a:A)(l s: list A):
    NoDup (a::l)-> NoDup (a::s)-> a::l [<=] a::s -> l [<=] s.
  Proof. { intros H H1 H2 x H3. assert (Hs: In x (a::s)). apply H2; auto.
         destruct Hs. subst x; absurd (In a l); auto. auto. } Qed.

  Lemma IsOrd_Subset_elim1 (e a: A)(l s: list A):
    IsOrd (e::l)-> IsOrd (a::s) -> e::l [<=] a::s -> a <=b e.
  Proof. intros H H1 H2. match_up a e. subst a;auto. auto. absurd (In e (a::s)); auto.  Qed.
  
  Lemma IsOrd_Subset_elim2 (e a: A)(l s: list A):
    IsOrd (e::l)-> IsOrd (a::s) -> e::l [<=] a::s -> e<>a -> e::l [<=] s.
  Proof. { intros H H1 H2 H3 x Hl.
         destruct Hl.
         { subst x. cut (In e (a::s)). intro H4. destruct H4.
           symmetry in H0. contradiction. auto. auto. }
         { assert(H4: In x (a::s)). auto. destruct H4. subst x.
           assert (H4: e <b a). eauto.
           assert (H5: a <=b e). eapply IsOrd_Subset_elim1;eauto.
           by_conflict. auto. } } Qed.
  

End OrderedLists.



Hint Resolve IsOrd_elim IsOrd_elim1 IsOrd_elim0 IsOrd_intro: core.
Hint Resolve IsOrd_elim2a IsOrd_elim3 IsOrd_elim4 IsOrd_elim5: core. 
Hint Resolve isOrd_elim isOrd_elim1 isOrd_elim0: core.
Hint Resolve isOrdP: core.

Hint Resolve NoDup_elim1 NoDup_elim2 NoDup_intro: core.
Hint Immediate head_equal tail_equal set_equal length_equal: core.
Hint Resolve IsOrd_NoDup: core.

Hint Resolve nodup_Subset_elim IsOrd_Subset_elim1 IsOrd_Subset_elim2:core.




           

