



(* This file contains some important results on lists of elements from an ordered type. 
   Following are some important notions formalized in this file----------------------
          
 IsOrd l           <==> l is an strictly increasing list
 isOrd l           ==> boolean function to check if the list is strictly increasing

 insert a l        => adds a to the list l (even if l is not ordered )
 remove a l        => removes the first occurence of a from l
 del_all a l       => removes all occurences of a in l


 Some of the useful results in this file are:

 Lemma IsOrd_NoDup (l: list A): IsOrd l -> NoDup l.
 Lemma IsOrdP (l:list A): reflect(IsOrd l)(isOrd l).
 
 Lemma head_equal (a b: A)(l s: list A): 
            IsOrd (a::l)-> IsOrd (b::s)-> Equal (a::l) (b::s)-> a=b.
 Lemma tail_equal (a b: A)(l s:list A):
            IsOrd (a::l)->IsOrd (b::s)->Equal (a::l)(b::s)-> Equal l s.
 Lemma set_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> l=s.
 Lemma length_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> |l|=|s|. 
 
 Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).

 Lemma remove_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (remove a l).
 Lemma remove_nodup (a:A)(l: list A): NoDup l -> NoDup (remove a l).

 Lemma list_del_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (del_all a l).
 Lemma list_del_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).      ------- *)


Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.
Require Export Omega.

Set Implicit Arguments.

Section OrderedLists.
  Context {A: ordType}. 
  (* Variable A: ordType.  *)

  Lemma decA (x y:A): {x=y}+{x<>y}.
  Proof. eapply reflect_dec with (b:= eqb x y). apply eqP. Qed.
  Check decA.
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
         apply H1. auto with hint_list. eauto. Qed.
  
  Hint Resolve IsOrd_elim IsOrd_elim1 IsOrd_elim0 IsOrd_intro: hint_list.
  
  
  Lemma IsOrd_elim2(l:list A): forall a:A, IsOrd (a::l)-> (forall x:A, In x l-> ltb a x).
  Proof. { induction l.
         { intros a H x H0. inversion H0.  }
         { intros a0 H x H0.
           assert (H1: x=a \/ In x l); auto with hint_list.
           destruct H1 as [H1 | H1]. rewrite H1. eauto with hint_list.
           assert (H2: a <b x). apply IHl; eauto with hint_list.
           assert (H3 : a0 <b a). eauto with hint_list. eauto.  } } Qed. 
      
  
  Lemma IsOrd_elim3 (x a: A)(l: list A): IsOrd (a::l)-> ltb x a -> ~ In x (a::l).
  Proof. { intros H H0 H1.
         assert (H2: x=a \/ In x l); eauto with hint_list.
         destruct H2. eapply ltb_not_eq; eauto.
         assert (H3: a <b x). eapply IsOrd_elim2;eauto.  eapply ltb_antisym;eauto. } Qed. 
  
  Lemma IsOrd_elim4 (a:A)(l: list A): IsOrd (a::l)-> ~ In a l.
  Proof. { intros H H1. assert (H2: ltb a a). eapply IsOrd_elim2;eauto.
           absurd (a <b a); auto. } Qed.

  Lemma IsOrd_elim5 (a b:A)(l: list A): IsOrd (a::l)-> In b (a::l)-> (b=a \/ a <b b).
    Proof.  { intros H1 H2. cut (b=a \/ In b l).
           intro H0; destruct H0 as [Ha | Hb]. left;auto.
           right; eapply IsOrd_elim2;eauto.  eauto with hint_list. } Qed.

  Hint Resolve IsOrd_elim2 IsOrd_elim3 IsOrd_elim4 IsOrd_elim5: hint_list.  

  Lemma IsOrd_NoDup (l: list A): IsOrd l -> NoDup l.
  Proof. { intros. induction l. constructor.
         constructor. eapply IsOrd_elim4;auto.  eauto with hint_list. } Qed. 

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

   Hint Resolve isOrd_elim isOrd_elim1 isOrd_elim0: hint_list.

  Lemma IsOrdP (l:list A): reflect(IsOrd l)(isOrd l).
  Proof. { apply reflect_intro. split.
         { intro H. induction l. 
         { simpl;auto. }
         { simpl. case l eqn:H1.  auto. apply /andP.
           split. eauto with hint_list. apply IHl; eauto with hint_list. } }
         {  intro H. induction l. constructor. case l eqn:H1.
            constructor. constructor. eauto with hint_list.
            apply IHl. eapply isOrd_elim. apply H.  } } Qed.

  Hint Resolve IsOrdP: hint_reflect.

  Lemma NoDup_elim1(a:A)(l:list A): NoDup (a::l) -> ~ In a l.
  Proof. eapply NoDup_cons_iff. Qed.

  Lemma NoDup_elim2 (a: A)(l: list A): NoDup (a::l) -> NoDup l.
  Proof. eapply NoDup_cons_iff. Qed.

  Lemma NoDup_intro (a: A)(l: list A): ~ In a l -> NoDup l -> NoDup (a::l).
  Proof. intros; eapply NoDup_cons_iff;auto. Qed.

  
  Hint Resolve NoDup_elim1 NoDup_elim2 NoDup_intro: hint_list.

  (* --------------------Equality of Ordered Lists---------------------------------------*)

  Definition empty: list A:= nil.
  
  Lemma empty_equal_nil (l: list A): l [=] empty -> l = empty.
  Proof. { case l. auto. intros s l0. unfold "[=]". intro H. specialize (H s).
           destruct H as [H1 H2]. absurd (In s empty). all: eauto with hint_list. } Qed.

  Lemma head_equal (a b: A)(l s: list A): IsOrd (a::l)-> IsOrd (b::s)-> Equal (a::l) (b::s)-> a=b.
  Proof. { intros H H1 H2.
         assert(H3: In b (a::l)).
         unfold "[=]" in H2. apply H2. auto with hint_list.   
         assert(H3A: b=a \/ a <b b). eauto with hint_list.  
         assert(H4: In a (b::s)). unfold "[=]" in H2. apply H2. auto with hint_list. 
         assert(H4A: a=b \/ b <b a). eauto with hint_list.
         destruct H3A; destruct H4A.
         auto. symmetry;auto. auto. absurd (b <b a); auto. } Qed.
         

  Lemma tail_equal (a b: A)(l s:list A):IsOrd (a::l)->IsOrd (b::s)->Equal (a::l)(b::s)-> Equal l s.
  Proof. { intros H H1 H2. unfold "[=]". intro x.
         assert(H0: a=b). eapply head_equal;eauto. subst b.
         split.
         { intro H3. assert (H3A: a <b x). eauto with hint_list.
           assert (H3B: In x (a::l)). eauto with hint_list.
           assert (H3C: x=a \/ In x s).
           { cut (In x (a::s)). eauto with hint_list. apply H2;auto. }
           destruct H3C. absurd (a <b x); eauto. auto. }
          { intro H3. assert (H3A: a <b x). eauto with hint_list.
           assert (H3B: In x (a::s)). eauto with hint_list.
           assert (H3C: x=a \/ In x l).
           { cut (In x (a::l)). eauto with hint_list. apply H2;auto. }
           destruct H3C. absurd (a <b x); eauto. auto. } } Qed.
         
  Lemma set_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> l=s.
  Proof. { revert s. induction l; induction s.
         { auto. }
         { intros; symmetry; apply empty_equal_nil; unfold empty; eauto with hint_list. }
         { intros; apply empty_equal_nil; unfold empty; auto. }
         { intros H H1 H2. replace a0 with a. replace s with l.
           auto. apply IHl. all: eauto with hint_list.
           eapply tail_equal; eauto. eapply head_equal;eauto. } } Qed.  
  
  Lemma length_equal (l s: list A): IsOrd l -> IsOrd s -> Equal l s -> |l|=|s|.
  Proof. intros. replace s with l. auto. eapply set_equal; eauto. Qed.

  Hint Resolve set_equal: hint_list.


  
  (* -------------- list_insert operation and its properties---------------------------  *)
  Fixpoint insert (a:A)(l: list A): list A :=
    match l with
    |nil => a::nil
    |a1::l1 => match comp a a1 with
              |Eq => a1::l1
              |Lt => a1:: (insert a l1)
              |Gt => a1:: (insert a l1)
              end
    end.
  (* this function adds an element correctly even in an unsorted list *)
  Lemma insert_intro1 (a b: A)(l: list A): In a l -> In a ( insert b l).
  Proof. { intro H. induction l.  inversion H.
         destruct H.
         { subst a0. simpl; destruct (on_comp b a); eauto with hint_list. }
         { simpl; destruct (on_comp b a0); eauto with hint_list. } } Qed.
  
  Lemma insert_intro2 (a b: A)(l: list A): a=b -> In a (insert b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (on_comp b a).
         subst b; auto with hint_list. all: auto with hint_list. } Qed.
  Lemma insert_intro (a b: A)(l: list A): (a=b \/ In a l) -> In a (insert b l).
  Proof. intro H. destruct H.  eapply insert_intro2;auto.  eapply insert_intro1;auto. Qed.
  Lemma insert_intro3 (a:A)(l: list A): In a (insert a l).
  Proof. { eapply insert_intro2. auto.  } Qed.
  Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: hint_list.
  
  Lemma insert_not_empty (a: A)(l:list A): insert a l <> (empty).
  Proof. intro H. absurd (In a empty). simpl; auto. rewrite <- H.
         eauto with hint_list. Qed. 
    
  Lemma insert_elim (a b: A)(l: list A): In a (insert b l)-> ( a=b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (on_comp b a0).  
         right;auto. destruct H. right;subst a0;auto with hint_list.
         cut (a=b \/ In a l). intro H1;destruct H1. left;auto. right; eauto with hint_list.
         auto.  destruct H. right; subst a0; eauto with hint_list.
         apply IHl in H. destruct H; eauto with hint_list. } Qed.
  
  Lemma insert_elim1 (a b: A)(l: list A): In a (insert b l)-> ~ In a l -> a=b.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  insert_elim2 (a b: A)(l: list A): In a (insert b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. absurd (a=b); auto. auto. } Qed.
  
  Hint Resolve insert_elim insert_elim1 insert_elim2: hint_list.
  Lemma insert_iff (a b:A)(l:list A): In a (insert b l) <-> (a=b \/ In a l).
  Proof. split; auto with hint_list. Qed.

  
  
  Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).
  Proof. { induction l. simpl. constructor;auto.
         { intro H. simpl. destruct (on_comp a a0).
           { auto. }
           { constructor. intro H1.
           assert (H2: a0 =a \/ In a0 l); eauto with hint_list.
           destruct H2. subst a0. absurd (a <b a); auto.
           absurd (In a0 l); auto with hint_list. eauto with hint_list. }
           { constructor. intro H1.
           assert (H2: a0 =a \/ In a0 l); eauto with hint_list.
           destruct H2. subst a0. absurd (a <b a); auto.
           absurd (In a0 l); auto with hint_list. eauto with hint_list. } } } Qed.
         
  Hint Resolve insert_nodup : hint_list.


   
  (*------------ list remove operation on ordered list ----------------------------------- *)
   Fixpoint remove (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match comp a a1 with
               |Eq => l1
               |Lt => a1:: remove a l1
               |Gt => a1:: remove a l1
               end
    end. (* This function deletes only the first occurence of 'a' from the list l *)
  
  Lemma remove_elim1 (a b:A)(l: list A): In a (remove b l)-> In a l.
  Proof. { induction l. simpl. auto.
         { simpl. destruct (on_comp b a0).
           { right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. } } } Qed.
  Lemma remove_elim2 (a b:A)(l: list A): NoDup l -> In a (remove b l)-> (a<>b).
  Proof. { induction l. simpl. auto.
         { simpl. destruct (on_comp b a0).
           { intros H1 H2. subst b. intro H3. subst a.
             absurd (In a0 l); eauto with hint_list. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             absurd (b <b b); eauto. eauto with hint_list. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             absurd (b <b b); eauto. eauto with hint_list. } } } Qed.
  
  Lemma remove_intro (a b: A)(l:list A): In a l -> a<>b -> In a (remove b l).
  Proof. { induction l. simpl.  auto.
         { simpl. destruct (on_comp b a0).
           { intros H1 H2. destruct H1. subst a; subst b.
             absurd (a0=a0); auto. auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. } } } Qed.
           
  Hint Resolve remove_elim1 remove_elim2 remove_intro: hint_list.
  Lemma remove_iff (a b:A)(l: list A): NoDup l -> (In a (remove b l) <-> (In a l /\ a<>b)).
  Proof. intro H. split. eauto with hint_list.
         intro H0. destruct H0 as [H0 H1]. eauto with hint_list.  Qed. 
  
  Lemma remove_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (remove a l).
  Proof. { induction l. simpl.  constructor.
         { intro H. simpl. destruct (on_comp a a0).
           { eauto with hint_list. }
           { apply IsOrd_intro. eauto with hint_list. intros x H1.
             cut(In x l); eauto with hint_list.  }
            { apply IsOrd_intro. eauto with hint_list. intros x H1.
              cut(In x l); eauto with hint_list.  } } } Qed.
           
  
  Lemma remove_nodup (a:A)(l: list A): NoDup l -> NoDup (remove a l).
  Proof.  { induction l. simpl. constructor.
          { intro H. simpl. destruct (on_comp a a0).
            { eauto with hint_list. }
            { constructor. intro H1. absurd (In a0 l). eauto with hint_list.
              eauto with hint_list. eauto with hint_list. }
            { constructor. intro H1. absurd (In a0 l). eauto with hint_list.
              eauto with hint_list. eauto with hint_list. } } } Qed.

  Hint Resolve remove_IsOrd remove_nodup: hint_list.


   
  (* ------------ list delete_all operation ---------------------------------------------  *)
  Fixpoint del_all (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match comp a a1 with
               |Eq => del_all a l1
               |Lt => a1 :: del_all a l1
               |Gt => a1 :: del_all a l1
               end
    end. (* This function deletes all occurences of a in the list l *)

  
  Lemma list_del_elim1 (a b:A)(l: list A): In a (del_all b l)-> In a l.
  Proof. Admitted.
  Lemma list_del_elim2 (a b:A)(l: list A): In a (del_all b l)-> (a<>b).
  Proof. Admitted.

  Lemma list_del_intro (a b: A)(l:list A): In a l -> a<>b -> In a (del_all b l).
  Proof. Admitted.
  Lemma list_del_iff (a b:A)(l: list A): (In a (del_all b l) <-> (In a l /\ a<>b)).
  Proof. Admitted.

  Hint Resolve list_del_elim1 list_del_elim2 list_del_intro: hint_list.
  
  Lemma list_del_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (del_all a l).
  Proof. Admitted.
  Lemma list_del_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).
  Proof. Admitted.

  Hint Resolve list_del_IsOrd list_del_nodup: hint_list.

End OrderedLists.



Hint Resolve IsOrd_elim IsOrd_elim1 IsOrd_elim0 IsOrd_intro: hint_list.
Hint Resolve IsOrd_elim2 IsOrd_elim3 IsOrd_elim4 IsOrd_elim5: hint_list. 
Hint Resolve isOrd_elim isOrd_elim1 isOrd_elim0: hint_list.
Hint Resolve IsOrdP: hint_reflect.

Hint Resolve NoDup_elim1 NoDup_elim2 NoDup_intro: hint_list.
Hint Immediate head_equal  tail_equal set_equal: hint_list.
Hint Resolve IsOrd_NoDup: hint_list.

Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: hint_list.
Hint Resolve insert_elim insert_elim1 insert_elim2 insert_nodup: hint_list.

Hint Resolve remove_elim1 remove_elim2 remove_intro: hint_list.
Hint Resolve remove_IsOrd remove_nodup: hint_list.

Hint Resolve list_del_elim1 list_del_elim2 list_del_intro: hint_list.
Hint Resolve list_del_IsOrd list_del_nodup: hint_list.

           

