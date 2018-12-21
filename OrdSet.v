




(* --------------------------- Description ----------------------------------------
   This file implements sets as Ordered Lists. Ordered lists here means strictly 
   increasing list according to the order relation on elemets of ordType (i.e, <b)
   
   Following list operations are defined on sets:
   rmv a l    ==> removes the first occurence of a from l 
   add a l       ==> adds a to the ordered list l (works only for ordered lists)
   inter l s     ==> returns intersection of sets represented by lists l and s
   union l s     ==> returns union of sets represented by lists l and s
   diff  l s     ==> returns elements of l which is not present in s

   Some useful results:


   Lemma set_rmv_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (remove a l).
   Lemma set_rmv_nodup (a:A)(l: list A): NoDup l -> NoDup (remove a l).
   
   Lemma set_add_IsOrd (a:A)(l: list A): IsOrd(l) -> IsOrd(add a l).
   Lemma set_add_nodup (a:A)(l: list A): IsOrd l -> NoDup (add a l).
  
   Lemma set_inter_IsOrd (x y: list A): IsOrd (inter x y).
   Lemma set_inter_nodup (x y:list A): NoDup (inter x y).
   Lemma inter_equal (x y:list A): inter x y = inter y x.

   Lemma set_union_IsOrd (x y: list A): IsOrd y -> IsOrd (union x y).
   Lemma set_union_nodup (x y: list A): IsOrd y -> NoDup (union x y).
   Lemma set_union_comm (x y:list A): Equal (union x y) (union y x).
   Lemma union_equal (x y:list A): IsOrd x -> IsOrd y -> union x y = union y x.

   Lemma set_diff_IsOrd (l s: list A): IsOrd (diff l s).
   Lemma set_diff_nodup (l s: list A): NoDup (diff l s). 
   --------------------------------------------------------------------------------*)

Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.
Require Export SetReflect OrdList.
Require Export Omega.

Require Export DecList. (* needed for cardinality results *)

Set Implicit Arguments.



Section Ord_sets.
 
  Variable A: ordType.
   Record set_on : Type := { S_of :> list A;
                             IsOrd_S : IsOrd S_of }.  
End Ord_sets.

Section OrderedSet.
  Context { A: ordType }. (* to declare A as implicit outside the section *)

  (* -----------------------Empty (spec) and its properties ------------------------*)
  Definition empty: list A:= nil.
  
  Lemma empty_spec : Empty (empty).
  Proof.  unfold Empty.  auto. Qed.
  
   
(*------------ list remove operation on ordered list ----------------------------------- *)
   Fixpoint rmv (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match comp a a1 with
               |Eq => l1
               |Lt => a1:: rmv a l1
               |Gt => a1:: rmv a l1
               end
    end. (* This function deletes only the first occurence of 'a' from the list l *)
  
  Lemma set_rmv_elim1 (a b:A)(l: list A): In a (rmv b l)-> In a l.
  Proof. { induction l. simpl. auto.
         { simpl. destruct (on_comp b a0).
           { right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. } } } Qed.
  Lemma set_rmv_elim (b:A)(l: list A): (rmv b l) [<=] l.
    Proof. unfold Subset. intros a;eapply set_rmv_elim1. Qed.
  Lemma set_rmv_elim2 (a b:A)(l: list A): NoDup l -> In a (rmv b l)-> (a<>b).
  Proof. { induction l. simpl. auto.
         { simpl. destruct (on_comp b a0).
           { intros H1 H2. subst b. intro H3. subst a.
             absurd (In a0 l); eauto. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             absurd (b <b b); eauto. apply IHl. eapply nodup_elim1;  eauto. auto. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             absurd (b <b b); eauto.  apply IHl. eapply nodup_elim1;  eauto. auto.  } } } Qed.
  Lemma set_rmv_elim3 (a:A)(l: list A): NoDup l -> ~ In a (rmv a l).
    Proof. intros H H1. absurd (a=a). eapply set_rmv_elim2. all: eauto. Qed.
  
  Lemma set_rmv_intro (a b: A)(l:list A): In a l -> a<>b -> In a (rmv b l).
  Proof. { induction l. simpl.  auto.
         { simpl. destruct (on_comp b a0).
           { intros H1 H2. destruct H1. subst a; subst b.
             absurd (a0=a0); auto. auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. } } } Qed.
           
  Hint Immediate set_rmv_elim1 set_rmv_elim set_rmv_elim2 set_rmv_elim3: core.
  Hint Resolve     set_rmv_intro: core.
  Lemma set_rmv_iff (a b:A)(l: list A): NoDup l -> (In a (rmv b l) <-> (In a l /\ a<>b)).
  Proof. intro H. split. eauto.
         intro H0. destruct H0 as [H0 H1]. eauto.  Qed. 
  
  Lemma set_rmv_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (rmv a l).
  Proof. { induction l. simpl.  constructor.
         { intro H. simpl. destruct (on_comp a a0).
           { eauto. }
           { apply IsOrd_intro. eauto. intros x H1.
             cut(In x l).
             { intro H2.  eapply IsOrd_elim2a. exact H. auto. }
             { eauto.  } }
            { apply IsOrd_intro. eauto. intros x H1.
              cut(In x l). intros; eapply IsOrd_elim2a; eauto. eauto. } } } Qed.
  
  Lemma set_rmv_nodup (a:A)(l: list A): NoDup l -> NoDup (rmv a l).
  Proof.  { induction l. simpl. constructor.
          { intro H. simpl. destruct (on_comp a a0).
            { eauto. }
            { constructor. intro H1. absurd (In a0 l). eauto.
              eauto. eauto. }
            { constructor. intro H1. absurd (In a0 l). eauto.
              eauto. eauto. } } } Qed.
  
  Lemma memb_prop_rmv (x a:A)(l: list A): x <> a -> memb x l = memb x (rmv a l).
  Proof.  { intro H. destruct (memb x l) eqn:H1.
          { symmetry. apply /membP. move /membP in H1. auto. }
          { symmetry. apply /membP.  move /membP in H1. intro H2; apply H1; eauto. } } Qed. 
  

  Hint Resolve set_rmv_IsOrd set_rmv_nodup memb_prop_rmv: core.

  Lemma rmv_card1 (a:A)(l: list A): In a l -> |rmv a l| = |l| - 1.
  Proof. { induction l.
         { simpl; auto. }
         { intro H. simpl. match_up a a0.
           {  omega. }
           { simpl. destruct H. by_conflict.
             apply IHl in H as H1. rewrite H1. cut (|l| > 0). omega. eauto. }
           { simpl. destruct H. by_conflict.
             apply IHl in H as H1. rewrite H1. cut (|l| > 0). omega. eauto. } } } Qed.
  Lemma rmv_card2  (a:A)(l: list A): ~ In a l -> |rmv a l| = |l|.
  Proof. { induction l.
         { simpl; auto. }
         { intro H. simpl. assert (H0: ~ In a l). auto.
           match_up a a0.
           {  subst a. absurd (In a0 (a0::l)); auto. }
           { simpl.  apply IHl in H0 as H2. rewrite H2.  omega. }
           { simpl.  apply IHl in H0 as H2. rewrite H2.  omega. } } } Qed.

  Lemma rmv_card  (a:A)(l: list A):  |rmv a l| <= |l|.
  Proof. { cut (In a l \/ ~ In a l). intro H.  destruct H.
         apply rmv_card1 in H as H1; rewrite H1; omega.
         apply rmv_card2 in H as H1; rewrite H1; omega.
         eapply reflect_EM; eauto. } Qed.

  Lemma rmv_card_min (a:A)(l: list A): |l| - 1 <=  |rmv a l|.
  Proof. induction l. simpl;omega. simpl;match_up a a0; simpl;omega. Qed.

  Hint Resolve rmv_card rmv_card1 rmv_card2 rmv_card_min: core.

  Lemma rmv_prop1 (a:A)(l s: list A): NoDup l-> l [<=] s -> (rmv a l) [<=] (rmv a s).
  Proof. { intros h1 h2 x h3. assert (h4: In x l /\ x<>a). apply set_rmv_iff;auto.
           destruct h4 as [h4 h5]. auto. }  Qed.

  Lemma rmv_prop2 (a:A)(l s: list A): NoDup l-> NoDup s-> l [=] s -> (rmv a l) [=] (rmv a s).
  Proof. intros h1 h2 h3. split;apply rmv_prop1; auto; apply h3. Qed.

  Hint Immediate rmv_prop1 rmv_prop2: core.
         

 
   (* ------------ set_add operation for ordered list -------------- ---------------  *)
  Fixpoint add (a:A)(l: list A): list A :=
    match l with
    | nil => a :: nil
    | a1::l1 => match comp a a1 with
               | Eq => a1:: l1
               | Lt => a::l
               | Gt => a1:: add a l1
               end
    end.
  (* the above operation works correctly only on sorted lists  *)
             
  Lemma set_add_intro1 (a b: A)(l: list A): In a l -> In a (add b l).
  Proof. { intro H. induction l.  inversion H.
         destruct H.
         { subst a0. simpl; destruct (on_comp b a); eauto. }
         { simpl; destruct (on_comp b a0); eauto. } } Qed.
  
  Lemma set_add_intro2 (a b: A)(l: list A): a= b -> In a (add b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (on_comp b a).
         subst b; auto. all: auto. } Qed.
  
  Lemma set_add_intro (a b: A)(l: list A): (a= b \/ In a l) -> In a (add b l).
  Proof. intro H. destruct H.  eapply set_add_intro2;auto.  eapply set_add_intro1;auto. Qed.
  Lemma set_add_intro3 (a:A)(l: list A): In a (add a l).
  Proof. { eapply set_add_intro2;auto.  } Qed.
  
  Hint Resolve set_add_intro1  set_add_intro3: core.
  
  Lemma set_add_not_empty (a: A)(l:list A): add a l <> (empty).
  Proof. { intro H. absurd (In a empty). simpl; auto. rewrite <- H.
           eauto. } Qed. 
    
  Lemma set_add_elim (a b: A)(l: list A): In a (add b l)-> ( a= b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (on_comp b a0).
         right;auto. destruct H. left; subst b;auto. right;auto.
         destruct H. right; subst a0; auto.
         apply IHl in H. destruct H; auto. } Qed.
  
  Lemma set_add_elim1 (a b: A)(l: list A): In a (add b l)-> ~ In a l -> a= b.
  Proof. { intros H H0.
         assert (H1: a= b \/ In a l). apply set_add_elim;auto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  set_add_elim2 (a b: A)(l: list A): In a (add b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a= b \/ In a l). apply set_add_elim;auto.
         destruct H1. absurd (a= b); auto. auto. } Qed.
  
  Hint Immediate set_add_elim set_add_elim1 set_add_elim2: core.
  Lemma set_add_iff (a b:A)(l:list A): In a (add b l) <-> (a= b \/ In a l).
  Proof. split; auto using set_add_intro. Qed.
  
  Lemma set_add_IsOrd (a:A)(l: list A): IsOrd(l) -> IsOrd(add a l).
  Proof. { induction l. simpl. constructor.
         { intro H.  simpl. destruct (on_comp a a0).
           auto. constructor;auto.
           apply IsOrd_intro. eauto.
           intros x H1. assert(H2: x=a \/ In x l). auto.
           destruct H2. subst x;auto. eapply IsOrd_elim2a; eauto.  } } Qed.
  
  Lemma set_add_nodup (a:A)(l: list A): IsOrd l -> NoDup (add a l).
  Proof. intro H. cut (IsOrd (add a l)). auto. apply set_add_IsOrd;auto. Qed.

  Lemma memb_prop_add (x a:A)(l: list A): x <> a -> memb x l = memb x (add a l).
   Proof. { intro H. destruct (memb x l) eqn:H1.
          { symmetry. apply /membP. move /membP in H1. auto. }
          { symmetry. apply /membP.  move /membP in H1. intro H2; apply H1; eauto. } } Qed.

   Hint Resolve set_add_IsOrd set_add_nodup memb_prop_add : core. 

   Lemma add_same (a:A)(l: list A): IsOrd l -> In a l-> (add a l) = l.
   Proof. { revert a. induction l.
          { simpl; tauto. }
          { intros x H H1.
            simpl.
            match_up x a.
            { auto. }
            { absurd (In x (a::l)); auto. }
            { assert (H2: In x l).
              { destruct H1. by_conflict. auto. }
              assert (H3: add x l = l). eauto.
              rewrite H3. auto. } } } Qed.

  
  Lemma add_card1  (a:A)(l: list A): ~ In a l -> |add a l| = S(|l|).
  Proof.  { induction l.
         { simpl; auto. }
         { intro H. simpl. assert (H0: ~ In a l). auto.
           match_up a a0.
           {  subst a. absurd (In a0 (a0::l)); auto. }
           { simpl.   omega. }
           { simpl.  apply IHl in H0 as H2. rewrite H2.  omega. } } } Qed.

  Lemma add_card  (a:A)(l: list A): |l| <= |add a l|.
  Proof.  induction l. simpl;auto. simpl;match_up a a0;simpl;omega. Qed.

  Lemma add_card_max  (a:A)(l: list A): |add a l| <= S(|l|).
  Proof. induction l. simpl;omega. simpl; match_up a a0;simpl;omega. Qed.
        

  Hint Resolve add_card add_card1 add_card_max add_same: core.

  Lemma add_prop1 (a:A)(l s: list A): l [<=] s -> (add a l) [<=] (add a s).
  Proof. { intros h1 x h2. assert (h3: x=a \/ In x l). auto.
           destruct h3 as [h3 | h3]. subst x; auto. cut (In x s);auto. } Qed.
  
  Lemma add_prop2 (a:A)(l s: list A): l [=] s -> (add a l) [=] (add a s).
  Proof. intros h1. destruct h1 as [h1 h2]. split; auto using add_prop1. Qed.

  Lemma add_add_is_add (a:A)(l:list A): add a l = add a (add a l).
  Proof. { induction l.
         { simpl. match_up a a. auto. all: by_conflict. }
         { simpl. match_up a a0.
           { subst a. simpl. match_up a0 a0. auto. all: by_conflict. }
           { simpl. match_up a a. auto. all: by_conflict. }
           { simpl. match_up a a0. subst a. by_conflict. by_conflict.
             rewrite <- IHl. auto. } } } Qed.

   Lemma add_add_is_add1 (a:A)(l: list A): add a l [=] add a (add a l).
   Proof. rewrite <- (add_add_is_add a l). auto. Qed.

   Lemma add_a_add_b (a b:A)(l: list A): add a (add b l) [=] add b (add a l).
   Proof. { split.
          { intros x h1. assert (h2: x= a \/ In x (add b l)). auto.
            destruct h2 as [h2 | h2].
            { subst x. cut (In a (add a l));auto. }
            { assert (h3: x = b \/ In x l). auto. destruct h3 as [h3 | h3].
              subst x. auto. cut (In x (add a l));auto. } }
           { intros x h1. assert (h2: x= b \/ In x (add a l)). auto.
            destruct h2 as [h2 | h2].
            { subst x. cut (In b (add b l));auto. }
            { assert (h3: x = a \/ In x l). auto. destruct h3 as [h3 | h3].
              subst x. auto. cut (In x (add b l));auto. } } } Qed.

   Lemma add_a_b (a b:A)(l: list A): IsOrd l -> add a (add b l) = add b (add a l).
   Proof. intro h. apply set_equal. all:auto. apply add_a_add_b. Qed.
   
   Hint Immediate add_prop1 add_prop2 add_add_is_add add_add_is_add1: core.
   Hint Resolve add_a_add_b add_a_b: core.

   
  (* ------------ set_inter operation ----------------------------------------------  *)
  
  Fixpoint inter (l s: list A): list A:=
    match l with
    |nil => nil
    |a::l' => match memb a s with
             |true => add a (inter l' s)
             |false => (inter l' s)
             end
    end.

  Lemma set_inter_intro (a:A)(x y: list A): In a x -> In a y-> In a (inter x y).
  Proof. { induction x.
         { intro H; inversion H. }
         { intros H H1.
           assert (H2: a=a0 \/ In a x); auto.
           destruct H2.
           { subst a0. simpl. destruct (memb a y) eqn: H2. auto.
             absurd (memb a y). switch;auto.  apply /membP;auto. }
           { simpl. destruct (memb a0 y) eqn: H2; auto. } } } Qed.
  Lemma set_inter_elim1 (a:A)(x y: list A): In a (inter x y)-> In a x.
  Proof. { induction x.
         { simpl. tauto. }
         { simpl. destruct (memb a0 y).
           { intro H0. assert(H: a= a0 \/ In a (inter x y)); auto.
             destruct H. left;symmetry;auto. right;auto. }
           { intro;right;auto. } } } Qed.
                      
  Lemma set_inter_elim2 (a:A)(x y: list A): In a (inter x y)-> In a y.
  Proof. { induction x.
         { simpl. tauto. }
         { simpl. destruct (memb a0 y) eqn: Hy.
           { intro H0. assert(H: a=a0 \/ In a (inter x y));auto.
             destruct H. subst a; apply /membP;auto. auto. }
           { auto. } } } Qed.
  
  Lemma set_inter_elim (a:A)(x y: list A): In a (inter x y)-> (In a x /\ In a y).
  Proof. intro. split. eapply set_inter_elim1;eauto. eapply set_inter_elim2;eauto. Qed.

  Lemma set_inter_elim3 (x y: list A): inter x y [<=] x.
  Proof. intros a h1. eauto using set_inter_elim1. Qed.

  Lemma set_inter_elim4 (x y: list A): inter x y [<=] y.
  Proof. intros a h1. eauto using set_inter_elim2. Qed.

  Lemma set_inter_elim5 (x y: list A): x [<=] y -> x [=] (inter x y).
  Proof. { intros h. split. intros a h1. apply set_inter_intro. all: auto.
           apply set_inter_elim3. } Qed.

  Lemma set_inter_elim6  (x y: list A): y [<=] x -> y [=] (inter x y).
  Proof. { intros h. split. intros a h1. apply set_inter_intro. all: auto.
           apply set_inter_elim4. } Qed.
    
  Lemma set_inter_IsOrd (x y: list A): IsOrd (inter x y).
  Proof. { induction x.
         { simpl. constructor. }
         { simpl. destruct (memb a y); auto. } } Qed.
  
  Lemma set_inter_nodup (x y:list A): NoDup (inter x y).
  Proof. { induction x.
         { simpl. constructor. }
         { simpl.  assert (H1: IsOrd (inter x y)). apply set_inter_IsOrd.
           destruct (memb a y); auto. } } Qed.

  Hint Immediate set_inter_intro set_inter_elim set_inter_elim1 set_inter_elim2: core.
  Hint Resolve set_inter_IsOrd set_inter_nodup: core.

  Hint Immediate set_inter_elim3 set_inter_elim4 set_inter_elim5 set_inter_elim6: core.
  
  Lemma set_inter_comm (x y:list A): Equal (inter x y) (inter y x).
  Proof.  { split; intros a H.
            assert (H1: In a x /\ In a y).
            { apply set_inter_elim. auto. } 
            destruct H1; auto.
            assert (H1: In a y /\ In a x). split;eauto.
            destruct H1; auto. }  Qed.

  Hint Resolve set_inter_comm: core.

  Lemma inter_equal (x y:list A): inter x y = inter y x.
  Proof. { assert (H1: Equal (inter x y) (inter y x)). auto.
          cut (IsOrd (inter x y)); cut (IsOrd (inter y x)); eauto. } Qed.
  
     
  (* ------------ set_union operation ----------------------------------------------  *)

  Fixpoint union (l s: list A): list A:=
    match l with
    |nil => s
    |a::l' => add a (union l' s)
    end.

  Lemma set_union_intro1 (a:A)(l s: list A): In a l -> In a (union l s).
  Proof. { induction l. simpl. tauto.
         simpl. intro H; destruct H. subst a. auto.
         auto. } Qed.
  Lemma set_union_intro2 (a:A)(l s: list A): In a s -> In a (union l s).
  Proof. induction l. simpl. auto. simpl. auto. Qed.
  
  Lemma set_union_elim (a:A)(l s:list A): In a (union l s) -> (In a l \/ In a s).
  Proof. { induction l. simpl. right;auto.
         simpl. intro H.
         assert (H1: a=a0 \/ In a (union l s)); auto.
         destruct H1.
         { left. left. symmetry;auto. }
         { assert (H1: In a l \/ In a s);auto. destruct H1. left;right;auto.
           right;auto. } } Qed.
  Hint Immediate set_union_intro1 set_union_intro2 set_union_elim: core.

  Lemma set_union_intro3 (l s: list A): l [<=] (union l s).
  Proof. intros a h1. eauto using set_union_intro1. Qed. 

  Lemma set_union_intro4 (l s: list A): s [<=] (union l s).
  Proof. intros a h1. eauto using set_union_intro2. Qed.

  Lemma set_union_intro5 (x y: list A): x [<=] y -> y [=] (union x y).
  Proof. { intros h. split. intros a h1. apply set_union_intro2. auto.
           intros a h1. cut(In a x \/ In a y).
           intro h2; destruct h2 as [h2 | h2]. all: auto. } Qed.

  Lemma set_union_intro6  (x y: list A): y [<=] x -> x [=] (union x y).
  Proof. { intros h. split. intros a h1. apply set_union_intro1. auto.
           intros a h1. cut(In a x \/ In a y).
           intro h2; destruct h2 as [h2 | h2]. all: auto. } Qed.

  Hint Immediate set_union_intro3 set_union_intro4 set_union_intro5 set_union_intro6: core.
  
  
  Lemma set_union_IsOrd (x y: list A): IsOrd y -> IsOrd (union x y).
  Proof. { induction x.
         { simpl. auto.  }
         { intros H1. simpl.  auto. } } Qed.
  Lemma set_union_nodup (x y: list A): IsOrd y -> NoDup (union x y).
  Proof. { induction x.
         { simpl. auto.  }
         { intros H1. simpl. cut(IsOrd (add a (union x y))).  auto.
           cut (IsOrd (union x y)). auto. apply set_union_IsOrd;auto. } } Qed.
  Lemma set_union_comm (x y:list A): Equal (union x y) (union y x).
  Proof. { split; intros a H.
           assert (H1: In a x \/ In a y); auto.
           destruct H1; auto.
           assert (H1: In a y \/ In a x); auto.
           destruct H1; auto. } Qed.
  
  Hint Resolve set_union_IsOrd set_union_nodup  : core.

  Lemma union_equal (x y:list A): IsOrd x -> IsOrd y -> union x y = union y x.
  Proof. { intros.
           cut (Equal (union x y) (union y x)).
           cut (IsOrd (union x y)). cut (IsOrd (union y x)).
           eauto. all: eauto.
           apply set_union_comm. } Qed.
  
  Hint Resolve inter_equal union_equal set_union_comm: core.

  Lemma union_intro7 (x y: list A)(a:A):  ~ In a y -> ~ In a x -> ~ In a (union x y).
  Proof. Admitted.

  Hint Immediate union_intro7: core.

  
  (* ------------ set_diff operation -----------------------------------------------  *)

  Fixpoint diff (l s: list A): list A:=
    match l with
    |nil=> nil
    |a::l' => match (memb a s) with
             |true => diff l' s
             |false => add a (diff l' s)
             end
    end.

  Lemma set_diff_intro (a: A)(l s: list A): In a l -> ~In a s -> In a (diff l s).
  Proof. { induction l.
         { simpl; auto. }
         { intros H H1. simpl.
           assert (H0: a=a0 \/ In a l); auto.
           destruct H0.
           destruct (memb a0 s) eqn:H2.
           { absurd ( In a0 s). subst a0;auto. apply /membP;auto. }
           { subst a0; auto. }
           destruct (memb a0 s) eqn:H2. auto.
           cut (In a (diff l s)); auto. } } Qed.
           
  Lemma set_diff_elim1 (a:A)(l s: list A): In a (diff l s) -> In a l.
  Proof. { induction l. simpl; auto.
         { simpl. destruct (memb a0 s) eqn: H0.
           intro; right; auto. intro H1.
           assert (H2: a= a0 \/ In a (diff l s)); auto.
           destruct H2. left; symmetry;auto. right;auto. } } Qed.
  Lemma set_diff_elim3 (l s: list A): (diff l s) [<=] l.
    Proof. intros x. eauto using set_diff_elim1. Qed.
  Lemma set_diff_elim2 (a:A)(l s: list A): In a (diff l s) -> ~In a s.
  Proof. { induction l. simpl;auto.
         { simpl. destruct (memb a0 s) eqn: H0.
           auto. intro H1. assert (H2: a= a0 \/ In a (diff l s)); auto.
           destruct H2. subst a. move /membP. switch_in H0. auto. auto. } } Qed.
  Lemma set_diff_empty (a:A)(l: list A): ~ In a (diff l l).
  Proof. { intro H. absurd (In a l). eapply set_diff_elim2;eauto.
           eapply set_diff_elim1;eauto. } Qed.

  Hint Immediate set_diff_elim1 set_diff_elim2 set_diff_intro set_diff_empty: core.

  Lemma set_diff_IsOrd (l s: list A): IsOrd (diff l s).
  Proof. { induction l.
           { simpl. constructor. }
           { simpl. destruct (memb a s); auto. } } Qed.
  
  Lemma set_diff_nodup (l s: list A): NoDup (diff l s).
  Proof. cut (IsOrd (diff l s)). auto. apply set_diff_IsOrd. Qed.

  Hint Resolve set_diff_IsOrd set_diff_nodup: core.

  Lemma filter_IsOrd (l: list A)(f: A-> bool): IsOrd l -> IsOrd (filter f l).
  Proof. { induction l.
           { simpl. auto. }
           { simpl. destruct (f a) eqn: H. intro H1.
             apply IsOrd_intro. eauto. intros x H2. cut (In x l). all: eauto. } } Qed.
             
  
          
End OrderedSet.

Hint Immediate set_rmv_elim1 set_rmv_elim set_rmv_elim2 set_rmv_elim3: core.
Hint Resolve     set_rmv_intro: core.
Hint Resolve set_rmv_IsOrd set_rmv_nodup memb_prop_rmv: core.
Hint Resolve rmv_card rmv_card1 rmv_card2 rmv_card_min: core.
Hint Immediate rmv_prop1 rmv_prop2: core.

Hint Resolve set_add_intro1  set_add_intro3: core.
Hint Immediate set_add_elim set_add_elim1 set_add_elim2: core.
Hint Resolve set_add_IsOrd set_add_nodup memb_prop_add: core.
Hint Resolve add_card add_card1 add_card_max add_same: core.
Hint Immediate add_prop1 add_prop2 add_add_is_add add_add_is_add1: core.
Hint Resolve add_a_add_b add_a_b: core.


 Hint Immediate set_inter_intro set_inter_elim set_inter_elim1 set_inter_elim2: core.
 Hint Immediate set_inter_elim3 set_inter_elim4 set_inter_elim5 set_inter_elim6: core.
Hint Resolve set_inter_comm: core.
Hint Resolve set_inter_IsOrd set_inter_nodup : core.

Hint Immediate set_union_intro1 set_union_intro2 set_union_elim set_union_comm: core.
Hint Immediate set_union_intro3 set_union_intro4 set_union_intro5 set_union_intro6: core.
Hint Resolve set_union_IsOrd set_union_nodup  : core.

Hint Resolve inter_equal union_equal: core.
Hint Immediate union_intro7: core.


Hint Immediate set_diff_elim1 set_diff_elim2 set_diff_elim3 set_diff_intro set_diff_empty: core.
Hint Resolve set_diff_IsOrd set_diff_nodup: core.

Hint Resolve filter_IsOrd: core.


Notation "s [i] t" := (inter s t) (at level 67, left associativity).
Notation "s [u] t" := (union s t) (at level 68, left associativity).
Notation "s [\] t" := (diff s t)  (at level 68, left associativity).


Section MoreOrdSet.

  Context { A: ordType }. (* to declare A as implicit outside the section *)
  Variable x y: list A.
  Hypothesis hx: IsOrd x.
  Hypothesis hy: IsOrd y.


  Lemma set_inter_elim15 : x [<=] y -> x = (inter x y).
  Proof. intros h; apply set_equal;  auto. Qed.

  Lemma set_inter_elim16 : y [<=] x -> y = (inter x y).
  Proof. intros h; apply set_equal;  auto. Qed. 

   Lemma set_union_intro15: x [<=] y -> y = (union x y).
  Proof. intros h; apply set_equal;  auto. Qed.

  Lemma set_union_intro16: y [<=] x -> x = (union x y).
  Proof. intros h; apply set_equal;  auto. Qed.

  Lemma y_as_disj_sum: x [<=] y -> y = x [u] (y [\] x).
  Proof. { intro h1. apply set_equal;auto. split. intros a h2. cut (In a x \/ ~ In a x).
           intro h3. destruct h3. auto. cut (In a (y [\] x)); auto. eauto.
           intros a h2. assert (h3: In a x \/ In a (y [\] x)). auto. destruct h3;eauto. } Qed.
  
  Lemma y_as_disj_sum1 : y =  (y [i] x) [u] (y [\] x).
  Proof. { apply set_equal;auto. split. intros a h2. cut (In a x \/ ~ In a x).
           intro h3. destruct h3.  cut (In a (y [i] x)); auto.
           cut (In a (y [\] x)); auto. eauto.
           intros a h2. assert (h3: In a (y [i] x) \/ In a (y [\] x)). auto.
           destruct h3;eauto. } Qed.

  Lemma y_as_disj_sum2 : y =  (y [\] x) [u] (y [i] x).
  Proof. replace ( y [\] x [u] y [i] x) with ((y [i] x) [u] (y [\] x)).
         apply y_as_disj_sum1. auto. Qed.

  Lemma union_minus_x : (x [u] y) [\] x = y [\] x.
  Proof. { apply set_equal;auto. split.
         { intros x0 h1. cut (In x0 y). cut (~ In x0 x). auto.
           eauto. assert (h2: In x0 (x [u] y)). eauto.
           assert (h3: ~ In x0 x). eauto. cut (In x0 x \/ In x0 y).
           intro h4. destruct h4. contradiction. auto. auto. }
         { intros x0 h1. cut (In x0 (x [u] y)). cut (~ In x0 x). auto.
           eauto. cut (In x0 y). auto. eauto. } } Qed.

  Lemma union_minus_y : (x [u] y) [\] y = x [\] y.
  Proof. { apply set_equal;auto. split.
         { intros x0 h1. cut (In x0 x). cut (~ In x0 y). auto.
           eauto. assert (h2: In x0 (x [u] y)). eauto.
           assert (h3: ~ In x0 y). eauto. cut (In x0 x \/ In x0 y).
           intro h4. destruct h4. auto. contradiction. auto. }
         { intros x0 h1. cut (In x0 (x [u] y)). cut (~ In x0 y). auto.
           eauto. cut (In x0 x). auto. eauto. } } Qed.

  Lemma union_as_disjoint_x: (x [u] y) = x [u] (y [\] x).
  Proof. Admitted.

  Lemma union_as_disjoint_y: (x [u] y) = y [u] (x [\] y).
  Proof. Admitted.
  
  Lemma x_disj_with: x [i] (y [\] x) = empty.
  Proof. { unfold empty. cut (x [i] (y [\] x) [<=] nil). auto.
           intros x0 h1. absurd (In x0 x). cut (In x0 (y [\] x));eauto. eauto. } Qed.

  Lemma yx_disj_with: (y [i] x) [i] (y [\] x) = empty.
  Proof. { unfold empty. cut ( y [i] x [i] (y [\] x) [<=] nil). auto.
           intros x0 h1. absurd (In x0 x). cut (In x0 (y [\] x)). eauto.
           eauto. cut (In x0 (y [i] x)); eauto. } Qed.

  Lemma y_disj_with: y [i] (x [\] y) = empty.
  Proof.  { unfold empty. cut ( y [i] (x [\] y) [<=] nil). auto.
           intros x0 h1. absurd (In x0 y). cut (In x0 (x [\] y));eauto. eauto. } Qed.

  Lemma xy_disj_with: (x [i] y) [i] (x [\] y) = empty.
  Proof. { unfold empty. cut ( (x [i] y) [i] (x [\] y) [<=] nil). auto.
           intros x0 h1. absurd (In x0 y). cut (In x0 (x [\] y)). eauto.
           eauto. cut (In x0 (x [i] y)); eauto. } Qed.
  

  Hint Immediate union_minus_x union_minus_y union_as_disjoint_x union_as_disjoint_y: core.
  Hint Resolve x_disj_with y_disj_with xy_disj_with yx_disj_with : core.
  
  Lemma inc_exc1: x [i] y = empty ->  | x [u] y | = |x| + |y|.
  Proof. { intro h1. induction x.
           { simpl;auto. } 
           { simpl.
             assert (h1a: (a :: l) [i] y [<=] empty). rewrite h1. auto.
             assert (h1b: empty [<=] a :: l [i] y). rewrite h1. auto.
             assert (h1c: l [i] y = empty).
             { apply set_equal;unfold empty;(auto || constructor). 
               intros x0 h2. apply h1a. cut (In x0 (a::l)). cut (In x0 y).
               auto. eauto. eauto. auto. }
             assert (h2:  (| add a (l [u] y) |) = S (|l [u] y|) ).
             { cut (~ In a (l [u] y)). auto. cut (~ In a l). cut (~ In a y).
               auto. intro h2. absurd (In a nil). auto. apply h1a. auto. auto. }
             rewrite h2.
             assert (h3:  (| l [u] y |) = (| l |) + (| y |)). eauto. rewrite h3.
             omega. } } Qed.


 

    
End MoreOrdSet.


Hint Resolve set_inter_elim15 set_inter_elim16: core.
Hint Resolve set_union_intro15 set_union_intro16: core.
Hint Resolve y_as_disj_sum y_as_disj_sum1 y_as_disj_sum2: core.

 Hint Immediate union_minus_x union_minus_y union_as_disjoint_x union_as_disjoint_y: core.
 Hint Resolve x_disj_with y_disj_with xy_disj_with yx_disj_with : core.


 Section Inc_Exc.

  Context { A: ordType }. (* to declare A as implicit outside the section *)
  Variable x y: list A.
  Hypothesis hx: IsOrd x.
  Hypothesis hy: IsOrd y.

  Lemma inclusion_exclusion: | x [u] y | = |x| + |y| - | x [i] y |.
  Proof. { assert (h1: | x [u] y | = |x| + | y [\] x |).
           { replace (x [u] y) with (x [u] (y [\] x)).
             eapply inc_exc1. auto. auto. symmetry;auto. }
           assert (h2: | y | = |y [i] x| + | y [\] x |).
           {  replace y with ((y [i] x) [u] (y [\] x)) at 1.
              eapply inc_exc1. auto. auto. symmetry. auto. }
           assert (h3: | x [i] y | = | y [i] x |).
           { replace (x [i] y) with (y [i] x). auto. auto. } omega. } Qed.
  
  End Inc_Exc.