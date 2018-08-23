




(* This file implements sets as Ordered Lists. Ordered lists here means strictly 
   increasing list according to the order relation on elemets of ordType (i.e, <b)
   
   Following list operations are defined on sets:
    
   add a l       ==> adds a to the ordered list l (works only for ordered lists)
   inter l s     ==> returns intersection of sets represented by lists l and s
   union l s     ==> returns union of sets represented by lists l and s
   diff  l s     ==> returns elements of l which is not present in s

   Some useful results:

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
   Lemma set_diff_nodup (l s: list A): NoDup (diff l s).  ------------------------*)

Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.
Require Export SetReflect OrdList.
Require Export Omega.


Set Implicit Arguments.

Section OrderedSet.
  Context { A: ordType }. (* to declare A as implicit outside the section *)

  (* -----------------------Empty (spec) and its properties ------------------------*)
  Definition empty: list A:= nil.
  
  Lemma empty_spec : Empty (empty).
  Proof.  unfold Empty.  auto with hint_list. Qed.

 
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
         { subst a0. simpl; destruct (on_comp b a); eauto with hint_list. }
         { simpl; destruct (on_comp b a0); eauto with hint_list. } } Qed.
  
  Lemma set_add_intro2 (a b: A)(l: list A): a=b -> In a (add b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (on_comp b a).
         subst b; auto with hint_list. all: auto with hint_list. } Qed.
  Lemma set_add_intro (a b: A)(l: list A): (a=b \/ In a l) -> In a (add b l).
  Proof. intro H. destruct H.  eapply set_add_intro2;auto.  eapply set_add_intro1;auto. Qed.
  Lemma set_add_intro3 (a:A)(l: list A): In a (add a l).
  Proof. { eapply set_add_intro2. auto.  } Qed.
  Hint Resolve set_add_intro set_add_intro1 set_add_intro2 set_add_intro3: hint_list.
  
  Lemma set_add_not_empty (a: A)(l:list A): add a l <> (empty).
  Proof. intro H. absurd (In a empty). simpl; auto. rewrite <- H.
         eauto with hint_list. Qed. 
    
  Lemma set_add_elim (a b: A)(l: list A): In a (add b l)-> ( a=b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (on_comp b a0).
         right;auto. destruct H. left; subst b;auto. right;auto.
         destruct H. right; subst a0; eauto with hint_list.
         apply IHl in H. destruct H; eauto with hint_list. } Qed.
  
  Lemma set_add_elim1 (a b: A)(l: list A): In a (add b l)-> ~ In a l -> a=b.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply set_add_elim;eauto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  set_add_elim2 (a b: A)(l: list A): In a (add b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply set_add_elim;eauto.
         destruct H1. absurd (a=b); auto. auto. } Qed.
  
  Hint Resolve set_add_elim set_add_elim1 set_add_elim2: hint_list.
  Lemma set_add_iff (a b:A)(l:list A): In a (add b l) <-> (a=b \/ In a l).
  Proof. split; auto with hint_list. Qed.
  
  Lemma set_add_IsOrd (a:A)(l: list A): IsOrd(l) -> IsOrd(add a l).
  Proof. { induction l. simpl. constructor.
         { intro H.  simpl. destruct (on_comp a a0).
           auto. constructor;auto.
           apply IsOrd_intro. eauto with hint_list.
           intros x H1. assert(H2: x=a \/ In x l). auto with hint_list.
           destruct H2. subst x;auto. eauto with hint_list. } } Qed.
  
  Lemma set_add_nodup (a:A)(l: list A): IsOrd l -> NoDup (add a l).
  Proof. intro H. cut (IsOrd (add a l)). auto with hint_list. apply set_add_IsOrd;auto. Qed.

  Hint Resolve set_add_IsOrd set_add_nodup : hint_list. 
 
  (* ------------ set_inter operation ----------------------------------------------  *)
  
  Fixpoint inter (l s: list A): list A:=
    match l with
    |nil => nil
    |a::l' => match mem a s with
             |true => add a (inter l' s)
             |false => (inter l' s)
             end
    end.

  Lemma set_inter_intro (a:A)(x y: list A): In a x -> In a y-> In a (inter x y).
  Proof. { induction x.
         { intro H; inversion H. }
         { intros H H1.
           assert (H2: a=a0 \/ In a x); auto with hint_list.
           destruct H2.
           { subst a0. simpl. destruct (mem a y) eqn: H2. auto with hint_list.
             absurd (mem a y). switch;auto.  apply /memP;auto. }
           { simpl. destruct (mem a0 y) eqn: H2; eauto with hint_list. } } } Qed.
  Lemma set_inter_elim1 (a:A)(x y: list A): In a (inter x y)-> In a x.
  Proof. { induction x.
         { simpl. tauto. }
         { simpl. destruct (mem a0 y).
           { intro H0. assert(H: a= a0 \/ In a (inter x y)); auto with hint_list.
             destruct H. left;symmetry;auto. right;auto. }
           { intro;right;auto. } } } Qed.
                      
  Lemma set_inter_elim2 (a:A)(x y: list A): In a (inter x y)-> In a y.
  Proof. { induction x.
         { simpl. tauto. }
         { simpl. destruct (mem a0 y) eqn: Hy.
           { intro H0. assert(H: a=a0 \/ In a (inter x y));auto with hint_list.
             destruct H. subst a; apply /memP;auto. auto. }
           { auto. } } } Qed.
  
  Lemma set_inter_elim (a:A)(x y: list A): In a (inter x y)-> (In a x /\ In a y).
  Proof. intro. split. eapply set_inter_elim1;eauto. eapply set_inter_elim2;eauto. Qed.

  Lemma set_inter_IsOrd (x y: list A): IsOrd (inter x y).
  Proof. { induction x.
         { simpl. constructor. }
         { simpl. destruct (mem a y); eauto with hint_list. } } Qed.
  
  Lemma set_inter_nodup (x y:list A): NoDup (inter x y).
  Proof. { induction x.
         { simpl. constructor. }
         { simpl.  assert (H1: IsOrd (inter x y)). apply set_inter_IsOrd.
           destruct (mem a y); eauto with hint_list. } } Qed.

  Hint Resolve set_inter_intro set_inter_elim1 set_inter_elim2: hint_list.
  Hint Resolve set_inter_IsOrd set_inter_nodup: hint_list.
  
  Lemma set_inter_comm (x y:list A): Equal (inter x y) (inter y x).
  Proof. split; intro H; cut (In a x); cut (In a y); eauto with hint_list. Qed.

  Hint Resolve set_inter_comm: hint_list.

  Lemma inter_equal (x y:list A): inter x y = inter y x.
  Proof.  assert (H1: Equal (inter x y) (inter y x)). auto with hint_list.
          cut (IsOrd (inter x y)); cut (IsOrd (inter y x)); eauto with hint_list. Qed.
  
     
  (* ------------ set_union operation ----------------------------------------------  *)

  Fixpoint union (l s: list A): list A:=
    match l with
    |nil => s
    |a::l' => add a (union l' s)
    end.

  Lemma set_union_intro1 (a:A)(l s: list A): In a l -> In a (union l s).
  Proof. { induction l. simpl. tauto.
         simpl. intro H; destruct H. subst a. auto with hint_list.
         auto with hint_list. } Qed.
  Lemma set_union_intro2 (a:A)(l s: list A): In a s -> In a (union l s).
  Proof. induction l. simpl. auto. simpl. auto with hint_list. Qed.
  
  Lemma set_union_elim (a:A)(l s:list A): In a (union l s) -> (In a l \/ In a s).
  Proof. { induction l. simpl. right;auto.
         simpl. intro H.
         assert (H1: a=a0 \/ In a (union l s)); auto with hint_list.
         destruct H1.
         { left. left. symmetry;auto. }
         { assert (H1: In a l \/ In a s);auto. destruct H1. left;right;auto.
           right;auto. } } Qed.
  Hint Resolve set_union_intro1 set_union_intro2 set_union_elim: hint_list.
  
  Lemma set_union_IsOrd (x y: list A): IsOrd y -> IsOrd (union x y).
  Proof. { induction x.
         { simpl. auto.  }
         { intros H1. simpl.  eauto with hint_list. } } Qed.
  Lemma set_union_nodup (x y: list A): IsOrd y -> NoDup (union x y).
  Proof. { induction x.
         { simpl. auto with hint_list.  }
         { intros H1. simpl. cut(IsOrd (add a (union x y))).  eauto with hint_list.
           cut (IsOrd (union x y)). eauto with hint_list. apply set_union_IsOrd;auto. } } Qed.
  Lemma set_union_comm (x y:list A): Equal (union x y) (union y x).
  Proof. { split; intro H.
         assert (H1: In a x \/ In a y); auto with hint_list.
         destruct H1; auto with hint_list.
         assert (H1: In a y \/ In a x); auto with hint_list.
         destruct H1; auto with hint_list. } Qed.
  
  Hint Resolve set_union_IsOrd set_union_nodup  : hint_list.

  Lemma union_equal (x y:list A): IsOrd x -> IsOrd y -> union x y = union y x.
  Proof. { intros.
         cut (Equal (union x y) (union y x)).
         cut (IsOrd (union x y)). cut (IsOrd (union y x)).
         eauto with hint_list. all: eauto with hint_list.
         apply set_union_comm. } Qed.
  
  Hint Resolve inter_equal union_equal set_union_comm: hint_list.

  
  (* ------------ set_diff operation -----------------------------------------------  *)

  Fixpoint diff (l s: list A): list A:=
    match l with
    |nil=> nil
    |a::l' => match (mem a s) with
             |true => diff l' s
             |false => add a (diff l' s)
             end
    end.

  Lemma set_diff_intro (a: A)(l s: list A): In a l -> ~In a s -> In a (diff l s).
  Proof. { induction l.
         { simpl. auto. }
         { intros H H1. simpl.
           assert (H0: a=a0 \/ In a l); auto with hint_list.
           destruct H0.
           destruct (mem a0 s) eqn:H2.
           { absurd ( In a0 s). subst a0;auto. apply /memP;auto. }
           { subst a0. auto with hint_list. }
           destruct (mem a0 s) eqn:H2. eauto.
           cut (In a (diff l s)); auto with hint_list. } } Qed.
           
  Lemma set_diff_elim1 (a:A)(l s: list A): In a (diff l s) -> In a l.
  Proof. { induction l. simpl; auto.
         { simpl. destruct (mem a0 s) eqn: H0.
           intro; right; auto. intro H1.
           assert (H2: a= a0 \/ In a (diff l s)); auto with hint_list.
           destruct H2. left; symmetry;auto. right;auto. } } Qed.
  Lemma set_diff_elim2 (a:A)(l s: list A): In a (diff l s) -> ~In a s.
  Proof. { induction l. simpl;auto.
         { simpl. destruct (mem a0 s) eqn: H0.
           auto. intro H1. assert (H2: a= a0 \/ In a (diff l s)). auto with hint_list.
           destruct H2. subst a. move /memP. switch_in H0. auto. auto. } } Qed.
  Lemma set_diff_empty (a:A)(l: list A): ~ In a (diff l l).
  Proof. intro H. absurd (In a l). eapply set_diff_elim2;eauto.
         eapply set_diff_elim1;eauto. Qed.

  Hint Resolve set_diff_elim1 set_diff_elim2 set_diff_intro set_diff_empty: hint_list.

  Lemma set_diff_IsOrd (l s: list A): IsOrd (diff l s).
  Proof. { induction l.
           { simpl. constructor. }
           { simpl. destruct (mem a s); eauto with hint_list. } } Qed.
  
  Lemma set_diff_nodup (l s: list A): NoDup (diff l s).
  Proof. cut (IsOrd (diff l s)). auto with hint_list. apply set_diff_IsOrd. Qed.

  Hint Resolve set_diff_IsOrd set_diff_nodup: hint_list.
          
End OrderedSet.


  

Hint Resolve set_add_intro set_add_intro1 set_add_intro2 set_add_intro3: hint_list.
Hint Resolve set_add_elim set_add_elim1 set_add_elim2: hint_list.
Hint Resolve set_add_IsOrd set_add_nodup: hint_list.

Hint Resolve set_inter_intro set_inter_elim1 set_inter_elim2 set_inter_comm: hint_list.
Hint Resolve set_inter_IsOrd set_inter_nodup : hint_list.

Hint Resolve set_union_intro1 set_union_intro2 set_union_elim set_union_comm: hint_list.
Hint Resolve set_union_IsOrd set_union_nodup  : hint_list.

Hint Resolve inter_equal union_equal: hint_list.

Hint Resolve set_diff_elim1 set_diff_elim2 set_diff_intro set_diff_empty: hint_list.
Hint Resolve set_diff_IsOrd set_diff_nodup: hint_list.