





Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.
Require Export            SetReflect OrdList.
Require Export Omega.



Set Implicit Arguments.

Section FromOrdSet.
  Context { A: ordType }.



   (* -------------- list_add operation and its properties---------------------------  *)
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
  Lemma list_add_intro1 (a b: A)(l: list A): In a l -> In a ( insert b l).
  Proof. { intro H. induction l.  inversion H.
         destruct H.
         { subst a0. simpl; destruct (on_comp b a); eauto with hint_list. }
         { simpl; destruct (on_comp b a0); eauto with hint_list. } } Qed.
  
  Lemma list_add_intro2 (a b: A)(l: list A): a=b -> In a (insert b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (on_comp b a).
         subst b; auto with hint_list. all: auto with hint_list. } Qed.
  Lemma list_add_intro (a b: A)(l: list A): (a=b \/ In a l) -> In a (insert b l).
  Proof. intro H. destruct H.  eapply list_add_intro2;auto.  eapply list_add_intro1;auto. Qed.
  Lemma list_add_intro3 (a:A)(l: list A): In a (insert a l).
  Proof. { eapply list_add_intro2. auto.  } Qed.
  Hint Resolve list_add_intro list_add_intro1 list_add_intro2 list_add_intro3: hint_list.
  
  Lemma list_add_not_empty (a: A)(l:list A): insert a l <> (empty).
  Proof. intro H. absurd (In a empty). simpl; auto. rewrite <- H.
         eauto with hint_list. Qed. 
    
  Lemma list_add_elim (a b: A)(l: list A): In a (insert b l)-> ( a=b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (on_comp b a0).  
         right;auto. destruct H. right;subst a0;auto with hint_list.
         cut (a=b \/ In a l). intro H1;destruct H1. left;auto. right; eauto with hint_list.
         auto.  destruct H. right; subst a0; eauto with hint_list.
         apply IHl in H. destruct H; eauto with hint_list. } Qed.
  
  Lemma list_add_elim1 (a b: A)(l: list A): In a (insert b l)-> ~ In a l -> a=b.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply list_add_elim;eauto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  list_add_elim2 (a b: A)(l: list A): In a (insert b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply list_add_elim;eauto.
         destruct H1. absurd (a=b); auto. auto. } Qed.
  
  Hint Resolve list_add_elim list_add_elim1 list_add_elim2: hint_list.
  Lemma list_add_iff (a b:A)(l:list A): In a (insert b l) <-> (a=b \/ In a l).
  Proof. split; auto with hint_list. Qed.


  End FromOrdSet.