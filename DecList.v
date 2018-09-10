



(* 
 Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).


 Lemma list_del_IsOrd (a:A)(l: list A): IsOrd l -> IsOrd (del_all a l).
 Lemma list_del_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).   *)







Require Export Lists.List.
Require Export GenReflect SetSpecs DecType.
Require Export SetReflect.

Set Implicit Arguments.

Section DecLists.

  Context { A: eqType }.

  Definition empty: list A:= nil.
  
  Lemma empty_equal_nil (l: list A): l [=] empty -> l = empty.
  Proof. { case l.  auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.

    
(*------------------ Uniform list -----------------------------------------------------*)

Inductive uniform : list A -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:A): uniform (a::nil)
|Ind_uni(a b:A)(l:list A): a=b -> uniform (b::l)-> uniform (a::b::l).

Lemma uniform_elim (a:A)(l: list A): uniform (a::l)-> (forall x, In x l -> x=a).
Proof. Admitted.
Lemma uniform_elim1 (a:A)(l: list A): uniform (a::l)-> (forall x, In x (a::l)-> x=a).
Proof. Admitted.
Lemma uniform_elim2 (a:A) (l: list A): uniform (a::l)-> uniform l.
Proof. Admitted.
Lemma uniform_intro (a:A)(l: list A): (forall x, In x l -> x=a) -> uniform (a::l).
Proof. Admitted.


 
 
  (* -------------- list_insert operation and its properties---------------------------  *)
  Fixpoint insert (a:A)(l: list A): list A :=
    match l with
    |nil => a::nil
    |a1::l1 => match a == a1 with
              |true => a1::l1
              |false => a1:: (insert a l1)
              end
    end.
  (* this function adds an element correctly even in an unsorted list *)
  Lemma insert_intro1 (a b: A)(l: list A): In a l -> In a ( insert b l).
  Proof. { intro H. induction l.  inversion H.
         destruct H.
         { subst a0. simpl; destruct (b == a); eauto. }
         { simpl; destruct (b == a0); eauto. } } Qed.
  
  Lemma insert_intro2 (a b: A)(l: list A): a=b -> In a (insert b l).
  Proof. { intro. subst a. induction l.
         simpl. left;auto. simpl. destruct (b == a) eqn:H. move /eqP in H.
         subst b; auto. all: auto. } Qed.
  Lemma insert_intro (a b: A)(l: list A): (a=b \/ In a l) -> In a (insert b l).
  Proof. intro H. destruct H.  eapply insert_intro2;auto.  eapply insert_intro1;auto. Qed.
  Lemma insert_intro3 (a:A)(l: list A): In a (insert a l).
  Proof. { eapply insert_intro2. auto.  } Qed.
  Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: core.
  
  Lemma insert_not_empty (a: A)(l:list A): insert a l <> (empty).
  Proof. intro H. absurd (In a empty). simpl; auto. rewrite <- H.
         eauto.  Qed. 
    
  Lemma insert_elim (a b: A)(l: list A): In a (insert b l)-> ( a=b \/ In a l).
  Proof. { induction l.
         simpl. left. symmetry. tauto. intro H.
         simpl in H. destruct (b == a0) eqn: eqH.  
         right;auto. destruct H. right;subst a0;auto.
         cut (a=b \/ In a l). intro H1;destruct H1. left;auto. right; eauto.
         auto.  } Qed. 
  
  Lemma insert_elim1 (a b: A)(l: list A): In a (insert b l)-> ~ In a l -> a=b.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. auto. absurd (In a l);auto. } Qed.
  Lemma  insert_elim2 (a b: A)(l: list A): In a (insert b l)-> a<>b-> In a l.
  Proof. { intros H H0.
         assert (H1: a=b \/ In a l). eapply insert_elim;eauto.
         destruct H1. absurd (a=b); auto. auto. } Qed.
  
  Hint Resolve insert_elim insert_elim1 insert_elim2: core.
  Lemma insert_iff (a b:A)(l:list A): In a (insert b l) <-> (a=b \/ In a l).
  Proof. split; auto. Qed.

  
  Lemma insert_nodup (a:A)(l: list A): NoDup l -> NoDup (insert a l).
  Proof. { induction l. simpl. constructor;auto.
         { intro H. simpl. destruct (a == a0) eqn: eqH.
           { auto. }
           { constructor. intro H1.
           assert (H2: a0 =a \/ In a0 l); eauto.
           destruct H2. subst a0. switch_in eqH. apply eqH. eauto. 
           absurd (In a0 l); auto. eauto. } } } Qed.
  
  Hint Resolve insert_nodup : core.

    
  (*------------ list remove operation on ordered list ----------------------------------- *)
   Fixpoint delete (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match a == a1 with
               |true => l1
               |false => a1:: delete a l1
               end
    end.
   (* This function deletes only the first occurence of 'a' from the list l *)
  
  Lemma delete_elim1 (a b:A)(l: list A): In a (delete b l)-> In a l.
  Proof. { induction l. simpl. auto.
         { simpl. destruct (b == a0) eqn: eqH.
           { right;auto. }
           { intro H1. destruct H1. left;auto. right;auto. } } } Qed.
  
  Lemma delete_elim2 (a b:A)(l: list A): NoDup l -> In a (delete b l)-> (a<>b).
  Proof. { induction l. simpl. auto.
         { simpl. destruct  (b == a0) eqn: eqH.
           { intros H1 H2. move /eqP in eqH. subst b. intro H3. subst a.
             absurd (In a0 l); eauto. }
           { intros H1 H2. destruct H2. intro. subst a0; subst a.
             switch_in eqH. apply eqH. eauto. eauto. } } } Qed.
  
  Lemma delete_intro (a b: A)(l:list A): In a l -> a<>b -> In a (delete b l).
  Proof. { induction l. simpl.  auto.
         { simpl. destruct (b == a0) eqn: eqH.
           { intros H1 H2. destruct H1. move /eqP in eqH. subst a; subst b.
             absurd (a0=a0); auto. auto. }
           { intros H1 H2. simpl. destruct H1. left;auto. right;auto. } } } Qed.
  Lemma delete_size (a:A) (l:list A): |delete a l| <=|l|.
  Proof. Admitted.
            
  Hint Resolve delete_elim1 delete_elim2 delete_intro delete_size: core.
  Lemma delete_iff (a b:A)(l: list A): NoDup l -> (In a (delete b l) <-> (In a l /\ a<>b)).
  Proof. intro H. split. eauto.
         intro H0. destruct H0 as [H0 H1]. eauto.  Qed. 
  

   Lemma delete_nodup (a:A)(l: list A): NoDup l -> NoDup (delete a l).
  Proof.  { induction l. simpl. constructor.
          { intro H. simpl. destruct (a == a0) eqn: eqH. 
            { eauto. }
            {  switch_in eqH. constructor. intro H1. absurd (In a0 l). all: eauto. } } } Qed.
              

  Hint Resolve delete_nodup: core.

  (* ----------------- delete_all operation ---------------------------------------------  *)
  
  Fixpoint del_all (a:A)(l: list A): list A:=
    match l with
    |nil => nil
    | a1::l1 => match  (a == a1) with
               |true => del_all a l1
               |false => a1 :: del_all a l1
               end
    end.
  
  (* This function deletes all occurences of a in the list l *)

  
  Lemma del_all_elim1 (a b:A)(l: list A): In a (del_all b l)-> In a l.
  Proof. Admitted.
  Lemma del_all_elim2 (a b:A)(l: list A): In a (del_all b l)-> (a<>b).
  Proof. Admitted.

  Lemma del_all_intro (a b: A)(l:list A): In a l -> a<>b -> In a (del_all b l).
  Proof. Admitted.
  Lemma del_all_iff (a b:A)(l: list A): (In a (del_all b l) <-> (In a l /\ a<>b)).
  Proof. Admitted.

  Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
  
  Lemma del_all_nodup (a:A)(l: list A): NoDup l -> NoDup (del_all a l).
  Proof. Admitted.

  Hint Resolve del_all_nodup: core.

  (* ------- count of an element a in the list l ----------------------------------------*)

  Fixpoint count (a:A) (l:list A) : nat:= match l with
                          | nil => 0
                          |a1::l1 => match a == a1 with
                                    |true => S (count a l1)
                                    |false => count a l1
                                    end
                                        end.
  Lemma countP1 (a:A) (l:list A): In a l -> (count a l >= 1).
  Proof. Admitted.
  Lemma countP2 (a:A)(l: list A): ~ In a l -> (count a l = 0).
  Proof. Admitted.
  Lemma countP3 (a:A)(l: list A): (count a l = 0) -> ~ In a l.
  Proof. Admitted.
  Lemma countP4 (a:A)(l: list A): count a (a::l) = S (count a l).
  Proof. Admitted.
  Lemma countP5 (a b:A)(l: list A): (count a l) <= count a (b::l).
  Proof. Admitted.
  Lemma countP6 (a: A)(l: list A): count a l <= |l|.
  Proof. Admitted.
  Lemma countP7 (a:A) (l:list A): In a l -> count a l = S(count a (delete a l)).
  Proof. Admitted.
  Lemma countP8 (a:A) (l:list A): forall x, x<>a-> count x (a::l) = count x l.
  Proof. Admitted.
  Lemma countP9 (a:A) (l:list A): forall x, x<>a -> count x l = count x (delete a l).
  Proof. Admitted.
  Lemma countP10 (a:A)(l s:list A): count a l <= count a s -> count a (a::l) <= count a (a::s).
  Proof. Admitted.
  Lemma countP11 (a:A)(l s: list A): count a l = count a s -> count a (a::l) = count a (a::s).
  Proof. Admitted.
  Lemma countP12 (a:A)(l s: list A): count a l < count a s -> count a (a::l) < count a (a::s).
  Proof. Admitted.
  
  
  
  Hint Immediate countP1 countP2 countP3: core.
  Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9: core.
 

End DecLists.



 Hint Resolve insert_intro insert_intro1 insert_intro2 insert_intro3: core.
 Hint Resolve insert_elim insert_elim1 insert_elim2: core.
 Hint Resolve insert_nodup :core.

 Hint Resolve delete_elim1 delete_elim2 delete_intro delete_size: core.
 Hint Resolve delete_nodup: core.

 Hint Resolve del_all_elim1 del_all_elim2 del_all_intro: core.
 Hint Resolve del_all_nodup: core.

 Hint Immediate countP1 countP2 countP3: core.
 Hint Resolve countP4 countP5 countP6 countP7 countP8 countP9:  core.
 Hint Resolve countP10 countP11 countP12: core.



  