


(* -------------------------Description--------------------------------------

   This file contains formalization of sorting for a list of elements of ordType
  
 max_in l d        ==> returns the maximum in list l (returns d if l is nil)
 min_in l d        ==> returns the minimum in list l (returns d if l is nil) 
 Sorted l         <==> l is sorted according to <=b relation
 put_in a l        ==> put a in correct place in a sorted list l
 sort_i l          ==> sort the list l in increasing order w.r.t <=b comp operator

 

--------------------------------------------------------------------------- *)

Require Export Lists.List.
Require Export GenReflect SetSpecs OrdType.
Require Export Omega.



Set Implicit Arguments.

Section ListSorting.
  Context { A: ordType }. (* to declare A as implicit outside the section *)

  (*-----------max_in and min_in functions on lists with ordType elements ---------------  *)

  Check hd. Check max.
  
   Fixpoint max_in (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => max_of a (max_in l' a)
    end.
   
   Lemma max_spec (l:list A)(d:A)(a:A): In a l -> (a <b (max_in l d) \/ a = (max_in l d)).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl.
            assert (H1: a = a0 \/ In a l). auto with hint_list. 
            destruct H1. subst a. eauto. 
            assert (H1: a<b max_in l a0 \/ a = max_in l a0). eauto.
            destruct H1. left. eauto. rewrite <- H1. eauto. } } Qed.
  Lemma max_in_elim (a:A) (l:list A) (d:A) : In (max_in (a::l) d) (a::l).
     Proof. { revert a. revert d. induction l.
            { simpl. intros; left. eauto. }
            { intros d a0. replace (max_in (a0 :: a :: l) d) with (max_of a0 (max_in (a::l) a0)).
              unfold max_of. match_up a0 (max_in (a::l) a0); eauto with hint_list.
              simpl;auto. } } Qed.
     
 Hint Resolve max_spec max_in_elim: hint_list.

     
   Fixpoint min_in (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => min_of a (min_in l' a)
    end.

   Lemma min_spec (l:list A)(d:A)(a:A): In a l -> ((min_in l d) <b a \/ (min_in l d)= a).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl.
            assert (H1: a = a0 \/ In a l). auto with hint_list. 
            destruct H1. subst a. eauto. 
            assert (H1: min_in l a0 <b a \/ min_in l a0 = a). eauto.
            destruct H1. left. eauto. rewrite H1. eauto. } } Qed.

   Lemma min_in_elim (a:A) (l:list A) (d:A): In (min_in (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left. eauto. }
            { intros d a0. replace (min_in (a0 :: a :: l) d) with (min_of a0 (min_in (a::l) a0)).
              unfold min_of. match_up a0 (min_in (a::l) a0); eauto with hint_list.
              simpl;auto. } } Qed.
   
   Hint Resolve min_spec min_in_elim: hint_list.

   (* ------------- sorting a list of elements with ordType------------------------------*)
  
  Inductive  Sorted : list A-> Prop:=
  | nil_sorted: Sorted nil
  | cons_sorted (a:A)(l: list A): Sorted l -> (forall x, (In x l -> (a <=b x))) -> Sorted (a::l).

  Lemma Sorted_elim1 (a:A) (b:A) (l: list A): (Sorted (a::b::l)) -> (a <=b b).
  Proof. intro H. inversion H.  eapply H3. eauto with hint_list. Qed.

   Lemma Sorted_elim2 (a:A) (l:list A):
    Sorted (a::l) ->(forall x, In x (a::l) -> a <=b x).
  Proof. intro H. inversion H. intros. destruct H4. subst x. eauto. eauto. Qed.
  
  Lemma Sorted_elim2a (a:A) (d:A) (l:list A): (Sorted (a::l)) -> a = (min_in (a::l) d). 
  Proof. {
    intro H. inversion H.
    assert (H4: In (min_in (a::l) d) (a::l)). eauto with hint_list.
    destruct H4. auto.
    apply H3 in H4 as H5. assert (H6: (min_in (a::l) d) <=b a).
    Check min_spec. apply /orP.
    cut (min_in (a :: l) d <b a \/ min_in (a :: l) d = a).
    intro H6; destruct H6. left;auto. right; apply /eqP;auto.
    apply min_spec. eauto with hint_list.
    move /orP in H5; move /orP in H6.
    destruct H5; destruct H6. absurd (min_in (a :: l) d <b a);eauto.
    move /eqP in H6. auto. all: apply /eqP; eauto using H5.  } Qed.

  Lemma Sorted_elim3 (a:A) (l:list A): (Sorted (a::l)) -> Sorted l.
  Proof. intro H. inversion H;auto. Qed.
  
  Lemma Sorted_elim4 (a:A) (l:list A): Sorted (a::l) ->(forall x, In x l -> a <=b x).
  Proof. intro H. inversion H. auto. Qed.

  Lemma Sorted_single (a:A) : (Sorted (a::nil)).
  Proof. constructor. constructor. intros;simpl;contradiction. Qed.

  Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim2a Sorted_elim3 Sorted_elim4: hint_list.
  Hint Resolve Sorted_single: hint_list.

     
  Fixpoint put_in (a: A) (l: list A) : list A:=
    match l with
    |nil=> a::nil
    |b::l1 => match comp a b with
             |Lt => a::l
             |Eq => a::l
             |Gt => b::(put_in a l1)
                    end
    end.

  Lemma put_in_intro (a:A) (l: list A): forall x, In x l -> In x (put_in a l).
  Proof. { intros x H. induction l. simpl in H. contradiction. simpl. match_up a a0.
          destruct H. subst x. (eauto with hint_list).
         eauto with hint_list. eauto with hint_list. destruct H. subst x;
         eauto with hint_list. apply IHl in H as H1;eauto with hint_list. } Qed.
         
  Lemma put_in_intro1 (a:A) (l: list A): In a (put_in a l).
  Proof. { induction l. simpl. tauto. simpl. destruct (on_comp a a0). eauto with hint_list.
         eauto with hint_list. eauto with hint_list. } Qed.

  Lemma put_in_elim (a:A) (l: list A): forall x, In x (put_in a l) -> (x=a)\/(In x l).
  Proof. { intros x H. induction l. simpl in H. simpl. destruct H. left. auto. auto.
         simpl in H. match_up a a0.   destruct H. auto. auto. eauto with hint_list.
         destruct H. right;subst x ;auto. eauto with hint_list. apply IHl in H as H2.
         destruct H2. auto. right. eauto with hint_list. } Qed.

  Lemma put_in_correct : forall (a:A) (l: list A), Sorted l -> Sorted (put_in a l).
  Proof. { intros a l. revert a. revert l. induction l.
         { intros a1 H.  simpl. apply Sorted_single. }
         simpl. intros a1 H.  destruct (on_comp a1 a).
         subst a1.
         { constructor. auto. inversion H. intros x H4. destruct H4. subst x.
           apply /orP. right. apply /eqP;auto. auto. }
         { constructor. auto.  intros x H2. destruct H2. subst x.
           apply /orP. left. auto. inversion H. apply H5 in H1 as H6.
           move /orP in H6. apply /orP.
           destruct H6. left;auto. eauto. left. move /eqP in H6. subst x. auto. }
         { assert (H1: Sorted l). eapply Sorted_elim3. eauto.
           eapply IHl  with (a:=a1) in H1 as H2. constructor. auto. intros x H3.
           apply put_in_elim in H3.  destruct  H3. subst x. apply /orP.  auto.
           eauto using Sorted_elim4. } } Qed.

  Hint Resolve put_in_intro put_in_intro1 put_in_elim put_in_correct: hint_list.
           
  Fixpoint sort_i (l: list A): list A:=
    match l with
    |nil => nil
    |a::l1 => put_in a (sort_i l1)
    end.
  
  
  Lemma sort_i_intro (l: list A): forall x, In x l -> In x (sort_i l).
  Proof. { intros x H. induction l. eauto. simpl. destruct H. subst x.
         apply put_in_intro1. eauto using put_in_intro. } Qed.

  Lemma sort_i_elim (l: list A): forall x, In x (sort_i l) -> In x l.
  Proof. { intros x H. induction l. simpl in H. contradiction.
         simpl in H. apply put_in_elim in H. destruct H. subst x;eauto with hint_list.
         eauto with hint_list. } Qed.

  Lemma sort_i_is_correct (l: list A): Sorted (sort_i l).
  Proof. induction l. simpl. constructor. simpl. eauto using put_in_correct. Qed.

  Hint Resolve sort_i_intro sort_i_elim sort_i_is_correct: hint_list.
  

End ListSorting.



Hint Resolve max_spec max_in_elim: hint_list. 
Hint Resolve min_spec min_in_elim: hint_list.

Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim2a Sorted_elim3 Sorted_elim4: hint_list.
Hint Resolve Sorted_single: hint_list.

Hint Resolve put_in_intro put_in_intro1 put_in_elim put_in_correct: hint_list.
Hint Resolve sort_i_intro sort_i_elim sort_i_is_correct: hint_list.


 
 (* Definition l := 12::42::12::11::20::0::3::30::20::0::nil.
 Eval compute in (sort_i l).  *)