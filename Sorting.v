




(* ------   In this file we formalize the concept of sorting in a list.  We consider lists
   of elements (on an arbitrary type A) with a boolean comparison operator (lr: A-> A-> bool).
   Most of  the results in this file assumes only   
   1. reflexive, 
   2. transitive and 
   3. complete 
   nature of the boolean operator lr. 
   Only the last result (equality of head) assumes the antisymmetric
   property of lr. 

   Following are the concepts formalized in this file: 

   sorted l      <==> l is sorted w.r.t comp operator lr 
   putin a l      ==> puts the element a into a sorted list at its correct position w.r.t lr
   sort l         ==> sorts the list l w.r.t the comp operator lr 

   Some of the useful results in this file are:

   Lemma putin_correct (H_trans: transitive lr)(H_comp: complete lr):
    forall (a:A) (l: list A), sorted l -> sorted (putin a l).

   Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).

   Lemma sort_correct (H_trans: transitive lr)(H_comp: complete lr):
    forall(l: list A), sorted (sort l).

   Lemma sort_equal (l: list A): Equal l (sort l).

   Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l). ------------------  *)



Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Omega.

Set Implicit Arguments.

Section Sorting.
  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  
 (* ------------- sorting a list of elements by lr relation ------------------------------*)
  
  Inductive  sorted : list A-> Prop:=
  | nil_sorted: sorted nil
  | cons_sorted (a:A)(l: list A): sorted l -> (forall x, (In x l -> (a <=r x))) -> sorted (a::l).

  Lemma sorted_intro (a:A)(b:A)(l: list A)(Htrans: transitive lr):
    a <=r b -> sorted (b::l)-> sorted (a::b::l).
  Proof. { intros H H0. constructor. auto. intros x H1. destruct H1. subst x. auto.
         eapply Htrans with (y:=b). eauto. inversion H0. eauto. } Qed.


  Lemma sorted_elim1 (a:A) (b:A) (l: list A): (sorted (a::b::l)) -> (a <=r b).
  Proof. intro H. inversion H.  eapply H3. auto.  Qed.
  Lemma sorted_elim4 (a:A) (l:list A): sorted (a::l) ->(forall x, In x l -> a <=r x).
  Proof. intro H. inversion H. auto. Qed.
  Lemma sorted_elim2 (a:A) (l:list A)(Hrefl: reflexive lr):
    sorted (a::l) ->(forall x, In x (a::l) -> a <=r x).
  Proof. intro H. inversion H. intros. destruct H4. subst x. eauto. eauto. Qed.
  Lemma sorted_elim3 (a:A) (l:list A): (sorted (a::l)) -> sorted l.
  Proof. intro H. inversion H;auto. Qed.
  Lemma sorted_single (a:A) : (sorted (a::nil)).
  Proof. constructor. constructor. intros;simpl;contradiction. Qed.

  Hint Resolve sorted_elim1 sorted_elim2 sorted_elim3 sorted_elim4
       sorted_single sorted_intro: core.

     
  Fixpoint putin (a: A) (l: list A) : list A:=
    match l with
    |nil=> a::nil
    |b::l1 => match a <=r b with
             |true => a::l
             |false => b::(putin a l1)
                    end
    end.

  Lemma putin_intro (a:A) (l: list A): forall x, In x l -> In x (putin a l).
  Proof. { intros x H. induction l. simpl in H. contradiction. simpl.
           destruct ( a <=r a0). destruct H. subst x. all: auto.  destruct H. subst x; auto.
          apply IHl in H as H1;auto.  } Qed.
         
  Lemma putin_intro1 (a:A) (l: list A): In a (putin a l).
  Proof. { induction l. simpl. tauto. simpl. destruct ( a <=r a0). all: auto.  } Qed.

  Lemma putin_elim (a:A) (l: list A): forall x, In x (putin a l) -> (x=a)\/(In x l).
  Proof. { intros x H. induction l. simpl in H. simpl. destruct H. left. auto. auto.
           simpl in H. destruct ( a <=r a0).   destruct H. auto. auto. destruct H.
           right;subst x;auto. apply IHl in H as H2. destruct H2. auto. right. auto.  } Qed.
   
  Definition complete (lr: A->A-> bool) := forall x y, lr x y=false -> lr y x.
 
  Lemma putin_correct (H_trans: transitive lr)(H_comp: complete lr):
    forall (a:A) (l: list A), sorted l -> sorted (putin a l).
  Proof. { intros a l. revert a.  induction l.
         { intros a1 H.  simpl. apply sorted_single. }
           simpl. intros a1 H.  destruct ( a1 <=r a) eqn:H0.
         {  auto.  }
         { cut ( a <=r a1 = true).
           intro H1.  constructor. eauto. 
           intros x H2. apply putin_elim in H2 as H3. destruct H3.
           subst x;auto. eauto.  apply H_comp. eauto. } } Qed.
  
  Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).
  Proof.  { revert a. induction l.
          { simpl. auto. }
          { intros a0 H. assert (Ha: NoDup (a::l)).  eauto. 
            simpl. destruct (a0 <=r a) eqn: H1. auto.
            constructor.
            { intro H2. assert ( H2a: a=a0 \/ In a l). eauto using putin_elim.
              destruct H2a. subst a. inversion H. eauto.  inversion Ha; contradiction. }
            apply IHl. inversion H. constructor; eauto.  } } Qed.

  
  
  Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin: core.


   Fixpoint sort (l: list A): list A:=
    match l with
    |nil => nil
    |a::l1 => putin a (sort l1)
    end.
  
  
  Lemma sort_intro (l: list A): forall x, In x l -> In x (sort l).
  Proof. { intros x H. induction l. eauto. simpl. destruct H. subst x.
         apply putin_intro1. eauto using putin_intro. } Qed.

  Lemma sort_elim (l: list A): forall x, In x (sort l) -> In x l.
  Proof. { intros x H. induction l. simpl in H. contradiction.
         simpl in H. apply putin_elim in H. destruct H. subst x;eauto. eauto. } Qed.

  Lemma sort_correct (H_trans: transitive lr)(H_comp: complete lr):
    forall(l: list A), sorted (sort l).
  Proof. induction l. simpl. constructor. simpl. eauto using putin_correct. Qed.

  Hint Resolve sort_elim sort_intro sort_correct: core.
  
  Lemma sort_equal (l: list A): Equal l (sort l).
  Proof. split;intro; eauto. Qed.

   Lemma sort_equal1 (l: list A): Equal (sort l) l.
  Proof. split;intro; eauto. Qed.

  Lemma sort_same_size (l: list A): |sort l| = |l|.
  Proof. Admitted.

  Lemma sorted_equal (l l': list A): Equal l l' -> Equal l (sort l').
  Proof. intro. cut (Equal l' (sort l')). eauto.  apply sort_equal. Qed.
  Lemma sorted_equal1(l l': list A): Equal l l' -> Equal (sort l) l'.
  Proof. intro. cut (Equal l (sort l)). eauto. apply sort_equal. Qed.

  Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l).
  Proof. { induction l. eauto.
         {  simpl. intro H.  cut (NoDup (a::sort l)). eauto.
            constructor.
            { intro H1. absurd (In a l). inversion H; auto. eapply  sort_equal;auto. }
            eauto. } } Qed.

  (*--upto this point only reflexive, transitive and complete property of <=r is needed--- *)

 
  (* ---------------------head in sorted lists l and l'-------------------------- *)

   Definition empty: list A:= nil.
  
  Lemma empty_equal_nil_l (l: list A): l [=] empty -> l = empty.
  Proof. { case l. auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.


  
   (*-------- antisymmetric requirement is only needed in the following lemma--------*)
  Lemma head_equal_l (a b: A)(l s: list A)(Href: reflexive lr)(Hanti: antisymmetric lr):
    sorted (a::l)-> sorted (b::s)-> Equal (a::l) (b::s)-> a=b.
  Proof. { intros H H1 H2. 
         assert(H3: In b (a::l)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H3A: a <=r b). eapply sorted_elim2;eauto.
         assert(H4: In a (b::s)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H4A: b <=r a). eapply sorted_elim2;eauto.
         eapply Hanti. split_;auto. } Qed.  

End Sorting. 


Hint Resolve sorted_elim1 sorted_elim2 sorted_elim3 sorted_elim4
     sorted_single sorted_intro: core.
Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin : core.
Hint Resolve sort_elim sort_intro sort_correct sort_same_size : core.
Hint Resolve sort_equal sort_equal1 sorted_equal sorted_equal1 nodup_sort: core.
Hint Resolve empty_equal_nil_l head_equal_l: core.




(*
 Definition l := 12::42::12::11::20::0::3::30::20::0::nil.
 Eval compute in (sort (fun x y => Nat.ltb y x) l).
 Eval compute in (sort (fun x y => ~~ (Nat.ltb x y)) l).
*)
 

