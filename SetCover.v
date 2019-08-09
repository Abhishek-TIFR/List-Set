

(*-------------Description ------------------------------------------------------  

This file implements the union of all sets present in a list (union_over). We 
also define the notion of sets covers (Set_Cov C S) as a proposition which 
states that the collection of sets C is a cover for the set S. 
 

Following are the notions defined in this file:

 Fixpoint pw (l: list A): list (list A):=
                                       match l with
                                          |nil => nil::nil
                                          |a::l' => union (a [::] (pw l')) (pw l')
                                       end.


 Predicate                  Boolean function                  Connecting Lemma
 Max_sub_in G I P           max_sub_in G I P                  max_sub_inP 
 Min_sub_in G I P           min_sub_in G I P                  min_sub_inP


Furthermore, we have results on existence of largest and smallest subsets with 
the property P

Lemma exists_largest_inb (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |Y| <=b |I|).

Lemma exists_largest_in (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |Y| <= |I|).

Lemma exists_smallest_inb (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |I| <=b |Y|).

Lemma exists_smallest_in (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |I| <= |Y|).


---------------------------------------------------------------------------------*)


Require Export Omega.
Require Export SetMaps.
Require Export Powerset.

Set Implicit Arguments.

Section SetCover.

  Context { A: ordType }.

  (* ------------ Definition of union of all the sets present in the list l ----------- *)
  

  Fixpoint union_over (C: list (list A)): list A:= match C with
                                                   | nil => nil
                                                   |c::C' => c [u] (union_over C')
                                                   end.

  Lemma union_over_intro (C: list (list A))(l: list A)(a: A):
    In a l -> In l C -> In a (union_over C).
  Proof.  { induction C as [| c C'].
            { simpl. auto. }
            { intros h1 h2. destruct h2 as [h2 | h2].
              { subst c. simpl. auto. }
              { simpl. specialize (IHC' h1 h2) as h3. auto. } } } Qed.

  Lemma union_over_intro1 (C: list (list A))(l: list A): In l C -> l [<=] (union_over C). 
  Proof. intros h1 a h2. eapply union_over_intro;eauto. Qed.

  Lemma union_over_elim (C: list (list A))(a: A):
    In a (union_over C)-> (exists (l: list A), In l C /\ In a l).
  Proof.  { induction C as [| c C'].
            { simpl. intro h1. destruct h1.  }
            { simpl. intros h1.
              assert (h2: In a c \/ In a (union_over C')). auto.
              destruct h2 as [h2 | h2].
              { exists c. split. left;auto. auto. }
              { specialize (IHC' h2) as h3. destruct h3 as [l h3].
                exists l. split. right;apply h3. apply h3. } } } Qed.

  Hint Resolve union_over_intro union_over_intro1: core.
  Hint Immediate union_over_elim: core.

  (*------------- Definition of (fix_nat n l) which appends n behind each entry in l ----- *)

  Fixpoint fix_nat (n:nat)(l: list A): list (A * nat):= match l with
                                                    |nil => nil
                                                    |a::l' => (a,n)::(fix_nat n l')
                                                    end.

  Lemma fix_nat_intro (n: nat)(l: list A)(x: A): In x l -> In (x,n) (fix_nat n l).
  Proof. { induction l as [|a l' ].
           { simpl. auto. }
           { simpl. intros h1.
             destruct h1 as [h1 | h1].
             subst a. left;auto. right;auto. } } Qed.

  Lemma fix_nat_elim (n: nat)(l: list A)(x: A): In (x,n) (fix_nat n l)-> In x l.
  Proof.  { induction l as [|a l' ].
           { simpl. auto. }
           { simpl. intros h1.
             destruct h1 as [h1 | h1].
             left;inversion h1;auto. right;auto. } } Qed.

  Lemma fix_nat_size (n: nat)(l: list A): | l | = | fix_nat n l |.
  Proof.  { induction l as [|a l' ].
           { simpl. auto. }
           { simpl. omega.  } } Qed.


  (*---- Definition of (mk_disj C) which makes each list in C disjoint with each other------*)

  Fixpoint mk_disj (C: list (list A)): list (list (A*nat))
    := match C with
       |nil => nil
       |l::C' => (fix_nat (idx l C) l) :: (mk_disj C')
       end.

  Lemma mk_disj_intro (C:list (list A))(l:list A): In l C -> In (fix_nat (idx l C) l) (mk_disj C).
  Proof. Admitted.

  Lemma mk_disj_elim (C: list (list A))(l:list (A * nat)):
    In l (mk_disj C) -> (exists l0, In l0 C /\ l = fix_nat (idx l0 C) l0).
  Proof. Admitted.

  Lemma mk_disj_size (C: list (list A)): | C | = | mk_disj C |.
  Proof. Admitted.

  (*--------------- Definition of (set_cover C l) ---------------------------------------*)

  Definition set_cover (C: list (list A)) (l: list A):= equal l (union_over C).


  Definition Set_cover (C: list (list A)) (l: list A):= l [=] (union_over C).

  Lemma set_coverP (C: list (list A))(l: list A): reflect (Set_cover C l)(set_cover C l).
  Proof. Admitted.

  Lemma Set_cover_elim (C: list (list A)) (l: list A)(c: list A):
    Set_cover C l -> In c C -> c [<=] l.
  Proof. Admitted.
  
    
  
  
  
  
 
