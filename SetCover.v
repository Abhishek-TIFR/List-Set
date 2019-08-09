

(*-------------Description --------------------------------------------------------------  

This file implements the union of all sets present in a list (union_over). We 
also define the notion of sets covers (Set_Cov C S) as a proposition which 
states that the collection of sets C is a cover for the set S. 
 

Following are the notions defined in this file:

 Fixpoint union_over (C: list (list A)): list A:= match C with
                                                   | nil => nil
                                                   |c::C' => c [u] (union_over C')
                                                   end.

 Fixpoint fix_nat (n:nat)(l: list A): list (A * nat):= match l with
                                                    |nil => nil
                                                    |a::l' => (a,n)::(fix_nat n l')
                                                    end.
 Notation "l [,] n" := (fix_nat n l) (at level 65).

 Definition mk_disj (C: list (list A)):= map (fun l => l [,] (idx l C) ) C.

 Definition set_cover (C: list (list A)) (l: list A):= equal l (union_over C).

 Definition Set_cover (C: list (list A)) (l: list A):= l [=] (union_over C).
 

Furthermore, we have following results on these definitions:

Lemma union_over_intro (C: list (list A))(l: list A)(a: A):
 In a l -> In l C -> In a (union_over C).
Lemma union_over_elim (C: list (list A))(a: A):
    In a (union_over C)-> (exists (l: list A), In l C /\ In a l).


Lemma fix_nat_intro (n: nat)(l: list A)(x: A): In x l -> In (x,n) (l [,] n).
Lemma fix_nat_elim (n: nat)(l: list A)(x: A): In (x,n) (l [,] n) -> In x l.

Lemma mk_disj_intro (C:list (list A))(l:list A): In l C -> In (l [,] (idx l C)) (mk_disj C).
Lemma mk_disj_elim (C: list (list A))(l:list (A * nat)):
    In l (mk_disj C) -> (exists l0, In l0 C /\ l = l0 [,] (idx l0 C)).

Lemma set_coverP (C: list (list A))(l: list A): reflect (Set_cover C l)(set_cover C l).
Lemma Set_cover_elim (C: list (list A)) (l: list A)(c: list A):
    Set_cover C l -> In c C -> c [<=] l.


------------------------------------------------------------------------------------------*)


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
  

  Notation "l [,] n" := (fix_nat n l) (at level 65).


  (*---- Definition of (mk_disj C) which makes each list in C disjoint with each other------*)


  Definition mk_disj (C: list (list A)):= map (fun l => l [,] (idx l C) ) C.

  Hint Resolve in_map map_cons map_length: core.
  Hint Immediate in_map_iff: core.
  
  Lemma mk_disj_intro (C:list (list A))(l:list A): In l C -> In (fix_nat (idx l C) l) (mk_disj C).
  Proof. { unfold mk_disj.
           set (f:= (fun l0 : list_eqType => fix_nat (idx l0 C) l0)).
           replace (fix_nat (idx l C) l) with (f l). auto. unfold f. auto. } Qed.

  Lemma mk_disj_elim (C: list (list A))(l:list (A * nat)):
    In l (mk_disj C) -> (exists l0, In l0 C /\ l = fix_nat (idx l0 C) l0).
  Proof.  { unfold mk_disj.
            set (f:= (fun l0 : list_eqType => fix_nat (idx l0 C) l0)).
            intros h1. apply in_map_iff in h1 as h2.
            destruct h2 as [l0 h2].
            exists l0. split. apply h2. symmetry;unfold f in h2;apply h2. }  Qed.

  Lemma mk_disj_size (C: list (list A)): | C | = | mk_disj C |.
  Proof. { unfold mk_disj. symmetry. apply map_length. } Qed.

  (*--------------- Definition of (set_cover C l) ---------------------------------------*)

  Definition set_cover (C: list (list A)) (l: list A):= equal l (union_over C).

  Definition Set_cover (C: list (list A)) (l: list A):= l [=] (union_over C).

  Lemma set_coverP (C: list (list A))(l: list A): reflect (Set_cover C l)(set_cover C l).
  Proof. unfold Set_cover. unfold set_cover. auto. Qed.

  Lemma Set_cover_elim (C: list (list A)) (l: list A)(c: list A):
    Set_cover C l -> In c C -> c [<=] l.
  Proof. { unfold Set_cover. intros h1 h2 x h3.
           cut (In x (union_over C)). apply h1.
           eapply union_over_intro. apply h3. auto. } Qed.
  
End SetCover.

 Notation "l [,] n" := (fix_nat n l) (at level 65).
  
  
 
