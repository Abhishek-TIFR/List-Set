


(* ------ This file contains results about minimum and maximum value in a list of elements 
   of an arbitrary type (A: Type) with a boolean comparison operator (lr: A-> A-> bool).
   

  The results in this file are prooved under the following three assumptions:

  Hypothesis lr_refl : reflexive lr.      (*  forall x : A, lr x x *)
  Hypothesis lr_trans: transitive lr.     (*  forall y x z : A, lr x y -> lr y z -> lr x z *) 
  Hypothesis lr_complete: complete lr.    (*  forall x y : A, lr x y=false -> lr y x   *)
  
  Functions defined are: 
  maxof a b   => returns maximum among a and b
  maxin l d   => returns the maximum value in the list l (returns d if l is nil) 
  minof a b   => returns minimum among a and b
  minin l d   => returns the minimum value in the list l (returns d if l is nil)  --- -- *)


Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Omega.


Set Implicit Arguments.

Section Min_Max.

  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  Definition complete (lr: A->A-> bool) := forall x y, lr x y=false -> lr y x.
  
 (*-----------Partial functions on lists ( maxin and minin ) ---------------------------  *)

  
  Definition maxof (a b :A): A := match a <=r b with
                                  |true => b
                                  |false => a           
                                  end.

  
  Hypothesis lr_refl : reflexive lr.
  Print reflexive. (*  forall x : T, R x x *)
  Hypothesis lr_trans: transitive lr.
  Hypothesis lr_complete: complete lr.
  
  Lemma maxof_spec1 (a b: A): a <=r maxof a b.
  Proof. unfold maxof. destruct (a <=r b) eqn:H; eauto using lr_refl. Qed. (* refl *)
  Lemma maxof_spec2 (a b: A): b <=r maxof a b. 
  Proof. unfold maxof. destruct (a <=r b) eqn:H; eauto. Qed. (* refl and complete *)
  Lemma maxof_spec3 (a b c:A): c <=r a -> c <=r maxof a b.
  Proof.  unfold maxof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.
  Lemma maxof_spec4 (a b c:A): c <=r b -> c <=r maxof a b.
  Proof. unfold maxof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.

  Hint Resolve maxof_spec1 maxof_spec2 maxof_spec3 maxof_spec4: core.
  
   Fixpoint maxin (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => maxof a (maxin l' a)
    end.

   Lemma maxin_elim (l: list A)(a d:A): maxin (a::l) d = maxin (a::l) a.
   Proof. simpl; auto. Qed.

   Lemma maxin_elim1 (a:A) (l:list A) (d:A) : In (maxin (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left.
              unfold maxof. replace (a <=r a) with true. auto. symmetry;apply lr_refl. }
            { intros d a0. replace (maxin (a0 :: a :: l) d) with (maxof a0 (maxin (a::l) a0)).
              unfold maxof.
              destruct (a0 <=r maxin (a :: l) a0) eqn:H; eauto.
              simpl;auto. } } Qed.

 Lemma maxin_spec (l:list A)(d:A)(a:A): In a l -> (a <=r (maxin l d)).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl. destruct H.
            { subst a; eauto. }  eauto. } } Qed.     

   Hint Resolve maxin_spec maxin_elim maxin_elim1: core.

    Definition minof (a b :A): A:= match a <=r b with
                                  |true => a
                                  |false => b
                                   end.
    
    Lemma minof_spec1 (a b: A): minof a b <=r a.
     Proof. unfold minof. destruct (a <=r b) eqn:H; eauto. Qed.
   
   Lemma minof_spec2 (a b: A): minof a b <=r b.
   Proof. unfold minof. destruct (a <=r b) eqn:H; eauto. Qed.

   Lemma minof_spec3 (a b c:A): a <=r c -> minof a b <=r c.
   Proof. unfold minof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed.  
   Lemma minof_spec4 (a b c:A): b <=r c ->  minof a b <=r c.
   Proof. unfold minof. destruct (a <=r b) eqn:H. all: try tauto. intro; eauto. Qed. 

   Hint Resolve minof_spec1 minof_spec2 minof_spec3 minof_spec4: core.

   Fixpoint minin (l: list A)(d: A): A:=
    match l with
    |nil => d
    |a::l' => minof a (minin l' a)
    end.

   Lemma minin_elim (l: list A)(a d:A): minin (a::l) d = minin (a::l) a.
   Proof. simpl; auto. Qed.

   Lemma minin_elim1 (a:A) (l:list A) (d:A) : In (minin (a::l) d) (a::l).
   Proof.  { revert a. revert d. induction l.
            { simpl. intros; left.
              unfold minof. replace (a <=r a) with true. auto. symmetry;apply lr_refl. }
            { intros d a0. replace (minin (a0 :: a :: l) d) with (minof a0 (minin (a::l) a0)).
              unfold minof.
              destruct (a0 <=r minin (a :: l) a0) eqn:H; eauto.
              simpl;auto. } } Qed.

   Lemma minin_spec (l:list A)(d:A)(a:A): In a l -> ((minin l d) <=r a).
   Proof. { generalize d. induction l.
          { intros d0 H. inversion H. }
          { intros d0 H. simpl. destruct H.
            { subst a; eauto. }  eauto. } } Qed.

   
   Hint Resolve minin_spec minin_elim minin_elim1: core.

End Min_Max.



Hint Resolve maxof_spec1 maxof_spec2 maxof_spec3 maxof_spec4: core.
Hint Resolve maxin_spec maxin_elim maxin_elim1: core.
Hint Resolve minof_spec1 minof_spec2 minof_spec3 minof_spec4: core.
Hint Resolve minin_spec minin_elim minin_elim1: core.
