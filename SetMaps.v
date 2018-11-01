


(*-------------Description ------------------------------------------------------  

This file implements maps on lists. Here we define functions to calculate range 
of a function on list l. We also define one-one function predicate and its boolean
counterpart. 

Following are the notions defined in this file:

 s_map f l                  : range set of f on list l
 one_one_on l f             : f is one one on l
 one_one_onb l f            : boolean counterpart of (one_one_on l f)

Lemma one_one_onP (l:list A) (f: A->B)(Hl: NoDup l):
    reflect (one_one_on l f)(one_one_onb l f).

Furthermore, we have results relating the cardinality of domain and range 
for various kinds of functions (many one/one one).

---------------------------------------------------------------------------------*)


Require Export SetReflect.
Require Export OrdList.
Require Export OrdSet.


Set Implicit Arguments.

Section Set_maps.
  Context { A B: ordType }.    

  Lemma EM_A: forall x y: A, x=y \/  x<>y.
  Proof.  eauto.  Qed.
  Lemma EM_B: forall x y:B, x=y \/ x<>y.
  Proof. eauto.  Qed.
  
  
  Fixpoint s_map (f:A->B) (l:list A): list B:= match l with
                                        | nil => nil
                                        | a1::l1 => add (f a1) (s_map f l1)
                                              end.

  Lemma IsOrd_s_map (f:A->B) (l:list A):  IsOrd (s_map f l).
  Proof. { induction l. simpl. constructor. simpl. eauto. } Qed.
  
  Lemma NoDup_s_map (f:A->B) (l:list A):  NoDup (s_map f l).
    Proof. cut (IsOrd (s_map f l)). eauto. apply IsOrd_s_map. Qed.
  
  Lemma s_map_intro1(f: A->B)(l: list A)(a:A)(y: B): In y (s_map f l)-> In y (s_map f (a::l)).
    Proof. simpl. eapply set_add_intro1. Qed.
  Lemma s_map_intro2 (f: A->B)(l: list A)(x:A): In x l -> In (f x) (s_map f l).
  Proof.  { induction l. simpl.  tauto.
          cut (x=a \/ x <> a). 
          intro H;destruct H as [Hl | Hr].
          { intro H. rewrite Hl. simpl. eapply set_add_intro2. auto. }
          { intro H. cut (In x l). intro H1. eapply s_map_intro1;eauto.
            eapply in_inv2;eauto.  } eauto. } Qed.

  Lemma s_map_elim (f:A->B) (l: list A)(a0:A)(fa:B): In (fa) (s_map f (a0::l))->
                                                    fa = f(a0) \/ In fa (s_map f l).
    Proof. simpl. eapply set_add_elim. Qed.

  Lemma s_map_elim2 (f:A->B) (l: list A)(a0:A)(fa:B): In (fa) (s_map f (a0::l))->
                                                   fa <> f(a0) -> In fa (s_map f l).
  Proof. simpl. eapply set_add_elim2.  Qed.
  
  Lemma s_map_elim3 (f:A->B)(l:list A)(a:A): ~ In a l -> In (f a) (s_map f l) ->
                                           (exists y, In y l /\ f a = f y).
  Proof. { intros H H1. induction l. inversion H1.
         assert (H2: ~ In a l). intro H2; apply H. simpl;tauto. 
         cut ( f a = f a0 \/ f a <> f a0 ). intro H3; destruct H3 as [H3a | H3b]. exists a0.
         split; auto. assert (H4: In (f a) (s_map f l)). eapply s_map_elim2.
         eapply H1. exact H3b. assert (H5: exists y : A, In y l /\ f a = f y). eauto.
         destruct H5 as [y0 H5]. exists y0. split;  simpl. tauto. tauto.
         eapply EM_B. } Qed.
  Lemma s_map_elim4 (f: A->B)(l: list A)(b:B): In b (s_map f l)-> (exists a, In a l /\ b = f a).
  Proof. { induction l.
         { simpl. tauto. }
         { intro H. apply s_map_elim in H as H1. destruct H1.
           { exists a. split;auto. }
           { apply IHl in H0 as H1.
             destruct H1 as [a' H1]; destruct H1 as [H1 H2].
             exists a'. split;auto. } } } Qed.
        
  Hint Resolve IsOrd_s_map NoDup_s_map : core.
  Hint Resolve s_map_intro1 s_map_intro2 s_map_elim: core.
  Hint Resolve s_map_elim2 s_map_elim3 s_map_elim4: core.
  
  Lemma funP (f: A->B)(x y: A): f x <> f y -> x <> y.
  Proof. intros H H1. apply H;rewrite H1; auto. Qed.
  
  Definition one_one (f: A->B): Prop:= forall x y, x <> y -> f x <> f y.
  
  Lemma one_oneP1 (f:A->B): one_one f -> forall x y, f x = f y -> x =y.
  Proof. { unfold one_one;intros H x y H1. elim (EM_A x y). tauto.
           intro H2; absurd (f x = f y); auto. } Qed.
  
  Hint Immediate one_oneP1: core.
  
  Definition one_one_on (l: list A) (f: A-> B):Prop:= forall x y, In x l-> In y l ->  x<>y -> f x <> f y.
  
  Lemma one_one_on_elim (l:list A)(f: A-> B): one_one_on l f ->
                                         (forall x y, In x l-> In y l-> f x = f y -> x = y). 
  Proof. { unfold one_one_on. intros H x y H1 H2. elim (EM_A x y). tauto.
           intros H3 H4. absurd (f x = f y); auto. } Qed.
  Lemma one_one_on_intro(l:list A)(f: A-> B): (forall x y, In x l-> In y l-> f x = f y -> x = y) ->
                                         (one_one_on l f).
  Proof. { intros H.  unfold one_one_on.
         intros x y H1 H2 H3 H4. apply H3. auto. } Qed.  

  Lemma one_one_on_nil (f:A->B): one_one_on nil f.
  Proof. unfold one_one_on. intros x y H H0 H1 H2. inversion H. Qed.

  Lemma one_one_on_intro1(l:list A) (f: A->B)(a:A):
             (~ In (f a) (s_map f l)) -> (one_one_on l f) -> one_one_on (a::l) f.
  Proof. { unfold one_one_on. intros H H1. 
         intros x y H2 H3. destruct H2; destruct H3.
         rewrite <- H0; rewrite <- H2.  tauto.
         rewrite <- H0. intros H3 H4. assert (H5: In (f a) (s_map f l)). rewrite H4.
         apply s_map_intro2;auto. absurd (In (f a) (s_map f l)); assumption.
         rewrite <- H2. intros H3 H4. absurd (In (f a) (s_map f l)). assumption.
         rewrite <- H4. apply s_map_intro2;auto. apply H1; auto. } Qed.
 
  Lemma one_one_on_elim1 (l:list A) (f: A->B)(a: A): one_one_on (a::l) f -> one_one_on l f.
  Proof. { unfold one_one_on.  intro H. intros x y H1 H2. eapply H; auto. } Qed.
  
  Lemma one_one_on_elim2 (l:list A) (f: A->B)(a: A)(Hl: NoDup (a::l)):
    one_one_on (a::l) f -> ~ In (f a)(s_map f l).
  Proof. { unfold one_one_on.  intros H H1.
         assert (H2: (exists y, In y l /\ f a = f y)).
         { eapply s_map_elim3. intro H2; inversion Hl;contradiction. auto. }
         destruct H2 as [b H2]; destruct H2 as [H2 H3].
         eapply H with (x:=a)(y:=b); auto. intro H4. rewrite <- H4 in H2.
         inversion Hl;contradiction. } Qed.
 
  
  Hint Immediate one_one_on_nil one_one_on_elim one_one_on_elim1 one_one_on_elim2 : core.
  Hint Immediate one_one_on_intro one_one_on_intro1: core.
   

  Fixpoint one_one_onb (l: list A) (f: A->B): bool:=
    match l with
    |nil => true
    | a1::l1 => (negb ( memb (f a1) (s_map f l1))) && (one_one_onb l1 f)
    end.


   Lemma one_one_onP (l:list A) (f: A->B)(Hl: NoDup l):
    reflect (one_one_on l f)(one_one_onb l f).
  Proof. { apply reflect_intro. split.
         { induction l.
           { unfold one_one_onb. reflexivity. }
           { intro H. simpl one_one_onb. apply /andP. split. cut (~ In (f a)(s_map f l)).
             intro H1. assert (H2:  memb (f a) (s_map f l) = false ). apply /membP.
             auto. rewrite H2. simpl. reflexivity. eapply one_one_on_elim2.
             apply Hl. auto. apply IHl.
             eauto. eauto. } }   
         { induction l.
           { auto.  }
           { simpl. move /andP. intro H; destruct H as [H H1].
             apply one_one_on_intro1.  
             intro H2. unfold negb in H.
             replace (memb (f a) (s_map f l)) with true in H. inversion H.
             symmetry; apply /membP; eauto. apply IHl. eauto. apply H1. } }  } Qed.

  (*--------- Some more properties of s_maps-----------------------------------*)

  Lemma one_one_s_map_elim (l: list A)(f: A->B)(x: A):
    one_one_on l f -> In (f x) (s_map f l) -> In x l.
  Proof. Admitted.
  
  Lemma s_map_subset (l s: list A)(f: A->B): l [<=] s -> (s_map f l) [<=] (s_map f s).
  Proof. Admitted.

  Lemma s_map_size_less (l: list A)(f: A->B): |s_map f l| <= |l|.
  Proof. Admitted.
  Lemma s_map_size_same (l: list A)(f: A->B): NoDup l -> one_one_on l f-> |l|=| s_map f l|.
  Proof. Admitted.
  

  Hint Resolve s_map_subset s_map_size_less s_map_size_same: core.

  
  Lemma s_map_strict_less (l: list A)(f: A->B):
    NoDup l -> (|s_map f l| < |l|) -> ~ one_one_on l f.
  Proof. Admitted.

  Hint Immediate one_one_s_map_elim s_map_strict_less : core.
  
  Lemma one_one_on_intro2 (l: list A)(f: A->B):
    NoDup l -> (|s_map f l| = |l|)->  one_one_on l f.
  Proof. Admitted.

  Lemma one_one_on_intro3 (l s: list A)(f: A-> B): s [<=] l -> one_one_on l f -> one_one_on s f.
  Proof. Admitted.

  Hint Immediate one_one_on_intro2 one_one_on_intro3 : core.
 
  
End Set_maps.

Hint Resolve IsOrd_s_map NoDup_s_map : core.
Hint Resolve s_map_intro1 s_map_intro2 s_map_elim: core.
Hint Resolve s_map_elim2 s_map_elim3 s_map_elim4 : core.
Hint Immediate one_oneP1: core.
Hint Immediate one_one_on_nil one_one_on_elim one_one_on_elim1 one_one_on_elim2 : core.
Hint Immediate one_one_on_intro one_one_on_intro1: core.
Hint Resolve one_one_onP: core.

Hint Resolve s_map_subset s_map_size_less s_map_size_same: core.
Hint Immediate one_one_s_map_elim s_map_strict_less : core.

Hint Immediate one_one_on_intro2 one_one_on_intro3 : core.

Section Map_composition.

  Context {A B C: ordType}.

  (*-------------------------  A  --f-->  B  --g-->  C    --------------------------------*)

  Lemma range_of_range (l:list A)(f: A->B)(g: B->C):
    s_map g (s_map f l) = s_map ( fun x => g (f x)) l.
  Proof. { assert (H: Equal  (s_map g (s_map f l)) (s_map ( fun x => g (f x)) l) ).
         { unfold Equal.
           split.
           { unfold Subset. intros c Hc.
             assert (Hb: exists b, In b (s_map f l) /\ c = g b). auto.
             destruct Hb as [b Hb]. destruct Hb as [Hb Hb1].
             assert (Ha: exists a, In a l /\ b = f a). auto.
             destruct Ha as [a Ha]. destruct Ha as [Ha Ha1].
             rewrite Hb1. set (gf := (fun x : A => g (f x))).
             rewrite Ha1. 
             assert (H: (g (f a)) = (gf a)). unfold gf. auto.
             rewrite H. eapply s_map_intro2. auto. }
           { unfold Subset. intros c Hc.
             assert (Ha: exists a, In a l /\ c = g (f a)). auto.
             destruct Ha as [a Ha]. destruct Ha as [Ha1 Ha2].
             subst c. auto. } }  auto. } Qed.

  Hint Resolve range_of_range: core.
End Map_composition.

 Hint Resolve range_of_range: core.




 