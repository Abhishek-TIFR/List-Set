

(*-------------Description ------------------------------------------------------  

This file implements powersets for ordered set of elements on ordered type.
Let A be an OrdType. We first define ordering on lists of elements from A.
Hence we connect the domain (list A) to the OrdType. Then we define and operation
to append an element a in front of each list present in a collection of lists.
Using this append (app) function we define a function (pw l) to generate a
list containing all the subsets of list l.
 

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

Require Export Lists.List.
Require Export MinMax.
Require Export GenReflect SetSpecs OrdType.
Require Export SetReflect OrdList.
Require Export Omega.
Require Export OrdSet.

Set Implicit Arguments.

Section OrderOnLists.

  Context { A: ordType }.

  (* ------------ Definition of decidable equality on list of elements from A ----------- *)
  Fixpoint eqbl (l1 l2: list A): bool := match (l1 , l2) with
                                      |(nil, nil)=> true
                                      |(nil, b::l2')=> false
                                      |(a::l1', nil)=> false
                                      |(a::l1', b::l2')=> match (comp a b) with
                                                         | Eq => eqbl l1' l2'
                                                         |Lt => false
                                                         |Gt => false
                                                         end
                                      end.

  Lemma eqbl_refl (l: list A): eqbl l l.
  Proof. induction l;simpl.  auto. match_up a a. all: (auto || by_conflict). Qed.
  
  Lemma eqbl_elim (l1 l2: list A): eqbl l1 l2 -> l1=l2.
  Proof. { revert l2. induction l1.
         { intros l2 H; destruct l2. auto. simpl in H; inversion H. }
         { intro l2; destruct l2. simpl. intro H;inversion H.
           simpl. match_up a e. subst a.
           intro H. assert(H1: l1 =l2);auto. subst l1; auto.
           all: intro H1;inversion H1. } } Qed.
  Lemma eqbl_intro (l1 l2: list A): l1=l2 -> eqbl l1 l2.
  Proof. intro H; subst l1; apply eqbl_refl. Qed.
  Lemma eqblP (l1 l2: list A): reflect (l1=l2)(eqbl l1 l2).
  Proof. apply reflect_intro. split. apply eqbl_intro. apply eqbl_elim. Qed.
  
  
  Canonical list_eqType: eqType:=
    {| Decidable.E:= list A; Decidable.eqb:= eqbl; Decidable.eqP:=eqblP |}.
  
  (*------------ Definition and properties of less than relation on lists of A----------- *)
  Fixpoint ltbl (l1 l2: list A): bool := match (l1 , l2) with
                                      |(nil, nil)=> false
                                      |(nil, b::l2')=> true
                                      |(a::l1', nil)=> false
                                      |(a::l1', b::l2')=> match (comp a b) with
                                                         |Eq => ltbl l1' l2'
                                                         |Lt => true
                                                         |Gt => false
                                                         end
                                      end.
    
Lemma ltbl_irefl (x : list A): ltbl x x = false.
Proof. induction x. auto. simpl; match_up a a; (auto || by_conflict). Qed.
Hint Resolve ltbl_irefl: core.

Lemma ltbl_antisym (x y:list A):  x <> y -> ltbl x y = ~~ ltbl y x.
Proof. { revert y. induction x.
       { intro y. case y. tauto. simpl. auto. }
       { intro y. case y.  simpl. auto.
         intros e l. intro H. simpl.
         match_up a e; match_up e a.
         subst a; apply IHx; intro H2; subst x;  apply H; auto.
         all: (try (subst a; by_conflict) || by_conflict).
         all: try (simpl;auto).  } } Qed.

Hint Resolve ltbl_antisym: core.


Lemma ltbl_trans (x y z:list A):  ltbl x y -> ltbl y z -> ltbl x z.
Proof. { revert y z. induction x.
       { intros y z H H1. destruct y. simpl in H. inversion H.
         destruct z. simpl in H1; inversion H1. simpl; auto. }
       { intros y z H H1. destruct y. simpl in H; inversion H.
         destruct z. simpl in H1; inversion H1.
         simpl; simpl in H; simpl in H1.
         match_up e e0.
         { subst e. match_up a e0. eapply IHx; [exact H | exact H1]. auto. inversion H. }
         { match_up a e0.
           { subst e0. match_up a e. subst a; by_conflict. by_conflict. inversion H. }
           { auto. }
           { match_up a e. subst a;by_conflict.
             assert (H4:e <b a). auto. by_conflict. inversion H. } }
         { match_up a e0;inversion H1. } } } Qed.

Hint Resolve ltbl_trans: core.

Canonical list_ordType: ordType:= {| Order.D:= list_eqType;
                                     Order.ltb:= ltbl;
                                     Order.ltb_irefl:= ltbl_irefl;
                                     Order.ltb_antisym := ltbl_antisym;
                                     Order.ltb_trans := ltbl_trans  |}.
  
End OrderOnLists.


Section Append.
  Context { A: Type }. (* to declare A as implicit outside the section *)
   
   Fixpoint app (a:A)(s: list (list A)): list (list A) :=
     match s with
     |nil=> nil
     |l::s1 => (a::l)::(app a s1)
     end.

   Notation "a [::] s" := (app a s) (at level 70, no associativity).
   
   Lemma app_intro (a:A)(x: list A)(s: list (list A)): In x s -> In (a::x) (a [::] s).
   Proof. { induction s. auto.
          intro H. destruct H.
          subst x; simpl; left; auto.
          simpl; right;auto. } Qed.
   Lemma app_elim (a:A)(x: list A)(s: list (list A)):
     In x (a [::] s)-> (exists x', In x' s /\ x = a::x').
   Proof. { induction s. simpl. tauto.
          simpl. intro H;destruct H.
          { exists a0. split. left;auto. auto. }
          { apply IHs in H as H1. destruct H1 as [x' H1].
            exists x'. split. right;apply H1. apply H1. } } Qed.
   Lemma app_elim1 (a:A)(x: list A)(s: list (list A)):  In (a::x) (a [::] s)-> In x s.
   Proof. { induction s. simpl. auto.
          simpl. intro H;destruct H. left. inversion H;auto. right;auto. } Qed.
   Lemma app_size_same1 (a:A)(s: list (list A)): |s| = | a [::] s |.
   Proof. induction s; simpl; auto. Qed. 
   Lemma app_size_same2 (a:A)(s: list (list A)): | a [::] s | = |s|.
   Proof. induction s; simpl; auto. Qed.
  
End Append.

Notation "a [::] s" := (app a s) (at level 70, no associativity).
Hint Immediate app_intro app_elim app_elim1 app_size_same1 app_size_same2: core.




Section PowerSet.
    Context { A: ordType }.  (* to declare A as implicit outside the section *)

  (*-------- Function to generate powerset for a set l --------------------*)
  Fixpoint pw (l: list A): list (list A):= match l with
                                              |nil => nil::nil
                                              |a::l' => union (a [::] (pw l')) (pw l')
                                           end.

   Lemma pw_is_ord (l: list A): IsOrd (pw l).
   Proof.  induction l; simpl; [constructor | auto ].  Qed.

  Lemma app_is_ord (a:A)(l:list (list A)): IsOrd l -> IsOrd (a[::]l).
  Proof. { induction l. simpl; auto.
         simpl. intro H.
         destruct l. simpl;constructor.
         simpl. constructor. simpl.
         match_up a a. inversion H;auto. all: try by_conflict.
         apply IHl; eauto. } Qed.
    
  Lemma pw_elim (x l: list A): In x (pw l) -> Subset x l.
  Proof. { revert x. induction l; intro x.
         { simpl;intro H;destruct H. subst x; auto. tauto. }
         { simpl. intro H.
           assert (Ha: In x (a[::] pw l) \/ In x (pw l)); auto.
           destruct Ha.
           { assert (H0a: exists x', In x' (pw l) /\ x = a::x'); auto.
             destruct H0a as [x' H0a]. destruct H0a as [H0a H0b]. subst x; auto. }
           { cut(x [<=] l); auto. } }  } Qed.
  Lemma pw_elim1 (x l: list A): IsOrd l ->  In x (pw l) -> IsOrd x.
  Proof.  { revert x. induction l.
          { intro x. simpl. intros H H1. destruct H1. subst x. auto. tauto. }
          { intros x H H1. simpl in H1.
            assert (H2: In x ( a[::] pw l) \/ In x (pw l)). auto.
            destruct H2.
            { (* when In x (a [::] pw l) *)
              assert (H2: exists x', In x' (pw l) /\ x = (a::x')). auto.
              destruct H2 as [x' H2]. destruct H2 as [H2 H3].
              assert (H4: IsOrd x'). eauto.
              assert (H5: x' [<=] l). auto using pw_elim.
              subst x. destruct x'. auto.
              assert (H6: a <b e). eauto. apply  IsOrd_cons;auto. }
            { (* when In x (pw l) *) eauto. } } } Qed.
              
  Lemma nil_in_pw (l: list A):  In nil (pw l).
  Proof. induction l. simpl; left;auto. simpl; cut(In nil (pw l)); auto. Qed.

  Lemma pw_intro (x l:list A): IsOrd x -> IsOrd l -> Subset x l -> In x (pw l).
  Proof. { revert x. induction l.
         { simpl. intros x H H1 H2. left. symmetry;auto. }
         { intros x H H1 H2. destruct x.
           { auto using nil_in_pw. }
           { destruct (e==a) eqn:Hea.
             { move /eqP in Hea. subst e.
               simpl. cut (In (a::x) (a[::] pw l)). auto.
               assert (H2a: x [<=] l). eauto.
               apply app_intro; apply IHl; eauto. }
             { assert (H2a: e::x [<=] l).  move /eqP in Hea.
               eapply IsOrd_Subset_elim2. all: auto. auto. 
               simpl. cut(In (e::x) (pw l)). auto. apply IHl;eauto. } } } } Qed.
                 
End PowerSet.


Hint Resolve pw_is_ord app_is_ord nil_in_pw: core.
Hint Immediate pw_elim pw_elim1 pw_intro: core.


Lemma length_refl (A:Type): reflexive ( fun (l s:list A) => |l| <=b |s|).
Proof. unfold reflexive. intros. auto. Qed.
Lemma length_trans (A:Type): transitive ( fun (l s:list A) => |l| <=b |s|).
Proof.  unfold transitive. auto. Qed.
Lemma length_comparable (A:Type): comparable  ( fun (l s:list A) => |l| <=b |s|).
Proof.  unfold comparable. auto. Qed.

Hint Resolve length_refl length_trans length_comparable: core.

Section PowerReflect.
  
  Context {A: ordType}.
  Definition Max_sub_in (G I: list A)(P: list A-> Prop):=
    I [<=] G /\ IsOrd I /\ P I /\ (forall I', In I' (pw G) -> P I' -> |I'| <= |I|).
  Definition max_sub_in (G I: list A)(B: list A-> bool):=
    subset I G && isOrd I && B I && forallb ( fun I'=> (negb (B I') || |I'| <=? |I|)) (pw G).

  Lemma Max_sub_in_elim1 (G I: list A)(B: list A -> bool):
    Max_sub_in G I B -> I [<=] G.
  Proof.  unfold Max_sub_in; tauto. Qed.
  
  Lemma Max_sub_in_elim2 (G I: list A)(B: list A -> bool):
    Max_sub_in G I B -> IsOrd I.
  Proof. unfold Max_sub_in; tauto. Qed.
  Lemma Max_sub_in_elim3 (G I: list A)(B: list A -> bool):
    Max_sub_in G I B -> B I.
   Proof. unfold Max_sub_in; tauto. Qed.

  Lemma max_has_biggest_size (G: list A)(B: list A-> bool)(X: list A)(M: list A):
    IsOrd G -> Max_sub_in G M B -> X[<=]G -> IsOrd X -> B X -> |X| <= |M|.
  Proof. unfold Max_sub_in. intros H H1 H2 H3 H4. apply H1;eauto.  Qed.
  Lemma max_sub_same_size (G: list A)(B: list A-> bool)(X: list A)(Y: list A):
    IsOrd G -> Max_sub_in G X B -> Max_sub_in G Y B -> |X|=|Y|.
  Proof.  { intros H H1 H2. cut (|X| <= |Y|). cut (|Y| <= |X|). omega.
          all: eapply max_has_biggest_size with (G:=G)(B:=B);
          unfold Max_sub_in in H1; unfold Max_sub_in in H2; (auto || apply H2 || apply H1). } Qed.
          
  
  Lemma max_sub_inbP (G I: list A)(B: list A-> bool):
    reflect (Max_sub_in G I B)(max_sub_in G I B).
  Proof. { apply reflect_intro. split.
         { unfold Max_sub_in. unfold max_sub_in.
           intro H. split_. split_. split_. apply /subsetP; apply H.
           apply /isOrdP;apply H. apply H.
           apply /forallbP. intros I' H2.
           destruct H as [H0 H]. destruct H as [H1 H]. destruct H as [H' H].
           apply /impP. intro H3.  apply /leP. auto. }
         {  unfold Max_sub_in. unfold max_sub_in.
            intro H. move /andP in H; destruct H as [H H2].
            move /andP in H; destruct H as [H H1].
            move /andP in H; destruct H as [H H'].
            split. auto. split. apply /isOrdP;auto. split;auto.
            move /forallbP in H2.
            intros I' H3 H4. apply /leP. specialize (H2 I').
            apply H2 in H3 as H5. move /impP in H5. auto. } } Qed.
  
  Lemma max_sub_inP (G I: list A)(P: list A-> Prop)(B: list A-> bool):
    (forall x, reflect (P x)(B x))-> reflect (Max_sub_in G I P)(max_sub_in G I B).
  Proof. { intro HP. eapply iffP with (P:= Max_sub_in G I B). 
         { apply max_sub_inbP. }
         { unfold Max_sub_in. intro H. split. apply H. split.
           apply H. split.  apply /HP;apply H.
           destruct H as [H0 H]. destruct H as [H' H].
           destruct H as [H1 H]. intros I' H2 H3.
           apply H. auto. apply /HP;auto. }
         { unfold Max_sub_in. intro H. split. apply H.
           split. apply H.  split. apply /HP;apply H.
           destruct H as [H0 H]. destruct H as [H' H].
           destruct H as [H1 H]. intros I' H2 H3.
           apply H. auto. apply /HP;auto. } } Qed.

   Definition Min_sub_in (G I: list A)(P: list A-> Prop):=
    I [<=] G /\ IsOrd I /\ P I /\ (forall I', In I' (pw G) -> P I' -> |I| <= |I'|).
   Definition min_sub_in (G I: list A)(B: list A-> bool):=
     subset I G && isOrd I && B I && forallb ( fun I'=> (negb (B I') || |I| <=? |I'|)) (pw G).

  Lemma Min_sub_in_elim1 (G I: list A)(B: list A -> bool):
    Min_sub_in G I B -> I [<=] G.
  Proof. unfold Min_sub_in;tauto. Qed.
  
  Lemma Min_sub_in_elim2 (G I: list A)(B: list A -> bool):
    Min_sub_in G I B -> IsOrd I.
  Proof.  unfold Min_sub_in;tauto. Qed.
  Lemma Min_sub_in_elim3 (G I: list A)(B: list A -> bool):
    Min_sub_in G I B -> B I.
  Proof.  unfold Min_sub_in;tauto. Qed.

   Lemma min_has_smallest_size (G: list A)(B: list A-> bool)(X: list A)(M: list A):
    IsOrd G -> Min_sub_in G M B -> X[<=]G -> IsOrd X -> B X -> |M| <= |X|.
  Proof. unfold Min_sub_in. intros H H1 H2 H3 H4. apply H1;eauto.  Qed.
    
  Lemma min_sub_same_size (G: list A)(B: list A-> bool)(X: list A)(Y: list A):
    IsOrd G -> Min_sub_in G X B -> Min_sub_in G Y B -> |X|=|Y|.
  Proof.  { intros H H1 H2. cut (|X| <= |Y|). cut (|Y| <= |X|). omega.
          all: eapply min_has_smallest_size with (G:=G)(B:=B);
          unfold Min_sub_in in H1; unfold Min_sub_in in H2; (auto || apply H2 || apply H1). } Qed.

  Lemma min_sub_inbP (G I: list A)(B: list A-> bool):
    reflect (Min_sub_in G I B)(min_sub_in G I B).
  Proof. { apply reflect_intro. split.
         { unfold Min_sub_in. unfold min_sub_in.
           intro H. split_. split_. split_. apply /subsetP; apply H.
           apply /isOrdP;apply H. apply H.
           apply /forallbP. intros I' H2.
           destruct H as [H0 H]. destruct H as [H1 H]. destruct H as [H' H].
           apply /impP. intro H3.  apply /leP. auto. }
         {  unfold Min_sub_in. unfold min_sub_in.
            intro H. move /andP in H; destruct H as [H H2].
            move /andP in H; destruct H as [H H1].
            move /andP in H; destruct H as [H H'].
            split. auto. split. apply /isOrdP;auto. split;auto.
            move /forallbP in H2.
            intros I' H3 H4. apply /leP. specialize (H2 I').
            apply H2 in H3 as H5. move /impP in H5. auto. } } Qed.
  Lemma min_sub_inP (G I: list A)(P: list A-> Prop)(B: list A-> bool):
    (forall x, reflect (P x)(B x))-> reflect (Min_sub_in G I P)(min_sub_in G I B).
  Proof. { intro HP. eapply iffP with (P:= Min_sub_in G I B). 
         { apply min_sub_inbP. }
         { unfold Min_sub_in. intro H. split. apply H. split.
           apply H. split. apply /HP;apply H.
           destruct H as [H0 H]. destruct H as [H' H].
           destruct H as [H1 H].  intros I' H2 H3.
           apply H. auto. apply /HP;auto. }
         { unfold Min_sub_in. intro H. split. apply H.
           split. apply H. split.  apply /HP;apply H.
           destruct H as [H0 H]. destruct H as [H' H].
           destruct H as [H1 H]. intros I' H2 H3.
           apply H. auto. apply /HP;auto. } } Qed.

  Lemma exists_largest_inb (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |Y| <=b |I|).
  Proof. { intros. eapply max_withP_exists. all: auto. } Qed.

  Lemma exists_largest_in (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |Y| <= |I|).
  Proof. { intros. apply exists_largest_inb in H as H1.
           destruct H1 as [I H1]. exists I.
           split. apply H1. split. apply H1.
           intros Y H2 H3. apply /lebP. apply H1;auto. } Qed.

  Lemma exists_smallest_inb (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |I| <=b |Y|).
  Proof. { intros. eapply min_withP_exists. all:auto. } Qed.

   Lemma exists_smallest_in (G: list A)(B: list A-> bool):
    (exists X, In X (pw G) /\ B X) ->
    (exists I, In I (pw G) /\ B I /\ forall Y, In Y (pw G)-> B Y -> |I| <= |Y|).
  Proof. { intros. apply exists_smallest_inb in H as H1.
           destruct H1 as [I H1]. exists I.
           split. apply H1. split. apply H1.
           intros Y H2 H3. apply /lebP. apply H1;auto. } Qed.
  
  
 
  
  
    
End PowerReflect.

Hint Resolve Max_sub_in_elim1 Max_sub_in_elim2 Max_sub_in_elim3 max_has_biggest_size: core.
Hint Resolve max_sub_inbP max_sub_inP: core.

Hint Resolve Min_sub_in_elim1 Min_sub_in_elim2 Min_sub_in_elim3  min_has_smallest_size: core.
Hint Resolve min_sub_inbP min_sub_inP: core.

Hint Resolve max_sub_same_size min_sub_same_size: core.

(* Eval compute in (pw (1::2::3::nil)). *)

Section MoreOnPower.

  Context {A: ordType}.

  Definition max_subs_of (G: list A)(B: list A -> bool):= filter (fun I => max_sub_in G I B) (pw G).

  Lemma max_subs_of_IsOrd (G: list A)(B: list A -> bool): IsOrd G -> IsOrd (max_subs_of G B).
  Proof. unfold max_subs_of. intro h1. cut (IsOrd (pw G)); auto. Qed.


  Lemma max_subs_of_intro (G I: list A)(B: list A -> bool):
    IsOrd G ->  Max_sub_in G I B-> In I (max_subs_of G B).
    Proof. { unfold max_subs_of.  set (f:= (fun I0 : list A => max_sub_in G I0 B)).
             intros h0 h1. move /max_sub_inbP in h1.
             replace (max_sub_in G I B) with (f I) in h1.
             cut (In I (pw G)). auto. unfold f in h1.
             move /max_sub_inbP in h1. cut ( I [<=] G).
             cut (IsOrd I). all: ( apply h1 || auto ). } Qed.

  Lemma max_subs_of_intro1 (G I: list A)(B: list A -> bool):
    IsOrd G -> max_sub_in G I B -> In I (max_subs_of G B).
  Proof. { unfold max_subs_of.  set (f:= (fun I0 : list A => max_sub_in G I0 B)).
           replace (max_sub_in G I B) with (f I). intros h0 h1.
           cut (In I (pw G)). auto. unfold f in h1. move /max_sub_inbP in h1.
           cut ( I [<=] G). cut (IsOrd I). all: ( apply h1 || auto ). } Qed.

  Lemma max_subs_of_elim (G I: list A)(B: list A -> bool):
    IsOrd G ->  In I (max_subs_of G B) -> Max_sub_in G I B.
  Proof. { unfold max_subs_of. 
           set (f:= (fun I0 : list A => max_sub_in G I0 B)).
           intros h1 h2.
           assert (h3: f I). eauto. apply /max_sub_inbP. apply h3. } Qed.

  Lemma max_subs_of_elim1 (G I: list A)(B: list A -> bool):
    IsOrd G ->  In I (max_subs_of G B) -> max_sub_in G I B.
  Proof. { unfold max_subs_of.
           set (f:= (fun I0 : list A => max_sub_in G I0 B)).
           intros h1 h2.
           assert (h3: f I). eauto.  apply h3. } Qed.

  Hint Immediate max_subs_of_intro max_subs_of_elim: core.

End MoreOnPower.

Hint Immediate max_subs_of_intro max_subs_of_elim: core.
