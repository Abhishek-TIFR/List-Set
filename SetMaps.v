





Require Export SetReflect.
Require Export OrdList.
Require Export OrdSet.


(*
Hint Resolve set_add_nodup set_remove_nodup: hint_nodup.
Hint Resolve set_union_nodup set_inter_nodup set_diff_nodup: hint_nodup. *)

Set Implicit Arguments.

Section Ord_sets.
  Context { A: ordType }. (* to declare A as implicit outside the section *)
   Lemma decA: forall x y: A, {x=y}+{x<>y}.
   Proof. intros; eapply reflect_dec with (b:= eqb x y); apply eqP. Qed.
   Record set_on : Type := { S_of :> list A;
                          S_IsOrd : IsOrd S_of }.
  
End Ord_sets.


Section Set_maps.
  Context { A B: ordType }.    

  Lemma EM_A: forall x y: A, x=y \/  x<>y.
  Proof.  eauto with hint_reflect.  Qed.
  Lemma EM_B: forall x y:B, x=y \/ x<>y.
  Proof. eauto with hint_reflect.  Qed.
  
  Fixpoint s_map (f:A->B) (l:list A): list B:= match l with
                                        | nil => nil
                                        | a1::l1 => add (f a1) (s_map f l1)
                                              end.

  Lemma IsOrd_s_map (f:A->B) (l:list A):  IsOrd (s_map f l).
  Proof. { induction l. simpl. constructor. simpl. eauto with hint_list. } Qed.
  Lemma NoDup_s_map (f:A->B) (l:list A):  NoDup (s_map f l).
    Proof. cut (IsOrd (s_map f l)). eauto with hint_list. apply IsOrd_s_map. Qed.
  
  Lemma s_map_intro1(f: A->B)(l: list A)(a:A)(y: B): In y (s_map f l)-> In y (s_map f (a::l)).
    Proof. simpl. eapply set_add_intro1. Qed.
  Lemma s_map_intro2 (f: A->B)(l: list A)(x:A): In x l -> In (f x) (s_map f l).
  Proof.  { induction l. simpl.  tauto.
          cut (x=a \/ x <> a). 
          intro H;destruct H as [Hl | Hr].
          { intro H. rewrite Hl. simpl. eapply set_add_intro2. auto. }
          { intro H. cut (In x l). intro H1. eapply s_map_intro1;eauto.
            eapply in_inv2;eauto.  } eauto with hint_reflect. } Qed.

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
         split; auto with hint_list. assert (H4: In (f a) (s_map f l)). eapply s_map_elim2.
         eapply H1. exact H3b. assert (H5: exists y : A, In y l /\ f a = f y). eauto.
         destruct H5 as [y0 H5]. exists y0. split;  simpl. tauto. tauto.
         eapply EM_B. } Qed. 
        
  Hint Resolve IsOrd_s_map NoDup_s_map : hint_list.
  Hint Resolve s_map_intro1 s_map_intro2 s_map_elim s_map_elim2 s_map_elim3: hint_map.
  Lemma funP (f: A->B)(x y: A): f x <> f y -> x <> y.
  Proof. intros H H1. apply H;rewrite H1; auto. Qed.
  
  Definition one_one (f: A->B): Prop:= forall x y, x <> y -> f x <> f y.
  Lemma one_oneP1 (f:A->B): one_one f -> forall x y, f x = f y -> x =y.
  Proof. { unfold one_one;intros H x y H1. elim (EM_A x y). tauto.
           intro H2; absurd (f x = f y); auto. } Qed.
  Hint Immediate one_oneP1: hint_map.
  
  Definition one_one_on (l: list A) (f: A-> B):Prop:= forall x y, In x l-> In y l ->  x<>y -> f x <> f y.
  
  Lemma one_one_onP1(l:list A)(f: A-> B): one_one_on l f ->
                                         (forall x y, In x l-> In y l-> f x = f y -> x = y). 
  Proof. { unfold one_one_on. intros H x y H1 H2. elim (EM_A x y). tauto.
           intros H3 H4. absurd (f x = f y); auto. } Qed.
  Lemma one_one_onP2(l:list A)(f: A-> B): (forall x y, In x l-> In y l-> f x = f y -> x = y) ->(one_one_on l f).
  Proof. { intros H.  unfold one_one_on.
         intros x y H1 H2 H3 H4. apply H3. auto. } Qed.  

  Lemma one_one_on_nil (f:A->B): one_one_on nil f.
  Proof. unfold one_one_on. intros x y H H0 H1 H2. inversion H. Qed.

  Lemma one_one_on_intro(l:list A) (f: A->B)(a:A):
             (~ In (f a) (s_map f l) /\ (one_one_on l f))-> one_one_on (a::l) f.
  Proof. { unfold one_one_on. intro H; destruct H as [H H1].
         intros x y H2 H3. destruct H2; destruct H3.
         rewrite <- H0; rewrite <- H2.  tauto.
         rewrite <- H0. intros H3 H4. assert (H5: In (f a) (s_map f l)). rewrite H4.
         apply s_map_intro2;auto. absurd (In (f a) (s_map f l)); assumption.
         rewrite <- H2. intros H3 H4. absurd (In (f a) (s_map f l)). assumption.
         rewrite <- H4. apply s_map_intro2;auto. apply H1; auto. } Qed.
 
  Lemma one_one_on_elim1 (l:list A) (f: A->B)(a: A): one_one_on (a::l) f -> one_one_on l f.
  Proof. { unfold one_one_on.  intro H. intros x y H1 H2. eapply H; eauto with hint_list. } Qed.
  
  Lemma one_one_on_elim2 (l:list A) (f: A->B)(a: A)(Hl: NoDup (a::l)):
    one_one_on (a::l) f -> ~ In (f a)(s_map f l).
  Proof. { unfold one_one_on.  intros H H1.
         assert (H2: (exists y, In y l /\ f a = f y)).
         { eapply s_map_elim3. intro H2; inversion Hl;contradiction. auto. }
         destruct H2 as [b H2]; destruct H2 as [H2 H3].
         eapply H with (x:=a)(y:=b); eauto with hint_list. intro H4. rewrite <- H4 in H2.
         inversion Hl;contradiction. } Qed.
 
  
  Hint Immediate one_one_on_nil one_one_onP1 one_one_on_elim1 : hint_map.
  Check negb. Print negb. Check mem.

  Fixpoint one_one_onb (l: list A) (f: A->B): bool:=
    match l with
    |nil => true
    | a1::l1 => (negb ( mem (f a1) (s_map f l1))) && (one_one_onb l1 f)
    end.


   Lemma one_one_onP (l:list A) (f: A->B)(Hl: NoDup l):
    reflect (one_one_on l f)(one_one_onb l f).
  Proof. { apply reflect_intro. split.
         { induction l.
           { unfold one_one_onb. reflexivity. }
           { intro H. simpl one_one_onb. apply /andP. split. cut (~ In (f a)(s_map f l)).
             intro H1. assert (H2:  mem (f a) (s_map f l) = false ). apply /memP.
             auto. rewrite H2. simpl. reflexivity. eapply one_one_on_elim2.
             apply Hl. auto. apply IHl.
             eauto with hint_list. eauto with hint_map. } }   
         { induction l.
           { auto with hint_map. }
           { simpl. move /andP. intro H; destruct H as [H H1].
             apply one_one_on_intro.  split.
             intro H2. unfold negb in H.
             replace (mem (f a) (s_map f l)) with true in H. inversion H.
             symmetry; apply /memP; eauto. apply IHl. eauto with hint_list. apply H1. } }  } Qed.
  
  
End Set_maps.

Hint Resolve NoDup_s_map : hint_nodup.
Hint Resolve s_map_intro1 s_map_intro2 s_map_elim s_map_elim2 s_map_elim3 NoDup_s_map: hint_map.
Hint Immediate one_one_on_nil one_one_onP1 one_one_on_elim1 one_one_on_elim2: hint_map.
Hint Resolve one_one_onP: hint_reflect.