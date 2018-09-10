



(* This file contains boolean functions corresponding to the different predicates
   commonly used in talking about sets. These boolean functions are connected to
   the corresponding predicates using the reflection technique by Gronthier et.al.
   The type of elements in the set (lists) are from eqType.


  Following is the boolean functions and their corresponding predicated  
 
  Propositions                        Boolean functions      Connecting Lemma 
  In a l                       <->    mem a l                memP
  IN a b l                     <->    mem2 a b l             mem2p
  NoDup l                      <->    noDup l                nodupP
  Empty l                      <->    is_empty l             emptyP
  Subset s s'                  <->    subset s s'            subsetP
  Equal s s'                   <->    equal s s'             equalP
  Exists P l                   <->    existsb f l            ExistsP
  exists x, (In x l /\ P x)    <->    existsb f l            existsP
  Forall P l                   <->    forallb f l            ForallP
  forall x, (In x l -> P x)    <->    forallb f l            forallP   ------------*)


From Coq Require Export ssreflect  ssrbool Lists.List.
Require Export SetSpecs GenReflect DecType.
Set Implicit Arguments.

Section SetReflections.
Context { A:eqType }. (* to declare A as implicit for all functions in this section *)
Lemma decA: forall x y:A, {x=y}+{x<>y}.
Proof. eauto. Qed.

  (*--------- set_mem (boolean function)  and its specification ---------*)
  Fixpoint mem (a:A)(l: list A){struct l}: bool:=
    match l with
    | nil =>false
    | a1::l1 => (a== a1) ||  mem a l1
    end.
  
  (* fix In (a : A) (l : list A) {struct l} : Prop :=
  match l with
  | nil => False
  | b :: m => b = a \/ In a m
  end *)

  Lemma set_mem_correct1: forall (a:A)(l:list A), mem a l -> In a l.
  Proof. { intros a l. induction l.
         { simpl;auto. }
         { simpl.  move /orP. intro H; destruct H.
           move /eqP in H;symmetry in H; left;auto.
           right; auto.  } } Qed.
  Lemma set_mem_correct2: forall (a:A)(l:list A), In a l ->  mem a l.
  Proof. { intros a l. induction l.
         { simpl;auto. }
         { simpl.  intro H. apply /orP. destruct H.
           left; apply /eqP; symmetry; auto. 
           right; auto.  } } Qed. 
  
  Lemma memP a l: reflect (In a l) (mem  a l).
  Proof. apply reflect_intro. split.
         apply set_mem_correct2. apply set_mem_correct1. Qed.
  
Hint Resolve memP : core.

Lemma In_EM: forall (a:A) (x: list A), In a x \/ ~ In a x.
Proof. eauto.  Qed.

Definition IN := fun (x:A)(y:A)(l:list A) => In x l /\ In y l.
Definition mem2 x y l := mem  x l && mem y l.

Lemma mem2P a b x : reflect (IN a b x) (mem2 a b x).
Proof. { apply reflect_intro. split.
       { unfold IN; unfold mem2. intro H; destruct H.
         apply /andP. split; apply /memP; auto. }
       { unfold IN; unfold mem2. move /andP.
         intro H; split; apply /memP; tauto. } } Qed.

Lemma mem2_comute (x y: A)(l: list A): mem2 x y l = mem2 y x l.
Proof. unfold mem2. case (mem  x l);case (mem y l); simpl;auto. Qed.

Hint Resolve mem2P: core.
Lemma IN_EM: forall (a b:A)(x:list A), IN a b x \/ ~ IN a b x.
Proof.  eauto. Qed.

(*---------- noDup  (boolean function) and its specification ---------*)
Fixpoint noDup (x: list A): bool:=
  match x with
    |nil => true
    |h :: x1 => if mem h x1 then false else noDup x1
  end.
Lemma NoDup_iff_noDup l: NoDup l <-> noDup l. 
Proof. { split. 
       { induction l.  auto.
       intro H; inversion H;  simpl.
       replace (mem a l) with false; auto.
       symmetry. apply /memP. auto. } 
       { induction l. constructor.
       simpl. case (mem a l) eqn: H1. discriminate.  intro H2.
       constructor. move /memP.  rewrite H1.  auto. tauto. }  } Qed. 
Lemma nodupP l: reflect (NoDup l) (noDup l).
Proof. {cut (NoDup l <-> noDup l). eauto. apply NoDup_iff_noDup. } Qed.

Hint Resolve nodupP : core.

Lemma NoDup_EM: forall l:list A, NoDup l \/ ~ NoDup l.
Proof. eauto. Qed.
Lemma NoDup_dec: forall l:list A, {NoDup l} + { ~ NoDup l}.
Proof. eauto. Qed.

Lemma nodup_spec: forall l:list A, NoDup (nodup decA l).
Proof. intros. eapply NoDup_nodup. Qed.


(*---------- is_empty (boolean function) and its specification -----------------*)
Definition is_empty (x:list A) : bool := match x with
                                 | nil => true
                                 | _ => false
                                      end.


Lemma emptyP l : reflect (Empty l) (is_empty l).
Proof. { destruct l eqn:H. simpl.  constructor. unfold Empty; auto.
       simpl. constructor. unfold Empty.  intro H1. specialize (H1 e).
       apply H1. auto.  } Qed. 
Hint Resolve emptyP : core.
Lemma Empty_EM (l:list A): Empty l \/ ~ Empty l.
  Proof. solve_EM. Qed.  
Lemma Empty_dec (l: list A): {Empty l} + {~Empty l}.
  Proof. solve_dec. Qed.  

(*----------- subset (boolean function) and its specification--------------------*)
Fixpoint subset (s s': list A): bool:=
  match s with
  |nil => true
  | a1 :: s1=> mem a1 s' && subset s1 s'
  end.

Lemma subsetP s s': reflect (Subset s s') (subset s s').
Proof. { induction s. simpl. constructor. intro. intros  H. absurd (In a nil); auto.
       apply reflect_intro. split.
       { intro H.  cut (In a s' /\ Subset s s'). Focus 2. split; eauto. simpl.
         intro H1; destruct H1 as [H1 H2].
         apply /andP. split. apply /memP;auto. apply /IHs;auto.  }
       { simpl.  move /andP. intro H; destruct H as [H1 H2]. unfold Subset.
         intros a0 H3. cut (a0= a \/ In a0 s). intro H4; destruct H4 as [H4 | H5].
         rewrite H4. apply /memP;auto. cut (Subset s s'). intro H6. auto. apply /IHs;auto.
         eauto.   }  } Qed.

Hint Resolve subsetP: core.
Lemma Subset_EM (s s': list A): Subset s s' \/ ~ Subset s s'.
Proof. solve_EM. Qed.
Lemma Subset_dec (s s': list A): {Subset s s'} + {~ Subset s s'}.
Proof. solve_dec. Qed.

(*----------- equal (boolean function) and its specifications--------------------*)
Definition equal (s s':list A): bool:= subset s s' && subset s' s.
Lemma equalP s s': reflect (Equal s s') (equal s s').
Proof. { apply reflect_intro.  split.
       { intro H. cut (Subset s s'/\ Subset s' s).
       Focus 2. auto. intro H1. unfold equal.
       apply /andP. split; apply /subsetP; tauto. }
       { unfold equal. move /andP. intro H. apply Equal_intro; apply /subsetP; tauto. }
       } Qed.

Hint Resolve equalP: core.
Lemma Equal_EM (s s': list A): Equal s s' \/ ~ Equal s s'.
Proof. solve_EM. Qed.
Lemma Equal_dec (s s': list A): {Equal s s'} + {~ Equal s s'}.
Proof. solve_dec. Qed.

(*----------- existsb (boolean function) and its specifications-------------------*)
  Print existsb.
  (* fix existsb (l : list A) : bool :=
  match l with
  | nil => false
  | a :: l0 => f a || existsb l0
  end *)
  Print Exists.
(* Inductive Exists (A : Type) (P : A -> Prop) : list A -> Prop :=
    Exists_cons_hd : forall (x : A) (l : list A), P x -> Exists P (x :: l)
  | Exists_cons_tl : forall (x : A) (l : list A), Exists P l -> Exists P (x :: l) *)
  Lemma ExistsP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (Exists P l) (existsb f l).
  Proof.  { intro H. eapply reflect_intro.
         induction l. simpl. constructor; intro H1; inversion H1.
         split.
         { intro H1.  inversion H1. simpl. apply /orP; left; apply /H;auto.
           simpl. apply /orP; right; apply /IHl; auto. }
         { simpl. move /orP. intro H1; destruct H1 as [H1| H2]. constructor. apply /H; auto.
           eapply Exists_cons_tl. apply /IHl; auto.  } } Qed.
  Hint Resolve ExistsP: core.      
   Check Exists_dec.
  (* Exists_dec
     : forall (A : Type) (P : A -> Prop) (l : list A),
       (forall x : A, {P x} + {~ P x}) -> {Exists P l} + {~ Exists P l} *)   
   Lemma Exists_EM P l:(forall x:A, P x \/ ~ P x )-> Exists P l \/ ~ Exists P l.
  Proof. { intros H. induction l. right. intro H1.  inversion H1.
         cut( P a \/ ~ P a).  intro Ha. cut (Exists P l \/ ~ Exists P l). intro Hl.
         { destruct Ha as [Ha1 | Ha2]; destruct Hl as [Hl1 | Hl2].
           left. constructor;auto. left; constructor;auto.
           left.  apply Exists_cons_tl;auto.
           right. intro H1. inversion H1. all:contradiction. }
         all: auto.  } Qed.
  
  Check Exists_exists.
  (* Exists_exists
     : forall (A : Type) (P : A -> Prop) (l : list A),
       Exists P l <-> (exists x : A, In x l /\ P x) *)
  Lemma existsP P f l: (forall x:A, reflect (P x)(f x))-> reflect (exists x, In x l /\ P x)(existsb f l).
  Proof. { intro H. eapply iffP with (P:= Exists P l). eapply ExistsP. apply H.
           all: apply Exists_exists. } Qed.
  Hint Resolve existsP: core. 
  Lemma exists_dec P l:
    (forall x:A, {P x} + {~ P x})-> { (exists x, In x l /\ P x) } + { ~ exists x, In x l /\ P x}.
  Proof. { intros. cut({Exists P l}+{ ~ Exists P l}). intro H;destruct H as [Hl |Hr].
         left. apply Exists_exists;auto.
         right;intro H1; apply Hr; apply Exists_exists;auto.
         eapply Exists_dec;auto.  } Qed.
  
  Lemma exists_EM P l:
     (forall x:A, P x \/ ~ P x) ->  (exists x, In x l /\ P x) \/  ~ (exists x, In x l /\ P x) .
  Proof. { intro H. cut(Exists P l \/ ~ Exists P l).
         intro H1; destruct H1 as [H1l| H1r]. left. eapply Exists_exists;auto.
         right; intro H2;apply H1r; apply Exists_exists;auto. eapply Exists_EM;auto. } Qed. 
  
    
(*----------- forallb ( boolean function) and its specifications----------------- *)
 Print forallb.
 (* fix forallb (l : list A) : bool :=
    match l with
     | nil => true
     | a :: l0 => f a && forallb l0
    end *)
 Print Forall.
 (* Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A), P x -> Forall P l -> Forall P (x :: l) *)

 Lemma ForallP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (Forall P l) (forallb f l).
 Proof.   { intro H. eapply reflect_intro.
         induction l. simpl. constructor; intro H1; inversion H1; auto.
         split.
         { intro H1.  inversion H1. simpl. apply /andP. split.  apply /H;auto.
           apply /IHl; auto. }
         { simpl. move /andP. intro H1; destruct H1 as [H1 H2]. constructor. apply /H; auto.
           apply /IHl; auto. } } Qed.
 
 Hint Resolve ForallP: core.
 Lemma Forall_EM P l:(forall x:A, P x \/ ~ P x ) -> Forall P l \/ ~ Forall P l.
 Proof.  { intros H. induction l. left. constructor. 
         cut( P a \/ ~ P a).  intro Ha. cut (Forall P l \/ ~ Forall P l). intro Hl.
         { destruct Ha as [Ha1 | Ha2]; destruct Hl as [Hl1 | Hl2].
           left. constructor;auto.
           right; intro H1;apply Hl2; inversion H1;auto.
           right; intro H1; apply Ha2; inversion H1; auto.
           right. intro H1. apply Ha2. inversion H1;auto.  }
         all: auto.  } Qed.
 Lemma forallP P f l: (forall x:A, reflect (P x) (f x) ) -> reflect (forall x, In x l -> P x) (forallb f l).
 Proof. { intro H. eapply iffP with (P:= Forall P l). eapply ForallP. apply H.
        all: apply Forall_forall. } Qed.
 
 Lemma forall_dec P  l:
   (forall x:A, {P x} + { ~ P x}) -> { (forall x, In x l -> P x) } + { ~ forall x, In x l -> P x}.
 Proof. { intros. cut({Forall P l} + {~ Forall P l}).
          intro H;destruct H as [Hl |Hr].
          left. apply Forall_forall;auto.
          right;intro H1; apply Hr; apply Forall_forall;auto.
          eapply Forall_dec; auto.  } Qed.
 Lemma forall_EM P l:
   (forall x:A, P x \/ ~ P x )->  (forall x, In x l -> P x)  \/  ~ (forall x, In x l -> P x).
 Proof. { intros H. cut(Forall P l \/ ~ Forall P l).
          intro H1; destruct H1 as [H1l| H1r]. left. eapply Forall_forall;auto.
          right; intro H2;apply H1r; apply Forall_forall;auto. eapply Forall_EM;auto. } Qed. 
 
 Lemma forall_exists_EM P l:
   (forall x:A, P x \/ ~ P x) -> (forall x, In x l -> P x) \/ (exists x, In x l /\ ~ P x).
 Proof. { intros. cut(Forall P l \/ ~ Forall P l).  
        Focus 2. eapply Forall_EM. auto.
        intro H1; destruct H1 as [Hl | Hr].
        left. apply Forall_forall. auto. right.
        cut(Exists (fun x : A => ~ P x) l). eapply Exists_exists.
        apply Exists_Forall_neg. all:auto. } Qed. 
 Lemma exists_forall_EM P l:
   (forall x:A, P x \/ ~ P x)-> (exists x, In x l /\ P x) \/ (forall x, In x l ->  ~ P x).
   Proof.  { intros. cut(Exists P l \/ ~ Exists P l).  
        Focus 2. eapply Exists_EM. auto.
        intro H1; destruct H1 as [Hl | Hr].
        left. apply Exists_exists. auto. right.
        cut(Forall (fun x : A => ~ P x) l). eapply Forall_forall.
        apply Forall_Exists_neg. all:auto. } Qed. 
  
End SetReflections.

Hint Resolve memP mem2P nodupP emptyP subsetP equalP
     existsP ExistsP ForallP forallP  mem2_comute: core.
Hint Resolve forall_exists_EM exists_forall_EM: core.




