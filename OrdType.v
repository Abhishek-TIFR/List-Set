

(* -------------------------Description--------------------------------------

   In this file we try to capture the notion of ordType. This type has
   elements with decidable equality and a less than relation with certain 
   properties. We also connect natural numbers to this type. 
 

   Structure type: Type:= 
       Pack { sort: Type;
              eqb: sort-> sort -> bool;
              ltb: sort-> sort -> bool;
              eq_P: forall x y, reflect (eq x y)(eqb x y);
              ltb_irefl: forall x, ltb x x=false;
              ltb_antisym: forall  x y, x<>y -> ltb x y = negb (ltb y x);
              ltb_trans: forall x y z, ltb x y -> ltb y z -> ltb x z }.

  Definition sort:= Order.sort.
  Definition eqb  := Order.eqb.
  Definition ltb := Order.ltb.
  Definition leb (T:ordType) := fun (x y:T) => (ltb x y || eqb x y).

  Notation "x == y":= (@eqb _ x y)(at level 70, no associativity): bool_scope.
  Notation "x <b y":= (@ltb _ x y)(at level 70, no associativity): bool_scope.
  Notation " x <=b y" := (@leb _ x y)(at level 70, no associativity): bool_scope.

  min_of a b        ==> returns the minimum among a and b
  max_of a b        ==> returns the maximum among a and b

  Some important results are:
  
  Lemma eqP  (T:ordType)(x y:T): reflect (x=y)(eqb  x y). 
  Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).
  Lemma ltP (x y:nat): reflect (x < y) (Nat.ltb x y).
  Lemma leP (x y: nat): reflect (x <= y) (Nat.leb x y).

  Canonical nat_ordType: ordType.
  refine ( {| Order.sort:= nat; Order.eqb:= Nat.eqb; Order.ltb:= Nat.ltb;
            Order.eq_P:= nat_eqP; Order.ltb_irefl:= nat_ltb_irefl;
            Order.ltb_antisym := nat_ltb_antisym;
            Order.ltb_trans := nat_ltb_trans  |}). Defined.
  
 Lemma on_comp (x y:T): CompareSpec (x=y) (x <b y) (y <b x) (comp x y).

 Ltac match_up a b := destruct (on_comp a b).
 
 Ltac conflict.                  
------------------------------ --------------- -------------------------------- *)

From Coq Require Export ssreflect  ssrbool. 
Require Export GenReflect Omega.

(* The following two options can be unset to disable the incompatible rewrite syntax 
   and allow reserved identifiers to appear in scripts. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Order.
  Structure type: Type:= Pack {
                             sort: Type;
                             eqb: sort-> sort -> bool;
                             ltb: sort-> sort -> bool;
                             eq_P: forall x y, reflect (eq x y)(eqb x y);
                             ltb_irefl: forall x, ltb x x=false;
                             ltb_antisym: forall  x y, x<>y -> ltb x y = negb (ltb y x);
                             ltb_trans: forall x y z, ltb x y -> ltb y z -> ltb x z }.
  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation ordType:= type.
    End Exports.
End Order.
Export Order.Exports.

Check Order.eqb.
Definition sort:= Order.sort.
Definition eqb  := Order.eqb.
Definition ltb := Order.ltb. 
Definition leb (T:ordType) := fun (x y:T) => (ltb x y || eqb x y).

Notation "x == y":= (@eqb _ x y)(at level 70, no associativity): bool_scope.
Notation "x <b y":= (@ltb _ x y)(at level 70, no associativity): bool_scope.
Notation " x <=b y" := (@leb _ x y)(at level 70, no associativity): bool_scope.

Lemma eqP  (T:ordType)(x y:T): reflect (x=y)(eqb  x y). 
Proof. apply Order.eq_P. Qed.


Hint Resolve eqP: hint_reflect.

Lemma eq_eqb (T:ordType)(x y:T): (x=y)-> (eqb  x y).
Proof.  intro; apply /eqP; auto. Qed.
Lemma eqb_eq (T:ordType) (x y:T): (x==y)-> (x=y).
Proof. intro;apply /eqP; auto. Qed.

Hint Immediate eq_eqb eqb_eq: core.

Lemma eq_ref (T: ordType)(x:T): x == x.
Proof. apply /eqP; auto. Qed.
Lemma eq_sym (T: ordType)(x y:T): (x==y)=(y==x).
Proof. { case (x==y) eqn:H1; case (y==x) eqn:H2;  try(auto).
       { assert (H3: x=y). apply /eqP;auto.
         rewrite H3 in H2; rewrite eq_ref in H2; inversion H2. }
       { assert (H3: y= x). apply /eqP; auto.
         rewrite H3 in H1; rewrite eq_ref in H1; inversion H1.  } } Qed.

Hint Resolve eq_ref eq_sym: core.

(* --------------------- properties of ltb -----------------------------------*)
Lemma ltb_irefl (T:ordType)(x:T): ~ ltb x x.
Proof. switch. eapply Order.ltb_irefl.  Qed.


Lemma ltb_not_eq (T:ordType)(x y:T): ltb x y -> x<>y.
Proof. { intros H1 H2. rewrite H2 in H1.
         generalize H1. switch. switch. apply ltb_irefl. } Qed.
Lemma eq_not_ltb (T:ordType)(x y:T): x=y ->  ~ ltb x y.
Proof.  intro H; rewrite H.  apply ltb_irefl.  Qed.


Lemma ltb_antisym0 (T:ordType)(x y:T):  x<>y -> ltb x y = negb (ltb y x).
Proof. apply Order.ltb_antisym. Qed.
Lemma ltb_antisym (T:ordType)(x y:T): ltb x y ->  ~ ltb y x.
Proof. { intros H1. replace (ltb y x) with (negb (ltb x y)).
       rewrite H1; simpl; auto.
       symmetry; apply ltb_antisym0; auto.
       intro H;symmetry in H.
       eapply ltb_not_eq;eauto.  } Qed.
Lemma ltb_antisym2 (T:ordType)(x y:T): x<>y-> ~ ltb x y ->  ltb y x.
Proof. { intros H H1. replace (ltb y x) with (negb(ltb x y)).
       switch_in H1. rewrite H1; simpl; auto.
       symmetry; apply ltb_antisym0; auto.  } Qed. 
Lemma ltb_trans (T:ordType)(x y z:T): ltb x y -> ltb y z -> ltb x z.
Proof. apply Order.ltb_trans. Qed.


Hint Resolve ltb_irefl ltb_not_eq eq_not_ltb ltb_antisym ltb_antisym2:core.
Hint Resolve ltb_trans: core.


(*---------------------- properties of leb ----------------------------------*)
Lemma leb_refl (T: ordType)(x:T): x <=b x.
Proof. unfold "<=b"; apply /orP. right; eauto. Qed.

Lemma eq_leb (T:ordType)(x y:T): x=y -> x <=b y.
Proof. unfold "<=b". intro;right_;auto. Qed.

Lemma ltb_leb (T: ordType)(x y:T): x <b y -> x <=b y.
Proof. unfold "<=b". intro. left_; auto.  Qed. 

Lemma leb_antisym (T: ordType)(x y:T): x <=b y -> y <=b x -> x=y.
Proof. unfold "<=b". move /orP. intro H; move /orP.
       intros H1. destruct H; destruct H1.
       cut (False); [tauto | eapply ltb_antisym; eauto].
       all: apply /eqP; eauto. Qed.


Hint Resolve leb_refl eq_leb ltb_leb leb_antisym: core.

Lemma leb_antisym1 (T: ordType)(x y:T): x <=b y = false -> y <=b x.
Proof. move /orP. intro H. cut ((~ x <b y) /\( ~ x == y)).
       intro H1. destruct H1 as [H1 H2].  apply ltb_leb.
       apply ltb_antisym2; eauto. tauto. Qed.

Lemma leb_antisym2 (T: ordType)(x y:T): x <> y -> x <=b y -> x <b y.
Proof. intros H H1. move /orP in H1. destruct H1. auto. absurd (x=y); eauto. Qed.

Hint Resolve leb_antisym1 leb_antisym2 : core.

Lemma leb_trans (T: ordType) (x y z:T): x <b y -> y <=b z -> x <=b z.
Proof. intros H H1. move /orP in H1. destruct H1. left_;eauto.
       replace z with y;eauto.  Qed.

Lemma leb_trans1 (T: ordType) (x y z:T): x <=b y -> y <b z -> x <=b z.
Proof. intros H H1; move /orP in H; destruct H. left_;eauto.
       replace x with y. eauto. symmetry;eauto.  Qed.

Lemma leb_trans2 (T: ordType) (x y z:T): x <=b y -> y <=b z -> x <=b z.
Proof. intros H H1. move /orP in H1.  destruct H1. eauto using leb_trans1.
       replace z with y;eauto. Qed.

Lemma leb_trans3 (T: ordType) (x y z:T): x <=b y -> y = z -> x <=b z.
Proof. intros H H1. replace z with y. eauto. Qed.

Lemma leb_trans4 (T: ordType) (x y z:T): x = y -> y <=b z -> x <=b z.
Proof. intros H H1. replace x with y. eauto. Qed.
Hint Resolve leb_trans leb_trans1 leb_trans2 leb_trans3 leb_trans4: core.


(*---------Ltac command for all the contradictory situations -------------*)

Lemma leb_not_gt (T:ordType)(x y z:T): x <=b y -> ~ (y <b x).
Proof. intros H H1. move /orP in H. destruct H.
       revert H; apply ltb_antisym;auto. move /eqP in H. symmetry in H.
       revert H. apply ltb_not_eq. auto. Qed.

Ltac conflict:=
    match goal with
    | H: is_true (?x <b ?y), H1: is_true (?y <b ?x)  |- _
       => cut (False); [tauto | eapply ltb_antisym; eauto]
    | H: is_true (?x <=b ?y), H1: is_true (?y <b ?x)  |- _
       => cut (False); [tauto | eapply leb_not_gt; eauto]
    | H: is_true (?x == ?y), H1: is_true (?x <b ?y)  |- _
       => cut (False); [tauto | move /eqP in H; eapply ltb_not_eq; eauto]
    | H: is_true (?y == ?x), H1: is_true (?x <b ?y)  |- _
      => cut (False); [tauto | move /eqP in H; eapply ltb_not_eq; eauto]
    | H:  ?x = ?y, H1: is_true (?x <b ?y)  |- _
      => cut (False); [tauto | eapply ltb_not_eq; eauto]
    | H:  ?y = ?x, H1: is_true (?x <b ?y)  |- _
       => cut (False); [tauto | eapply ltb_not_eq; eauto]                 
    end.
                                                              

(*--------- Natural numbers is an instance of ordType---------------------*)

Lemma nat_eqb_ref (x:nat): Nat.eqb x x = true.
Proof. induction x;simpl;auto. Qed.
Hint Resolve nat_eqb_ref:core.

Lemma nat_eqb_elim (x y:nat):  Nat.eqb x y -> x = y.
Proof. { revert y. induction x.
       { intro y. case y. tauto. simpl; intros n H; inversion H. }
       intro y. case y. simpl; intro H; inversion H. simpl. eauto. } Qed.
Hint Resolve nat_eqb_elim: core.

Lemma nat_eqb_intro (x y:nat): x=y -> Nat.eqb x y.
Proof. intro H. subst x. eauto. Qed.
Hint Resolve nat_eqb_intro: core.

Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).
Proof. apply reflect_intro. split;eauto. Qed. 
Hint Resolve nat_eqP: core.

Lemma nat_ltb_irefl (x : nat): Nat.ltb x x = false.
Proof. induction x; unfold "<?"; auto. Qed.
Hint Resolve nat_ltb_irefl: core.

Lemma nat_ltb_antisym (x y:nat):  x <> y -> Nat.ltb x y = ~~ Nat.ltb y x.
Proof. { unfold "<?". revert y. induction x.
       { intro y. case y. tauto. simpl. auto. }
       { intro y. case y.  simpl. auto. intro n.
         intro H. replace (S (S x) <=? S n) with (S x <=? n);
         replace (S (S n) <=? S x) with ( S n <=? x ); eauto. } } Qed.
Hint Resolve nat_ltb_antisym: core.


Lemma ltP (x y:nat): reflect (x < y) (Nat.ltb x y).
Proof. { apply reflect_intro. split.
       { unfold "<"; unfold "<?".
         revert y. induction x. intro y; case y. simpl.
         intro H. inversion H. simpl. auto.
         intro y;case y.
         intro H; inversion H. intros n H. 
         replace (S (S x) <=? S n) with (S x <=? n). apply IHx. omega.
         simpl. auto. }
       { unfold "<"; unfold "<?".
         revert y. induction x. intro y; case y. simpl.
         intro H. inversion H. intros; omega.
         intro y;case y. simpl. intro H; inversion H.
         intro n. replace (S (S x) <=? S n) with (S x <=? n).
         intro H; apply IHx in H. omega. simpl;auto. } } Qed.

Lemma leP (x y: nat): reflect (x <= y) (Nat.leb x y).
Proof. { apply reflect_intro. split.
       { revert y. induction x. intro y; case y; simpl; auto.
         intro y;case y.
         intro H; inversion H. intros n H. 
         replace (S  x <=? S n) with ( x <=? n). apply IHx. omega.
         simpl. auto. }
       { revert y. induction x. intro y; case y; intros; omega. 
         intro y;case y. simpl. intro H; inversion H.
         intro n. replace (S x <=? S n) with ( x <=? n).
         intro H; apply IHx in H. omega. simpl;auto. } } Qed.

Hint Resolve leP ltP nat_eqP: hint_reflect.

Lemma nat_ltb_trans (x y z:nat):  Nat.ltb x y -> Nat.ltb y z -> Nat.ltb x z.
Proof. intros H H1.  move /ltP in H;  move /ltP in H1; apply /ltP. omega. Qed. 
Hint Resolve nat_ltb_trans: core.

Canonical nat_ordType: ordType.
refine ( {| Order.sort:= nat; Order.eqb:= Nat.eqb; Order.ltb:= Nat.ltb;
            Order.eq_P:= nat_eqP; Order.ltb_irefl:= nat_ltb_irefl;
            Order.ltb_antisym := nat_ltb_antisym;
            Order.ltb_trans := nat_ltb_trans  |}). Defined.


Section CompSpec.
  Variable T: ordType.

  Definition comp (x y:T): comparison:= match (x==y) with
                                        | true => Eq
                                        |false => match (ltb x y) with
                                                 | true => Lt
                                                 |false => Gt
                                                 end
                                        end.
  Lemma on_comp (x y:T): CompareSpec (x=y) (x <b y) (y <b x) (comp x y).
  Proof. { unfold comp. case (x==y) eqn:H.
         { constructor.  apply /eqP;auto. }
         { case (ltb x y) eqn:H1.
           constructor;auto. constructor. switch_in H1.
           cut (x<>y). eauto. switch_in H. move /eqP. auto.  } } Qed. 
  
End CompSpec.


Ltac match_up a b := destruct (on_comp a b).



Section Min_Max.
  
  Context {A: ordType}.
  
   Definition max_of (a b :A): A := match comp a b with
                                   |Eq => a
                                   |Lt => b
                                   |Gt => a
                                   end.
  
  Lemma max_of_spec1 (a b: A): a <b max_of a b \/ a = max_of a b.
  Proof. unfold max_of. destruct (on_comp a b); tauto. Qed.
  Lemma max_of_spec2 (a b: A): b <b max_of a b \/ b = max_of a b.
  Proof. unfold max_of. destruct (on_comp a b).
         symmetry in H;tauto. all: tauto. Qed.
  Lemma max_of_spec3 (a b c:A): c <b a -> c <b max_of a b.
  Proof.  unfold max_of. destruct (on_comp a b). all: try tauto. intro; eauto. Qed.
  Lemma max_of_spec4 (a b c:A): c <b b -> c <b max_of a b.
  Proof. unfold max_of. destruct (on_comp a b). subst a.  all: try tauto. intro; eauto. Qed.

  Lemma max_of_spec5 (a: A): a = (max_of a a).
    Proof.  unfold max_of; match_up a a;auto. Qed.

    Hint Resolve max_of_spec1 max_of_spec2 max_of_spec3 max_of_spec4 max_of_spec5: core.

   Definition min_of (a b :A): A:= match comp a b with
                                  |Eq => a
                                  |Lt => a
                                  |Gt => b
                                   end.
   Lemma min_of_spec1 (a b: A): min_of a b <b a \/ min_of a b = a.
   Proof. unfold min_of. destruct (on_comp a b); tauto. Qed.

   Lemma min_of_spec2 (a b: A): min_of a b <b b \/ min_of a b = b.
   Proof. unfold min_of. destruct (on_comp a b). tauto. all: tauto. Qed.

   Lemma min_of_spec3 (a b c:A): a <b c -> min_of a b <b c.
   Proof.  unfold min_of. destruct (on_comp a b). all: try tauto. intro; eauto. Qed.
   Lemma min_of_spec4 (a b c:A): b <b c ->  min_of a b <b c.
   Proof. unfold min_of. destruct (on_comp a b). subst a.  all: try tauto. intro; eauto. Qed.

    Lemma min_of_spec5 (a: A): a = (min_of a a).
    Proof.  unfold min_of; match_up a a;auto. Qed.

   Hint Resolve min_of_spec1 min_of_spec2 min_of_spec3 min_of_spec4 min_of_spec5: core.

  
End Min_Max.


Hint Resolve max_of_spec1 max_of_spec2 max_of_spec3 max_of_spec4 max_of_spec5: core.
Hint Resolve min_of_spec1 min_of_spec2 min_of_spec3 min_of_spec4 min_of_spec5: core.