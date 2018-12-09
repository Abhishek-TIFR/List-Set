

(* -------------------------Description--------------------------------------

   In this file we  capture the notion of ordType. This type has
   elements with decidable equality and a less than relation with certain 
   properties. We also connect natural numbers to this type. 
 

   Structure type: Type:= 
       Pack { D: Type;
              ltb: E-> E -> bool;
              ltb_irefl: forall x, ltb x x=false;
              ltb_antisym: forall  x y, x<>y -> ltb x y = negb (ltb y x);
              ltb_trans: forall x y z, ltb x y -> ltb y z -> ltb x z }.

  Definition E:= Order.E.
  Definition eqb  := Order.eqb.
  Definition ltb := Order.ltb.
  Definition leb (T:ordType) := fun (x y:T) => (ltb x y || eqb x y).

  Notation "x =b y":= (@eqb _ x y)(at level 70, no associativity): bool_scope.
  Notation "x <b y":= (@ltb _ x y)(at level 70, no associativity): bool_scope.
  Notation " x <=b y" := (@leb _ x y)(at level 70, no associativity): bool_scope.

  min_of a b        ==> returns the minimum among a and b
  max_of a b        ==> returns the maximum among a and b

  Some important results are:
  
  Lemma eqP  (T:ordType)(x y:T): reflect (x=y)(eqb  x y). 
  Lemma nat_eqP (x y:nat): reflect (x=y)(Nat.eqb x y).
  Lemma ltP (x y:nat): reflect (x < y) (Nat.ltb x y).
  Lemma leP (x y: nat): reflect (x <= y) (Nat.leb x y).
  Lemma lebP (x y: nat): reflect (x <= y) (leb x y).

  Canonical nat_ordType: ordType.
  refine ( {| Order.E:= nat; Order.eqb:= Nat.eqb; Order.ltb:= Nat.ltb;
            Order.eq_P:= nat_eqP; Order.ltb_irefl:= nat_ltb_irefl;
            Order.ltb_antisym := nat_ltb_antisym;
            Order.ltb_trans := nat_ltb_trans  |}). Defined.
  
 Lemma on_comp (x y:T): CompareSpec (x=y) (x <b y) (y <b x) (comp x y).

 Ltac match_up a b := destruct (on_comp a b).
 
 Ltac conflict.                  
------------------------------ --------------- -------------------------------------- *)

From Coq Require Export ssreflect  ssrbool. 
Require Export GenReflect Omega DecType.

(* The following two options can be unset to disable the incompatible rewrite syntax 
   and allow reserved identifiers to appear in scripts. *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Order.
  Definition E:= Decidable.E.
  Definition eqb:= Decidable.eqb.
  Definition eq_P:= Decidable.eqP.
  
  Structure type: Type:= Pack {
                             D : eqType;
                             ltb: E D -> E D -> bool;
                             ltb_irefl: forall x, ltb x x=false;
                             ltb_antisym: forall  x y, x<>y -> ltb x y = negb (ltb y x);
                             ltb_trans: forall x y z, ltb x y -> ltb y z -> ltb x z }.
  Module Exports.
    Coercion D : type >-> eqType.
    Notation ordType:= type.
    End Exports.
End Order.
Export Order.Exports.


Definition E:= Order.E.
Definition eqb  := Order.eqb.
Definition ltb := Order.ltb. 
Definition leb (T:ordType) := fun (x y:T) => (ltb x y || eqb x y).

Notation "x =b y":= (@eqb _ x y)(at level 70, no associativity): bool_scope.
Notation "x <b y":= (@ltb _ x y)(at level 70, no associativity): bool_scope.
Notation " x <=b y" := (@leb _ x y)(at level 70, no associativity): bool_scope.

Lemma eq_P  (T:ordType)(x y:T): reflect (x=y)(eqb  x y). 
Proof. apply Order.eq_P. Qed.


Hint Resolve eq_P: hint_reflect.

Lemma eq_eqb (T:ordType)(x y:T): (x=y)-> (eqb  x y).
Proof.  intro; apply /eq_P; auto. Qed.
Lemma eqb_eq (T:ordType) (x y:T): (x =b y)-> (x=y).
Proof. intro;apply /eq_P; auto. Qed.

Hint Immediate eq_eqb eqb_eq: core.

Lemma eq_ref (T: ordType)(x:T): x =b x.
Proof. apply /eq_P; auto. Qed.
Lemma eq_sym (T: ordType)(x y:T): (x=b y)=(y =b x).
Proof. { case (x=b y) eqn:H1; case (y=b x) eqn:H2;  try(auto).
       { assert (H3: x=y). apply /eq_P;auto.
         rewrite H3 in H2; rewrite eq_ref in H2; inversion H2. }
       { assert (H3: y= x). apply /eq_P; auto.
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
Lemma ltb_trans1 (T:ordType)(x y z:T): ltb x y -> y=z -> ltb x z.
Proof. intros;subst z;auto. Qed.
Lemma ltb_trans2 (T:ordType)(x y z:T): x=y-> ltb y z -> ltb x z.
Proof. intros;subst x;auto. Qed.

Hint Resolve ltb_irefl ltb_not_eq eq_not_ltb ltb_antisym ltb_antisym2:core.

Hint Extern 0 (is_true (?x <b ?z) ) =>
match goal with
| H: is_true (x <b ?y) |- _ => apply (@ltb_trans _ x y z)
| H: is_true (?y <b z) |- _ => apply (@ltb_trans  _ x y z)                                   
end.

Hint Resolve ltb_trans1 ltb_trans2: core. 


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
       all: apply /eq_P; eauto. Qed.


Hint Resolve leb_refl eq_leb ltb_leb leb_antisym: core.

Lemma leb_antisym1 (T: ordType)(x y:T): x <=b y = false -> y <=b x.
Proof. move /orP. intro H. cut ((~ x <b y) /\( ~ x =b y)).
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

Hint Extern 0 (is_true (?x <=b ?z) ) =>
match goal with
| H: is_true (x <=b ?y) |- _ => apply (@leb_trans2 _ x y z)
| H: is_true (?y <=b z) |- _ => apply (@leb_trans2 _ x y z)                                   
end.

Lemma leb_trans3 (T: ordType) (x y z:T): x <=b y -> y = z -> x <=b z.
Proof. intros H H1. replace z with y. eauto. Qed.

Lemma leb_trans4 (T: ordType) (x y z:T): x = y -> y <=b z -> x <=b z.
Proof. intros H H1. replace x with y. eauto. Qed.
Hint Resolve leb_trans leb_trans1 leb_trans3 leb_trans4: core.


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
       => cut (False); [tauto | eapply leb_not_gt; eauto ]
    | H: is_true (?x =b ?y), H1: is_true (?x <b ?y)  |- _
       => cut (False); [tauto | move /eqP in H; eapply ltb_not_eq; eauto]
    | H: is_true (?y =b ?x), H1: is_true (?x <b ?y)  |- _
      => cut (False); [tauto | move /eqP in H; eapply ltb_not_eq; eauto]
    | H:  ?x = ?y, H1: is_true (?x <b ?y)  |- _
      => cut (False); [tauto | eapply ltb_not_eq; eauto]
    | H:  ?y = ?x, H1: is_true (?x <b ?y)  |- _
      => cut (False); [tauto | eapply ltb_not_eq; eauto]
    | H: is_true ( ?x <b ?x) |- _
      => absurd (x <b x);auto                      
    end.

Ltac by_conflict :=  (conflict_eq || conflict ).

(*--------- Natural numbers is an instance of ordType---------------------*)

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


Hint Resolve leP ltP nat_eqP: core.

Lemma nat_ltb_trans (x y z:nat):  Nat.ltb x y -> Nat.ltb y z -> Nat.ltb x z.
Proof. intros H H1.  move /ltP in H;  move /ltP in H1; apply /ltP. omega. Qed. 
Hint Resolve nat_ltb_trans: core.

Canonical nat_ordType: ordType.
refine ( {| Order.D:= nat_eqType;
            Order.ltb:= Nat.ltb;
            Order.ltb_irefl:= nat_ltb_irefl;
            Order.ltb_antisym := nat_ltb_antisym;
            Order.ltb_trans := nat_ltb_trans  |}). Defined.

Lemma lebP (x y: nat): reflect (x <= y) (leb x y).
Proof. { apply reflect_intro. split.
       { intro H. unfold "<=b". apply /orP.
         destruct H. right. auto. left. apply /ltP. omega. }
       { unfold "<=b". move /orP. intro H.
         destruct H. move /ltP in H; omega. move /eqP in H.
         subst x;auto. } } Qed.
Hint Resolve lebP:core.


Section CompSpec.
  Variable T: ordType.

  Definition comp (x y:T): comparison:= match (x=b y) with
                                        | true => Eq
                                        |false => match (ltb x y) with
                                                 | true => Lt
                                                 |false => Gt
                                                 end
                                        end.
  Lemma on_comp (x y:T): CompareSpec (x=y) (x <b y) (y <b x) (comp x y).
  Proof. { unfold comp. case (x=b y) eqn:H.
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