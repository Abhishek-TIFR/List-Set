

(*-------------Description --------------------------------------------------------------  

This file implements the union of all sets present in a list C as (union_over C). We 
then define the notion of sets covers (Set_Cov C l) as a proposition which 
states that the collection of sets C is a cover for the set l. Furthermore, we also
define a function (mk_disj C) which produces another collection of sets which are 
disjoint to each other.  
 

Following are the exact deinition of these  notions present in this file:

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
 

Furthermore, we have the following results specifying these definitions:

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

  Lemma union_over_intro3 (C: list (list A))(c: list A)(x:A): In x c -> In x (union_over (c::C)).
  Proof. simpl. auto. Qed.

  Lemma union_over_intro4 (C: list (list A))(c: list A)(x:A):
    In x (union_over C) -> In x (union_over (c::C)).
  Proof. simpl;auto. Qed.
  
 
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

  Lemma union_over_elim1 (C: list (list A))(c: list A)(x:A):
    In x (union_over (c::C)) -> (In x c \/ In x (union_over C)).
  Proof. simpl. auto. Qed.
  

  Hint Resolve union_over_intro union_over_intro1: core.
  Hint Resolve union_over_intro3 union_over_intro4: core.
  
  Hint Immediate union_over_elim union_over_elim1: core.

  Lemma union_over_intro2 (C: list (list A))(S: list A):
    (forall X, In X C -> X [<=] S) -> (union_over C [<=] S).
  Proof. { intros h1 x h2. specialize (union_over_elim C x h2) as h3.
           destruct h3 as [l h3]. cut (In x l). apply h1. all: apply h3. } Qed.

  Hint Immediate union_over_intro2: core.

  Lemma union_over_IsOrd (C: list (list A)): IsOrd (union_over C).
  Proof. induction C as [| c C']. simpl; constructor. simpl;auto. Qed.
  
 Hint Resolve union_over_IsOrd: core.
  

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

  Definition set_cover (C: list (list A)) (l: list A):= (l == (union_over C)).

  Definition Set_cover (C: list (list A)) (l: list A):=  l = (union_over C).

  Lemma set_coverP (C: list (list A))(l: list A): reflect (Set_cover C l)(set_cover C l).
  Proof. { unfold Set_cover. unfold set_cover. auto.  } Qed.

  Lemma Set_cover_elim (C: list (list A)) (l: list A)(c: list A):
    Set_cover C l -> In c C -> c [<=] l.
  Proof. { unfold Set_cover. intros h1 h2 x h3. subst l.
           eapply union_over_intro; eauto. } Qed.

  Lemma Set_cover_elim1 (C: list (list A)) (l: list A)(x: A):
    Set_cover C l -> In x l-> (exists c, In c C /\ In x c).
  Proof. unfold Set_cover. intro h1. subst l. auto. Qed.
  

  Lemma Set_cover_IsOrd (C: list (list A)) (l: list A): Set_cover C l -> IsOrd l.
  Proof. unfold Set_cover;intros;subst l;auto. Qed.

  Hint Resolve Set_cover_IsOrd: core.
  Hint Immediate Set_cover_elim Set_cover_elim1: core.

  Lemma cover_dij_intro (C: list (list A)) (c: list A):
    (forall y, In y C -> (c [i] y = nil))-> (c [i] (union_over C) = nil).
  Proof. { intros h1.
           assert (h2: (c [i] union_over C = nil) \/ ~(c [i] union_over C = nil)).
           { eauto. }
           destruct h2 as [h2 | h2].
           { auto. }
           { assert (h3: exists x, In x (c [i] union_over C)). auto.
             destruct h3 as [x h3].
             assert (h3a: In x c). eauto.
             assert (h3b: In x (union_over C)). eauto.
             assert (h3c: exists c', In c' C /\ In x c'). auto.
             destruct h3c as [c' h3c]. destruct h3c as [h3c h3d].
             specialize (h1 c' h3c) as h4.
             absurd (In  x (c [i] c')). rewrite h4. auto. auto. } } Qed.

 
  

   Lemma cover_dij_elim (C: list (list A)) (c: list A):
     (c [i] (union_over C) = nil) -> (forall y, In y C -> (c [i] y = nil)).
   Proof. { induction C as [| c' C'].
            { simpl. auto. }
            { simpl. intros h1 y h2.
              destruct h2 as [h2 | h2].
              { subst y.  eauto. }
              { apply IHC'. eauto. auto. } } } Qed.

                
Hint Immediate cover_dij_elim cover_dij_intro: core.
  

  (*------------- Cardinalities and set covers ------------------------------------------*)


  Lemma disj_cover_card (C: list (list A))(l: list A)(n: nat):
    Set_cover C l -> NoDup C-> (forall x, In x C -> (IsOrd x /\ |x|=n))->
    (forall x y, In x C -> In y C-> x <> y -> x [i] y = nil)-> |l| = |C| * n.
  Proof. { revert l. induction C as [|c C'].
           { intros l h1 h2 h3 h4. unfold Set_cover in h1.
             subst l. simpl. auto. }
           { intros l h1 h2 h3 h4. unfold Set_cover in h1.
             subst l. simpl.
             replace (| c [u] union_over C' |) with (|c| + |union_over C'|).
             set (l':= union_over C').
             assert (h5: Set_cover C' l').
             { unfold Set_cover. subst l'. auto. }
             assert (h6: (|l'|) = (|C'|)* n).
             { apply IHC'. auto. eauto.
               intros x h6. apply h3. auto.
               intros x y hx hy. apply h4. all: auto. } 
             rewrite h6. cut (|c| = n). omega.
             apply h3. auto. symmetry; apply inc_exc1.
             apply h3. auto. apply cover_dij_intro.
             intros y h5. apply h4. auto. auto. intro h6; subst c.
             absurd (In y C'); auto. } } Qed.
 
   
  Lemma large_set_in_cover (C: list (list A))(l: list A):
   l <> nil-> (forall x, In x C -> IsOrd x)-> Set_cover C l -> (exists x, In x C /\ (|x| * |C|) >= |l|).
  Proof. { revert l. induction C as [| c C'].
           { intros l h1 h2.  unfold Set_cover in h2. simpl in h2. contradiction. }
           { intros l h1 h2 hl.
             set (l':= union_over C').
             assert (h3: l = c [u] l').
             { unfold Set_cover in hl. subst l;subst l'. simpl. auto. }
             assert (h4: l' = nil \/ l' <> nil). eauto.
             destruct h4 as [h4 | h4].
             { (* ----l' = nil--- *) 
               exists c. split. auto. rewrite h4 in h3.
               replace (c [u] nil) with (nil [u] c) in h3. simpl in h3.
               subst l. simpl. auto using mult_le.
               apply union_equal. constructor. auto. }
             { (*-----  l' <> nil -----*)
               specialize (IHC' l' h4) as h4a.
               assert (h6: exists x : list A, In x C' /\ (| x |) * (| C' |) >= (| l' |)).
               { apply h4a. intros x h6. apply h2. auto.
                 unfold Set_cover. subst l';auto. }
               destruct h6 as [x' h6].
               
               assert (h7: (|c| <= |x'|) \/ ~ (|c| <= |x'|)). eauto.
               destruct h7 as [h7 | h7].
               {(*-- (| c |) <= (| x' |) --*)
                 exists x'.
                 split.
                 { cut (In x' C'). auto. apply h6. }
                 { destruct h6 as [h6 h6a]. simpl. rewrite h3.
                   assert (h8: (| c [u] l' |) <= (|c|) + (|l'|)).
                   { cut (IsOrd c). cut (IsOrd l'). auto.
                     subst l'. auto. auto. }
                   assert (h9: (| c |) + (| l' |) <=  (| c |) + (| x' |) * (| C' |) ).
                   omega.
                   assert (h10: (| c |) + (| x' |) * (| C' |) <= (| x' |) + (| x' |) * (| C' |)).
                   omega.
                   replace ((| x' |) * S (| C' |)) with ((| x' |) * (| C' |) + |x'|).
                   omega. auto with arith. } }
               {(*--- ~ (| c |) <= (| x' |) ----*)
                 assert (h7a: |c| > |x'|). omega.
                 exists c.
                 split.
                 { auto. }
                 { destruct h6 as [h6 h6a]. simpl. rewrite h3.
                   assert (h8: (| c [u] l' |) <= (|c|) + (|l'|)).
                   { cut (IsOrd c). cut (IsOrd l'). auto.
                     subst l'. auto. auto. }
                   assert (h9: (| c |) + (| l' |) <=  (| c |) + (| x' |) * (| C' |) ).
                   omega.
                   assert (h9a:  (| x' |) * (| C' |) <=  (| c |) * (| C' |) ).
                   { apply mult_le1. omega. }
                   assert (h10: (| c |) + (| x' |) * (| C' |) <= (| c |) + (| c |) * (| C' |)).
                   omega.
                   replace ((| c |) * S (| C' |)) with ((| c |) * (| C' |) + |c|).
                   omega. auto with arith. } } } } } Qed. 

 
End SetCover.




Hint Resolve in_map map_cons map_length: core.
Hint Immediate in_map_iff: core.

Hint Resolve union_over_intro3 union_over_intro4: core.
Hint Immediate union_over_elim union_over_elim1: core.
Hint Immediate union_over_intro2: core.
Hint Resolve union_over_IsOrd: core.


Hint Resolve Set_cover_elim:core.
Hint Resolve Set_cover_IsOrd: core.

Notation "l [,] n" := (fix_nat n l) (at level 65).

 Hint Immediate cover_dij_elim cover_dij_intro: core.


Section LocateInC.

  Context { A: ordType }.
  

  (*--- Following function (idc x C) finds the location of set in C which contains x ----*)
  Fixpoint idc (x:A)(C: list (list A)):= match C with
                                |nil => 0
                                |c::C' => match (memb x c) with
                                        | true => 1
                                        |false => match (memb x (union_over C')) with
                                                 |true => S (idc x C')
                                                 |false => 0
                                                 end
                                         end
                                          end.

Lemma absnt_idc_zero (x:A)(C:list (list A)): ~ In x (union_over C) -> (idc x C) = 0.
Proof. { induction C.
       { simpl. auto. }
       { intro H. simpl.
         replace (memb x a) with false. replace (memb x (union_over C)) with false. auto.
         symmetry;switch; auto.
         symmetry;switch. move /membP. intro H1. auto.  } } Qed.

Lemma idc_zero_absnt (x:A)(C:list (list A)): (idc x C) = 0 -> ~ In x (union_over C).
Proof. { induction C.
         { simpl. auto. }
         { intros H1 H2. inversion H1.
           destruct (memb x a) eqn:Hxa. inversion H0.
           destruct (memb x (union_over C)) eqn: Hxl. move /membP in Hxl.
           inversion H0. assert (H3: In x a \/ In x (union_over C)). auto.
           destruct H3.
           { move /membP in Hxa. contradiction. }
           { move /membP in Hxl. contradiction. } } } Qed.

Lemma idc_gt_zero (x:A)(C:list (list A)) : In x (union_over C) -> (idc x C) > 0.
Proof. { intro H. assert (H1: idc x C = 0 \/ ~ idc x C = 0). eauto.
       destruct H1.
       { absurd (In x (union_over C)). apply idc_zero_absnt. auto. auto. }
       { omega. } } Qed.

Lemma idc_is_one (x:A)(c: list A)(C: list (list A)): In x c -> idc x (c::C) = 1.
Proof. simpl. intro h1. replace (memb x c) with true; auto. Qed.

Hint Immediate absnt_idc_zero idc_zero_absnt idc_gt_zero idc_is_one: core.

Lemma idc_from_idx (x: A)(C: list (list A)): In x (union_over C)->
                                             exists c, In c C /\  In x c /\ idc x C = idx c C.
Proof. { revert x. induction C as [|l C'].
       { intros x. simpl. tauto. }
       { intros x h1. 
         assert (h2: In x l \/ In x (union_over C')). auto.
         simpl idc. destruct (memb x l) eqn: Hxl.
         { exists l. split. auto.  split. move /membP in Hxl. auto. symmetry;auto. }
         { assert (h3: In x (union_over C')).
           { destruct h2. move /membP in Hxl. contradiction. auto. }
           specialize (IHC' x h3) as h4.
           destruct h4 as [c h4].
           exists c. split. cut (In c C'). auto. apply h4.
           split. apply h4. replace (memb x (union_over C')) with true.
           simpl idx. replace (eqbl c l) with false. replace (memb c C') with true.
           cut (idc x C' = idx c C'). omega. apply h4.
           symmetry; apply /membP; apply h4.
           symmetry. apply /eqP.
           intro h5. subst c.
           absurd (In x l). move /membP in Hxl; auto. apply h4.
           symmetry;auto. } } } Qed.

Lemma idc_eq_both_in (x y: A)(C: list (list A)): In x (union_over C) -> idc x C = idc y C ->
                                                 In y (union_over C).
Proof. { intros h1 h2.
         assert (h3: In y (union_over C) \/ ~ In y (union_over C)). eauto.
         destruct h3 as [h3 | h3]. auto.
         replace (idc y C) with 0 in h2.
         absurd (In x (union_over C));auto. symmetry;auto. } Qed.


Lemma idc_eq_same_set (x y: A)(C: list (list A)): In x (union_over C) -> idc x C = idc y C ->
                                                  exists c, In c C /\ In x c /\ In y c.
Proof. { intros h1 h2. specialize (idc_eq_both_in x y C h1 h2) as h3.
         apply idc_from_idx in h1 as h1a. apply idc_from_idx in h3 as h3a.
         destruct h1a as [c1 h1a]. destruct h3a as [c2 h3a].
         assert (h4: c1 = c2).
         { cut (idx c1 C = idx c2 C).
           cut (In c2 C).
           cut (In c1 C).
           apply same_index. apply h1a. apply h3a.
           cut (idc x C = idx c1 C).
           cut (idc y C = idx c2 C).
           intros;omega. apply h3a. apply h1a. }
         subst c2. exists c1.
         split. apply h1a.  split. apply h1a. apply h3a. } Qed.


         
End LocateInC.

Hint Immediate absnt_idc_zero idc_zero_absnt idc_gt_zero idc_is_one: core.

Hint Immediate idc_from_idx idc_eq_same_set: core.
  
  
 
