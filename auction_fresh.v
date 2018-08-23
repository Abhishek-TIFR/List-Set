





Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs SetReflect.
Require Export OrdList OrdSet.



Record Bid:Type:= Mk_bid{
                        b_id:>nat;
                        bp:nat  }.

Definition b_eqb (x y:Bid): bool:= (b_id x == b_id y) && ( bp x == bp y).
Definition b_ltb (x y: Bid): bool:= (bp x <? bp y) || ((bp x == bp y) && (b_id x <? b_id y)).


 
Record Ask:Type:= Mk_ask{
                        s_id:>nat;
                        sp:nat   }.


Definition a_eqb (x y: Ask): bool:= (s_id x == s_id y) && (  sp x ==  sp y).
Definition a_ltb (x y:  Ask): bool:= ( sp x <?  sp y) || (( sp x ==  sp y) && (s_id x <? s_id y)).

(*----------------  Attaching Bid to the ordType ----------------------------------*)
Lemma b_eqb_ref (x:Bid): b_eqb x x = true.
Proof. Admitted.
Hint Resolve b_eqb_ref: hint_auction.
Lemma b_eqb_elim (x y:Bid):  b_eqb x y -> x = y.
Proof. Admitted.

Lemma b_eqb_intro (x y:Bid): x=y -> b_eqb x y = true.
Proof. Admitted.

Hint Immediate b_eqb_elim b_eqb_intro: hint_auction.

Lemma b_eqP (x y:Bid): reflect (x=y)(b_eqb x y).
Proof. apply reflect_intro. split; auto with hint_auction. Qed. 
Hint Resolve b_eqP: hint_auction.

Lemma b_ltb_irefl (x : Bid): b_ltb x x = false.
Proof. Admitted.
Hint Resolve b_ltb_irefl: hint_auction.

Lemma b_ltb_antisym (x y:Bid):  x <> y -> b_ltb x y = ~~ b_ltb y x.
Proof. Admitted.
Hint Resolve b_ltb_antisym: hint_auction.

Lemma b_ltb_trans (x y z:Bid):  b_ltb x y -> b_ltb y z -> b_ltb x z.
Proof. Admitted.
Hint Resolve b_ltb_trans: hint_auction.

Canonical bid_ordType: ordType:= {| Order.sort:= Bid; Order.eqb:= b_eqb; Order.ltb:= b_ltb; Order.eq_P:=b_eqP;
            Order.ltb_irefl:=b_ltb_irefl; Order.ltb_antisym:= b_ltb_antisym;
            Order.ltb_trans:= b_ltb_trans|}.

(*------------------ Attaching Ask to ordType ------------------------------------ *)

Lemma a_eqb_ref (x: Ask): a_eqb x x = true.
Proof. Admitted.
Hint Resolve a_eqb_ref: hint_auction.
Lemma a_eqb_elim (x y: Ask):  a_eqb x y -> x = y.
Proof. Admitted.

Lemma a_eqb_intro (x y: Ask): x=y -> a_eqb x y = true.
Proof. Admitted.

Hint Immediate a_eqb_elim a_eqb_intro: hint_auction.

Lemma a_eqP (x y: Ask): reflect (x=y)(a_eqb x y).
Proof. apply reflect_intro. split; auto with hint_auction. Qed. 
Hint Resolve a_eqP: hint_auction.

Lemma a_ltb_irefl (x :  Ask): a_ltb x x = false.
Proof. Admitted.
Hint Resolve a_ltb_irefl: hint_auction.

Lemma a_ltb_antisym (x y: Ask):  x <> y -> a_ltb x y = ~~ a_ltb y x.
Proof. Admitted.
Hint Resolve a_ltb_antisym: hint_auction.

Lemma a_ltb_trans (x y z: Ask):  a_ltb x y -> a_ltb y z -> a_ltb x z.
Proof. Admitted.
Hint Resolve a_ltb_trans: hint_auction.

Canonical  ask_ordType: ordType:= {| Order.sort:=  Ask; Order.eqb:= a_eqb;
                                     Order.ltb:= a_ltb; Order.eq_P:=a_eqP;
            Order.ltb_irefl:=a_ltb_irefl; Order.ltb_antisym:= a_ltb_antisym;
            Order.ltb_trans:= a_ltb_trans|}.

Definition a0:= ({|s_id:= 0 ; sp:= 0|}).
Definition b0:= ({|b_id:= 0 ; bp:= 0 |}).

Definition best_bid (B: list Bid) := (max_in B b0).
Definition best_ask (A: list Ask) := (min_in A a0).

(* ----------- Notation for product type  and projection functions --------------------------*)
Check pair.
Print prod.
Notation "A [*] B":=(prod A B) (at level 100).


Definition fill_type:= ((Bid [*] Ask) [*] nat).

Definition bid_of (m: fill_type):= (fst (fst m)).
Definition ask_of (m: fill_type):= (snd (fst m)).
Definition trade_price_of (m:fill_type):= (snd  m).


Fixpoint bids_of (F: list fill_type) : (list Bid) :=
  match F with
  |nil => nil
  |f::F'=> (bid_of f)::(bids_of F')
  end.


Lemma bids_of_intro (F: list fill_type) (m: fill_type):
  In m F -> (In (bid_of m) (bids_of F)).
Proof. { intro H. induction F. simpl. simpl in H. contradiction. destruct  H.
        subst m. simpl. left. auto. simpl. right. auto. } Qed.

Lemma bids_of_elim (F: list fill_type): forall b, In b (bids_of F)->
                                             exists m, In m F /\ b = bid_of m.
Proof. { intros b H. induction F. simpl in H. contradiction. simpl in H.
       destruct  H as [H1 | H2]. exists a. split; auto with hint_list.
       apply IHF in H2 as H0. destruct H0 as [m H0]. exists m. destruct H0. split.
       eauto with hint_list. auto. } Qed.

Fixpoint asks_of (F: list fill_type) : (list Ask) :=
  match F with
  |nil => nil
  |f::F'=> (ask_of f)::(asks_of F')
  end.

Lemma asks_of_intro (F: list fill_type) (m: fill_type):
  In m F -> (In (ask_of m) (asks_of F)).
Proof. { intro H. induction F. simpl. simpl in H. contradiction. destruct  H.
        subst m. simpl. left. auto. simpl. right. auto. } Qed.
  
Lemma asks_of_elim (F: list fill_type): forall a, In a (asks_of F)->
                                            exists m, In m F /\ a = ask_of m.
Proof. { intros b H. induction F. simpl in H. contradiction. simpl in H. 
       destruct  H as [H1 | H2]. exists a. split; auto with hint_list.
       apply IHF in H2 as H0. destruct H0 as [m H0]. exists m. destruct H0. split.
       eauto with hint_list. auto. } Qed.

Fixpoint bid_ask_pairs_of (F: list fill_type): (list (Bid [*] Ask)):=
  match F with
  |nil => nil
  |f::F'=> (bid_of f, ask_of f)::(bid_ask_pairs_of F')
  end.

Fixpoint trade_prices_of (F: list fill_type) : (list nat) :=
  match F with
  |nil => nil
  |f::F'=> (trade_price_of f)::(trade_prices_of F')
  end.
Lemma trade_prices_of_intro (F: list fill_type) (m: fill_type):
  In m F -> In (trade_price_of m) (trade_prices_of F).
Proof. { intro H. induction F. eauto. destruct H. subst m.
       simpl. left;auto. simpl. right;auto.
       } Qed.

                           
Lemma trade_prices_of_elim (F: list fill_type): forall p, In p (trade_prices_of F) ->
                                                     exists m, In m F /\ p = trade_price_of m.
Proof. { intros p H. induction F. simpl in H. contradiction. simpl in H. destruct H.
       exists a. split. eauto with hint_list. auto. apply IHF in H as H0. destruct  H0 as [m H0].
       destruct H0 as [H1 H2]. exists m. split;eauto with hint_list. } Qed.


       
Hint Resolve bids_of_intro bids_of_elim asks_of_intro asks_of_elim: hint_auction.
Hint Resolve trade_prices_of_intro trade_prices_of_elim: hint_auction.

(*----------------- Notion of matching and a maximal matching ------------------------*)

Definition matchable (b: Bid)(a: Ask):=  (sp (a)) <= (bp (b)).

Definition Is_matchable(M: list fill_type):= forall m, In m M -> matchable (bid_of m) (ask_of m).

Definition Is_a_matching (M: list fill_type) (B: list Bid) (A: list Ask):=
  (Is_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)) /\
  (bids_of M [<=] B) /\ (asks_of M [<=] A).

Definition Is_MM (M : list fill_type) (B: list Bid) (A: list Ask):=
  Is_a_matching M B A /\ 
  (forall M': list fill_type, Is_a_matching M' B A -> |M'| <= |M|).

(*----------------- Individual rational, uniform and  fair matching--------------------------*)

Definition rational (m: fill_type):=
  (bp (bid_of m)  >= trade_price_of m) /\ (trade_price_of m >= sp(ask_of m)).
Definition Is_ind_rational (M: list fill_type):= forall m, In m M -> rational m.

Definition Is_fair_on_bids (M: list fill_type)(B: list Bid)(A: list Ask):=
  (forall b b', In b B /\ In b' B -> (bp b) > (bp b') -> In b' (bids_of M) -> In b (bids_of M)).

Definition Is_fair_on_asks (M: list fill_type)(B: list Bid)(A: list Ask):=
  (forall s s', In s A /\ In s' A -> (sp s) < (sp s') -> In s' (asks_of M) -> In s (asks_of M)).

  
Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  :=  Is_fair_on_asks M B A /\ Is_fair_on_bids M B A.

Inductive uniform : list nat -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:nat): uniform (a::nil)
|Ind_uni(a b:nat)(l:list nat): a=b -> uniform (b::l)-> uniform (a::b::l).

Definition Is_uniform (M : list fill_type) := uniform (trade_prices_of M).


(*-------------- buyers_above and sellers above relationship and results------------------*)

Definition buyers_above (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb p (bp x))  B.

Lemma buyers_above_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_above p B)-> bp(x) >= p.
Proof.  induction B. simpl. tauto.
        simpl.  destruct ((p <=? bp a)%nat) eqn: H1. intro H2. destruct H2. subst x. Admitted.
        

  
Lemma buyers_above_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ bp(x) >= p ) -> In x (buyers_above p B).
Proof. Admitted.

Definition sellers_above (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb p (sp x)) (A).

Lemma sellers_above_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_above p A)-> sp(x) >= p.
Proof. Admitted.
Lemma sellers_above_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ sp(x) >= p ) -> In x (sellers_above p A).
Proof. Admitted.

Definition buyers_below (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb (bp x) p) (B).

Lemma buyers_below_intro (p:nat)(B: list Bid)(x:Bid):
 ( In x B /\ bp(x) <= p ) -> In x (buyers_below p B).
Proof. Admitted.
Lemma buyers_below_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_below p B)-> bp(x) <= p.
Proof. Admitted.

Definition sellers_below (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb (sp x) p) (A).

Lemma sellers_below_intro (p:nat)(A: list Ask)(x:Ask):
 ( In x A /\ sp(x) <= p ) -> In x (sellers_below p A).
Proof. Admitted.
Lemma sellers_below_elim (p:nat)(A: list Ask)(x:Ask):
  In x (sellers_below p A)-> sp(x) <= p.
Proof. Admitted.

Hint Resolve buyers_above_elim buyers_above_intro: hint_auction.
Hint Resolve sellers_above_elim sellers_above_intro: hint_auction.

Hint Resolve buyers_below_elim buyers_below_intro: hint_auction.
Hint Resolve sellers_below_elim sellers_below_intro: hint_auction.

Theorem buyers_above_ge_sellers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> | buyers_above p (bids_of M)| >= | sellers_above p (asks_of M)|.
Proof. Admitted.

Theorem sellers_below_ge_buyers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> | buyers_below p (bids_of M)| <= | sellers_below p (asks_of M)|.
Proof. Admitted.


Lemma removed_is_matching(a:fill_type)(M: list fill_type)(B: list Bid)(A: list Ask):
  Is_a_matching (a :: M) B A-> Is_a_matching M B A.
Proof. Admitted.
Print matchable.
Lemma best_matchable_in_left (M M': list fill_type) (B: list Bid) (A:list Ask):
  (Is_a_matching M B A) -> (Is_a_matching M' B A) -> (| M | < |M'|) ->
  matchable (best_bid (diff B (bids_of M)))  (best_ask (diff A (asks_of M))).
Proof. Admitted.

Locate "==".
Locate "<=b".

(*----------------- There exists a fair matching -------------------------------------- *)



Lemma ask_same_fair (M M': list fill_type)(B: list Bid)(A: list Ask):
  Is_fair_on_asks M B A -> (asks_of M = asks_of M')-> Is_fair_on_asks M' B A.
Proof. intros H1 H2. unfold Is_fair_on_asks. unfold Is_fair_on_asks in H1.
       rewrite <- H2. auto. Qed.

Lemma bid_same_fair (M M': list fill_type)(B: list Bid)(A: list Ask):
  Is_fair_on_bids M B A -> (bids_of M = bids_of M')-> Is_fair_on_bids M' B A.
Proof. intros H1 H2. unfold Is_fair_on_bids. unfold Is_fair_on_bids in H1.
       rewrite <- H2. auto. Qed.

Theorem exists_fair_on_bids (M: list fill_type) (B: list Bid) (A:list Ask):
  Is_a_matching M B A->
  (exists M':list fill_type, Is_a_matching M' B A  /\ (|M| = |M'|) /\ asks_of M = asks_of M'
   /\ Is_fair_on_bids M' B A).
Proof. Admitted.

Theorem exists_fair_on_asks (M: list fill_type) (B: list Bid) (A:list Ask):
  Is_a_matching M B A->
  (exists M':list fill_type, Is_a_matching M' B A /\  (|M| = |M'|) /\ bids_of M = bids_of M'
   /\ Is_fair_on_asks M' B A).
Proof. Admitted.


Theorem exists_fair_matching (M: list fill_type) (B: list Bid) (A:list Ask):
  Is_a_matching M B A-> (exists M':list fill_type, Is_a_matching M' B A /\ Is_fair M' B A /\ |M|= |M'|).
Proof. { intros H0. apply exists_fair_on_bids in H0 as H1.
       destruct H1 as [M' H1].
       destruct H1 as [H1a H1]. destruct H1 as [H1b H1]. destruct H1 as [H1c H1d].
       apply exists_fair_on_asks in H1a as H2.
       destruct H2 as [M'' H2].
       destruct H2 as [H2a H2]. destruct H2 as [H2b H2]. destruct H2 as [H2c H2d].
       exists M''. split.
       { auto. }
       split.
       { split. auto. eauto using bid_same_fair. } eauto. } Qed.
              
         
(* ----------------- There exists an Individual Rational Matching------------------------ *)
  
Fixpoint produce_IR (M:list fill_type):(list fill_type):=
  match M with
  |nil => nil
  |m::M' => (fst m, sp (ask_of m))::(produce_IR M')
  end.

Lemma fst_same_IR (M: list fill_type) :
  forall m', In m' (produce_IR M) -> exists m, In m M /\ (fst m) = (fst m').
Proof. { intros m' H. induction M. simpl in H. contradiction.
       simpl in H.  destruct H. exists a. split. auto with hint_list.
       subst m'. simpl;auto. auto.
       assert (H1:  exists m : fill_type, In m M /\ fst m = fst m'); auto.
       destruct H1 as [m H1]. destruct H1.  exists m. split; eauto with hint_list. } Qed.

Lemma same_fst_IR (M: list fill_type) :
  forall m, In m M -> exists m', In m' (produce_IR M) /\ (fst m) = (fst m').
  Proof. Admitted.
  
Lemma same_bids (M:list fill_type):
  (bids_of M) = (bids_of (produce_IR M)).
Proof. {
induction M. simpl. auto. simpl.
replace (bid_of (fst a, sp (ask_of a))) with (bid_of a).
rewrite IHM. auto. unfold bid_of. simpl. auto. } Qed.

Lemma same_asks (M:list fill_type):
  (asks_of M) = (asks_of (produce_IR M)).
Proof. {
  induction  M. simpl. auto. simpl.
  replace (ask_of (fst a, sp (ask_of a))) with (ask_of a).
  rewrite IHM. auto. unfold ask_of. simpl. auto. } Qed.

Lemma produce_IR_is_matching (M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> (Is_a_matching (produce_IR M) B A).
Proof. { intro H0. unfold Is_a_matching. unfold Is_matchable. split.
        { intros m' H1. assert (H2: exists m, (In m M) /\ (fst m = fst m')). apply fst_same_IR. auto.
          unfold bid_of. unfold ask_of. destruct H2 as [m H2]. destruct H2 as [H2 H3].
          rewrite <- H3. apply H0. auto. }
        { replace (bids_of (produce_IR M)) with (bids_of M).
          replace (asks_of (produce_IR M)) with (asks_of M). apply H0.
          apply same_asks. apply same_bids. } } Qed.  

Lemma produce_IR_trade_ask_same (M:list fill_type):
  forall m: fill_type, In m (produce_IR M) -> sp (ask_of m)=(trade_price_of m).
Proof. {  intros m H0. induction M. simpl in H0. contradiction.
           simpl in H0. destruct H0. subst m. simpl. unfold ask_of. simpl. auto. auto. } Qed.
Lemma produce_IR_is_IR (M: list fill_type) (B: list Bid) (A: list Ask):
 Is_a_matching M B A-> Is_ind_rational (produce_IR M).
Proof. { intro H0. unfold Is_ind_rational. intro m'. intro H.
       unfold rational. replace (trade_price_of m') with (sp (ask_of m')). Focus 2.
       apply produce_IR_trade_ask_same with (M:=M). auto. split. Focus 2. auto.
       assert (H1: exists m, In m M /\ fst m = fst m'). apply fst_same_IR;auto.
       destruct H1 as [m H1]. destruct H1 as [H1 H2].
       unfold bp; unfold sp; unfold bid_of; unfold ask_of. rewrite <- H2. simpl.
       unfold Is_a_matching in H0. destruct H0 as [H0 H3]. apply H0. auto. } Qed.

Theorem exists_IR_matching (M: list fill_type) (B: list Bid) (A:list Ask):
  Is_a_matching M B A -> (exists M': list fill_type, bids_of M = bids_of M' /\ asks_of M = asks_of M'
                                               /\ Is_a_matching M' B A /\ Is_ind_rational M').
Proof. { intros  H.   exists (produce_IR M). split. apply same_bids. split. apply same_asks.
         split. apply produce_IR_is_matching. auto. eapply produce_IR_is_IR. eauto. } Qed.



(* ----------------- Equilibrium Matching Algorithms and their properties ------------------*)



Fixpoint UM_matching (B:list Bid) (A:list Ask)  :=
  match (B,A) with
  |(nil, _) => nil
  |(_,nil)=> nil
  |(b::B',a::A') => match Nat.leb (sp a) (bp b) with
                        |false =>nil
                        |true  => ((b,a),0)::UM_matching B' A'
  end
  end.

Lemma UM_correct (B:list Bid) (A:list Ask) : forall m, In m (UM_matching B A) ->
                                (bp (bid_of m)) >= (sp (ask_of m)).
Proof. Admitted.



Lemma bids_of_UM_sorted (B: list Bid) (A: list Ask) :
  ((IsOrd (rev B)) /\ (IsOrd A)) -> (IsOrd (rev (bids_of (UM_matching B A)))).
Proof. Admitted.

Lemma asks_of_UM_sorted (B: list Bid) (A: list Ask) :
  ((IsOrd (rev B)) /\ (IsOrd A)) -> (IsOrd (asks_of (UM_matching B A))).
Proof. Admitted.


Definition uniform_price (B: list Bid) (A: list Ask):=
  (bp (bid_of (last (UM_matching B A) ((b0,a0),0)))).

Lemma bid_order_price_order (b1 b2: Bid): b1 <=? b2 -> bp (b1) <= bp (b2).
Proof. Admitted.
Lemma ask_order_price_order (a1 a2: Ask): a1 <=? a2 -> sp (a1) <= sp (a2).
Proof. Admitted.


(*------------------------------------------------------------------------------------------- *)
(* move the general version of the following lemmas to the OrdList file ------------------ *)
Lemma last_is_smallest (l: list Bid): IsOrd (rev l)-> forall m, In m l -> ((last l b0) <=? m).
Proof. Admitted.
Lemma last_is_largest (l: list Ask): IsOrd l-> forall m, In m l -> (m <=? (last l a0)).
Proof. Admitted.
Lemma last_in_list (T:Type)(l:list T)(p:T)(d:T) : In (last (p :: l) d)  (p :: l).
Proof. Admitted.
(*--------------------------------------------------------------------------------------------*)

Lemma bid_of_last_and_last_of_bids (F: list fill_type):
  (bid_of (last F ((b0,a0),0))) = (last (bids_of F) b0).
Proof.
Admitted.
Lemma ask_of_last_and_last_of_asks (F: list fill_type):
  (ask_of (last F ((b0,a0),0))) = (last (asks_of F) a0).
Proof.
Admitted.


Lemma UP_returns_IR (B : list Bid)(A:list Ask):
    IsOrd (rev B)-> IsOrd A -> forall m, In m (UM_matching B A) ->
   (bp (bid_of m))>= (uniform_price B A)  /\ (sp (ask_of m)) <= (uniform_price B A).
  
Proof.   { intros H1 H2 m. unfold uniform_price. intro H3. split.
         {
         assert (H4: IsOrd (rev (bids_of (UM_matching B A)))).
         apply bids_of_UM_sorted. split;auto.
         assert (H5: (last (bids_of (UM_matching B A)) b0) <=?(bid_of m)).
         apply last_is_smallest. auto. eauto with hint_auction. 
         apply bid_order_price_order.
         replace (bid_of (last (UM_matching B A) (b0, a0, 0))) with
             (last (bids_of (UM_matching B A)) b0).
         auto. symmetry. apply bid_of_last_and_last_of_bids. }
         
         {  assert (H_on_ask: (sp (ask_of m)) <= sp (ask_of (last (UM_matching B A) (b0,a0,0)))).  
         assert (H4: IsOrd ((asks_of (UM_matching B A)))).
         apply asks_of_UM_sorted. split;auto.
         assert (H5: ask_of m <=? (last (asks_of (UM_matching B A)) a0)).
      
         apply last_is_largest. auto. eauto with hint_auction. 
         apply ask_order_price_order.
         replace (ask_of (last (UM_matching B A) (b0, a0, 0))) with
             (last (asks_of (UM_matching B A)) a0). auto. symmetry.
         apply ask_of_last_and_last_of_asks.
         eapply le_trans with (m:=sp (ask_of (last (UM_matching B A) (b0, a0, 0)))).
         auto. eapply UM_correct with (B:=B)(A:=A). case (UM_matching B A) eqn: H4.
         simpl;contradiction. apply last_in_list.  }  } Qed.


Fixpoint replace_column (l:list fill_type)(n:nat):=
  match l with
  |nil=>nil
  |m::l'=> ((fst m),n)::(replace_column l' n)
  end.

Lemma replace_column_is_uniform (l: list fill_type)(n:nat):
  uniform (trade_prices_of (replace_column l n)).
Proof. { induction l. simpl.  constructor.
       case l eqn: H. simpl.  constructor. simpl. simpl in IHl. constructor;auto. } Qed.

Lemma last_column_is_trade_price (l:list fill_type)(m:fill_type)(n:nat): In m (replace_column l n)->
                                                                  (trade_price_of m = n).
Proof. Admitted.

Lemma replace_column_elim (l: list fill_type)(n:nat): forall m', In m' (replace_column l n)->
                                                          exists m, In m l /\ bid_of m = bid_of m' /\ ask_of m = ask_of m'.
  Proof. Admitted.


Set Implicit Arguments.

Definition UM (B:list Bid) (A:list Ask) : (list fill_type) :=
  replace_column (UM_matching B A)
                (uniform_price B A).

Theorem UM_is_fair(B: list Bid) (A:list Ask): Is_fair ( UM B A) B A.
Proof. Admitted.

Theorem UM_is_Ind_Rat (B: list Bid) (A:list Ask):
  (IsOrd (rev B)) -> (IsOrd A) -> Is_ind_rational (UM B A).
Proof. { intros HB HA. unfold Is_ind_rational. intros m H. unfold rational. unfold UM in H.
       replace (trade_price_of m) with (uniform_price B A).
       assert (H0: exists m', In m' (UM_matching B A) /\ bid_of m' = bid_of m /\ ask_of m' = ask_of m).
       apply replace_column_elim with (n:= uniform_price B A). auto.
       destruct H0 as [m' H0]. destruct H0 as [H1 H0]. destruct H0 as [H2 H0].
       rewrite <- H2. rewrite <- H0. split; apply UP_returns_IR; auto.
       symmetry; eapply last_column_is_trade_price;eauto.  } Qed.

Theorem UM_is_Uniform (B: list Bid) (A:list Ask) : Is_uniform ( UM B A).
Proof.  unfold Is_uniform. unfold UM. apply replace_column_is_uniform. Qed.

Theorem UM_is_maximal_Uniform (B: list Bid) (A:list Ask): forall M: list fill_type, Is_uniform M -> |M| <= | (UM B A ) |.
Proof. Admitted.



(*----------------- Maximum Matching (MM) Algorithm and its properties------------------*)

Fixpoint count (B:list nat) (A: list nat):nat:=
  match B with
  |nil => 0
  |b::B' => match A with
           |nil =>0
           |a::A' => match (Nat.leb a b) with
                    |true => S (count B' A')
                    |false => count B A'
                    end
           end
  end.

Definition B1 := 125::120::112::91::83::82::69::37::12::nil.
Definition A1 := 121::113::98::94::90::85::79::53::nil.
Eval compute in (count B1 A1).

Fixpoint erase_top (T:Type) (n:nat) (l:list T): list T:=
  match l with
  |nil => nil
  |a::l' => match n with
           |0 => l
           |S n' => erase_top n' l'
           end
  end.

Eval compute in (erase_top 3 B1).
Check nil.
Definition nil_on (T1:Type)(T2:Type): list ((T1 [*] T2) [*] nat):= nil.

Fixpoint pair_top (n:nat) (l:list Bid) (s:list Ask): (list ((Bid [*] Ask)[*] nat)):=
  match (l,s) with
  |(nil,_) => (nil_on Bid Ask)
  |(_,nil) => (nil_on Bid Ask)
  |(b::l',a::s') => match n with
                   |0 => (nil_on Bid Ask)
                   |S n' => ((b,a),  (bp b)) ::(pair_top n' l' s')
                                   end
  end.

Definition produce_FM (M: list fill_type) (B: list Bid) (A: list Ask):=
  pair_top (|M|) B (erase_top (|A| - |M|) A).

Lemma Is_a_matching_FM (M: list fill_type) (B: list Bid) (A: list Ask):
 (IsOrd (rev B)) -> (IsOrd (rev A))-> (Is_a_matching M B A)-> Is_a_matching (produce_FM M B A) B A.
Proof.
  intros H1 H2 H3. Admitted.

Fixpoint bid_prices_of (B: list Bid) : (list nat) :=
  match B with
  |nil => nil
  |b::B'=> (bp b)::(bid_prices_of B')
  end.

Fixpoint ask_prices_of (A: list Ask) : (list nat) :=
  match A with
  |nil => nil
  |a::A'=> (sp a)::(ask_prices_of A')
  end.



Definition MM (B:list Bid) (A: list Ask):list fill_type :=
  pair_top (count (bid_prices_of B) (ask_prices_of A)) (B)
           (erase_top ((length A)-(count (bid_prices_of B) (ask_prices_of A))) A).   
Require Extraction.
Extraction MM.
Extraction pair_top. Extraction Nat.div2.
Check Bid.
Print Bid.

Definition B2:= ({|b_id:= 1 ; bp:= 125 |}) ::({|b_id:= 2 ; bp:= 120 |}) ::({|b_id:= 3 ; bp:= 112 |}) ::({|b_id:= 4 ; bp:= 91 |}) ::({|b_id:= 5 ; bp:= 83 |}) ::({|b_id:= 6 ; bp:= 82 |}) ::({|b_id:= 7 ; bp:= 69 |}) ::({|b_id:= 8 ; bp:= 37 |}) :: nil.

Definition A2:= ({|s_id:= 1 ; sp:= 121 |}) ::({|s_id:= 3 ; sp:= 113 |}) ::({|s_id:= 5 ; sp:= 98 |}) ::({|s_id:= 9 ; sp:= 94 |}) ::({|s_id:= 90 ; sp:= 90 |}) ::({|s_id:= 78 ; sp:= 85 |}) ::({|s_id:= 67 ; sp:= 79 |}) ::({|s_id:= 45 ; sp:= 53 |}) ::nil.

Eval compute in (MM B2 A2).
Eval compute in (EM B2 (rev A2)).


Theorem MM_is_fair(B: list Bid) (A:list Ask) : Is_fair (MM B A) B A.
Proof. Admitted.

Theorem MM_is_Ind_Rat (B: list Bid) (A:list Ask): Is_ind_rational ( MM B A).
Proof. Admitted.

Theorem MM_is_orderly (B: list Bid) (A:list Ask): Is_orderly ( MM B A).
Proof. Admitted.


Theorem MM_is_maximal (B: list Bid) (A:list Ask): forall M: list fill_type, Is_a_matching M -> |M| <= | (MM B A) |.
Proof. Admitted.

(* There does not exist an algorithm which gives Individual rational, maximum and uniform matching*)

Theorem maximum_is_not_uniform : exists (B:list Bid), exists (A:list Ask), forall (M:list fill_type), Is_a_matching M -> ~(Is_ind_rational M /\ Is_uniform M /\ Is_MM M).
Proof.
  Admitted.

  (* Corresponding theorem for algorithm *)

Theorem No_algorithm : forall Algo : list Bid -> list Ask -> list fill_type, exists (B:list Bid), exists (A:list Ask), Is_a_matching (Algo B A) -> ~(Is_ind_rational (Algo B A) /\ Is_uniform (Algo B A) /\ Is_MM (Algo B A)).
Proof.
Admitted.




