





Require Import ssreflect ssrbool.
Require Export Lists.List.
Require Export GenReflect SetSpecs SetReflect.


(*Inductive OrderType: Type:= bid | ask. *)

(* Record Order:Type:= Mk_order{
                        id:>nat;
                        p:nat; }. 
Definition B := {| id:=1; p:= 23; t:= bid |}.
Check B.
Eval compute in (B.(t)).*)

Record Bid:Type:= Mk_bid{
                        b_id:>nat;
                        bp:nat  }.

Definition b_eqb (x y:Bid): bool:= (b_id x == b_id y) && ( bp x == bp y).
Definition b_ltb (x y: Bid): bool:= (bp x <? bp y) || ((bp x == bp y) && (b_id x <? b_id y)).

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

Definition b1:= ({|b_id:= 1 ; bp:= 125 |}).
Definition b2:= ({|b_id:= 2 ; bp:= 125 |}).


Eval compute in (b1<? b2).
 

 
Record Ask:Type:= Mk_ask{
                        s_id:>nat;
                        sp:nat   }.


Definition a_eqb (x y: Ask): bool:= (s_id x == s_id y) && (  sp x ==  sp y).
Definition a_ltb (x y:  Ask): bool:= ( sp x <?  sp y) || (( sp x ==  sp y) && (s_id x <? s_id y)).

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


Print ordType.
(*Canonical nat_ordType: ordType:=
refine ( {| Order.sort:= nat; eqb:= Nat.eqb; ltb:= Nat.ltb |}).
*)
Lemma decN: forall n m:nat, {n=m}+{n<>m}.
Proof. decide equality. Qed.

Lemma decBid: forall b1 b2:Bid, {b1=b2}+{b1<>b2}.
Proof. decide equality; eapply decN. Qed.

Lemma decAsk: forall s1 s2:Ask, {s1=s2}+{s1<>s2}.
Proof. decide equality; eapply decN. Qed.


Variable B: list Bid.
Variable A: list Ask.
Check pair.
Print prod.
Notation "A [*] B":=(prod A B) (at level 100).

Lemma decBidAsk: forall p1 p2: (Bid[*]Ask), {p1=p2}+{p1<>p2}.
Proof. decide equality. eapply decAsk. eapply decBid. Qed.

Definition fill_type:= ((Bid [*] Ask) [*] nat).

Definition bid_of (m: fill_type):= (fst (fst m)).
Definition ask_of (m: fill_type):= (snd (fst m)).
(*
Definition buyer (m:fill_type):= (fst (fst m)). (*bid*)
Definition seller (m: fill_type):= (snd (fst m)). (* ask *)
 *)

Definition trade_price_of (m:fill_type):= (snd  m).

Lemma decFill: forall f1 f2:fill_type, {f1=f2}+{f1<>f2}.
Proof. decide equality. eapply decN. eapply decBidAsk. Qed.


Fixpoint bids_of (F: list fill_type) : (list Bid) :=
  match F with
  |nil => nil
  |f::F'=> (bid_of f)::(bids_of F')
  end.
(*
Fixpoint buyers (F: list fill_type) : (list Bid) :=
  match F with
  |nil => nil
  |f::F'=> (buyer f)::(buyers F')
  end.
 *)

Fixpoint asks_of (F: list fill_type) : (list Ask) :=
  match F with
  |nil => nil
  |f::F'=> (ask_of f)::(asks_of F')
  end.
(*
Fixpoint sellers (F: list fill_type) : (list Ask) :=
  match F with
  |nil => nil
  |f::F'=> (seller f)::(sellers F')
  end.
 *)
Fixpoint bid_ask_pair_of (F: list fill_type): (list (Bid [*] Ask)):=
  match F with
  |nil => nil
  |f::F'=> (bid_of f, ask_of f)::(bid_ask_pair_of F')
  end.
(*
Fixpoint bid_matched_to (a: Ask)(F: list (Bid [*] Ask))(db: Bid):=
  match F with
    |nil => db
          |(b',a')::F' =>  
*)
Fixpoint trade_prices_of (F: list fill_type) : (list nat) :=
  match F with
  |nil => nil
  |f::F'=> (trade_price_of f)::(trade_prices_of F')
  end.

Definition matchable (b: Bid)(a: Ask):=  (sp (a)) <= (bp (b)).
(*
Definition matchable (m: Bid [*] Ask):= sp (snd (m)) <= bp (fst (m)). *)

Definition Is_matchable(M: list fill_type):= forall m, In m M -> matchable (bid_of m) (ask_of m).

(*
Definition Is_matchable(M: list fill_type):= forall m, In m M -> matchable(fst (m)).
 *)

Definition Is_a_matching (M: list fill_type) (B: list Bid) (A: list Ask):=
  (Is_matchable M) /\ (NoDup (bids_of M)) /\ (NoDup (asks_of M)) /\ (bids_of M [<=] B) /\ (asks_of M [<=] A).

Definition Is_MM (M : list fill_type) (B: list Bid) (A: list Ask):=
  Is_a_matching M B A /\ 
  (forall M': list fill_type, Is_a_matching M' B A -> |M'| <= |M|).



Definition rational (m: fill_type):=
  (bp (bid_of m)  >= trade_price_of m) /\ (trade_price_of m >= sp(ask_of m)).
Definition Is_ind_rational (M: list fill_type):= forall m, In m M -> rational m. 


Definition Is_fair (M: list fill_type) (B: list Bid) (A: list Ask) 
  := (forall b b', In b B /\ In b' B -> (bp b) > (bp b') -> In b' (bids_of M) -> In b (bids_of M))  /\
     (forall s s', In s A /\ In s' A -> (sp s) < (sp s') -> In s' (asks_of M) -> In s (asks_of M)).

Lemma decFair (M: list fill_type) (B: list Bid) (A: list Ask):
  {Is_fair M B A}+{~ Is_fair M B A}. Admitted.

Inductive uniform : list nat -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:nat): uniform (a::nil)
|Ind_uni(a b:nat)(l:list nat): a=b -> uniform (b::l)-> uniform (a::b::l).


Fixpoint uniformb (l: list nat): bool:= match l with
                                   |nil => true
                                   |a::l'=> match l' with
                                           |nil => true
                                           |b::l''=> (Nat.eqb a b) && uniformb l'
                                           end
                                   end.
Lemma uniformP (l: list nat): reflect (uniform l)(uniformb l).
Proof. Admitted.


Definition Is_uniform (M : list fill_type) := uniform (trade_prices_of M).

Definition Is_orderly (M : list fill_type):= forall m m', In m M -> In m' M ->
                                                  ((bp (bid_of m) >= bp (bid_of m')) <->
                                                   (sp (ask_of m) >= sp (ask_of m'))).

(*Notation "| M |":= (length M) (at level 100).*)



Check filter.
                   
Definition buyers_above (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb p (bp x))  B.
Lemma buyers_above_elim (p:nat)(B: list Bid)(x:Bid):
  In x (buyers_above p B)-> bp(x) >= p.
Proof. Admitted.
Lemma buyers_above_intro (p:nat)(B: list Bid)(x:Bid):
  bp(x) >= p -> In x (buyers_above p B).
Proof. Admitted.

Definition sellers_above (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb p (sp x)) (A).

Definition buyers_below (p: nat)(B: list Bid): list Bid :=
  filter (fun x:Bid => Nat.leb (bp x) p) (B).

Definition sellers_below (p: nat)(A: list Ask): list Ask :=
  filter (fun x:Ask => Nat.leb (sp x) p) (A).


Lemma buyers_above_ge_sellers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> | buyers_above p (bids_of M)| >= | sellers_above p (asks_of M)|.
Proof. Admitted.

Lemma sellers_below_ge_buyers (p:nat)(M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> | buyers_below p (bids_of M)| <= | sellers_below p (asks_of M)|.
Proof. Admitted.

Theorem exists_fair_matching (M: list fill_type) (B: list Bid) (A:list Ask):
  Is_a_matching M B A -> (exists M': list fill_type, Is_a_matching M' B A /\ Is_fair M' B A /\ |M|= |M'|).
Proof. Admitted.
  
Fixpoint produce_IR (M:list fill_type):(list fill_type):=
  match M with
  |nil => nil
  |m::M' => (fst m, sp (ask_of m))::(produce_IR M')
  end.

Lemma fst_same_IR (M: list fill_type) :
  forall m', In m' (produce_IR M) -> exists m, In m M /\ (fst m) = (fst m').
Proof. intros m' H. induction M. simpl in H. contradiction.
       simpl in H.  destruct H. exists a. split. auto with hint_list.
       subst m'. simpl;auto. auto.
       assert (H1:  exists m : fill_type, In m M /\ fst m = fst m'); auto.
       destruct H1 as [m H1]. destruct H1.  exists m. split; eauto with hint_list. Qed.
Lemma same_fst_IR (M: list fill_type) :
  forall m, In m M -> exists m', In m' (produce_IR M) /\ (fst m) = (fst m').
  Proof. Admitted.
  
Lemma same_bids (M:list fill_type):
  (bids_of M) = (bids_of (produce_IR M)).
Proof.
Admitted.

Lemma same_asks (M:list fill_type):
  (asks_of M) = (asks_of (produce_IR M)).
Proof.
Admitted.

Lemma produce_IR_is_matching (M: list fill_type) (B: list Bid) (A: list Ask):
  Is_a_matching M B A -> (Is_a_matching (produce_IR M) B A).
Proof.
Admitted.

Lemma produce_IR_trade_ask_same (M:list fill_type):
  forall m: fill_type, In m (produce_IR M) -> sp (ask_of m)=(trade_price_of m).
  Proof. Admitted.

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


Proof. intros  H.   exists (produce_IR M). split. apply same_bids. split. apply same_asks.
       split. apply produce_IR_is_matching. auto. eapply produce_IR_is_IR. eauto. Qed.

(* ----------------- Equilibrium Matching Algorithms and their properties ------------------*)

Fixpoint UM_matching (B:list Bid) (A:list Ask)  :=
  match (B,A) with
  |(nil, _) => nil
  |(_,nil)=> nil
  |(b::B',a::A') => match Nat.leb (sp a) (bp b) with
                        |false =>nil
                        |true  => (b,a)::UM_matching B' A'
  end
  end.
Check UM_matching. Check last.

Fixpoint Uniform_Price (M:list (Bid [*] Ask ))(dp:nat): nat:=
  match M with
  |nil => dp
  |m::nil => Nat.div2 ((bp (fst m)) + (sp (snd m)))
  |m::M' => Uniform_Price M' (Nat.div2 ((bp (fst m)) + (sp (snd m))))
  end.

Variable sort_ask_inc : (list Ask)-> list Ask.
Variable sort_bid_dec : (list Bid)-> list Bid.

(*--------------prove the specifications for above sorting functions ------------*)

Fixpoint attach_column (T:Type)(l:list T)(n:nat):=
  match l with
  |nil=>nil
  |m::l'=> (m,n)::(attach_column T l' n)
  end.

(* Inductive uniform : list nat -> Prop:=
| Nil_uni: uniform nil
|Sing_uni(a:nat): uniform (a::nil)
|Ind_uni(a b:nat)(l:list nat): a=b -> uniform (b::l)-> uniform (a::b::l). *)

Lemma attach_column_is_uniform (l: list (Bid[*]Ask))(n:nat):
  uniform (trade_prices_of (attach_column _ l n)).
Proof. induction l. simpl.  constructor.
       case l eqn: H. simpl.  constructor. simpl. simpl in IHl. constructor;auto. Qed.



Set Implicit Arguments.

Definition UM (B:list Bid) (A:list Ask) : (list fill_type) :=
  attach_column _ (UM_matching (sort_bid_dec B) (sort_ask_inc A))
                (Uniform_Price (UM_matching (sort_bid_dec B) (sort_ask_inc A)) 0).
Print Is_fair.

Theorem UM_is_fair(B: list Bid) (A:list Ask): Is_fair ( UM B A) B A.
Proof. Admitted.

Theorem UM_is_Ind_Rat (B: list Bid) (A:list Ask): Is_ind_rational ( UM B A).
Proof. Admitted.

Theorem UM_is_Uniform (B: list Bid) (A:list Ask) : Is_uniform ( UM B A).
Proof. Print Is_uniform. Print uniform. unfold Is_uniform. unfold UM.
       apply attach_column_is_uniform. Qed.

Theorem UM_is_maximal_Uniform (B: list Bid) (A:list Ask): forall M: list fill_type, Is_uniform M -> |M| <= | (UM B A ) |.
Proof. Admitted.


Eval compute in (Nat.leb 3 4).


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
                   |S n' => ((b,a), (Nat.div2 ((sp a) + (bp b)))) ::(pair_top n' l' s')
                                   end
  end.

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




