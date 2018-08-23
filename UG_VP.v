
(* From Coq Require Export ssreflect  ssrbool. *)
 
(* Require Export MSets MSetInterface MSetFacts MSetDecide  MSetWeakList.*)
(* Require Export MSetProperties MSetEqProperties. *)
(* The following two options can be unset to disable the incompatible rewrite syntax 
   and allow reserved identifiers to appear in scripts. *)


Require Export Dec_UG.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset SsrRewrite.
Unset SsrIdents.





Module VertP <: DecidableType.
  Inductive VP:Set:= vp(_:nat)(_:nat).
  Definition t:= VP.
  Definition eq(v:VP):= eq v.
  Lemma eq_equiv: Equivalence eq.
     Proof. Print Equivalence. constructor.
            constructor.
            unfold Symmetric;unfold eq;auto.
            unfold Transitive;unfold eq;intros x y z H;rewrite H;auto.
     Qed.
     Definition eq_dec:forall (x y:VP), {x=y} + {x<>y}.
       repeat (decide equality). Defined.
End VertP.



Module G2:= MakeDecGraph (VertP).






(*

(* countable vertices pairs v(i)(j) as DecidableNodes------------------------ *)
Module VertPair <: DecidableNodes.
  Inductive VP:Set:= vp(_:nat) (_:nat).
  Definition U:=VP.
  Definition eq_U_dec: forall (x y:U), {x=y} + {x<>y}.
   repeat(decide equality). Defined.
  Module Nodes <: DecidableType with Definition t:=U.
   Definition t:=U.                                       
   Definition eq(u:U):= eq u.
   Lemma eq_equiv: Equivalence eq.
   Proof. Print Equivalence. constructor.
          constructor.
          unfold Symmetric;unfold eq;auto.
          unfold Transitive;unfold eq;intros x y z H;rewrite H;auto.
   Qed.
   Definition eq_dec:=eq_U_dec.
 End Nodes.
 End VertPair.

Module G2:= DecUgraphs(VertPair).
Print Module G2.

*)