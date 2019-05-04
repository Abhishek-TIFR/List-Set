





Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.Eqdep_dec.

Require Export DecUG.

Set Implicit Arguments.

Section EqualGraphs.

  Context { A: ordType }.


  Let fun_ex:= (@functional_extensionality A (A->bool)).
  Lemma rel_ex (f g: A-> A-> bool): (forall x y, f x y = g x y) -> f = g.
  Proof. intros h1. eapply fun_ex. intro x0. remember (f x0) as f0. remember (g x0) as g0.
         eapply functional_extensionality. intro y0. subst f0. subst g0. auto. Qed.
  
  Lemma graph_eq0 (G1 G2: @dG A): (nodes G1 = nodes G2) -> (edg G1 = edg G2) -> G1 = G2.
  Proof. { destruct G1 as [N1 P11 E1 P12 P13].
           destruct G2 as [N2 P21 E2 P22 P23]. simpl. intros h1 h2. subst N1. subst E1.
           cut (P11 = P21). cut (P12 = P22). cut (P13 = P23). intros h1 h2 h3.
           rewrite h1. rewrite h2. rewrite h3. auto.
           all: apply eq_proofs_unicity; eauto. } Qed.

  Lemma graph_eq (G1 G2: @dG A): (nodes G1 = nodes G2) ->
                                   (forall x y, edg G1 x y = edg G2 x y) -> G1 = G2.
  Proof. intros h1 h2. apply graph_eq0. auto. apply rel_ex. auto. Qed.

 
  End EqualGraphs.