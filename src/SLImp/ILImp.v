Require Import ILogic ILTac ILInsts ImpDependencies.

Definition Assertion := state -> Prop.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

(* Assertions are an intuitionistic logic *)

Instance AssertionILogic : ILogic Assertion := _.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).
  
Definition not (P: Assertion) := P -->> lfalse.
Check not.
Notation "~ x" := (not x) : type_scope.

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); assumption. Qed.
  
Definition assn_sub (X: id) a Q : Assertion :=
  fun (st : state) => Q (update st X (aeval st a)).

Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.  Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{P //\\ bassn b}} c1 {{Q}} ->
  {{P //\\ ~ (bassn b)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
Admitted.


Lemma bexp_eval_false : forall b st,
  beval st b = false |-- (~ (bassn b)) st.
Proof.
  intros b st.
  apply limplAdj.
  intros lhs.
  inversion lhs.
  unfold bassn in H0.
  rewrite H in H0.
  inversion H0.
Qed.  

Theorem hoare_while : forall P b c,
  {{P //\\ bassn b}} c {{P}} ->
  {{P}} WHILE b DO c END {{P //\\ ~ (bassn b)}}.
Proof.
  intros P b c H st st' Hc HP.
  remember (WHILE b DO c END) as w.
  induction Hc; inversion Heqw.
  Case "E_WhileEnd".
    split. assumption.
    apply bexp_eval_false. subst.
    assumption.
  Case "E_WhileLoop".
  	apply IHHc2. subst.
  	reflexivity.
  	apply (H st st'). subst.
  	assumption.
  	split.
  		assumption.
  		unfold bassn.
  		subst.
  		assumption.
Qed.
    
