Require Export ILogic ILTac ILInsts.
Require Export ImpDep.
Require Import MapNotations MapInterface.
Require Import BILogic SepAlgMap.

Module ILImp.

(* HEAP *)
Definition Heap := Map [ nat, nat ].

Fixpoint alloc (addr cells : nat) (heap : Heap) : Heap :=
  match cells with
  | 0 => heap
  | S c => add addr 0 (alloc (addr+1) c heap)
  end.

Definition dealloc (addr : nat) (heap : Heap) : Heap :=
  remove addr heap.
   
Definition read (addr : nat) (heap : Heap) : nat :=
  match find addr heap with
  | Some n => n
  | None => 0
  end.
 
Definition write (addr value : nat) (heap : Heap) : Heap :=
  match find addr heap with
  | Some _ => add addr value (remove addr heap)
  | None   => add addr value heap
  end.

(* com *)
Inductive com : Type :=
  | CSkip    : com
  | CAss     : id -> aexp -> com
  | CSeq     : com -> com -> com
  | CIf      : bexp -> com -> com -> com
  | CWhile   : bexp -> com -> com
  | CAlloc   : id -> nat -> com
  | CDealloc : aexp -> com
  | CRead    : id -> aexp -> com
  | CWrite   : aexp -> aexp -> com.
  
Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "ALLOC" | Case_aux c "DEALLOC" | Case_aux c "READ"
  | Case_aux c "WRITE" ].

Notation "'SKIP'" := 
  CSkip.
Notation "X '::=' a" := 
  (CAss X a) (at level 60).
Notation "c1 ; c2" := 
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := 
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" := 
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "X &= 'ALLOC' a" :=
  (CAlloc X a) (at level 80).
Notation "'DEALLOC' a" :=
  (CDealloc a) (at level 80).
Notation "X '<~' '[' a ']'" :=
  (CRead X a) (at level 80). 
Notation "'[' a1 ']' '<~' a2" :=
  (CWrite a1 a2) (at level 80).
  
Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Definition cstate := (state * Heap)%type.

Definition get opcstate : cstate :=
  match opcstate with
  | Some cs => cs
  | None    => (empty_state, empty nat)
  end.

Definition cstack (cs : cstate) : state :=
  match cs with
  | (st, _) => st
  end.
  
Definition cheap (cs : cstate) : Heap :=
  match cs with
  | (_, h) => h
  end.

Inductive ceval : com -> cstate -> option cstate -> Prop :=
  | E_Skip : forall st,
      SKIP / st || Some st
  | E_Ass  : forall st a1 n X,
      aeval (cstack st) a1 = n ->
      (X ::= a1) / st || Some ((update (cstack st) X n), cheap st)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || Some st' ->
      c2 / st' || Some st'' ->
      (c1 ; c2) / st || Some st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval (cstack st) b1 = true ->
      c1 / st || Some st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || Some st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval (cstack st) b1 = false ->
      c2 / st || Some st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || Some st'
  | E_WhileEnd : forall b1 st c1,
      beval (cstack st) b1 = false ->
      (WHILE b1 DO c1 END) / st || Some st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval (cstack st) b1 = true ->
      c1 / st || Some st' ->
      (WHILE b1 DO c1 END) / st' || Some st'' ->
      (WHILE b1 DO c1 END) / st || Some st'' 
  | E_Alloc : forall st X addr cells,
  	  ~ In addr (cheap st) ->
  	  (forall n, (n >= addr /\ n <= addr+cells) -> ~ In n (cheap st)) ->
  	  (X &= ALLOC cells) / st || Some (update (cstack st) X addr, alloc addr cells (cheap st))
  | E_Dealloc : forall st a1 addr,
  	  aeval (cstack st) a1 = addr ->
  	  In addr (cheap st) ->
      (DEALLOC a1) / st || Some (cstack st, dealloc addr (cheap st))
  | E_DeallocError : forall st a1 addr,
  	  aeval (cstack st) a1 = addr ->
  	  ~ In addr (cheap st) ->
      (DEALLOC a1) / st || None
  | E_Read : forall st X a1 addr n,
      aeval (cstack st) a1 = addr ->
      find addr (cheap st) = Some n ->
      (X <~ [ a1 ]) / st || Some (update (cstack st) X n, cheap st)
  | E_ReadError : forall st X a1 addr,
      aeval (cstack st) a1 = addr ->
  	  ~ In addr (cheap st) ->
      (X <~ [ a1 ]) / st || None
  | E_Write : forall st a1 a2 addr value n,
  	  aeval (cstack st) a1 = addr ->
  	  aeval (cstack st) a2 = value ->
  	  find addr (cheap st) = Some n -> 
      ([ a1 ] <~ a2) / st || Some (cstack st, write addr value (cheap st))
  | E_WriteError : forall st a1 a2 addr,
  	  aeval (cstack st) a1 = addr ->
  	  ~ In addr (cheap st) ->
      ([ a1 ] <~ a2) / st || None
  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Alloc" | Case_aux c "E_Dealloc"
  | Case_aux c "E_DeallocError" | 
  | Case_aux c "E_Read" | Case_aux c "E_ReadError"
  | Case_aux c "E_Write" | Case_aux c "E_WriteError"
  ].
(* /com *)

(* Assertions *)
Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.
Local Existing Instance ILPre_Ops.
Local Existing Instance SABIOps.
Local Existing Instance SABILogic.

(* Assertions are an intuitionistic logic *)

Definition Assertion := ILPreFrm (@Equiv.equiv Heap _) (state -> Prop).
Check mkILPreFrm.
Instance AssertionILogic : BILogic Assertion := _.

Local Transparent ILFun_Ops.
Local Transparent ILPre_Ops.
Local Transparent SABIOps.

Definition mk_asn (f: Heap -> state -> Prop) (Hheap: forall h h' st, h === h' -> f h st -> f h' st) : Assertion.
  refine (mkILPreFrm (fun h st => f h st) _).
  simpl.
  intros.
  apply Hheap with t.
  assumption.
  assumption.
Defined.
  
Definition notA (P: Assertion) := P -->> lfalse.
Notation "~ x" := (notA x) : type_scope.

Definition safe c st := not (c / st || None).
    
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st, 
       P (cheap st) (cstack st)  ->
       safe c st /\ forall st', c / st || Some st'  ->
       Q (cheap st') (cstack st').

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

Global Instance hoare_triple_lentails:
  Proper (lentails --> eq ==> lentails ++> impl) hoare_triple.
Proof.
  intros P Q f c c' ceq R S RimplS H st H'.
  unfold hoare_triple in H.
  rewrite <- ceq.
  split.
  Case "safe".
    apply f in H'.
    specialize (H st H').
    inversion H.
    assumption.
    intuition.
  Case "S (cheap st') (cstack st')".
    intros.
    apply RimplS.
    intuition.
    apply f in H'.
    specialize (H st H').
    inversion H.
    apply H2.
    assumption.
    intuition.
Qed.

Global Instance hoare_triple_lequiv:
  Proper (lequiv ==> eq ==> lequiv ==> iff) hoare_triple.
Proof.
  intros P Q PiffQ c c' ceq R S RiffS.
  split.
    Case "({{P}} c {{R}}) -> {{Q}} c' {{S}}".
      intros.
      rewrite <- ceq.
      unfold hoare_triple.
      intros.
      split.
      SCase "safe".
        destruct PiffQ.
        apply H2 in H0.
        unfold hoare_triple in H.
        specialize (H st H0).
        inversion H.
        assumption.
        intuition.
      SCase "S (cheap st') (cstack st')".     
        intros.
        apply RiffS.
        intuition.
        unfold hoare_triple in H.
        apply PiffQ in H0.
        specialize (H st H0).
        inversion H.
        apply H3.
        assumption.
        intuition.
    Case "({{Q}} c' {{S}}) -> {{P}} c {{R}}".  
      intros.
      rewrite ceq.
      unfold hoare_triple in *.
      intros.
      split.
      SCase "safe".
        apply PiffQ in H0.
        specialize (H st H0).
        inversion H.
        assumption.
        intuition.
      SCase "R (cheap st') (cstack st')".
        intros.
        apply RiffS.
        intuition.
        apply PiffQ in H0.
        specialize (H st H0).
        inversion H.
        apply H3.
        assumption.
        intuition.
Qed.

(* Points-to, i.e. e |-> v *)
Program Definition points_to_precise a v : Assertion :=
  mk_asn (fun h st => Equiv.equiv h (add (aeval st a) (aeval st v) (empty nat))) _.
Next Obligation.
  rewrite <- H.
  assumption.
Defined.

Program Definition points_to_sub a v (X : id) n : Assertion :=
  mk_asn (fun h st => Equiv.equiv h (add (aeval (update st X n) a) (aeval (update st X n) v) (empty nat))) _.
Next Obligation.
  rewrite <- H.
  assumption.
Defined.

(* Heap membership *)
Program Definition points_to_weak a : Assertion :=
  Exists v, points_to_precise a v.

(* Heap membership *)
Program Definition in_heap a v : Assertion :=
  mk_asn (fun h st => MapsTo (aeval st a) (aeval st v) h)  _.
Next Obligation.
  rewrite <- H.
  assumption.
Defined.

Notation "a '|->' v" :=
  (points_to_precise a v) (at level 74).
Notation "e '|->_'" :=
  (points_to_weak e) (at level 74).
Notation "e '|~>' v" :=
  (in_heap e v) (at level 100).
Notation "e '|->' [ v : n // X ]" :=
  (points_to_sub e v X n) (at level 100).

(* bassn *)
Program Definition bassn b : Assertion :=
  mk_asn (fun h st => beval st b = true) _.
(* No Obligations *)

(* aexp equality *)
Program Definition aexp_eq (a1 a2 : aexp) : Assertion :=
  mk_asn (fun h st => aeval st a1 = aeval st a2) _.
(* No Obligations *)

Program Definition aexp_eq_sub (a1 : id) (a2 : aexp) (X : id) (n : nat) : Assertion :=
  mk_asn (fun h st => aeval st (AId a1) = aeval (update st X n) a2) _.
(**
Next Obligation.
  split.
  reflexivity.
  rewrite <- H.
  assumption.
Defined.*)

Lemma bexp_eval_true : forall st b,
  beval (cstack st) b = true <-> (bassn b) (cheap st) (cstack st).
Proof.
  split; (intros; simpl; assumption).
Qed.

Lemma bexp_eval_false: forall st b,
  beval (cstack st) b = false <-> not ((bassn b) (cheap st) (cstack st)).
Proof.
  split.
    intros.
	unfold not.
	intros.
	congruence.
  
    intros.
    apply not_true_iff_false.
    assumption.
Qed.

Definition pure (P : Assertion) :=
  Forall Q, (P ** Q -|- P //\\ Q).

Lemma convert_pure P Q (H: pure P) :
  P ** Q -|- P //\\ Q.
Proof. apply H. Qed.

Local Transparent ILFun_Ops.
Local Transparent ILPre_Ops.
Local Transparent SABIOps.

Lemma aexp_eq_sub_pure : forall X v v',
  pure (aexp_eq_sub X v X v').
Proof.
  intros X v v'.
  unfold pure.
  split.
    intros Pre h s.
    simpl.

    intros.
    destruct H.
    destruct H.
    destruct H.
    inversion H.
    split.

Admitted.

(* Function calls *)


Require Import Orders.
(**
Definition FunctionBody := list id -> com -> aexp.

Definition Prog := Map [ id, FunctionBody ].

Definition ProgSpec := Prog -> nat -> Prop.

Instance ProgSpecILogic : ILogic ProgSpec := _.

Definition mkspec (f: Prog -> nat -> Prop) 
					(Spec: forall c st n (P: Assertion) (Q: Assertion), 
						P (cheap st) (cstack st) -> forall n', n' < n -> 
						safe c st /\ forall st', c / st || Some st' ->
						Q (cheap st') (cstack st')) : ProgSpec.
	Admitted.			
*)						
Definition substitution := (id * aexp)%type.

Fixpoint substitute (ast: state) (ost: state) (subs: list (id * aexp)) : state :=
	match subs with
	| nil => ast
	| sub :: subz => substitute (ImpDep.update ast (fst sub) (aeval ost (snd sub))) ost subz
	end.

(* End function calls *) 


(** Hoare rules *)
Section Hoare_Rules.
Require Import MapFacts SepAlg.
  

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st H.
  split.
    unfold safe.
    unfold not. intros.
    inversion H0.
  
    intros.
    inversion H0.
    subst.
    assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     {{P}} c1 {{Q}} ->
     {{Q}} c2 {{R}} ->
     {{P}} c1;c2 {{R}}.
Proof. 
  intros P Q R c1 c2 H1 H2 st HP.
  
  split.
    unfold safe; unfold not; intros.  
    inversion H; subst.
    
    intros.
    inversion H.
    
    subst.(**
    apply H1 with st'0.
    apply H2 with st.
    assumption.
    assumption.
    assumption.*)
 Admitted.


Program Definition assn_sub (X: id) a (Q : Assertion) : Assertion :=
  mk_asn (fun h st => Q h (ImpDep.update st X (aeval st a))) _.
Next Obligation.
  assert (Q h |-- Q h').
    apply ILPreFrm_closed.
    apply H.
  apply H1. 
  assumption. 
Defined.
  

Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  intros Q X a st Pre.
  split.
    unfold safe; unfold not; intros.
    inversion H.
    
    intros.
    inversion H; subst.
    simpl in *.
    assumption.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{P //\\ bassn b}} c1 {{Q}} ->
  {{P //\\ ~ (bassn b)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
	intros P Q b c1 c2 H1 H2 st HP.
	split.
	  unfold safe; unfold not; intros.
	  inversion H.
	  
	  intros.
	  inversion H; subst.
	  Case "b is true".
	    apply H1 with st.
	    split; assumption.
	    assumption.
	  Case "b is false".
	    apply H2 with st.
	    split.
	      assumption.
	      simpl; intros; congruence.
	      assumption.
Qed.

Theorem hoare_while : forall P b c,
  {{P //\\ bassn b}} c {{P}} ->
  {{P}} WHILE b DO c END {{P //\\ ~ (bassn b)}}.
Proof.
  intros P b c H1 st HP.
  unfold hoare_triple in H1.
  split.
    unfold safe; unfold not; intros.
    inversion H.
  intros.
  remember (WHILE b DO c END) as wcom.
  remember (Some st') as st''.
  induction H; try (inversion Heqwcom); subst.
  inversion Heqst''.
  rewrite <- H2.
  split.
    assumption.
    simpl. intros. congruence.
  
  apply IHceval2.
  apply H1 with st.
  split.
    assumption.
    assumption.
  assumption.
  reflexivity.
  assumption.
Qed.

(**
  {{fun st => Q st /\ st X = x}}
    X ::= a
  fun st => Q st' /\ st X = aeval st' a
  (where st' = update st X x)
*)
(**
e |-> 5 /\ 5 = 5   X <~ [ e ]  { e |-> 5 }
*)
  
(**
Q ** exists vs, r {vs/modifies c}
                                 length vs = length modifies c
                                 (exists s, r s /\ dom s / modifies c)
                                 subst_fresh r vs
                                 
exists v, subst X/v e->e' //\\ subst X/v X=e'
*)

Require Export Coq.Logic.FunctionalExtensionality.

Lemma update_stack_same : forall X st n,
  ImpDep.update (ImpDep.update st X n) X (st X) = st.
Proof.
  intros.
  apply functional_extensionality.
  intros x.
  rewrite update_shadow.
  rewrite update_same.
  reflexivity.
  reflexivity.
Qed.

Theorem hoare_read : forall X e e',
  {{ (e |-> e') }} X <~ [ e ] {{ Exists v, (points_to_sub e e' X v) //\\ (aexp_eq_sub X e' X v) }}.                            
Proof.
  intros X e e' st Pre.
  simpl.
  split.
  Case "safe".
    unfold safe; unfold not; intros.
    inversion H; subst.
    simpl in *.
    apply H4.
    rewrite Pre.
    apply add_in_iff.
    left. reflexivity.
  Case "postcondition".
    intros.
    inversion H; subst.
    simpl in *.
    exists ((cstack st) X).
    split.
    SCase "e |-> e'".
      rewrite Pre.
      rewrite update_stack_same.
      reflexivity.
    SCase "X = e'".
      rewrite update_eq.
      rewrite update_stack_same.
      assert (Hfind: find (aeval (cstack st) e) (cheap st) = Some (aeval (cstack st) e')).
        rewrite Pre.
        intuition.
      rewrite Hfind in H5.
      inversion H5.
      reflexivity.
Qed.

Theorem hoare_read' : forall P Q X e e',
  {{ P //\\  Q ** (e |-> e') }} X <~ [ e ] {{ Exists v, (assn_sub X (ANum v) (P //\\  Q ** (e |-> e'))) //\\ (aexp_eq_sub X e' X v) }}.                            
Proof.

Admitted.

Lemma remove_addedL : forall a (v : nat) (h : Heap),
 h === []%map -> Equiv.equiv (remove a (add a v h)) h.
Proof.
  intros.
  unfold Equiv.equiv, MapEquiv.
  apply Equal_mapsto_iff.
  intros.
  split.
  	intros.
  	apply remove_mapsto_iff in H0.
  	inversion H0.
  	apply add_mapsto_iff in H2.
  	inversion H2.
  	inversion H3.
  	congruence.
  	inversion H3.
  	assumption.
  	
  	intros.
  	rewrite H in H0.
  	inversion H0.
Qed.

Lemma remove_addedR : forall a (v : nat) (h : Heap),
  h === []%map -> Equiv.equiv h (remove a (add a v h)).
Proof.
  intros a v h.
  unfold Equiv.equiv, MapEquiv.
  intros.
  apply Equal_mapsto_iff.
  intros.
  split.
  	intros.
  	rewrite H in H0.
  	inversion H0.
  	
  	intros.
  	apply remove_mapsto_iff in H0.
  	inversion H0.
  	apply add_mapsto_iff in H2.
  	apply or_commut in H2.
  	inversion H2.
  	inversion H3.
  	assumption.
  	inversion H3.
  	congruence.
Qed.

Theorem hoare_write : forall e e',
  {{ e |->_ }} [ e ] <~ e' {{ (e |-> e') }}.
Proof.
  intros e e' st Pre.
  split.
  Case "safe".
    unfold safe; unfold not; intros.
    inversion H. subst.
    apply H4.
    simpl in Pre.
    inversion Pre.
    rewrite H0.
    apply add_in_iff.
    left.
      reflexivity.
  Case "postcondition".
    simpl in *.
    intros.
    inversion H. subst. simpl.
  	unfold write.
  	rewrite H6.
  	inversion Pre.
  	rewrite H0.
  	assert ((remove (aeval (cstack st) e) ([]) [aeval (cstack st) e <- aeval (cstack st) x]) === []%map).
        apply remove_addedL.
        reflexivity.
    rewrite H1.
    reflexivity.
Qed.

Theorem hoare_write'' : forall e e' X,
  {{ (aexp_eq X e') //\\ (e |->_) }} [ e ] <~ X {{ (aexp_eq X e') //\\ (e |-> X) }}.
Proof.
  intros e e' X st Pre.
  split.
  Case "safe".
    unfold safe; unfold not; intros.
    inversion H. subst.
    apply H4.
    simpl in Pre.
    inversion Pre.
    inversion H1.
    rewrite H2.
    apply add_in_iff.
    left.
      reflexivity.
  Case "postcondition".
    simpl in *.
    intros.
    inversion H. subst. simpl.
    split.
      inversion Pre. assumption.
  	unfold write.
  	rewrite H6.
  	inversion Pre.
  	inversion H1.
  	rewrite H2.
  	assert ((remove (aeval (cstack st) e) ([]) [aeval (cstack st) e <- aeval (cstack st) x]) === []%map).
        apply remove_addedL.
        reflexivity.
    rewrite H3.
    rewrite H0.
    reflexivity.
Qed.

Theorem frame_rule' : forall P Q R (c : com),
  {{ P }} c {{ Q }} ->
  {{ P ** R }} c {{ Q ** R }}.
Proof.
Admitted.

Theorem frame_rule'' : forall P Q R (c : com),
  {{ P }} c {{ Q }} ->
  {{ R ** P }} c {{ R ** Q }}.
Proof.
Admitted.

Theorem hoare_write''' : forall e X v' R,
  {{ (aexp_eq X v' //\\ (e |->_)) ** R }} [ e ] <~ X {{ (aexp_eq X v' //\\ (e |-> X)) ** R }}.
Proof.
  intros.
  apply frame_rule'.
  apply hoare_write''.
Qed.
  

Theorem hoare_write' : forall (P : Assertion) e e',
  {{ (e |->_) ** P }} [ e ] <~ e' {{ (e |-> e') ** P }}.
Proof.
  intros.
  apply frame_rule' with (c:=[ e ] <~ e').
  apply hoare_write.
Qed.

Theorem hoare_deallocate : forall e,
  {{ e |->_ }} DEALLOC e {{ empSP }}.
Proof.
  intros e st Pre.
  split.
  Case "safe".
    unfold safe; unfold not; intros.
    inversion H; subst.
    unfold not in H2.
    apply H2.
    simpl in Pre.
    inversion Pre.
    rewrite H0.	
    apply add_in_iff.
    left. reflexivity.
  Case "postcondition".
    intros.
    inversion H. subst.
    simpl.
    unfold dealloc.
    split.
    SCase "[] === (remove (aeval (cstack st) e) (cheap st))".
      inversion Pre.
      simpl in H0.
      rewrite H0.
      apply remove_addedR.
      reflexivity.
    SCase "True".
      trivial.
Qed.

Lemma heap_eq : forall (h h': Heap),
  Equiv.equiv h h' = (h === h').
Proof.
  reflexivity.
Qed.

Theorem sep_hoare_consequence_pre : forall (P P' Q : Assertion) c,
  P |-- P' ->
  {{ P' }} c {{ Q }} ->
  {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple.
  intros.
  split.
  Case "safety".
    apply H in H1.
    specialize (H0 _ H1).
    apply H0.
    intuition.
  Case "".
    apply H0.
    apply H in H1.
    apply H1.
    intuition.
Qed.

Theorem sep_hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{ P }} c {{ Q' }} ->
  Q' |-- Q ->
  {{ P }} c {{ Q }}.
Proof.
  unfold hoare_triple.
  intros.
  specialize (H _ H1).
  split.
  Case "left".
    apply H.
  Case "right".
    intros.
    apply H0.
    intuition.
    apply H.
    assumption.
Qed. 

Fixpoint modified_by (c : com) : list id :=
  match c with
  | SKIP => nil
  | i ::= _ => i :: nil
  | c1; c2 =>  modified_by c1 ++ modified_by c2
  | IFB _ THEN c1 ELSE c2 FI => modified_by c1 ++ modified_by c2
  | WHILE _ DO c END => modified_by c
  | i &= ALLOC _ => i :: nil
  | DEALLOC _ => nil
  | i <~ [ _ ] => i :: nil
  | [ _ ] <~ _ => nil
  end.
  
Fixpoint list_sub (vs : list nat) (l : list id) (ost : state) (ast : state) : state :=
  match vs with
  | vsh :: vs =>
    match l with
      | lh :: l => list_sub vs l ost (substitute ast ost (cons (lh, ANum(vsh)) nil))
      | _ => ast
    end
  | _ =>
    match l with
      | h :: t => ast
      | _ => ast
    end
  end. 
  
Program Definition var_sub (R : Assertion) vs xs : Assertion :=
  mk_asn (fun h st => R h (list_sub vs xs st st)) _.
Next Obligation.
  assert( R h |-- R h').
    apply ILPreFrm_closed.
    apply H.
  apply H1.
  apply H0.
Qed.

Definition empty_heap : Heap := []%map.
      
Local Opaque ILFun_Ops.
Local Opaque ILPre_Ops.
(**
Local Opaque SABIOps.
   *)
Local Opaque MapSepAlgOps.     
Theorem frame_rule : forall P Q R c,
  {{ P }} c {{ Q }} ->
  {{ P ** R }} c {{ Q ** (Exists vs, var_sub R vs (modified_by c )) }}. 
Proof. 
  induction c; unfold hoare_triple; intros; (do 4 destruct H0).
  Case "Skip".
    split.
    SCase "Safety".
      unfold safe, not. 
      intros. 
      inversion H2.
    SCase "Post condition".
      intros.
      simpl.
      exists x, x0.
      specialize (H ((cstack st'), x)).
      split.
      SSCase "left".
        inversion H2; subst.
      	assumption.
      SSCase "right".
      	split.
      	SSSCase "left".	
      	  simpl in *.
      	  inversion H2; subst.
      	  specialize (H H0).
      	  destruct H.
      	  specialize (H3 ((cstack st'), x)).
      	  simpl in *.
      	  apply H3.
      	  apply E_Skip.
      	SSSCase "right".
          exists nil.
          simpl.
          inversion H2; subst.
          assumption.
  Case "assignment".
    split.
    SCase "Safety".
      unfold safe, not. 
      intros. 
      inversion H2.
    SCase "Post condition".
      intros.
      simpl in *.
      inversion H2; subst.
      exists x, x0.
      split.
      SSCase "left".
        inversion H2.
        subst.
        assumption.
      SSCase "right".
        split.
        SSSCase "left".
          specialize (H ((cstack st), x)).
          simpl in *.
          specialize (H H0).
          destruct H.
          specialize (H3 ((ImpDep.update (cstack st) i (aeval (cstack st) a)), x)).
          apply H3.
          simpl in *.
          apply E_Ass with (st := (cstack st, x)).
          reflexivity.
        SSCase "right".
      	  exists [((cstack st) i)].
      	  simpl.
      	  rewrite update_stack_same with (X := i) (n := aeval (cstack st) a).
      	  assumption.
  Case "Sequencing".
    split.
    SCase "Safety".
      unfold safe, not. 
      intros. 
      inversion H2.
    SCase "Post condition".
      intros.
      specialize (H ((cstack st), x)).
      specialize (H H0).
      destruct H.
      specialize (H3 st').
      Local Opaque SABIOps.
      simpl.
      simpl in H0.
      simpl.
      exists x, x0.
      split.
      SSCase "left".
        inversion H2; subst.
        simpl in *.
        admit.
      SSCase "right".
        split.
        SSSCase "left".
      	  admit.
      	SSSCase "right". 
          admit. 
  Case "IFB".
    intros.
    unfold hoare_triple.
    intros.
    split.
    SCase "Safety".
      unfold safe, not. intros. inversion H2.
    SCase "postcondition".
      intros.
      simpl.
      simpl in H0.
      exists x, x0.
      split.
      SSCase "left".
        admit.
      SSCase "right".
        split.
        SSSCase "left".
          admit.
        SSSCase "right".
          admit.
  Case "WHILE".
    intros.
    unfold hoare_triple.
    intros.
    split.
    SCase "Safety".
      unfold safe, not. intros. inversion H2.
    SCase "postcondition".
      intros.
      simpl in H0.
      simpl.
      exists x, x0.
      split.
      SSCase "left".      
        admit.
      SSCase "right".
        split.
        SSSCase "left".
          admit.
        SSSCase "right".
          admit.
  Case "ALLOC".
    split.
    SCase "Safety".
      unfold safe, not. intros. inversion H2.
    SCase "postcondition".
      intros.
      simpl in *.
      inversion H2; subst.
      exists (alloc addr n x), x0.
      split.
      SSCase "left".
        simpl.
        Local Transparent MapSepAlgOps.
        simpl in *.
        intros.
        specialize (x1 k).
        remember (cheap st) as heap.
        remember (heap [k]%map) as heapk.
        destruct heapk.
        remember ((alloc addr n heap) [k]%map) as o.
        destruct o.
        
        inversion x1.
        left.
        split.
        
      SSCase "right".
        split.
        SSSCase "left".
          specialize (H ((cstack st), x)).
          simpl in *.
          specialize (H H0).
          destruct H.
          specialize (H3 ((ImpDep.update (cstack st) i addr), (alloc addr n x))).
          simpl in *.
          apply H3.
		  apply E_Alloc with (st := (cstack st, x)). 
		  SSSSCase "".
		    simpl. 
		    Local Transparent MapSepAlgOps.
		    simpl in x1.
		    specialize (x1 addr).
		    apply not_find_in_iff in H7.
		    rewrite H7 in x1.
		    apply x1.
		  SSSSCase "".
		    simpl.
		    intros.
		    specialize (H8 n0).
		    simpl in x1.
		    specialize (x1 n0).
		    apply not_find_in_iff in H8.
		    rewrite H8 in x1.
		    apply x1.
		    assumption.
        SSSCase "right".
          exists [((cstack st) i)].
          inversion H2; subst.
      	  simpl.
          rewrite update_stack_same.
          assumption.
  Local Opaque MapSepAlgOps.
  Case "DEALLOC".
    intros.
    unfold hoare_triple.
    intros.
    split.
    SCase "Safety".
      specialize (H ((cstack st), x)).
      simpl in *.
      specialize (H H0).
      destruct H.
      unfold safe in H.
      Local Transparent MapSepAlgOps.
      simpl in *.
      unfold safe.
      intros H3.
      apply H.
      inversion H3; subst.
      destruct st.
      simpl in *.
      specialize (x1 (aeval s a)).
      apply not_find_in_iff in H6.
      rewrite H6 in x1.
      apply E_DeallocError with (addr := (aeval s a)).
      reflexivity.
      apply x1.	
    SCase "postcondition".
      Local Opaque MapSepAlgOps.
      intros.
      simpl in H0.
      simpl.
      inversion H2; subst.
      simpl.
      exists (dealloc (aeval (cstack st) a) x), x0.
      split.
        admit.
      split. 
        specialize (H ((cstack st), x)).
        simpl in *.
        specialize (H H0).
        destruct H.
        specialize (H3 ((cstack st), (dealloc (aeval (cstack st) a) x))).
        simpl in *.
        apply H3.
        apply E_Dealloc with (st := (cstack st, x)).
          reflexivity.
          simpl.
          Local Transparent MapSepAlgOps.
          simpl.
		  simpl in x1.
		  specialize (x1 (aeval (cstack st) a)).
		  unfold In in H7.
		  destruct H7.
		  apply find_mapsto_iff in H4.
		  rewrite H4 in x1.
		  destruct x1.
		  unfold In.
		  exists x2.
		  apply H5.
		  unfold safe in H.
		  apply ex_falso_quodlibet.
		  apply H.
		  apply E_DeallocError with (addr := aeval (cstack st) a). 
		  reflexivity.
		  simpl.
		  apply H5.
      exists nil.
      simpl.
      assumption.
  Local Opaque MapSepAlgOps.
  Case "read".
    split. 
    SCase "Safety".
      specialize (H ((cstack st), x)).
      simpl in *.
      specialize (H H0).
      destruct H.
      unfold safe in H.
      Local Transparent MapSepAlgOps.
      simpl in *.
      unfold safe.
      intros H3.
      apply H.
      inversion H3; subst.
      destruct st.
      simpl in *.
      specialize (x1 (aeval s a)).
      apply not_find_in_iff in H8.
      rewrite H8 in x1.
      apply E_ReadError with (addr := aeval s a).
      reflexivity.
      apply x1.
    SCase "postcondition".
      intros.
      simpl.
      exists x, x0.
      split.
      inversion H2; subst.
      simpl.
      intuition.
      split.
        specialize (H ((cstack st), x)).
        simpl in H.
        specialize (H H0).
        destruct H.
        inversion H2; subst.
        specialize (H3 ((ImpDep.update (cstack st) i n), x)).
        simpl in *.
        apply H3.
        apply E_Read with (st := (cstack st, x)) (addr := (aeval (cstack st) a)).
        simpl.
        reflexivity.
        simpl.
        Local Transparent MapSepAlgOps.
        simpl in x1.
        specialize (x1 (aeval (cstack st) a)).
        rewrite H9 in x1.
        inversion x1.
        inversion H4.
        apply find_mapsto_iff.
        assumption.
        unfold safe in H.
      	apply ex_falso_quodlibet.
      	apply H.
      	apply E_ReadError with (addr := (aeval (cstack st) a)).
      	reflexivity.
      	simpl.
      	apply H4.
      exists [((cstack st) i)].
      simpl.
      inversion H2; subst.
	  simpl.
	  rewrite update_stack_same.
	  assumption.
  Local Opaque MapSepAlgOps.
  Case "write".
    split.
    SCase "Safety".
      specialize (H ((cstack st), x)).
      simpl in *.
      specialize (H H0).
      destruct H.
      unfold safe in H.
      Local Transparent MapSepAlgOps.
      simpl in *.
      unfold safe.
      intros H3.
      apply H.
      inversion H3; subst.
      destruct st.
      simpl in *.
      specialize (x1 (aeval s a)).
      apply not_find_in_iff in H8.
      rewrite H8 in x1.
      apply E_WriteError with (addr := aeval s a).
      reflexivity.
      apply x1.
    SCase "postcondition".
      intros.
      simpl in *.
      exists (write (aeval (cstack st) a) (aeval (cstack st) a0) x), x0.
      split.
      split.
        specialize (H ((cstack st), x)).
        specialize (H H0).
        destruct H.
        specialize (H3 ((cstack st'), (write (aeval (cstack st) a) (aeval (cstack st) a0) x))).
        apply H3.
        inversion H2; subst.
        simpl in *.
        apply E_Write with (st := (cstack st, x)) (n := n).
        reflexivity.
        reflexivity.
        simpl.
        Local Transparent MapSepAlgOps.
        simpl in x1.
        specialize (x1 (aeval (cstack st) a)).
        rewrite H10 in x1.
        inversion x1.
        inversion H4.
        apply find_mapsto_iff.
        assumption.
        unfold safe in H.
      	apply ex_falso_quodlibet.
      	apply H.
      	apply E_WriteError with (addr := (aeval (cstack st) a)).
      	reflexivity.
      	simpl.
      	apply H4.
	    exists nil.
      	simpl.
      	inversion H2; subst; simpl.
      	intuition.
Qed.

Program Definition alloc_cell a : Assertion :=
  (ANum a) |-> (ANum 0).
 
Program Fixpoint alloc_cells (a n : nat) : Assertion :=
  match n with
  | 0    => empSP
  | S n' => alloc_cell a ** alloc_cells (a+1) (n')
  end.

(**
forall heaps exists n, not In n heap -> forall n' > n, not In n' heap
*)
    
(**
P a s -> Q b s -> sa_mul a b c -> (P*Q) c s

sa_mul h ([x <- 0]) (h[x<-0])
*)

Lemma conj_comp : forall (P Q : Assertion) (a b c : Heap) s,
  P a s ->
  Q b s ->
  sa_mul a b c ->
  (P ** Q) c s.
Proof.
  intros.
  simpl.
  exists a.
  exists b.
  simpl in H1.
  split.
    intros k.
    specialize (H1 k).
    destruct (find k c).
    assumption.
    
    assumption.
  
  split; assumption.
Qed.

Lemma find_in_smaller_heap : forall a k n m (h: Heap),
  find k (add a m h) = Some n ->
  a =/= k ->
  MapsTo k n h.
Proof.
  intros.
  apply find_mapsto_iff in H.
  apply add_mapsto_iff in H.
  apply or_commut in H.
  inversion H.
  inversion H1.
  assumption.
  inversion H1.
  congruence.
Qed.

Lemma not_in_smaller_heap : forall a n k (h: Heap),
  find k (add a n h) = None ->
  a =/= k ->
  not (In k h).
Proof.
  intros.
  unfold not; intros.
  apply not_find_in_iff in H.
  unfold not in H.
  apply H.
  apply add_in_iff.
  right. assumption.
Qed.

Lemma not_in_larger_heap : forall (h: Heap) a b n,
  not (In a h) ->
  a < b \/ a >= (b+n) ->
  not (In a (alloc b n h)).
Proof.
  intros.
  generalize dependent b.
  induction n.
  Case "n = 0".
    intros.
    simpl.
    assumption.
  Case "n = S n'".
    intros.
    simpl.
    unfold not; intros.
    apply add_in_iff in H1.
    inversion H1.
    inversion H2.
    inversion H0.
    omega.
    omega.
    apply IHn with (b+1).
    omega.
    assumption. 
Qed.

(* Make operators opaque, so separating conjunction does not unfold *)
Local Opaque ILFun_Ops.
Local Opaque ILPre_Ops.
Local Opaque SABIOps.

Theorem hoare_allocate : forall X n,
  {{ empSP }} X &= ALLOC n {{ Exists a, (aexp_eq (AId X) (ANum a) //\\ alloc_cells a n) }}.
Proof.
  intros X n st Pre.
  split.
  Case "safe".
    unfold safe; unfold not; intros.
    inversion H.
  Case "postcondition".
    intros.
    inversion H; subst.
    exists addr.
    simpl.
    split.
    SCase "aexp_eq".
      apply update_eq.
    
    (* Do induction on number of cells allocated *)
    SCase "alloc_cells".
      clear H.
      inversion Pre.
      simpl in *.  
      generalize dependent (ImpDep.update (cstack st) X addr).
      generalize dependent addr.
      induction n.
  
      SSCase "n = 0".
        intros. simpl.
        assumption.
  
      SSCase "n = S n'". 
        intros.
	    simpl.
        apply conj_comp with (a:=(add addr 0 (cheap st))) (b:=(alloc (addr+1) n (cheap st))).
        SSSCase "add addr 0 (cheap st)".
          simpl.
          rewrite x.
          reflexivity.
        SSSCase "alloc (addr+1) n (cheap st)".
          apply IHn with (addr:=addr+1).
          apply H5.
          omega.
          intros.
          unfold not; intros.
          apply H4.
          rewrite <- x in H1.
          inversion H1.
          inversion H2.
        SSSCase "sa_mul (heap composition)".
          simpl.
          intros.
          destruct (eq_dec addr k) as [H'|]. (* Divide possible addresses into addr === k and addr =/= k *)
          SSSSCase "addr === k".
            rewrite <- H'.
  
            assert (Hfind: find addr (add addr 0 (alloc (addr + 1) n (cheap st))) = Some 0).
              intuition.
              
            rewrite Hfind.
            left. split.
            SSSSSCase "MapsTo addr 0 (add addr 0 (cheap st))".
              intuition.
            SSSSSCase "~ In addr (alloc (addr + 1) n (cheap st))".
              apply not_in_larger_heap.
              assumption.
              omega.
          SSSSCase "addr =/= k".
            remember (find k (add addr 0 (alloc (addr + 1) n (cheap st)))) as h.
            destruct h.
            SSSSSCase "find k = Some n".
              right. split.
              SSSSSSCase "MapsTo k n0 (alloc (addr + 1) n (cheap st))".
                apply find_in_smaller_heap with (a:=addr) (m:=0).
		        symmetry.
		        assumption.
                assumption.
              SSSSSSCase "~ In k (add addr 0 (cheap st))".
                rewrite <- x.
                rewrite add_neq_in_iff.
                unfold not; intros.
                inversion H1. inversion H2.
                assumption.
            SSSSSCase "find k = None".
              split.
              SSSSSSCase "~ In k (add addr 0 (cheap st))".
                rewrite <- x.
                rewrite add_neq_in_iff.
                unfold not; intros.
                inversion H1. inversion H2.
                assumption.
              SSSSSSCase "~ In k (alloc (addr + 1) n (cheap st))".
                apply not_in_smaller_heap with (a:=addr) (n:=0).
                symmetry.
                assumption.
                assumption.
Qed.

End Hoare_Rules.

Section Examples.

Require Export ImpDep.

Definition X := Id 0.
Definition Y := Id 1.
Definition Z := Id 2.
Definition V := Id 3.
Definition a := (ANum 0).
Definition b := (ANum 1).
Definition c := (ANum 2).
Definition d := (ANum 3).
	
Definition heap_swap :=
  X <~ [ a ];
  Y <~ [ b ];
  [ a ] <~ (AId Y);
  [ b ] <~ (AId X).
  
(* Make operators opaque, so separating conjunction does not unfold *)
Local Transparent ILFun_Ops.
Local Transparent ILPre_Ops.
Local Transparent SABIOps.
    
Lemma sepSPC4 (P Q R S : Assertion) :
  (P ** Q) ** R ** S -|- (P ** S) ** R ** Q.
Proof.
  split.
    rewrite <- sepSPA.
    rewrite sepSPC.
    rewrite sepSPC.
Admitted.

Lemma exists_conj_elim : forall X a c,
  Exists v, ((points_to_sub a c X v) //\\ aexp_eq_sub X c X v) |-- (Exists v, (points_to_sub a c X v)) //\\ (Exists v', aexp_eq_sub X c X v').
Proof.
  intros.
  lexistsL.
  intros.
  lexistsR a1.
  lexistsR a1.
  reflexivity.
Qed.

Local Transparent ILFun_Ops.
Local Transparent ILPre_Ops.
Local Transparent SABIOps.

Example heap_swap_prog :
  {{ a |-> c ** b |-> d }}
  heap_swap
  {{ a |-> d ** b |-> c }}.
Proof.
  unfold heap_swap.
  eapply hoare_seq.
  apply frame_rule.
  apply hoare_read.
  rewrite sepSPC.
  eapply hoare_seq.
  apply frame_rule.
  apply hoare_read.
  
  eapply hoare_seq.
  rewrite sepSPC.
  apply frame_rule'.
  rewrite exists_conj_elim.
  rewrite landC.
  rewrite <- convert_pure.
  rewrite sepSPC.
  apply frame_rule'.
  apply sep_hoare_consequence_pre with (P':=a |->_).
  simpl.
  intros.
  exists (ANum 2).
  simpl in H0.
  simpl.
  inversion H0.
  assumption.
  
  apply hoare_write.
  admit. (*pure*)
  
  rewrite sepSPC.
  eapply sep_hoare_consequence_post.
  apply frame_rule'.
  rewrite exists_conj_elim.
  rewrite landC.
  rewrite <- convert_pure.
  rewrite sepSPC.
  apply frame_rule'.
  apply sep_hoare_consequence_pre with (P':=b |->_).
  simpl.
  intros.
  exists (ANum 3).
  simpl.
  inversion H0.
  assumption.
  
  apply hoare_write.
  admit. (*pure*)
  rewrite sepSPA.
  rewrite sepSPC with (P:=a |-> AId Y).
  rewrite sepSPC with (P:=b |-> AId X).
  rewrite sepSPA.
  rewrite sepSPA.
  rewrite sepSPC with (Q:=b |-> AId X).
  rewrite sepSPC with (P:=(Exists v', aexp_eq_sub Y d Y v')).
  rewrite sepSPA2.
  rewrite sepSPA1 with (P:=(Exists v', aexp_eq_sub X c X v') ** b |-> AId X).
  rewrite sepSPC.
  apply scME.
  rewrite sepSPC.
  rewrite convert_pure.
  simpl.
  intros.
  inversion H0.
  inversion H1.
  rewrite H3 in H2.
  assumption.
  admit. (*pure*)
  rewrite convert_pure.
  simpl.
  intros.
  inversion H0.
  inversion H1.
  rewrite H3 in H2.
  assumption.
  admit. (*pure*)
Qed.

Definition list_cell (addr elem next : aexp) : Assertion :=
  addr |-> elem ** APlus addr (ANum 1) |-> next.

Fixpoint heap_list (X : aexp) (l : list nat) : Assertion :=
  match l with
  | nil => empSP
  | x :: xs => X |-> (ANum x) ** 
		 	   (match xs with
		 	   | nil => APlus X (ANum 1) |-> (ANum 0)
		 	   | y :: ys => APlus X (ANum 1) |-> APlus X (ANum 2)
		 	   end) **
		 	   heap_list (APlus X (ANum 2)) xs
  end.
		 	    
		 	   
Definition alloc_list := 
  {{ empSP }}
  X &= ALLOC 8;
  [ (AId X) ] <~ (ANum 1);
  [ APlus (AId X) (ANum 1) ] <~ APlus (AId X) (ANum 2);
  [ APlus (AId X) (ANum 2) ] <~ (ANum 2);
  [ APlus (AId X) (ANum 3) ] <~ APlus (AId X) (ANum 4);
  [ APlus (AId X) (ANum 4) ] <~ (ANum 3);
  [ APlus (AId X) (ANum 5) ] <~ APlus (AId X) (ANum 6);
  [ APlus (AId X) (ANum 6) ] <~ (ANum 4);
  [ APlus (AId X) (ANum 7) ] <~ (ANum 0)
  {{ heap_list (AId X) (1::2::3::4::nil) }}.
  
Definition list_reversal :=
  Y ::= (ANum 0);
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    V <~ [ APlus (AId X) (ANum 1) ];
  	Z <~ [ AId V ];
  	[ AId V ] <~ (AId Y);
  	Y ::= (AId X);
  	X ::= (AId Z)
  END.
  
Local Transparent ILFun_Ops.
Local Transparent ILPre_Ops.
Local Opaque SABIOps.

Definition l : list nat := 1::2::nil.

Program Definition l_rev l (a b : list nat) :=
  mk_asn (fun h st => rev l = (rev a) ++ b) _.

Definition list_rev_inv l (X Y : aexp) :=
  Exists a, Exists b, l_rev l a b ** heap_list X a ** heap_list Y b.

Example list_reversal_proof :
  {{ heap_list (AId X) l }}
  list_reversal
  {{ heap_list (AId Y) (rev l) }}.
Proof.
  unfold list_reversal.
  eapply hoare_seq.
  apply sep_hoare_consequence_pre with (P':=assn_sub Y (ANum 0) ((heap_list (AId X) l) //\\ aexp_eq (AId Y) (ANum 0))).
    simpl.
    intros.
    split.
    assumption.
    rewrite update_eq.
    reflexivity.
  apply hoare_asgn.
  apply sep_hoare_consequence_pre with (P':=list_rev_inv l (AId X) (AId Y)).
  unfold list_rev_inv.
  apply lexistsR with l.
  apply lexistsR with nil.
  simpl.
  intros.
  admit.
  eapply sep_hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq.
  unfold list_rev_inv.
  apply sep_hoare_consequence_pre with (P':= (l_rev (1::2::nil) (1::(2::nil)) (nil)) **
                                             (AId X) |-> (ANum 1) ** (APlus (AId X) (ANum 1)) |-> (APlus (AId X) (ANum 2)) **
                                             heap_list (APlus (AId X) (ANum 2)) (1::2::nil) ** heap_list (AId Y) (nil)).
    lexistsL.
    intros.
    lexistsL.
    intros.
    admit.
  
  rewrite sepSPC.
  rewrite <- sepSPC with (Q:= AId X |-> ANum 1).
  apply frame_rule'.
  apply frame_rule'.
  apply frame_rule'.
  apply hoare_read.
  
  eapply hoare_seq.
  apply frame_rule'.
  apply frame_rule'.
  apply frame_rule'.
  rewrite exists_conj_elim.
  rewrite landC.
  rewrite <- convert_pure.
  rewrite sepSPC.
  apply sep_hoare_consequence_pre with (P':= (AId V) |-> APlus (AId X) (ANum 2)).
    admit.
  apply hoare_read.
  admit. (*pure aexp_eq_sub*)
  
  eapply hoare_seq.
  apply frame_rule'.
  apply frame_rule'.
  apply frame_rule'.
  rewrite exists_conj_elim.
  rewrite landC.
  rewrite <- convert_pure.
  rewrite sepSPC.
  apply frame_rule'.
  apply sep_hoare_consequence_pre with (P':= (AId V) |->_).
    lexistsL.
    intros.
    simpl.
    intros.
    exists (APlus (AId X) (ANum 2)).
    simpl.
    rewrite update_neq in H0.
    rewrite update_neq in H0.
    assumption.
    reflexivity.
    reflexivity.
  
  apply hoare_write.
   admit. (*pure*)
  
  eapply hoare_seq.
  apply sep_hoare_consequence_pre with (P':= assn_sub Y (AId X) ((((AId V |-> AId Y **
        (Exists v', aexp_eq_sub Z (APlus (AId X) (ANum 2)) Z v')) **
       heap_list (APlus (AId X) (ANum 2)) (1::2::nil) ** heap_list (AId Y) nil) **
      AId X |-> ANum 1) ** l_rev (1::2::nil) (1::2::nil) nil)).
      admit.
  apply hoare_asgn.
  eapply sep_hoare_consequence_post.
  apply sep_hoare_consequence_pre with (P':= assn_sub X (AId Z) ((((AId V |-> AId Y **
        (Exists v', aexp_eq_sub Z (APlus (AId X) (ANum 2)) Z v')) **
       heap_list (APlus (AId X) (ANum 2)) (1::2::nil) ** heap_list (AId Y) nil) **
      AId X |-> ANum 1) ** l_rev (1::2::nil) (1::2::nil) nil)).
    admit.
  
  apply hoare_asgn.
  unfold list_rev_inv.
  Local Opaque ILPre_Ops.
  simpl.
  
  
    
    
  
  
  
  
  
  

End Examples.

End ILImp.