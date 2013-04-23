Require Import ILogic ILTac ILInsts.
Require Import ImpDependencies.
Require Import MapNotations MapInterface.
Require Import BILogic SepAlgMap.

Module ILImp.

(* HEAP *)
Definition Heap := Map [ nat, nat ].

Fixpoint alloc (addr cells : nat) (heap : Heap) : Heap :=
  match cells with
  | 0 => heap
  | S c => alloc (addr+1) c (add addr 0 heap)
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
  | Some _ => add addr value heap
  | None   => heap
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
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval (cstack st) b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval (cstack st) b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval (cstack st) b1 = false ->
      (WHILE b1 DO c1 END) / st || Some st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval (cstack st) b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / get st' || st'' ->
      (WHILE b1 DO c1 END) / st || st'' 
  | E_Alloc : forall st X a1 cells addr,
  	  ~ In addr (cheap st) ->
  	  (* aeval (cstack st) a1 = cells -> *)
  	  (X &= ALLOC a1) / st || Some (update (cstack st) X addr, alloc addr cells (cheap st))
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
Check ILPreFrm.

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

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', 
       c / st || Some st'  ->
       P (cheap st) (cstack st)  ->
       Q (cheap st') (cstack st').

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) 
                                  (at level 90, c at next level) 
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

(* Points-to, i.e. e |-> v *)
Program Definition points_to_precise a v : Assertion :=
  mk_asn (fun h st => (MapsTo (aeval st a) (aeval st v) h) /\ h === (add (aeval st a) (aeval st v) (empty nat))) _.
Next Obligation.
  split.
  rewrite <- H.
  assumption.
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
  (points_to_precise a v) (at level 100).
Notation "e '|->_'" :=
  (points_to_weak e) (at level 100).
Notation "e '|~>' v" :=
  (in_heap e v) (at level 100).

(* bassn *)
Program Definition bassn b : Assertion :=
  mk_asn (fun h st => beval st b = true) _.
(* No Obligations *)

(* aexp equality *)
Program Definition aexp_eq (a1 a2 : aexp) : Assertion :=
  mk_asn (fun h st => aeval st a1 = aeval st a2) _.
(* No Obligations *)

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


(** Hoare rules *)
Section Hoare_Rules.
Require Import MapFacts SepAlg.
  

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


Program Definition assn_sub (X: id) a (Q : Assertion) : Assertion :=
  mk_asn (fun h st => Q h (ImpDependencies.update st X (aeval st a))) _.
Next Obligation.
  unfold ImpDependencies.update, aeval.
  (* rewrite <- H. *)
  
Admitted.
  

Theorem hoare_asgn : forall Q X a,
  {{assn_sub X a Q}} (X ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  simpl.
  simpl in HQ.
  assumption.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  {{P //\\ bassn b}} c1 {{Q}} ->
  {{P //\\ ~ (bassn b)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
	intros P Q b c1 c2 H1 H2 st st' H3 H4.
	inversion H3; subst.
	Case "b is true".
		apply (H1 st st').
		assumption.
		split; assumption.
	Case "b is false".
		apply (H2 st st').
		assumption.
		split.
		assumption.
		simpl; intros; congruence.
Qed.

(**
Theorem hoare_while : forall P b c,
  {{P //\\ bassn b}} c {{P}} ->
  {{P}} WHILE b DO c END {{P //\\ ~ (bassn b)}}.
Proof.
  intros.
  unfold hoare_triple.
  intros.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom.
  induction He; try (inversion Heqwcom); subst.
  Case "E_WhileEnd".
  	split. 
   		assumption.
  		simpl; intros; congruence.
  Case "E_WhileLoop".
    subst.
  	apply IHHc2. reflexivity.
  	inversion Hc2.
  	apply (H st st''). assumption.
  	split.
  		assumption.
  		assumption.
  		
    
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom.
  induction He; try (inversion Heqwcom); subst.
  
  Case "E_WhileEnd".
    split. assumption. apply bexp_eval_false. assumption.

  Case "E_WhileLoop".
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption. Qed.

  		
  | E_WhileEnd : forall b1 st c1,
      beval (cstack st) b1 = false ->
      (WHILE b1 DO c1 END) / st || Some st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval (cstack st) b1 = true ->
      c1 / st || Some st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st'' 
Qed.
*)

Lemma Some_eq : forall m (n : nat),
  m = n <-> Some m = Some n.
Proof.
  intros.
  split.
    intros.
    rewrite H.
    reflexivity.
    
    intros.
    destruct m. destruct n.
    reflexivity.
    inversion H.
    inversion H.
    reflexivity.
Qed.
    
(* Second backward-reasoning form *)
Theorem hoare_read : forall X e Q,
  {{ Exists e', (e |~> e') //\\ assn_sub X e' Q }} X <~ [ e ] {{ Q }}.
Proof.
  intros X e Q st st' H H'.
  inversion H; subst.
  inversion H'.
  inversion H0.
  
  simpl in *.
  apply find_mapsto_iff in H1.
  rewrite H5 in H1.
  apply Some_eq in H1.
  rewrite <- H1 in H2.
  assumption.
Qed.

Lemma or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

Lemma add_same : forall a (v : nat) v' (h : Heap),
 Equiv.equiv (write a v (write a v' h)) (write a v h).
Proof.
  intros.
  unfold Equiv.equiv, MapEquiv.
  apply Equal_mapsto_iff.
  intros.
  split.
  	intros.
  	apply find_mapsto_iff in H.
  	apply find_mapsto_iff.
  	rewrite <- H.
  	inversion H.
  	apply add_mapsto_iff.
  	left.
  	  assumption.
  	  
  	
 
  	right.
  	  split.
  	  apply or_commut in H.
  	  inversion H.
  	  
Admitted.
  
Theorem hoare_write : forall e e',
  {{ e |->_ }} [ e ] <~ e' {{ (e |-> e') }}.
Proof.
  intros e e' st st' H H'.
  simpl in *.
  inversion H. subst. simpl.
  
  split.
    unfold write.
    rewrite H6.
    apply add_mapsto_iff.
    left.
  	  split; reflexivity.
  	
  	unfold write.
  	rewrite H6.
  	inversion H'.
  	inversion H0.
  	rewrite H2.
  	rewrite <- add_same.
  	

Admitted.

Lemma remove_added : forall a (v : nat) (h: Heap),
  Equiv.equiv (remove a (add a v h)) h.
Proof.
  intros a v h.
  unfold Equiv.equiv.
  unfold MapEquiv.
  apply Equal_mapsto_iff.
  intros.
  split.
  	intros.
  	apply remove_mapsto_iff in H.
  	inversion H.
  	apply add_mapsto_iff in H1.
  	apply or_commut in H1.
  	inversion H1.
  	inversion H2.
  	assumption.
  	inversion H2.
  	congruence.
  	
  	intros.
  	apply find_mapsto_iff in H.
  	apply remove_mapsto_iff.
  	split.
  	  
  	  admit.
  	  
  	  apply add_mapsto_iff.
  	  right.
  	    split.
  	    admit.
  	    assumption.
Qed.

Theorem hoare_deallocate : forall e,
  {{ e |->_ }} DEALLOC e {{ empSP }}.
Proof.
  intros e st st' H H'.
  
  inversion H. subst. simpl in H'.
  simpl.
  unfold dealloc.
  split.
    inversion H'.
    inversion H0.
    rewrite H2.
    rewrite remove_added.
    intuition.
    trivial.
Qed.

Program Definition alloc_cell a : Assertion :=
  a |-> (ANum 0).
 

Fixpoint alloc_cells (a n : nat) : Assertion :=
  match n with
  | 0    => empSP
  | S n' => alloc_cell (ANum a) ** alloc_cells (a+1) (n')
  end.

Theorem hoare_allocate : forall X v n,
  {{ empSP }} X &= ALLOC n {{ Exists a, aexp_eq (AId X) (ANum a) //\\ alloc_cells a n }}.
Proof.
  intros X v' st st' Hx Pre.
  inversion Hx. subst.
  simpl.
  inversion Pre.
  simpl in *.
  intros.
  exists addr.
  subst.
  split.
Admitted.

End Hoare_Rules.

End ILImp.