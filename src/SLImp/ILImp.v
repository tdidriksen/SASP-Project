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
  Proper (lentails --> eq ==> lentails --> impl) hoare_triple.
Proof.
Admitted.

Global Instance hoare_triple_lequiv:
  Proper (lequiv ==> eq ==> lequiv ==> iff) hoare_triple.
Proof.
Admitted.

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

Fixpoint modified_by (c : com) (l : list id) : list id :=
  match c with
  | SKIP => l
  | i ::= _ => i :: l
  | c1; c2 =>  modified_by c2 l ++ modified_by c2 l ++ l 
  | IFB _ THEN c1 ELSE c2 FI => modified_by c1 l ++ (modified_by c2 l ++ l)
  | WHILE _ DO c END => modified_by c l ++ l
  | i &= ALLOC _ => i :: l
  | DEALLOC _ => l
  | i <~ [ _ ] => i :: l
  | [ _ ] <~ _ => l
  end.
  
Fixpoint list_sub (vs : list id) (l : list id) (ost : state) (ast : state) : state :=
  match vs with
  | vsh :: vs =>
    match l with
      | lh :: l => list_sub vs l ost (substitute ast ost (cons (vsh, ANum(ost lh)) nil))
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
        
Theorem frame_rule : forall P Q R c,
  {{ P }} c {{ Q }} |--
  {{ P ** R }} c {{ Q ** (Exists vs, var_sub R vs (modified_by c nil)) }}. 
Proof. 
  unfold hoare_triple.
  intros.
  split.
    apply H.
    
    
    
  
Admitted.

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
Local Opaque ILFun_Ops.
Local Opaque ILPre_Ops.
Local Opaque SABIOps.

Lemma aexp_permute : forall X Y v v' P Q,
  ((P //\\ aexp_eq X v) ** (Q //\\ aexp_eq Y v')) -|-
  aexp_eq X v //\\ aexp_eq Y v' //\\ (P ** Q).
Proof.
Admitted.

Example heap_swap_prog :
  {{ a |-> c ** b |-> d }}
  heap_swap
  {{ a |-> d ** b |-> c }}.
Proof.
  unfold heap_swap.
  eapply hoare_seq.
  apply frame_rule'.	
  apply hoare_read.
  rewrite sepSPC.
  eapply hoare_seq.
  apply frame_rule'.
  apply hoare_read.
  
  rewrite sepSPC.
  eapply hoare_seq.
  replace (AId Y) with (d).
  apply frame_rule'.
  apply sep_hoare_consequence_pre with (P':= a|->_).
  admit.
  eapply hoare_write.
  admit.
  replace (AId X) with (c).
  rewrite sepSPC.
  eapply sep_hoare_consequence_post.
  apply frame_rule'.
  apply sep_hoare_consequence_pre with (P':= b|->_).
  admit.
  apply hoare_write.
  rewrite sepSPC.
  reflexivity.
  admit.

  rewrite H.
  apply hoare_write.
  
  admit.
  apply hoare_write.
  rewrite sepSPC.
  eapply sep_hoare_consequence_post.
  apply frame_rule'.
  apply sep_hoare_consequence_pre with (P':= b|->_).
  lexistsL; intros.
  apply landL1.
  admit.
  apply hoare_write.
  
  
  eapply hoare_seq.
  apply frame_rule'.
  apply hoare_read.
  eapply hoare_seq.
  eapply hoare_seq.
  apply frame_rule''.
  apply hoare_write.
  apply sep_hoare_consequence_post with (Q':= (aexp_eq (AId X) c //\\ b |-> (AId X))).
  apply hoare_write''.
  Case "X = c /\ (b |-> X) |-- (b |-> c)".
    simpl.
    intros.
    inversion H0.
    rewrite H1 in H2.
    assumption.
  apply frame_rule'.
  apply sep_hoare_consequence_post with (Q':=aexp_eq (AId Y) d //\\ a |-> (AId Y)).
  apply hoare_write''.
  Case "Y = d /\ (a |-> Y) |-- (a |-> d)". 
    simpl.
    intros.
    inversion H0.
    rewrite H1 in H2.
    assumption.
  apply sep_hoare_consequence_post with (Q':=(Exists v, points_to_sub b d Y v //\\ aexp_eq_sub Y d Y v)).
  apply hoare_read.
  lexistsL.
  intros.
  apply landR.
  simpl.
    intros.
    inversion H0.
    assumption.
    simpl.
    intros.
    exists d.
    simpl.
    inversion H0.
    assumption.
  firstorder.
  admit.
  simpl.
  intros.
  exists d.
  simpl.
  inversion H0.
  inversion H1.
  assumption.
  eapply sep_hoare_consequence_pre.
  apply sep_hoare_consequence_post with (Q':=(Exists v, points_to_sub a c X v //\\ aexp_eq_sub X c X v)).
  apply hoare_read.
  apply lexistsL.
  intros.
  apply landR.
  admit.
  
    
  replace ((aexp_eq (AId X) c //\\ b |->_) ** aexp_eq (AId Y) d //\\ a |->_) with (aexp_eq (AId X) c //\\ b |->_ ** aexp_eq (AId Y) d //\\ a |->_).

  
  
  apply landR.
  simpl.
  intros.
  split.
  instantiate (1:=c).
  simpl.
  intros.
  inversion H0.
  rewrite H1 in H2.
  assumption.
  (**
  eapply sep_hoare_consequence_post with (Q':=(aexp_eq (AId X) c //\\ (b |->_)) ** (Exists vs, var_sub (a |-> d) vs (modified_by ([a]<~ AId Y) nil))).
  *)
  apply frame_rule''.
  eapply sep_hoare_consequence_post.
  apply hoare_write''.
  instantiate (1:=d).
  simpl.
  intros.
  inversion H0.
  rewrite H1 in H2.
  assumption.
  eapply sep_hoare_consequence_post with (Q':=aexp_eq (AId X) c //\\ aexp_eq (AId Y) d //\\ (b |->_) ** (a |->_)).
  eapply sep_hoare_consequence_post.
  apply hoare_read.
  apply lexistsL.
  intros.
  instantiate (1:=d).
  simpl.
    intros.
    split.
    inversion H0.
    assumption.
    exists d.
    simpl.
    inversion H0.
    assumption.
  
  simpl.
    
    
  apply landL2.
  apply landR.
  simpl.
  intros.
  assumption.

    
  
  simpl.
  intros.
  
  
  apply H.
  apply frame_rule'.
  eapply sep_hoare_consequence_post. 
  apply hoare_write''.
  
  apply sep_hoare_consequence_pre with (P':=(aexp_eq (AId X) c //\\ (b |-> d))).
  apply sep_hoare_consequence_pre with (P':=(aexp_eq (AId X) c //\\ (b |->_))).
  apply sep_hoare_consequence_post with (Q':=(aexp_eq (AId X) c //\\ (b |-> (AId X)))).
  apply hoare_write''.
  simpl.
  intros.
  inversion H0.
  rewrite H1 in H2.
  assumption.
  
  simpl.
  intros.
  split.
    inversion H0.
    assumption.
    exists d.
    simpl.
    inversion H0.
    assumption.
  

    
  apply landL1.
  apply hoare_write.
  
  
  
  apply hoare_write.
  apply sep_hoare_consequence_post with (Q':=(aexp_eq (AId X) c) //\\ (b |-> (AId X))).
  apply hoare_write.	
  admit.
  apply landAdj.
  apply landR.
  
  firstorder.
Admitted.
  

End Examples.

End ILImp.