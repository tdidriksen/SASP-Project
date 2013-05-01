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

(* Points-to, i.e. e |-> v *)
Program Definition points_to_precise a v : Assertion :=
  mk_asn (fun h st => Equiv.equiv h (add (aeval st a) (aeval st v) (empty nat))) _.
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

(* Function calls *)


Require Import Orders.

Definition FunctionBody := list id -> com -> aexp.

(**
Inductive id_eq : id -> id -> Prop :=
  | id_eq_eq : forall id1 id2, true = beq_id id1 id2 -> id_eq id1 id2.

Inductive id_lt : id -> id -> Prop :=
  | id_lt_lt : forall id1 id2, true = blt_id id1 id2 -> id_lt id1 id2.

Program Instance id_Equivalence `(Equivalence nat _eq) :
  Equivalence (id_eq).
Next Obligation.
  simpl_relation.
  apply id_eq_eq.
  apply beq_id_refl.
Qed.
Next Obligation.
  simpl_relation.
  apply id_eq_eq.
  apply beq_id_sym.
  inversion H0.
  assumption.
Qed.
Next Obligation.
  simpl_relation.
  inversion H0.
  inversion H1.
  apply id_eq_eq.
  apply beq_id_eq in H2.
  apply beq_id_eq in H5.
  subst.
  inversion H0.
  assumption.
Qed.  
  
Program Instance IdOrderedType : OrderedType.StrictOrder id_lt id_eq.
Next Obligation.
	simpl_relation.
	inversion H.
	inversion H0.
	
	
	Admitted.
Next Obligation.
	
  
  Admitted.

Program Instance id_UsualStrictOrder :
  OrderedType.StrictOrder (@id_lt ) (@Logic.eq _).
Next Obligation.
  Admitted.
  
Fixpoint id_compare (x y : id) :=
  match beq_id x y with
    | true => Eq
    | _ =>
      match blt_id x y with
        | true => Lt 
        | _ => Gt
      end
  end.

Check id_compare.

Program Instance id_OrderedType: OrderedType (id) := 
  {
    _eq := id_eq;
    _cmp := id_compare;
    _lt := id_lt;
    _cmp := id_compare;
    OT_Equivalence := id_Equivalence _;
    OT_StrictOrder := id_StrictOrder 
  }.
 *)
Definition Prog := Map [ id, FunctionBody ]. 

Definition ProgSpec := Prog -> nat -> Prop.

Instance ProgSpecILogic : ILogic ProgSpec := _.

Definition mkspec (f: Prog -> nat -> Prop) 
					(Spec: forall c st n (P: Assertion) (Q: Assertion), 
						P (cheap st) (cstack st) -> forall n', n' < n -> 
						safe c st /\ forall st', c / st || Some st' ->
						Q (cheap st') (cstack st')) : ProgSpec.
	Admitted.			
						
Definition substitution := (id * aexp)%type.

Fixpoint substitute (ast: state) (ost: state) (subs: list substitution) : state :=
	match subs with
	| nil => ast
	| sub :: subz => substitute (ImpDependencies.update ast (fst sub) (aeval ost (snd sub))) ost subz
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
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof. 
  intros P Q R c1 c2 H1 H2 st HP.
  
  split.
    unfold safe; unfold not; intros.
    inversion H; subst.
    
    intros.
    inversion H.
    subst.
    apply H1 with st'0.
    apply H2 with st.
    assumption.
    assumption.
    assumption.
 Qed.


Program Definition assn_sub (X: id) a (Q : Assertion) : Assertion :=
  mk_asn (fun h st => Q h (ImpDependencies.update st X (aeval st a))) _.
Next Obligation.
  unfold ImpDependencies.update, aeval.
  (* rewrite <- H. *)
  
Admitted.
  

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
  split.
    unfold safe; unfold not; intros.
    inversion H.
  intros.    
  remember (WHILE b DO c END) as wcom.
  induction H; try (inversion Heqwcom); subst.
  assert (st = st').
    admit.
  rewrite <- H0.
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
Qed.


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

Lemma aeval_update_extend : forall (st : state) (e : aexp) (e' n : nat) (X : id),
  st X = (ImpDependencies.update st X e') X -> aeval st e = aeval (ImpDependencies.update st X e') e.
Proof.
  
  (**
  rewrite <- update_same.
  rewrite <- H.
  apply update_.
  generalize dependent e.
  induction e.
  simpl. intros. reflexivity.
  simpl. intros. rewrite update_eq in H.
  *)
Admitted.



Lemma test : forall a v (h : Heap) st,
  Equiv.equiv h (add (aeval st a) (aeval st v) (empty nat)) -> MapsTo (aeval st a) (aeval st v) h.
Proof.
  intros.

      
Admitted.


Theorem hoare_read : forall X e e',
  {{ (e |-> e') //\\ aexp_eq (AId X) e' }} X <~ [ e ] {{ (e |-> e') }}.
Proof.
  intros X e e' st H.
  inversion H; subst.
  split.
  Case "safe".
    unfold safe. unfold not. intros.
    inversion H2. subst.
    simpl in H0.
    rewrite H0 in H7.
    unfold not in H7.
    apply H7.
    apply add_in_iff.
    left. reflexivity.
  Case "postcondition".
    intros.
    simpl in *.    
    inversion H2; subst.
    simpl.
    assert ((cstack st) X = ImpDependencies.update (cstack st) X (aeval (cstack st) e') X).
      rewrite update_same.
      reflexivity.
      assumption.
    
    assert (MapsTo (aeval (cstack st) e) (aeval (cstack st) e') (cheap st)).
      apply test.
      assumption.
    apply find_mapsto_iff in H4.
    rewrite H4 in H8.
    inversion H8.
    simpl.
    rewrite H0.
    inversion H2; subst.
    repeat rewrite <- aeval_update_extend with (X:=X) (e':=aeval (cstack st) e').
    reflexivity.
    intuition.
    admit.
    admit.
    admit.
Qed.

Lemma or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

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
    unfold not in H4.
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

Program Definition alloc_cell a : Assertion :=
  (ANum a) |-> (ANum 0).
 
Program Fixpoint alloc_cells (a n : nat) : Assertion :=
  match n with
  | 0    => empSP
  | S n' => alloc_cell a ** alloc_cells (a+1) (n')
  end.

Lemma heap_eq : forall (h h': Heap),
  Equiv.equiv h h' = (h === h').
Proof.
  reflexivity.
Qed.

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

Lemma not_in_alloc_heap : forall h a addr n,
  h === (empty nat) ->
  a < addr ->
  not (In a (alloc addr n h)).
Proof.
  intros.
  induction n.
  simpl.
  rewrite H.
  unfold not; intros.
  inversion H1.
  inversion H2.
  
  unfold not; intros.
  unfold alloc in H1.
Admitted.
  

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
  intros.
  inversion H; subst.
  exists addr.
  simpl.
  split.
  Case "aexp_eq".
    apply update_eq.
    clear H.
    simpl in Pre.
    inversion Pre.
    generalize dependent (ImpDependencies.update (cstack st) X addr).
    generalize dependent addr.
    induction n.
  
  Case "n = 0".
    intros. simpl.
    assumption.
  
  Case "n = S n'". 
    intros.
	simpl.
    
    apply conj_comp with (a:=(add addr 0 (cheap st))) (b:=((alloc (addr+1) n (cheap st)))).
    SCase "(alloc_cell addr) (cheap st) [addr <- 0]".
      unfold alloc_cell.
      simpl.
      rewrite x.
      reflexivity.
    SCase "(alloc_cells (addr + 1) n) (alloc (addr + 1) n (cheap st))".
      apply IHn with (addr:=addr+1).
      assert (forall a, a > addr -> not (In a (cheap st))).
        intros.
        rewrite <- x.
        unfold not; intros.
        inversion H1.
        inversion H2.
      apply H0.
      omega.
    SCase "sa_mul".
      simpl.
      intros.
      destruct (eqb_dec addr k) as [H'|].
      SSCase "addr === k".
        rewrite <- H'.
    
        assert (find addr (alloc (addr + 1) n (add addr 0 (cheap st))) = Some 0).
          admit.
    
        rewrite H0.
        left. split.
        intuition.
        apply not_in_alloc_heap.
        symmetry.
        assumption.
        omega.
      SSCase "addr =/= k".
        remember (find k (alloc (addr + 1) n (add addr 0 (cheap st)))) as h.
        destruct h.
        right. split.
        assert (((alloc (addr + 1) n (cheap st) [addr <- 0]) [k]%map = Some n0) ->
                addr =/= k ->
                MapsTo k n0 (alloc (addr + 1) n (cheap st))).
                admit.
        apply H0.
        symmetry.
        assumption.
        assumption.
        rewrite <- x.
        simpl.
        rewrite add_neq_in_iff.
        unfold not; intros.
        inversion H0. inversion H1.
        assumption.
      
        split.
        rewrite <- x.
        simpl.
        rewrite add_neq_in_iff.
        unfold not; intros.
        inversion H0. inversion H1.
        assumption.
        assert (((alloc (addr + 1) n (cheap st) [addr <- 0]) [k]%map = None) ->
                addr =/= k ->
                not (In k (alloc (addr + 1) n (cheap st)))).
                admit.
        apply H0.
        symmetry.
        assumption.
        assumption.
Qed.

End Hoare_Rules.

(* Function calls *)
Module Functions.

Definition prog := Map [ (id -> list id -> com), com ]. 

Definition substitution := (id * aexp)%type.

Fixpoint substitute (ast: state) (ost: state) (subs: list substitution) : state :=
	match subs with
	| nil => ast
	| sub :: subz => substitute (ImpDependencies.update ast (fst sub) (aeval ost (snd sub))) ost subz
	end.

End Functions.

End ILImp.