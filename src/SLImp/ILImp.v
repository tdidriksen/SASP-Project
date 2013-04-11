Require Import ILogic ILTac ILInsts ImpDependencies Maps MapNotations MapInterface.

Module ILImp.

Definition Assertion := state -> Prop.

Local Existing Instance ILFun_Ops.
Local Existing Instance ILFun_ILogic.

(* HEAP *)
Definition Heap := Map [ nat, nat ].

Fixpoint alloc (key cells : nat) (heap : Heap) : nat :=
  match cells with
  | 0 => key
  | S c => alloc (key-1) c (heap [ key <- 0 ])
  end.

Definition dealloc (key : nat) (heap : Heap) : Heap :=
  remove key heap.
   
Definition read (key : nat) (heap : Heap) : option nat :=
  heap [ key ].
 
Definition write (key value : nat) (heap : Heap) : Heap :=
  match find key heap with
  | Some _ => heap [ key <- value ]
  | None   => heap
  end.

(* com *)
Inductive com : Type :=
  | CSkip    : com
  | CAss     : id -> aexp -> com
  | CSeq     : com -> com -> com
  | CIf      : bexp -> com -> com -> com
  | CWhile   : bexp -> com -> com
  | CAlloc   : aexp -> com
  | CDealloc : aexp -> com
  | CRead    : aexp -> com
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
Notation "'ALLOC' a" :=
  (CAlloc a) (at level 80).
Notation "'DEALLOC' a" :=
  (CDealloc a) (at level 80).
Notation "'[' a ']'" :=
  (CRead a) (at level 80). 
Notation "'[' a1 ']' '<~' a2" :=
  (CWrite a1 a2) (at level 80).
  
Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Definition getHeap opheap : Heap :=
  match opheap with
  | Some h => h
  | None   => []
  end.

Inductive ceval : com -> (state * Heap) -> (state * option Heap) -> Prop :=
  | E_Skip : forall st,
      SKIP / st || (fst st, Some (snd st))
  | E_Ass  : forall st a1 n X,
      aeval (fst st) a1 = n ->
      (X ::= a1) / st || ((update (fst st) X n), Some (snd st))
  | E_Seq : forall c1 c2 st st' st'' h,
      c1 / st  || st' ->
      (snd st') = Some h ->
      c2 / (fst st, getHeap (snd st')) || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval (fst st) b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval (fst st) b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval (fst st) b1 = false ->
      (WHILE b1 DO c1 END) / st || (fst st, Some (snd st))
  | E_WhileLoop : forall st st' st'' b1 c1 h,
      beval (fst st) b1 = true ->
      c1 / st || st' ->
      (snd st') = Some h ->
      (WHILE b1 DO c1 END) / (fst st', getHeap (snd st')) || st'' ->
      (WHILE b1 DO c1 END) / st || st'' 
  | E_Alloc : forall st st' a1,
  	  (ALLOC a1) / st || st'
  | E_Dealloc : forall st st' a1,
  	  In (aeval (fst st) a1) (snd st) ->
      (DEALLOC a1) / st || st'
  | E_DeallocError : forall st a1,
  	  ~ In (aeval (fst st) a1) (snd st) ->
      (DEALLOC a1) / st || (fst st, None)
  | E_Read : forall st a1,
      In (aeval (fst st) a1) (snd st) ->
      ([ a1 ]) / st || (fst st, Some (snd st))
  | E_ReadError : forall st a1,
  	  ~ In (aeval (fst st) a1) (snd st) ->
      ([ a1 ]) / st || (fst st, None)
  | E_Write : forall st st' a1 a2,
  	  In (aeval (fst st) a1) (snd st) ->
      ([ a1 ] <~ a2) / st || st'
  | E_WriteError : forall st a1 a2,
  	  ~ In (aeval (fst st) a1) (snd st) ->
      ([ a1 ] <~ a2) / st || (fst st, None)

  where "c1 '/' st '||' st'" := (ceval c1 st st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Ass" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop"
  | Case_aux c "E_Alloc" | Case_aux c "E_Dealloc"
  | Case_aux c "E_Read" | Case_aux c "E_Write"
  ].
(* /com *)

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
	intros P Q b c1 c2 H1 H2 st st' H3 H4.
	inversion H3; subst.
	Case "b is true".
		apply (H1 st st').
		assumption.
		split.
		assumption.
		unfold bassn.
		assumption.
	Case "b is false".
		apply (H2 st st').
		assumption.
		split.
		assumption.
		apply bexp_eval_false.
		assumption.
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

End ILImp.