Lemma not_None_iff_Some : forall n (m : nat),
   (n = Some m <-> n <> None).
Proof.
Admitted.

Program Definition hassn_sub (X: id) a (Q : Assertion) : Assertion :=
  mk_asn (fun h st => forall n, (find (aeval st a) h) = Some n -> Q h (ImpDependencies.update st X n)) _.
Next Obligation.
  unfold read.
(**
  unfold ImpDependencies.update, read.
  rewrite <- H.
 *) 
Admitted.

Lemma in_update_extend : forall (st : state) (h : Heap) (e : aexp) (e' : nat) (X : id),
  In (aeval st e) h -> 
  aeval st e = aeval (ImpDependencies.update st X e') e ->
  In (aeval (ImpDependencies.update st X e') e) h.
Proof.
  intros.
  rewrite <- H0.
  assumption.
Qed.

Lemma aeval_update_extend : forall (st : state) (e : aexp) (e' : nat) (X : id),
  aeval st e = aeval (ImpDependencies.update st X e') e.
Proof.
  intros.
  induction e.
  simpl. reflexivity.
  simpl. rewrite update_neq. reflexivity.
  
Admitted.

Fixpoint free_in_heap_prop (a n : nat) (h : Heap) : Prop :=
  match n with
  | 0    => True
  | S n' => not (In a h) /\ free_in_heap_prop (a+1) (n') h
  end.
  
Program Definition free a n : Assertion :=
  mk_asn (fun h st => free_in_heap_prop (aeval st a) n h) _.
Next Obligation.
Admitted.

(**
Theorem hoare_allocate : forall X n a Q,
  {{ free a n //\\ ((a |-> (ANum 0)) -* assn_sub X a Q) }} X &= ALLOC n {{ Q }}.
Proof.
  intros X n a Q st st' Hc Pre.
  inversion Hc. subst. simpl in *.
  inversion Pre.
  apply H0.
  
  split.
    inversion Hc. subst.
    simpl in *.
*)    

(** 
{{ empSP }} X &= ALLOC n {{ aexp_eq (AId X) a //\\ ((ANum a) |-> (ANum 0)) ** (((APlus (ANum a) (ANum 1)) |-> ANum 0)) }}.
*)