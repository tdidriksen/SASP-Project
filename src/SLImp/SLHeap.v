Require Export Maps MapNotations MapInterface MapFacts.

Module Heap.

Inductive MemoryCell :=
    Holds : nat -> MemoryCell
  | Free : MemoryCell.

Definition Heap := Map [ nat, MemoryCell ].

Definition alloc (key : nat) (heap : Heap) : Heap :=
  heap [ key <- Free ].

Definition dealloc (key : nat) (heap : Heap) : Heap :=
  remove key heap.
   
Definition read (key : nat) (heap : Heap) : option MemoryCell :=
  heap [ key ].
 
Definition write (key value : nat) (heap : Heap) : Heap :=
  match find key heap with
    | Some mc => heap [ key <- Holds value ]
    | None => heap
  end.

(* Allocation *)
Theorem allocation_cardinality : forall heap key,
  ~ In key heap -> S (cardinal heap) = cardinal (alloc key heap).
Proof.
  intros.
  symmetry.
  rewrite cardinal_2 with (m:=heap) (x:=key) (e:=Free).
  reflexivity.
  assumption.
  
  unfold Add.
  reflexivity.
Qed.

Theorem allocate_none : forall heap key,
  (alloc key heap) [ key ] = Some Free.
Proof.
  unfold alloc.
  intuition.
Qed.

(* Deallocation *)

Theorem deallocation_cardinality : forall heap key,
  In key heap -> cardinal heap = S (cardinal (dealloc key heap)).

Theorem deallocate_key : forall heap key,
  (dealloc key heap) [ key ] = None.
  
Theorem deallocate_empty_heap : forall heap key,
	Empty heap -> Empty (dealloc key heap). 

(* Write *)

(** Theorem write_sound : forall heap heap' key value,
  In key heap -> write key value heap = heap'. *)

(* Read *)

Theorem read_sound : forall heap key value,
  read key (write key value heap) = Some (Holds value).
  

End Heap.