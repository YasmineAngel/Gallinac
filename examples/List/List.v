From GallinaC Require Import Programming.

(* print_ll ist not implemented as it performs only I/O *)
(* Instead, it is stubbed and will be excluded from extraction *)
Definition print_ll (ptr : Pointer.t) : program (State ListStore list_heap_carrier) unit :=
  ret tt.

Module List.

  Definition length (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) N.t :=
    do var (node: Pointer.t) <- ptr;
    do var (count: N.t) <- (0%N : N.t); 
    while (do curr <- read_var node; do c <- eq_ptr curr Pointer.NULL; ret (negb c))
      (
        do (nd: Pointer.t) <- read_var node;
        do next_ptr <- nd ~+> n_ofst;
        do (next: Pointer.t) <- read_ptr next_ptr;
        write_var node next;; 
        do (c: N.t) <- read_var count;
        write_var count ((c + 1)%N : N.t)
      );;
    read_var count.

  Definition is_empty (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) bool :=
    eq_ptr ptr Pointer.NULL.

  Definition cons [MS: MemStorable] (ptr: Pointer.t) (n_ofst: N.t) (d_ofst: N.t) (v: MS): program (State ListStore list_heap_carrier) Pointer.t.
  Admitted.

  Definition tl (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t.
  Admitted.

  Definition nth (ptr: Pointer.t) (n_ofst: N.t) (nth: nat): program (State ListStore list_heap_carrier) Pointer.t.
  Admitted.

  Definition reverse (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t :=
    do var (node: Pointer.t) <- ptr;
    do var (new_next: Pointer.t) <- Pointer.NULL;
    write_var node ptr;;
    while (do curr <- read_var node; do c <- eq_ptr curr Pointer.NULL; ret (negb c))
      (
        do (nd: Pointer.t) <- read_var node ;
        do node_next_ptr <- nd ~+> n_ofst ;
        do (old_next: Pointer.t) <- read_ptr node_next_ptr ;
        do (new_next_v : Pointer.t) <- read_var new_next ;
        write_ptr node_next_ptr new_next_v ;;
        write_var new_next nd ;;
        write_var node old_next
      );;
    read_var new_next.

  Definition append (l0 l1: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t.
  Admitted.

End List.

Module ListExample.

  Import List.

  Definition allocate : program (State ListStore list_heap_carrier) Pointer.t :=
    do last <- alloc_ptr 2 Pointer.NULL;
    write_ptr last 3;;
    do middle <- Primitives.alloc_ptr 2 Pointer.NULL;
    write_ptr middle 2;;
    do ptr_shift <- shift_fw_ptr middle 1;
    write_ptr ptr_shift last;;
    do first <- Primitives.alloc_ptr 2 Pointer.NULL;
    write_ptr first 1;;
    do ptr_shift <- shift_fw_ptr first 1;
    write_ptr ptr_shift middle;;
    ret first.

  Definition main: program _ nat :=
    do ptr <- allocate;
    print_ll ptr;;
    do ptr <- List.reverse ptr 1%N;
    print_ll ptr;;
    ret 0.

End ListExample.
