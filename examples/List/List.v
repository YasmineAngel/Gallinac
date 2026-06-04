From GallinaC Require Import Programming.
From GallinaC Require Import Frame GenAssertion Hoare InternalTriples ListAssertion Pred PrimitivesTriples SepTriples StateAssertion.

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
  
  Lemma length_spec (ptr: Pointer.t) (l: list memval) (s0: State ListStore list_heap_carrier) :
  {{ fun s => s = s0 /\ llist ptr l s }}
    length ptr (1%N)
  {{ fun res s' => res = N.of_nat (Datatypes.length l) /\ heap s' = heap s0 }}.
  
  Proof. Admitted.

  Definition is_empty (ptr: Pointer.t): program (State ListStore list_heap_carrier) bool :=
    eq_ptr ptr Pointer.NULL.

  Lemma is_empty_spec (ptr: Pointer.t) (s0 : State ListStore list_heap_carrier):
    {{ fun s => s = s0 /\ Facts.WValid (heap s) ptr /\ Pointer.Allows ptr Operation.Cmp}}
      is_empty ptr
    {{ fun res s' => Pointer.cmp ptr Pointer.NULL = Some res /\ s' = s0 }}.
  Proof.
    unfold is_empty.
    eapply sep_weaken.
    - apply sep_eq_ptr_triple.
    - intros s (-> & HWValid & HAllows).
      split. { exact HWValid. }
      split. { right. right. reflexivity. }
      split. { exact HAllows. }
      split. { constructor. }
      intros b' Hcmp. split; auto.
  Qed.

  Definition cons [MS: MemStorable] (ptr: Pointer.t) (n_ofst: N.t) (d_ofst: N.t) (v: MS): program (State ListStore list_heap_carrier) Pointer.t :=
    do new_node <- alloc_ptr 2 Pointer.NULL;
    do data_ptr <- new_node ~+> d_ofst;
    write_ptr data_ptr v ;;
    do next_ptr <- new_node ~+> n_ofst;
    write_ptr next_ptr ptr ;;
    ret new_node.

Lemma cons_spec [MS: MemStorable] (ptr: Pointer.t) (n_ofst d_ofst: N.t) (v: MS) (s0 : State ListStore list_heap_carrier):
  {{ fun s => s = s0 /\
              Facts.WValid (Primitives.heap s) ptr /\
              d_ofst <> n_ofst /\
              (d_ofst < 2)%N /\
              (n_ofst < 2)%N /\
              exists bid, GenId.get (list_heap_to_allocator (heap s)) = Some bid }}
    cons ptr n_ofst d_ofst v
  {{ fun new_node s' =>
     Primitives.store s' = Primitives.store s0 /\
     s' <> s0 /\
     exists hp_alloc data_ptr next_ptr hp_mut1,
       list_heap_alloc (heap s0) 2 (StorablePtr.ptr_encode Pointer.NULL) = Some (hp_alloc, new_node) /\
       Pointer.shift_fw new_node d_ofst = Some data_ptr /\
       list_heap_mutate hp_alloc data_ptr (encode v) = Some hp_mut1 /\
       Pointer.shift_fw new_node n_ofst = Some next_ptr /\
       list_heap_mutate hp_mut1 next_ptr (StorablePtr.ptr_encode ptr) = Some (heap s') }}.

 Proof.
    unfold cons.
    eapply sep_bind_rule with
      (Q := fun new_node s1 =>
        store s1 = store s0 /\
        exists ha,
          Heap.alloc (heap s0) 2 (encode Pointer.NULL) = Some (ha, new_node) /\
          heap s1 = ha /\
          Facts.WValid (heap s1) new_node /\
          (d_ofst < 2)%N /\ (n_ofst < 2)%N /\ d_ofst <> n_ofst).
    - intro new_node.
      eapply sep_bind_rule with
        (Q := fun data_ptr s2 =>
          store s2 = store s0 /\
          exists ha,
            Heap.alloc (heap s0) 2 (encode Pointer.NULL) = Some (ha, new_node) /\
            heap s2 = ha /\
            Facts.WValid (heap s2) new_node /\
            Pointer.shift_fw new_node d_ofst = Some data_ptr /\
            (d_ofst < 2)%N /\ (n_ofst < 2)%N /\ d_ofst <> n_ofst).
      + intro data_ptr.
        eapply sep_seq_rule with
          (Q := fun s3 =>
            store s3 = store s0 /\
            exists ha,
              Heap.alloc (heap s0) 2 (encode Pointer.NULL) = Some (ha, new_node) /\
              Pointer.shift_fw new_node d_ofst = Some data_ptr /\
              Heap.mutate ha data_ptr (encode v) = Some (heap s3) /\
              Facts.WValid (heap s3) new_node /\
              (d_ofst < 2)%N /\ (n_ofst < 2)%N /\ d_ofst <> n_ofst).
        * eapply sep_bind_rule with
            (Q := fun next_ptr s4 =>
              store s4 = store s0 /\
              exists ha,
                Heap.alloc (heap s0) 2 (encode Pointer.NULL) = Some (ha, new_node) /\
                Pointer.shift_fw new_node d_ofst = Some data_ptr /\
                Heap.mutate ha data_ptr (encode v) = Some (heap s4) /\
                Pointer.shift_fw new_node n_ofst = Some next_ptr /\
                (d_ofst < 2)%N /\ (n_ofst < 2)%N).
          -- intro next_ptr.
             eapply sep_seq_rule with
               (Q := fun s5 =>
                 store s5 = store s0 /\
                 heap s5 <> heap s0 /\
                 exists ha hm,
                   Heap.alloc (heap s0) 2 (encode Pointer.NULL) = Some (ha, new_node) /\
                   Pointer.shift_fw new_node d_ofst = Some data_ptr /\
                   Heap.mutate ha data_ptr (encode v) = Some hm /\
                   Pointer.shift_fw new_node n_ofst = Some next_ptr /\
                   Heap.mutate hm next_ptr (encode ptr) = Some (heap s5)).
             ++ eapply sep_weaken.
                ** apply sep_ret_triple.
                ** intros s [Hst [Hne [ha [hm [HA [HD [HM1 [HN HM2]]]]]]]].
                   refine (conj Hst (conj _ (ex_intro _ ha (ex_intro _ data_ptr
                     (ex_intro _ next_ptr (ex_intro _ hm _)))))).
                   { intro Heq; apply Hne; exact (f_equal heap Heq). }
                   exact (conj HA (conj HD (conj HM1 (conj HN HM2)))).
             ++ eapply sep_weaken.
                ** apply sep_write_ptr_triple.
                ** intros s [Hst [ha [HA [HD [HM1 [HN [Hd Hn]]]]]]].
                   destruct (alloc_mutate_mutate_succeeds_gen
                     (heap s0) 2 (encode Pointer.NULL)
                     ha new_node d_ofst data_ptr n_ofst next_ptr
                     (heap s) (encode v) (encode ptr)
                     HA Hd HD HM1 Hn HN) as [lh2 HM2].
                   exists lh2. split. exact HM2.
                   split. exact Hst.
                   split.
                   { exact (alloc_heap_neq_orig_gen
                       (heap s0) 2 _ ha new_node data_ptr next_ptr
                       (heap s) lh2 (encode v) (encode ptr) HA HM1 HM2). }
                   exists ha, (heap s).
                   exact (conj HA (conj HD (conj HM1 (conj HN HM2)))).
          -- eapply sep_weaken.
             ** apply sep_shift_fw_ptr_triple.
             ** intros s [Hst [ha [HA [HD [HM1 [HWV [Hd [Hn _]]]]]]]].
                split. exact HWV.
                destruct (alloc_shift_fw_succeeds_gen
                  (heap s0) 2 (encode Pointer.NULL) ha new_node n_ofst HA Hn) as [np HN].
                exists np. split. exact HN.
                split.
                { exact (alloc_shift_wvalid_after_mut_gen
                    (heap s0) 2 (encode Pointer.NULL)
                    ha new_node n_ofst np (heap s)
                    data_ptr (encode v) HA Hn HN HM1). }
                exact (conj Hst (ex_intro _ ha
                  (conj HA (conj HD (conj HM1 (conj HN (conj Hd Hn))))))).
        * eapply sep_weaken.
          -- apply sep_write_ptr_triple.
          -- intros s_wr [Hst_wr [ha_wr [HA_wr [Heq_wr [HWV_wr [HD_wr [Hd_wr [Hn_wr Hdiff_wr]]]]]]]].
             destruct (alloc_mutate_succeeds_gen
               (heap s0) 2 (encode Pointer.NULL) ha_wr new_node d_ofst data_ptr (encode v)
               HA_wr Hd_wr HD_wr) as [lh_mut HM1_mut].
             exists lh_mut. split.
             { rewrite Heq_wr. exact HM1_mut. }
             split.
             { exact Hst_wr. }
             exists ha_wr.
             refine (conj HA_wr (conj HD_wr (conj HM1_mut (conj _ _)))).
             ++ eapply alloc_wvalid_after_mut_gen; eauto. reflexivity.
             ++ exact (conj Hd_wr (conj Hn_wr Hdiff_wr)).
      + eapply sep_weaken.
        * apply sep_shift_fw_ptr_triple.
        * intros s [Hst [ha [HA [Heq [HWV [Hd [Hn Hdiff]]]]]]].
          split. exact HWV.
          destruct (alloc_shift_fw_succeeds_gen
            (heap s0) 2 (encode Pointer.NULL) ha new_node d_ofst HA Hd) as [dp Hsd].
          exists dp. split. exact Hsd.
          split.
          { rewrite Heq.
            exact (alloc_shift_wvalid_gen
                     (heap s0) 2 (encode Pointer.NULL) ha new_node d_ofst dp HA Hd Hsd). }
          exact (conj Hst (ex_intro _ ha
            (conj HA (conj Heq (conj HWV (conj Hsd (conj Hd (conj Hn Hdiff)))))))).
    - eapply sep_weaken.
      + apply sep_alloc_ptr_triple.
      + intros s [Heqs [_ [Hdiff [Hd [Hn [bid Hbid]]]]]].
        subst s.
        split.
        * destruct (heap s0) as [mbs b] eqn:Hh; destruct b.
          { eexists _, _; cbn; reflexivity. }
          { cbn in Hbid; discriminate. }
        * intros hp new_node_p HA_p.
          split. { reflexivity. }
          exists hp.
          refine (conj HA_p (conj eq_refl (conj _ _))).
          -- eapply alloc_wvalid_gen with (v := encode Pointer.NULL); eauto.
             reflexivity.
          -- exact (conj Hd (conj Hn Hdiff)).
  Qed.

  Definition tl (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t :=
      do next_ptr <- ptr ~+> n_ofst;
      read_ptr next_ptr.

  Lemma tl_spec (ptr next_ptr next_node: Pointer.t) (n_ofst: N.t) (s0 : State ListStore list_heap_carrier):
    {{ fun s => s = s0 /\ 
                Facts.WValid (Primitives.heap s) ptr /\ 
                Pointer.Allows ptr Operation.Read /\
                Pointer.shift_fw ptr n_ofst = Some next_ptr /\
                Facts.WValid (Primitives.heap s) next_ptr /\
                Pointer.Allows next_ptr Operation.Read /\
                Heap.lookup (Primitives.heap s) next_ptr = Some (encode next_node) }}
      tl ptr n_ofst
    {{ fun res s' => res = next_node /\ s' = s0 }}.

 Proof.
  unfold tl.
  eapply sep_bind_rule with
    (Q := fun np s1 =>
       np = next_ptr /\
       Heap.lookup (heap s1) next_ptr = Some (encode next_node) /\
       s1 = s0).
  - intro np.
    eapply sep_weaken.
    + apply sep_read_ptr_triple.
    + intros s (Hnp & Hlookup & ->).
      exists next_node. split.
      * rewrite Hnp. exact Hlookup.
      * split; reflexivity.
  - eapply sep_weaken.
    + apply sep_shift_fw_ptr_triple.
    + intros s (-> & Hptrv & _ & Hshift & Hnextv & _ & Hlookup).
      split. { exact Hptrv. }
      exists next_ptr. split. { exact Hshift. }
      split. { exact Hnextv. }
      split. { reflexivity. }
      split. { exact Hlookup. }
      reflexivity.
Qed.


  Definition nth (ptr: Pointer.t) (n_ofst: N.t) (nth: nat): program (State ListStore list_heap_carrier) Pointer.t :=
      do var (node: Pointer.t) <- ptr;
      do var (idx: nat) <- nth;
      while (do curr <- read_var node ; do c <- eq_ptr curr Pointer.NULL ; do i <- read_var idx ; ret ( andb (negb c) (Nat.ltb 0 i)))
        (
          do (nd: Pointer.t) <- read_var node ;
          do node_next_ptr <- nd ~+> n_ofst ;
          do (old_next: Pointer.t) <- read_ptr node_next_ptr ;
          write_var node old_next ;;
          do i <- read_var idx ;
          write_var idx (i - 1)
        );;
      read_var node.

  Lemma nth_spec (ptr: Pointer.t) (l: list memval) (k: nat) (s0: State ListStore list_heap_carrier) :
  {{ fun s => s = s0 /\ llist ptr l s }}
    nth ptr (1%N) k
  {{ fun res s' => llist res (List.skipn k l) s' /\ heap s' = heap s0 }}.

  Proof. Admitted.

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

  Lemma reverse_spec (ptr: Pointer.t) (l: list memval) (s0: State ListStore list_heap_carrier) :
  {{ fun s => s = s0 /\ llist ptr l s }}
    reverse ptr (1%N)
  {{ fun res s' => llist res (List.rev l) s' }}.

  Proof. Admitted.

  Definition append (l0 l1: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t :=
    do is_null <- eq_ptr l0 Pointer.NULL;
    if is_null then ret l1
    else
      do var (node: Pointer.t) <- l0;
      while
        (do (nd: Pointer.t) <- read_var node ;
         do next_ptr <- nd ~+> n_ofst ;
         do (nxt: Pointer.t) <- read_ptr next_ptr ;
         do c <- eq_ptr nxt Pointer.NULL ;
         ret (negb c))
        (do (nd: Pointer.t) <- read_var node ;
        do next_ptr <- nd ~+> n_ofst ;
        do (nxt: Pointer.t) <- read_ptr next_ptr ;
        write_var node nxt
        );;
      do last <- read_var node ;
      do last_next <- last ~+> n_ofst ;
      write_ptr last_next l1 ;;
      ret l0.

  Lemma append_spec (l0 l1: Pointer.t) (la lb: list memval) (s0: State ListStore list_heap_carrier) :
  {{ fun s => s = s0 /\ llist l0 la s /\ llist l1 lb s }}
    append l0 l1 (1%N)
  {{ fun res s' => llist res (la ++ lb) s' }}.

  Proof. Admitted.

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
    do len <- List.length ptr 1%N;
    do empty <- List.is_empty ptr ;
    do ptr_cons <- List.cons ptr 1%N 0%N 0;
    print_ll ptr_cons;;
    do ptr_tl <- List.tl ptr_cons 1%N;
    print_ll ptr_tl;;
    do ptr_nth <- List.nth ptr_cons 1%N 2;
    print_ll ptr_nth;;
    do ptr_rev <- List.reverse ptr_cons 1%N;
    print_ll ptr_rev;;
    do ptr_new <- allocate;
    do ptr_appended <- List.append ptr_rev ptr_new 1%N;
    print_ll ptr_appended;;
    ret 0.

End ListExample.
