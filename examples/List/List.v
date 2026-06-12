(*
GallinaC: Unifying Verification and Certified Compilation of System Programs in Rocq
Copyright (C) 2024-2026 Frédéric Fort
Copyright (C) 2026 Yasmine Boudour



This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.
*)




From Stdlib Require Import Lia NArith List.
From GallinaC Require Import Programming.
From GallinaC Require Import Frame GenAssertion Hoare InternalTriples ListAssertion Pred PrimitivesTriples SepTriples StateAssertion.
Import ListNotations.

Local Open Scope state_scope.
Local Open Scope separation_scope.

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
  
  Lemma length_spec (ptr: Pointer.t) (l: list memval) P
      (HWF: forall s, P s -> Store.WF (store s))
      (HPindep: indep_store P) :
  {{ P && llist ptr l }}
    length ptr (1%N)
  {{ fun res s' => res = N.of_nat (Datatypes.length l) /\ llist ptr l s' /\ P s' }}.

  Proof.
    unfold length.
    eapply sep_with_var_triple.
    intros s_init n_node st1 [HP Hllist] Hpush_node.
    pose proof (push_spec2 _ _ _ _ (HWF s_init HP) Hpush_node) as Hbn1.
    pose proof (push_wf _ _ _ _ (HWF s_init HP) Hpush_node) as HWF1.
    pose proof (llist_reach_of_llist ptr l s_init Hllist) as Hreach0.
    eapply sep_with_var_triple.
    intros s1 n_count st2 -> Hpush_count.
    pose proof (push_spec2 _ _ _ _ HWF1 Hpush_count) as Hbc2.
    pose proof (push_spec_preserve _ _ _ _ _ _ HWF1 Hpush_count Hbn1) as Hbn2.
    pose proof (fun v' => push_spec1 _ _ _ _ v' HWF1 Hpush_count) as Hfresh.
    assert (Hn_ne : n_node <> n_count) by
      (intro Heq; subst; exact (Hfresh _ Hbn1)).
    pose (Iw := fun (b : bool) (s : State ListStore list_heap_carrier) =>
      heap s = heap s_init /\
      exists (curr : Pointer.t) (l_rem : list memval) (k : N.t),
        llist_reach (heap s_init) curr l_rem /\
        BindsTo n_node (encode curr) (store s) /\
        BindsTo n_count (encode k) (store s) /\
        (k + N.of_nat (Datatypes.length l_rem))%N = N.of_nat (Datatypes.length l) /\
        match b with true => ~ (l_rem = nil) | false => l_rem = nil end).
    eapply sep_seq_rule with (Q := fun s => Iw false s).
    - eapply sep_weaken.
      + apply sep_read_var_triple.
      + intros s HIw.
        destruct HIw as [Hheap [curr [l_rem [k [_ [Hbn_s [Hbc_s [Hinv Hnil]]]]]]]].
        cbn in Hnil; subst l_rem.
        cbn in Hinv; rewrite N.add_0_r in Hinv.
        exists k.
        split. exact Hbc_s.
        destruct (pop_pop_fwd (store s) n_count (encode k) n_node (encode curr)
          (fun H => Hn_ne (eq_sym H)) Hbc_s Hbn_s) as [t1 [t2 [Hp1 Hp2]]].
        exists t1. split. exact Hp1.
        exists t2. split. exact Hp2.
        exact (conj Hinv (conj (llist_indep_regs ptr l s_init {|store := t2; heap := heap s|} (eq_sym Hheap) Hllist) (HPindep s_init {|store := t2; heap := heap s|} (eq_sym Hheap) HP))).
    - eapply sep_weaken.
      + apply sep_while_rule with (I := Iw).
        * eapply sep_bind_rule with
            (Q := fun cv s =>
              heap s = heap s_init /\
              exists (lr : list memval) (k : N.t),
                llist_reach (heap s_init) cv lr /\
                BindsTo n_node (encode cv) (store s) /\
                BindsTo n_count (encode k) (store s) /\
                (k + N.of_nat (Datatypes.length lr))%N = N.of_nat (Datatypes.length l)).
          -- intro cv.
             eapply sep_bind_rule with (Q := fun c s => Iw (negb c) s).
             ++ intro c. apply sep_ret_triple.
             ++ eapply sep_weaken.
                ** apply sep_eq_ptr_triple_cmp.
                ** intros s [Hheap [lr [k [Hreach_cv [Hbn_s [Hbc_s Hinv]]]]]].
                   destruct lr as [ | vh lr'].
                   --- cbn in Hreach_cv; subst cv.
                       split. right; right; reflexivity.
                       split. right; right; reflexivity.
                       split. exact Pointer.AllowsNull.
                       split. exact Pointer.AllowsNull.
                       intros c Hcmp.
                       cbn in Hcmp; inversion Hcmp; subst.
                       cbn. unfold Iw.
                       split. exact Hheap.
                       exists Pointer.NULL; exists (@nil memval); exists k.
                       split. cbn; reflexivity.
                       split. exact Hbn_s.
                       split. exact Hbc_s.
                       split. exact Hinv.
                       exact eq_refl.
                   --- destruct Hreach_cv as
                           [HNN [HWV [HCmp_cv [HRd_cv [addr_cv [np_cv [next_cv
                             [HRef_cv [Hshift_cv [HWVnp [HRdnp [HWrite_cv [Hlookup_cv Htail_cv]]]]]]]]]]]]].
                       split. rewrite Hheap; exact HWV.
                       split. right; right; reflexivity.
                       split. exact HCmp_cv.
                       split. exact Pointer.AllowsNull.
                       intros c Hcmp.
                       assert (Hallow : Pointer.allows cv Operation.Cmp = true).
                       { destruct (Pointer.allows_spec cv Operation.Cmp);
                         [reflexivity | contradiction]. }
                       unfold Pointer.cmp in Hcmp.
                       rewrite Hallow in Hcmp; cbn in Hcmp.
                       inversion Hcmp; subst.
                       assert (Hceqb : Pointer.eqb cv Pointer.NULL = false).
                       { apply Pointer.eqb_neq; exact HNN. }
                       rewrite Hceqb; cbn.
                       unfold Iw.
                       split. exact Hheap.
                       exists cv; exists (@cons memval vh lr'); exists k.
                       split.
                       { exact (conj HNN (conj HWV (conj HCmp_cv (conj HRd_cv
                           (ex_intro _ addr_cv (ex_intro _ np_cv (ex_intro _ next_cv
                             (conj HRef_cv (conj Hshift_cv (conj HWVnp
                               (conj HRdnp (conj HWrite_cv (conj Hlookup_cv Htail_cv))))))))))))). }
                       split. exact Hbn_s.
                       split. exact Hbc_s.
                       split. exact Hinv.
                       discriminate.
          -- eapply sep_weaken.
             ++ apply sep_read_var_triple.
             ++ intros s [b HIw].
                destruct HIw as [Hheap [curr [lr [k [Hreach_s [Hbn_s [Hbc_s [Hinv _]]]]]]]].
                exists curr.
                split. exact Hbn_s.
                split. exact Hheap.
                exact (ex_intro _ lr (ex_intro _ k
                  (conj Hreach_s (conj Hbn_s (conj Hbc_s Hinv))))).
        * eapply sep_bind_rule with (Q := fun nd s => heap s = heap s_init /\
              exists (lr' : list memval) (vh : memval) (k : N.t),
                llist_reach (heap s_init) nd (vh :: lr') /\
                BindsTo n_node (encode nd) (store s) /\
                BindsTo n_count (encode k) (store s) /\
                (k + N.of_nat (S (Datatypes.length lr')))%N = N.of_nat (Datatypes.length l)).
          -- intro nd.
             eapply sep_bind_rule with
               (Q := fun np s =>
                 heap s = heap s_init /\
                 exists (lr' : list memval) (k : N.t) (next_v : Pointer.t),
                   Pointer.shift_fw nd 1%N = Some np /\
                   Heap.lookup (heap s_init) np = Some (encode next_v) /\
                   llist_reach (heap s_init) next_v lr' /\
                   BindsTo n_node (encode nd) (store s) /\
                   BindsTo n_count (encode k) (store s) /\
                   (k + N.of_nat (S (Datatypes.length lr')))%N = N.of_nat (Datatypes.length l)).
             ++ intro np.
                eapply sep_bind_rule with
                  (Q := fun nxt s =>
                    heap s = heap s_init /\
                    exists (lr' : list memval) (k : N.t),
                      llist_reach (heap s_init) nxt lr' /\
                      BindsTo n_node (encode nd) (store s) /\
                      BindsTo n_count (encode k) (store s) /\
                      (k + N.of_nat (S (Datatypes.length lr')))%N = N.of_nat (Datatypes.length l)).
                ** intro nxt.
                   eapply sep_bind_rule with
                     (Q := fun _ s =>
                       heap s = heap s_init /\
                       exists (lr' : list memval) (k : N.t),
                         llist_reach (heap s_init) nxt lr' /\
                         BindsTo n_node (encode nxt) (store s) /\
                         BindsTo n_count (encode k) (store s) /\
                         (k + N.of_nat (S (Datatypes.length lr')))%N = N.of_nat (Datatypes.length l)).
                   --- intro .
                       eapply sep_bind_rule with
                         (Q := fun (c : N.t) s =>
                           heap s = heap s_init /\
                           exists (lr' : list memval),
                             llist_reach (heap s_init) nxt lr' /\
                             BindsTo n_node (encode nxt) (store s) /\
                             BindsTo n_count (encode c) (store s) /\
                             (c + N.of_nat (S (Datatypes.length lr')))%N = N.of_nat (Datatypes.length l)).
                       +++ intro c.
                           eapply sep_weaken.
                           *** apply sep_write_var_triple.
                           *** intros s [Hheap [lr' [Hreach_n [Hbn_s [Hbc_s Hinv]]]]].
                               exists (encode c).
                               split. exact Hbc_s.
                               destruct lr' as [ | v' lr''].
                               ---- cbn in Hreach_n.
                                    exists false. unfold Iw.
                                    split. exact Hheap.
                                    exists nxt; exists (@nil memval); exists (c + 1)%N.
                                    split. cbn; exact Hreach_n.
                                    split.
                                    { apply Store.Facts.mutate_unchecked_spec_lr.
                                      intro H; exact (Hn_ne H).
                                      exact Hbn_s. }
                                    split.
                                    { apply Store.Facts.mutate_unchecked_spec_ll;
                                      reflexivity. }
                                    split.
                                    { cbn in Hinv; rewrite N.add_0_r; lia. }
                                    exact eq_refl.
                               ---- exists true. unfold Iw.
                                    split. exact Hheap.
                                    exists nxt; exists (@cons memval v' lr''); exists (c + 1)%N.
                                    split. exact Hreach_n.
                                    split.
                                    { apply Store.Facts.mutate_unchecked_spec_lr.
                                      intro H; exact (Hn_ne H).
                                      exact Hbn_s. }
                                    split.
                                    { apply Store.Facts.mutate_unchecked_spec_ll;
                                      reflexivity. }
                                    split. lia.
                                    intro H; discriminate.
                       +++ eapply sep_weaken.
                           *** apply sep_read_var_triple.
                           *** intros s [Hheap [lr' [k [Hreach_n [Hbn_s [Hbc_s Hinv]]]]]].
                               exists k.
                               split. exact Hbc_s.
                               exact (conj Hheap (ex_intro _ lr'
                                 (conj Hreach_n (conj Hbn_s (conj Hbc_s Hinv))))).
                   --- eapply sep_weaken.
                       +++ apply sep_write_var_triple.
                       +++ intros s [Hheap [lr' [k [Hreach_n [Hbn_s [Hbc_s Hinv]]]]]].
                           exists (encode nd).
                           split. exact Hbn_s.
                           split. exact Hheap.
                           exists lr', k.
                           split. exact Hreach_n.
                           split.
                           { apply Store.Facts.mutate_unchecked_spec_ll; reflexivity. }
                           split.
                           { apply Store.Facts.mutate_unchecked_spec_lr.
                             intro H; exact (Hn_ne (eq_sym H)).
                             exact Hbc_s. }
                           exact Hinv.
                ** eapply sep_weaken.
                   --- apply sep_read_ptr_triple.
                   --- intros s [Hheap [lr' [k [next_v [Hshift [Hlookup [Hreach_np [Hbn_s [Hbc_s Hinv]]]]]]]]].
                       exists next_v.
                       split. rewrite Hheap; exact Hlookup.
                       exact (conj Hheap (ex_intro _ lr' (ex_intro _ k
                         (conj Hreach_np (conj Hbn_s (conj Hbc_s Hinv)))))).
             ++ eapply sep_weaken.
                ** apply sep_shift_fw_ptr_triple.
                ** intros s [Hheap [lr' [vh [k [Hreach_nd [Hbn_s [Hbc_s Hinv]]]]]]].
                   destruct Hreach_nd as
                       [HNN [HWV [HCmp [HRd [addr_nd [np_nd [next_nd
                         [HRef [Hshift [HWVnp [HRdnp [HWrite_nd [Hlookup Htail]]]]]]]]]]]]].
                   split. rewrite Hheap; exact HWV.
                   exists np_nd.
                   split. exact Hshift.
                   split. rewrite Hheap; exact HWVnp.
                   split. exact Hheap.
                   exists lr'; exists k; exists next_nd.
                   split. exact Hshift.
                   split. exact Hlookup.
                   split. exact Htail.
                   split. exact Hbn_s.
                   split. exact Hbc_s.
                   exact Hinv.
          -- eapply sep_weaken.
             ++ apply sep_read_var_triple.
             ++ intros s [Hheap [curr [lr [k [Hreach_s [Hbn_s [Hbc_s [Hinv Hlr_ne]]]]]]]].
                cbn in Hlr_ne.
                destruct lr as [ | vh lr'].
                ** exact (False_rect _ (Hlr_ne eq_refl)).
                ** exists curr.
                   split. exact Hbn_s.
                   split. exact Hheap.
                   exists lr'; exists vh; exists k.
                   split. exact Hreach_s.
                   split. exact Hbn_s.
                   split. exact Hbc_s.
                   exact Hinv.
      + intros s ->.
        destruct l as [ | vh l'].
        * cbn in Hreach0.
          exists false. unfold Iw. cbn.
          split. reflexivity.
          exists ptr; exists (@nil memval); exists 0%N.
          split. cbn; exact Hreach0.
          split. exact Hbn2.
          split. exact Hbc2.
          split. cbn; lia.
          exact eq_refl.
        * exists true. unfold Iw. cbn.
          split. reflexivity.
          exists ptr; exists (@cons memval vh l'); exists 0%N.
          split. exact Hreach0.
          split. exact Hbn2.
          split. exact Hbc2.
          split. cbn; lia.
          intro H; discriminate.
  Qed.

  Definition is_empty (ptr: Pointer.t): program (State ListStore list_heap_carrier) bool :=
    eq_ptr ptr Pointer.NULL.

  Lemma is_empty_spec (ptr: Pointer.t) P (Q: bool -> Pred _):
    {{ P && (fun s => forall b, Q b s) && fun s => Facts.WValid (heap s) ptr /\ Pointer.Allows ptr Operation.Cmp}}
      is_empty ptr
    {{ fun res => P && Q res }}.
  Proof.
    unfold is_empty.
    eapply sep_weaken.
    - apply sep_eq_ptr_triple.
    - intros s ((HP & HQ) & VALID & ALLOWS).
      split; [ assumption | ].
      split; [ now repeat constructor | ].
      split; [ assumption | ].
      split; [ now constructor | ].
      intros b'. split; auto.
  Qed.

  Definition cons [MS: MemStorable] (ptr: Pointer.t) (n_ofst: N.t) (d_ofst: N.t) (v: MS): program (State ListStore list_heap_carrier) Pointer.t :=
    do new_node <- alloc_ptr 2 Pointer.NULL;
    do data_ptr <- new_node ~+> d_ofst;
    write_ptr data_ptr v ;;
    do next_ptr <- new_node ~+> n_ofst;
    write_ptr next_ptr ptr ;;
    ret new_node.

Lemma cons_spec [MS: MemStorable] (ptr: Pointer.t) (n_ofst d_ofst: N.t) (v: MS)
    (Q: Pointer.t -> Pred _):
  {{ fun s =>
       Facts.WValid (Primitives.heap s) ptr /\
       d_ofst <> n_ofst /\
       (d_ofst < 2)%N /\
       (n_ofst < 2)%N /\
       (exists bid, GenId.get (list_heap_to_allocator (heap s)) = Some bid) /\
       forall new_node hp_alloc data_ptr next_ptr hp_mut1 hp_final,
         list_heap_alloc (heap s) 2 (StorablePtr.ptr_encode Pointer.NULL) = Some (hp_alloc, new_node) ->
         Pointer.shift_fw new_node d_ofst = Some data_ptr ->
         list_heap_mutate hp_alloc data_ptr (encode v) = Some hp_mut1 ->
         Pointer.shift_fw new_node n_ofst = Some next_ptr ->
         list_heap_mutate hp_mut1 next_ptr (StorablePtr.ptr_encode ptr) = Some hp_final ->
         Q new_node {| store := Primitives.store s; heap := hp_final |} }}
    cons ptr n_ofst d_ofst v
  {{ Q }}.

  Proof.
    unfold cons.
    eapply sep_bind_rule with
      (Q := fun new_node s1 =>
        exists h0 ha,
          Heap.alloc h0 2 (encode Pointer.NULL) = Some (ha, new_node) /\
          heap s1 = ha /\
          Facts.WValid (heap s1) new_node /\
          (d_ofst < 2)%N /\ (n_ofst < 2)%N /\ d_ofst <> n_ofst /\
          (forall dp np hm1 hf,
            Pointer.shift_fw new_node d_ofst = Some dp ->
            list_heap_mutate ha dp (encode v) = Some hm1 ->
            Pointer.shift_fw new_node n_ofst = Some np ->
            list_heap_mutate hm1 np (StorablePtr.ptr_encode ptr) = Some hf ->
            Q new_node {|store := store s1; heap := hf|})).
    - intro new_node.
      eapply sep_bind_rule with
        (Q := fun data_ptr s2 =>
          exists h0 ha,
            Heap.alloc h0 2 (encode Pointer.NULL) = Some (ha, new_node) /\
            heap s2 = ha /\
            Facts.WValid (heap s2) new_node /\
            Pointer.shift_fw new_node d_ofst = Some data_ptr /\
            (d_ofst < 2)%N /\ (n_ofst < 2)%N /\ d_ofst <> n_ofst /\
            (forall np hm1 hf,
              list_heap_mutate ha data_ptr (encode v) = Some hm1 ->
              Pointer.shift_fw new_node n_ofst = Some np ->
              list_heap_mutate hm1 np (StorablePtr.ptr_encode ptr) = Some hf ->
              Q new_node {|store := store s2; heap := hf|})).
      + intro data_ptr.
        eapply sep_seq_rule with
          (Q := fun s3 =>
            exists h0 ha hm1,
              Heap.alloc h0 2 (encode Pointer.NULL) = Some (ha, new_node) /\
              Pointer.shift_fw new_node d_ofst = Some data_ptr /\
              Heap.mutate ha data_ptr (encode v) = Some hm1 /\
              heap s3 = hm1 /\
              Facts.WValid (heap s3) new_node /\
              (d_ofst < 2)%N /\ (n_ofst < 2)%N /\ d_ofst <> n_ofst /\
              (forall np hf,
                Pointer.shift_fw new_node n_ofst = Some np ->
                list_heap_mutate hm1 np (StorablePtr.ptr_encode ptr) = Some hf ->
                Q new_node {|store := store s3; heap := hf|})).
        * eapply sep_bind_rule with
            (Q := fun next_ptr s4 =>
              exists h0 ha hm1,
                Heap.alloc h0 2 (encode Pointer.NULL) = Some (ha, new_node) /\
                Pointer.shift_fw new_node d_ofst = Some data_ptr /\
                Heap.mutate ha data_ptr (encode v) = Some hm1 /\
                heap s4 = hm1 /\
                Pointer.shift_fw new_node n_ofst = Some next_ptr /\
                (d_ofst < 2)%N /\ (n_ofst < 2)%N /\
                (forall hf,
                  list_heap_mutate hm1 next_ptr (StorablePtr.ptr_encode ptr) = Some hf ->
                  Q new_node {|store := store s4; heap := hf|})).
          -- intro next_ptr.
             eapply sep_seq_rule with (Q := fun s5 => Q new_node s5).
             ++ apply sep_ret_triple.
             ++ eapply sep_weaken.
                ** apply sep_write_ptr_triple.
                ** intros s [h0 [ha [hm1 [HA [HD [HM1 [Heq [HN [Hd [Hn HQpart]]]]]]]]]].
                   destruct (alloc_mutate_mutate_succeeds_gen
                     h0 2 (encode Pointer.NULL) ha new_node
                     d_ofst data_ptr n_ofst next_ptr hm1
                     (encode v) (encode ptr)
                     HA Hd HD HM1 Hn HN) as [lh2 HM2].
                   exists lh2. split.
                   { rewrite Heq. exact HM2. }
                   exact (HQpart lh2 HM2).
          -- eapply sep_weaken.
             ++ apply sep_shift_fw_ptr_triple.
             ++ intros s [h0 [ha [hm1 [HA [HD [HM1 [Heq [HWV [Hd [Hn [Hdiff HQpart]]]]]]]]]]].
                split. { exact HWV. }
                destruct (alloc_shift_fw_succeeds_gen
                  h0 2 (encode Pointer.NULL) ha new_node n_ofst HA Hn) as [np HN].
                exists np. split. { exact HN. }
                split.
                { rewrite Heq.
                  exact (alloc_shift_wvalid_after_mut_gen
                    h0 2 (encode Pointer.NULL)
                    ha new_node n_ofst np hm1
                    data_ptr (encode v) HA Hn HN HM1). }
                exists h0, ha, hm1.
                refine (conj HA (conj HD (conj HM1 (conj Heq (conj HN (conj Hd (conj Hn _))))))).
                intros hf HM2.
                exact (HQpart np hf HN HM2).
        * eapply sep_weaken.
          -- apply sep_write_ptr_triple.
          -- intros s [h0 [ha [HA [Heq [HWV [HD [Hd [Hn [Hdiff HQpart]]]]]]]]].
             destruct (alloc_mutate_succeeds_gen
               h0 2 (encode Pointer.NULL) ha new_node d_ofst data_ptr (encode v)
               HA Hd HD) as [hm1 HM1].
             exists hm1. split.
             { rewrite Heq. exact HM1. }
             exists h0, ha, hm1.
             refine (conj HA (conj HD (conj HM1 (conj eq_refl (conj _ (conj Hd (conj Hn (conj Hdiff _)))))))).
             ++ eapply alloc_wvalid_after_mut_gen; [exact HA | reflexivity | exact HM1].
             ++ intros np hf HN HM2.
                exact (HQpart np hm1 hf HM1 HN HM2).
      + eapply sep_weaken.
        * apply sep_shift_fw_ptr_triple.
        * intros s [h0 [ha [HA [Heq [HWV [Hd [Hn [Hdiff HQpart]]]]]]]].
          split. { exact HWV. }
          destruct (alloc_shift_fw_succeeds_gen
            h0 2 (encode Pointer.NULL) ha new_node d_ofst HA Hd) as [dp Hsd].
          exists dp. split. { exact Hsd. }
          split.
          { rewrite Heq.
            exact (alloc_shift_wvalid_gen h0 2 (encode Pointer.NULL) ha new_node d_ofst dp HA Hd Hsd). }
          exists h0, ha.
          refine (conj HA (conj Heq (conj HWV (conj Hsd (conj Hd (conj Hn (conj Hdiff _))))))).
          intros np hm1 hf HM1 HN HM2.
          exact (HQpart dp np hm1 hf Hsd HM1 HN HM2).
    - eapply sep_weaken.
      + apply sep_alloc_ptr_triple.
      + intros s (Hvalid & Hdiff & Hd & Hn & [bid Hbid] & HQ).
        split.
        * destruct (heap s) as [mbs b] eqn:Hh; destruct b.
          { eexists _, _; cbn; reflexivity. }
          { cbn in Hbid; discriminate. }
        * intros ha new_node_p HA_p.
          exists (heap s), ha.
          refine (conj HA_p (conj eq_refl (conj _ (conj Hd (conj Hn (conj Hdiff _)))))).
          -- eapply alloc_wvalid_gen; [exact HA_p | reflexivity].
          -- intros dp np hm1 hf HD_p HM1_p HN_p HM2_p.
             exact (HQ new_node_p ha dp np hm1 hf HA_p HD_p HM1_p HN_p HM2_p).
  Qed.

  Definition tl (ptr: Pointer.t) (n_ofst: N.t): program (State ListStore list_heap_carrier) Pointer.t :=
      do next_ptr <- ptr ~+> n_ofst;
      read_ptr next_ptr.

  Lemma tl_spec (ptr next_ptr next_node: Pointer.t) (n_ofst: N.t) P (Q: Pointer.t -> Pred _):
    {{ P && (fun s => Q next_node s) && fun s =>
         Facts.WValid (Primitives.heap s) ptr /\
         Pointer.Allows ptr Operation.Read /\
         Pointer.shift_fw ptr n_ofst = Some next_ptr /\
         Facts.WValid (Primitives.heap s) next_ptr /\
         Pointer.Allows next_ptr Operation.Read /\
         Heap.lookup (Primitives.heap s) next_ptr = Some (encode next_node) }}
      tl ptr n_ofst
    {{ fun res => P && Q res }}.

 Proof.
  unfold tl.
  eapply sep_bind_rule with
    (Q := fun np s1 =>
       np = next_ptr /\
       Heap.lookup (heap s1) next_ptr = Some (encode next_node) /\
       P s1 /\ Q next_node s1).
  - intro np.
    eapply sep_weaken.
    + apply sep_read_ptr_triple.
    + intros s (Hnp & Hlookup & HP & HQn).
      exists next_node. split.
      * rewrite Hnp. exact Hlookup.
      * split. exact HP. exact HQn.
  - eapply sep_weaken.
    + apply sep_shift_fw_ptr_triple.
    + intros s ((HP & HQn) & Hptrv & _ & Hshift & Hnextv & _ & Hlookup).
      split. { exact Hptrv. }
      exists next_ptr. split. { exact Hshift. }
      split. { exact Hnextv. }
      split. { reflexivity. }
      split. { exact Hlookup. }
      split. { exact HP. }
      exact HQn.
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

  Lemma nth_spec (ptr: Pointer.t) (l: list memval) (k: nat) P
      (HWF: forall s, P s -> Store.WF (store s))
      (HPindep: indep_store P) :
  {{ P && llist ptr l }}
    nth ptr (1%N) k
  {{ fun res s' => llist_reach (heap s') res (List.skipn k l) /\ llist ptr l s' /\ P s' }}.

  Proof.
    unfold nth.
    eapply sep_with_var_triple.
    intros s_init n_node st1 [HP Hllist] Hpush_node.
    pose proof (push_spec2 _ _ _ _ (HWF s_init HP) Hpush_node) as Hbn1.
    pose proof (push_wf _ _ _ _ (HWF s_init HP) Hpush_node) as HWF1.
    pose proof (llist_reach_of_llist ptr l s_init Hllist) as Hreach0.
    eapply sep_with_var_triple.
    intros s1 n_idx st2 -> Hpush_idx.
    pose proof (push_spec2 _ _ _ _ HWF1 Hpush_idx) as Hbi2.
    pose proof (push_wf _ _ _ _ HWF1 Hpush_idx) as HWF2.
    pose proof (push_spec_preserve _ _ _ _ _ _ HWF1 Hpush_idx Hbn1) as Hbn2.
    pose proof (fun v' => push_spec1 _ _ _ _ v' HWF1 Hpush_idx) as Hfresh.
    assert (Hn_ne : n_node <> n_idx) by
      (intro Heq; subst; exact (Hfresh _ Hbn1)).
    pose (Iw := fun (b : bool) (s : State ListStore list_heap_carrier) =>
      heap s = heap s_init /\
      exists (curr : Pointer.t) (l_rem : list memval) (k_rem : nat),
        llist_reach (heap s_init) curr l_rem /\
        BindsTo n_node (encode curr) (store s) /\
        BindsTo n_idx  (encode k_rem) (store s) /\
        Nat.le k_rem k /\
        l_rem = List.skipn (k - k_rem) l /\
        match b with
        | true  => curr <> Pointer.NULL /\ 0 < k_rem
        | false => curr = Pointer.NULL  \/ k_rem = 0
        end).
    eapply sep_seq_rule with (Q := fun s => Iw false s).
    - eapply sep_weaken.
      + apply sep_read_var_triple.
      + intros s [Hheap [curr [l_rem [k_rem [Hreach [Hbn_s [Hbi_s [Hle [Hlrem Hterm]]]]]]]]].
        exists curr.
        split. exact Hbn_s.
        destruct (pop_pop_fwd (store s) n_node (encode curr) n_idx (encode k_rem)
          Hn_ne Hbn_s Hbi_s) as [t1 [t2 [Hp1 Hp2]]].
        exists t1. split. exact Hp1.
        exists t2. split. exact Hp2.
        destruct Hterm as [Hnull | Hzero].
        * subst curr.
          assert (Hlnil : l_rem = [])
            by exact (proj1 (llist_reach_null_iff (heap s_init) Pointer.NULL l_rem Hreach) eq_refl).
          subst l_rem.
          assert (Hskipk : List.skipn k l = []).
          { replace k with (k_rem + (k - k_rem)) by lia.
            rewrite <- List.skipn_skipn.
            rewrite Hlnil.
            apply List.skipn_nil. }
          split.
          -- rewrite Hheap, Hskipk. cbn. reflexivity.
          -- split.
             ++ exact (llist_indep_regs ptr l s_init {|store := t2; heap := heap s|} (eq_sym Hheap) Hllist).
             ++ exact (HPindep s_init {|store := t2; heap := heap s|} (eq_sym Hheap) HP).
        * subst k_rem.
          rewrite Nat.sub_0_r in Hlrem. subst l_rem.
          split.
          -- rewrite Hheap. exact Hreach.
          -- split.
             ++ exact (llist_indep_regs ptr l s_init {|store := t2; heap := heap s|} (eq_sym Hheap) Hllist).
             ++ exact (HPindep s_init {|store := t2; heap := heap s|} (eq_sym Hheap) HP).
    - eapply sep_weaken.
      + apply sep_while_rule with (I := Iw).
        * eapply sep_bind_rule with
            (Q := fun (cv : Pointer.t) s =>
              heap s = heap s_init /\
              exists (l_rem : list memval) (k_rem : nat),
                llist_reach (heap s_init) cv l_rem /\
                BindsTo n_node (encode cv) (store s) /\
                BindsTo n_idx  (encode k_rem) (store s) /\
                Nat.le k_rem k /\
                l_rem = List.skipn (k - k_rem) l).
          -- intro cv.
             eapply sep_bind_rule with
               (Q := fun (c : bool) s =>
                 heap s = heap s_init /\
                 BindsTo n_node (encode cv) (store s) /\
                 exists (l_rem : list memval) (k_rem : nat),
                   llist_reach (heap s_init) cv l_rem /\
                   BindsTo n_idx (encode k_rem) (store s) /\
                   Nat.le k_rem k /\
                   l_rem = List.skipn (k - k_rem) l /\
                   ((c = true /\ cv = Pointer.NULL) \/ (c = false /\ cv <> Pointer.NULL))).
             ++ intro c.
                eapply sep_bind_rule with
                  (Q := fun (i : nat) s => Iw (andb (negb c) (Nat.ltb 0 i)) s).
                ** intro i. apply sep_ret_triple.
                ** eapply sep_weaken.
                   --- apply sep_read_var_triple.
                   --- intros s [Hheap [Hbn_s [l_rem [k_rem [Hreach [Hbi_s [Hle [Hlrem Hcase]]]]]]]].
                       exists k_rem. split. exact Hbi_s.
                       unfold Iw.
                       split. exact Hheap.
                       exists cv, l_rem, k_rem.
                       refine (conj Hreach (conj Hbn_s (conj Hbi_s (conj Hle (conj Hlrem _))))).
                       destruct Hcase as [[-> ->] | [-> Hcvnn]].
                       { cbn. left. reflexivity. }
                       { cbn.
                         destruct k_rem as [ | k_rem']; cbn.
                         - right. reflexivity.
                         - split.
                           + exact Hcvnn.
                           + apply Nat.lt_0_succ. }
             ++ eapply sep_weaken.
                ** apply sep_eq_ptr_triple_cmp.
                ** intros s [Hheap [l_rem [k_rem [Hreach [Hbn_s [Hbi_s [Hle Hlrem]]]]]]].
                   destruct l_rem as [ | vh l_rem'].
                   { cbn in Hreach. subst cv.
                     split. right; right; reflexivity.
                     split. right; right; reflexivity.
                     split. exact Pointer.AllowsNull.
                     split. exact Pointer.AllowsNull.
                     intros c Hcmp.
                     cbn in Hcmp. inversion Hcmp; subst c.
                     split. exact Hheap.
                     split. exact Hbn_s.
                     exists (@nil memval), k_rem.
                     split. cbn. reflexivity.
                     split. exact Hbi_s.
                     split. exact Hle.
                     split. exact Hlrem.
                     left. split; reflexivity. }
                   { destruct Hreach as
                         [HNN [HWV [HCmp [HRd [addr [np [nxt [HRef [Hshift [HWVnp [HRdnp [HWrite_np [Hlookup Htail]]]]]]]]]]]]].
                     split. rewrite Hheap. exact HWV.
                     split. right; right; reflexivity.
                     split. exact HCmp.
                     split. exact Pointer.AllowsNull.
                     intros c Hcmp.
                     assert (Hallow : Pointer.allows cv Operation.Cmp = true).
                     { destruct (Pointer.allows_spec cv Operation.Cmp); [reflexivity | contradiction]. }
                     unfold Pointer.cmp in Hcmp.
                     rewrite Hallow in Hcmp. cbn in Hcmp.
                     inversion Hcmp; subst c.
                     assert (Hceqb : Pointer.eqb cv Pointer.NULL = false).
                     { apply Pointer.eqb_neq. exact HNN. }
                     split. exact Hheap.
                     split. exact Hbn_s.
                     exists (vh :: l_rem'), k_rem.
                     split.
                     { exact (conj HNN (conj HWV (conj HCmp (conj HRd
                         (ex_intro _ addr (ex_intro _ np (ex_intro _ nxt
                           (conj HRef (conj Hshift (conj HWVnp (conj HRdnp (conj HWrite_np (conj Hlookup Htail))))))))))))). }
                     split. exact Hbi_s.
                     split. exact Hle.
                     split. exact Hlrem.
                     right. exact (conj Hceqb HNN). }
          -- eapply sep_weaken.
             ++ apply sep_read_var_triple.
             ++ intros s [b [Hheap [curr [l_rem [k_rem [Hreach [Hbn_s [Hbi_s [Hle [Hlrem _]]]]]]]]]].
                exists curr. split. exact Hbn_s.
                exact (conj Hheap (ex_intro _ l_rem (ex_intro _ k_rem
                  (conj Hreach (conj Hbn_s (conj Hbi_s (conj Hle Hlrem))))))).
        * eapply sep_bind_rule with
            (Q := fun (nd : Pointer.t) s =>
              heap s = heap s_init /\
              exists (l_rem : list memval) (k_rem : nat),
                llist_reach (heap s_init) nd l_rem /\
                BindsTo n_node (encode nd) (store s) /\
                BindsTo n_idx  (encode k_rem) (store s) /\
                Nat.le k_rem k /\
                l_rem = List.skipn (k - k_rem) l /\
                nd <> Pointer.NULL /\
                0 < k_rem).
          -- intro nd.
             eapply sep_bind_rule with
               (Q := fun (np : Pointer.t) s =>
                 heap s = heap s_init /\
                 exists (l_rem' : list memval) (k_rem : nat) (old_nxt : Pointer.t),
                   Pointer.shift_fw nd 1%N = Some np /\
                   Heap.lookup (heap s_init) np = Some (encode old_nxt) /\
                   llist_reach (heap s_init) old_nxt l_rem' /\
                   BindsTo n_node (encode nd) (store s) /\
                   BindsTo n_idx  (encode k_rem) (store s) /\
                   0 < k_rem /\ Nat.le k_rem k /\
                   l_rem' = List.skipn (k - (k_rem - 1)) l).
             ++ intro np.
                eapply sep_bind_rule with
                  (Q := fun (old_nxt : Pointer.t) s =>
                    heap s = heap s_init /\
                    exists (l_rem' : list memval) (k_rem : nat),
                      llist_reach (heap s_init) old_nxt l_rem' /\
                      BindsTo n_node (encode nd) (store s) /\
                      BindsTo n_idx  (encode k_rem) (store s) /\
                      0 < k_rem /\ Nat.le k_rem k /\
                      l_rem' = List.skipn (k - (k_rem - 1)) l).
                ** intro old_nxt.
                   eapply sep_bind_rule with
                     (Q := fun (_ : unit) s =>
                       heap s = heap s_init /\
                       exists (l_rem' : list memval) (k_rem : nat),
                         llist_reach (heap s_init) old_nxt l_rem' /\
                         BindsTo n_node (encode old_nxt) (store s) /\
                         BindsTo n_idx  (encode k_rem) (store s) /\
                         0 < k_rem /\ Nat.le k_rem k /\
                         l_rem' = List.skipn (k - (k_rem - 1)) l).
                   --- intro.
                       eapply sep_bind_rule with
                         (Q := fun (i : nat) s =>
                           heap s = heap s_init /\
                           exists (l_rem' : list memval),
                             llist_reach (heap s_init) old_nxt l_rem' /\
                             BindsTo n_node (encode old_nxt) (store s) /\
                             BindsTo n_idx  (encode i) (store s) /\
                             0 < i /\ Nat.le i k /\
                             l_rem' = List.skipn (k - (i - 1)) l).
                       +++ intro i.
                           eapply sep_weaken.
                           *** apply sep_write_var_triple.
                           *** intros s [Hheap [l_rem' [Hreach [Hbn_s [Hbi_s [Hi_pos [Hi_le Hlrem']]]]]]].
                               exists (encode i). split. exact Hbi_s.
                               destruct l_rem' as [ | vh' l_rest].
                               { cbn in Hreach. subst old_nxt.
                                 exists false. unfold Iw.
                                 split. exact Hheap.
                                 exists Pointer.NULL, (@nil memval), (i - 1).
                                 split. cbn. reflexivity.
                                 split.
                                 { apply Store.Facts.mutate_unchecked_spec_lr.
                                   exact Hn_ne. exact Hbn_s. }
                                 split.
                                 { apply Store.Facts.mutate_unchecked_spec_ll; reflexivity. }
                                 split. lia.
                                 split. exact Hlrem'.
                                 left. reflexivity. }
                               { destruct Hreach as [HNN' Hreach_rest].
                                 destruct (Nat.eq_dec (i - 1) 0) as [Hi1z | Hi1nz].
                                 - exists false. unfold Iw.
                                   split. exact Hheap.
                                   exists old_nxt, (vh' :: l_rest), (i - 1).
                                   split. exact (conj HNN' Hreach_rest).
                                   split.
                                   { apply Store.Facts.mutate_unchecked_spec_lr.
                                     exact Hn_ne. exact Hbn_s. }
                                   split.
                                   { apply Store.Facts.mutate_unchecked_spec_ll; reflexivity. }
                                   split. lia.
                                   split. exact Hlrem'.
                                   right. exact Hi1z.
                                 - exists true. unfold Iw.
                                   split. exact Hheap.
                                   exists old_nxt, (vh' :: l_rest), (i - 1).
                                   split. exact (conj HNN' Hreach_rest).
                                   split.
                                   { apply Store.Facts.mutate_unchecked_spec_lr.
                                     exact Hn_ne. exact Hbn_s. }
                                   split.
                                   { apply Store.Facts.mutate_unchecked_spec_ll; reflexivity. }
                                   split. lia.
                                   split. exact Hlrem'.
                                   cbn. split. exact HNN'. lia. }
                       +++ eapply sep_weaken.
                           *** apply sep_read_var_triple.
                           *** intros s [Hheap [l_rem' [k_rem [Hreach [Hbn_s [Hbi_s [Hk_pos [Hle Hlrem']]]]]]]].
                               exists k_rem. split. exact Hbi_s.
                               split. exact Hheap.
                               exists l_rem'.
                               exact (conj Hreach (conj Hbn_s (conj Hbi_s (conj Hk_pos (conj Hle Hlrem'))))).
                   --- eapply sep_weaken.
                       +++ apply sep_write_var_triple.
                       +++ intros s [Hheap [l_rem' [k_rem [Hreach [Hbn_s [Hbi_s [Hk_pos [Hle Hlrem']]]]]]]].
                           exists (encode nd). split. exact Hbn_s.
                           split. exact Hheap.
                           exists l_rem', k_rem.
                           split. exact Hreach.
                           split. apply Store.Facts.mutate_unchecked_spec_ll; reflexivity.
                           split. apply Store.Facts.mutate_unchecked_spec_lr.
                           { intro H; exact (Hn_ne (eq_sym H)). }
                           exact Hbi_s.
                           exact (conj Hk_pos (conj Hle Hlrem')).
                ** eapply sep_weaken.
                   --- apply sep_read_ptr_triple.
                   --- intros s [Hheap [l_rem' [k_rem [old_nxt [Hshift [Hlookup [Hreach [Hbn_s [Hbi_s [Hk_pos [Hle Hlrem']]]]]]]]]]].
                       exists old_nxt. split. rewrite Hheap. exact Hlookup.
                       split. exact Hheap.
                       exists l_rem', k_rem.
                       exact (conj Hreach (conj Hbn_s (conj Hbi_s (conj Hk_pos (conj Hle Hlrem'))))).
             ++ eapply sep_weaken.
                ** apply sep_shift_fw_ptr_triple.
                ** intros s [Hheap [l_rem [k_rem [Hreach [Hbn_s [Hbi_s [Hle [Hlrem [HNN Hk_pos]]]]]]]]].
                   destruct l_rem as [ | vh l_rem'].
                   { cbn in Hreach. subst nd. exfalso. exact (HNN eq_refl). }
                   destruct Hreach as
                       [_ [HWV [_ [_ [addr [np_nd [nxt_nd [_ [Hshift [HWVnp [HRdnp [HWrite_nd [Hlookup Htail]]]]]]]]]]]]].
                   split. rewrite Hheap. exact HWV.
                   exists np_nd. split. exact Hshift.
                   split. rewrite Hheap. exact HWVnp.
                   split. exact Hheap.
                   exists l_rem', k_rem, nxt_nd.
                   split. exact Hshift.
                   split. exact Hlookup.
                   split. exact Htail.
                   split. exact Hbn_s.
                   split. exact Hbi_s.
                   split. exact Hk_pos.
                   split. exact Hle.
                   replace (k - (k_rem - 1)) with (1 + (k - k_rem)) by lia.
                   rewrite <- (List.skipn_skipn 1 (k - k_rem)).
                   rewrite <- Hlrem.
                   reflexivity.
          -- eapply sep_weaken.
             ++ apply sep_read_var_triple.
             ++ intros s [Hheap [curr [l_rem [k_rem [Hreach [Hbn_s [Hbi_s [Hle [Hlrem [HNN Hk_pos]]]]]]]]]].
                exists curr. split. exact Hbn_s.
                split. exact Hheap.
                exists l_rem, k_rem.
                exact (conj Hreach (conj Hbn_s (conj Hbi_s (conj Hle (conj Hlrem (conj HNN Hk_pos)))))).
      + intros s ->.
        destruct l as [ | vh l'].
        { cbn in Hreach0. subst ptr.
          exists false. unfold Iw. split. cbn. reflexivity.
          exists Pointer.NULL, (@nil memval), k.
          split. cbn. reflexivity.
          split. exact Hbn2.
          split. exact Hbi2.
          split. lia.
          split. rewrite Nat.sub_diag. reflexivity.
          left. reflexivity. }
        { pose proof (proj1 Hreach0) as HNN.
          destruct (Nat.eq_dec k 0) as [-> | Hkpos].
          - exists false. unfold Iw. split. cbn. reflexivity.
            exists ptr, (vh :: l'), 0.
            split. exact Hreach0.
            split. exact Hbn2.
            split. exact Hbi2.
            split. lia.
            split. rewrite Nat.sub_0_r. reflexivity.
            cbn. right. reflexivity.
          - exists true. unfold Iw. split. cbn. reflexivity.
            exists ptr, (vh :: l'), k.
            split. exact Hreach0.
            split. exact Hbn2.
            split. exact Hbi2.
            split. lia.
            split. rewrite Nat.sub_diag. reflexivity.
            cbn. split. exact HNN. lia. }
  Qed.

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

  Lemma reverse_spec (ptr: Pointer.t) (l: list memval) P
      (HWF: forall s, P s -> Store.WF (store s))
      (HPindep: indep_store P) :
  {{ P ** llist ptr l }}
    reverse ptr (1%N)
  {{ fun res s' => (P ** llist res (List.rev l)) s' }}.

    Proof.
    unfold reverse.
    eapply sep_with_var_triple.
    intros s_init n_node st1 (s_P & s_ll & Hst1 & _ & Hpart_init & HP0 & Hllist0) Hpush_node.
    set (hp_P := heap s_P).
    set (hp_ll_init := heap s_ll).
    assert (HWF_init : Store.WF (store s_init)).
    { pose proof (HWF s_P HP0) as H. rewrite <- Hst1 in H. exact H. }
    pose proof (push_spec2 _ _ _ _ HWF_init Hpush_node) as Hbn1.
    pose proof (push_wf _ _ _ _ HWF_init Hpush_node) as HWF1.
    eapply sep_with_var_triple.
    intros s1 n_new_next st2 -> Hpush_new_next.
    pose proof (push_spec2 _ _ _ _ HWF1 Hpush_new_next) as Hbnn1.
    pose proof (push_wf _ _ _ _ HWF1 Hpush_new_next) as HWF2.
    pose proof (push_spec_preserve _ _ _ _ _ _ HWF1 Hpush_new_next Hbn1) as Hbn2.
    pose proof (fun v' => push_spec1 _ _ _ _ v' HWF1 Hpush_new_next) as Hfresh.
    assert (Hn_ne : n_node <> n_new_next) by
      (intro Heq; subst; exact (Hfresh _ Hbn1)).
    pose (Iw := fun (b : bool) (s : State ListStore list_heap_carrier) =>
      exists (curr acc : Pointer.t) (l_rem l_acc : list memval) (hp_ll : list_heap_carrier),
        (llist curr l_rem ** llist acc l_acc) {|store := store s; heap := hp_ll|} /\
        hp_P $+ hp_ll = Some (heap s) /\
        List.rev l_acc ++ l_rem = l /\
        BindsTo n_node (encode curr) (store s) /\
        BindsTo n_new_next (encode acc) (store s) /\
        match b with
        | true  => curr <> Pointer.NULL
        | false => curr = Pointer.NULL
        end).
    eapply sep_seq_rule with (Q := fun s => exists b, Iw b s).
    - eapply sep_seq_rule with (Q := fun s => Iw false s).
      + eapply sep_weaken.
        * apply sep_read_var_triple.
        * intros s HIw.
          destruct HIw
            as [curr [acc [l_rem [l_acc [hp_ll [Hll [Hpart_full [Hinv [Hbn_s [Hbnn_s Hcurr_null]]]]]]]]]].
          subst curr.
          exists acc. split. exact Hbnn_s.
          destruct Hll as (sa & sb & Hsta & Hstb & Hpart_sub & Hlla & Hllb).
          pose proof (proj1 ((llist_null l_rem) sa) Hlla) as [-> Hheap_sa].
          rewrite List.app_nil_r in Hinv.
          apply (f_equal (@List.rev memval)) in Hinv.
          rewrite List.rev_involutive in Hinv. subst l_acc.
          rewrite Hheap_sa, op_id_l in Hpart_sub.
          injection Hpart_sub as Hheap_sb.
          destruct (pop_pop_fwd (store s) _ _ _ _ Hn_ne Hbn_s Hbnn_s)
            as [t1 [t2 [Hpop1 Hpop2]]].
          exists t1. split. exact Hpop1.
          exists t2. split. exact Hpop2.
          exists {|store := t2; heap := hp_P|}, {|store := t2; heap := hp_ll|}.
          refine (conj eq_refl (conj eq_refl (conj Hpart_full (conj _ _)))).
          -- exact (HPindep s_P {|store := t2; heap := hp_P|} eq_refl HP0).
          -- exact (llist_indep_regs acc (List.rev l) sb {|store := t2; heap := hp_ll|}
               Hheap_sb Hllb).
      + apply sep_while_rule with (I := Iw).
        * eapply sep_bind_rule with (Q := fun cv s =>
            exists acc l_rem l_acc hp_ll,
              (llist cv l_rem ** llist acc l_acc) {|store := store s; heap := hp_ll|} /\
              hp_P $+ hp_ll = Some (heap s) /\
              List.rev l_acc ++ l_rem = l /\
              BindsTo n_node (encode cv) (store s) /\
              BindsTo n_new_next (encode acc) (store s)).
          -- intro cv.
             eapply sep_bind_rule with (Q := fun c s => Iw (negb c) s).
             ++ intro c. apply sep_ret_triple.
             ++ eapply sep_weaken.
                ** apply sep_eq_ptr_triple_cmp.
                ** intro s. intro Hpre.
                   destruct Hpre as (acc & l_rem & l_acc & hp_ll & Hll & Hpart_full & Hinv & Hbn & Hbnn).
                   destruct Hll as (sa & sb & Hst_sa & Hst_sb & Hpart_sub & Hlla & Hllb).
                   destruct l_rem as [ | v l_rem'].
                   --- cbn in Hlla. destruct Hlla as [Hcv_null Hheap_sa]. subst cv.
                       refine (conj _ (conj _ (conj Pointer.AllowsNull (conj Pointer.AllowsNull _)))).
                       +++ right; right; reflexivity.
                       +++ right; right; reflexivity.
                       +++ intros b Hcmp.
                           unfold Pointer.cmp in Hcmp; cbn in Hcmp.
                           inversion Hcmp; subst. cbn. unfold Iw.
                           exact (ex_intro _ Pointer.NULL (ex_intro _ acc
                             (ex_intro _ (@nil memval) (ex_intro _ l_acc (ex_intro _ hp_ll
                               (conj (ex_intro _ sa (ex_intro _ sb
                                 (conj Hst_sa (conj Hst_sb (conj Hpart_sub
                                   (conj (conj eq_refl Hheap_sa) Hllb))))))
                               (conj Hpart_full (conj eq_refl (conj Hbn (conj Hbnn eq_refl)))))))))).
                   --- assert (Hcv_nn : cv <> Pointer.NULL).
                       { cbn in Hlla.
                         destruct Hlla as (? & ? & _ & _ & _ & ((H & _) & _) & _).
                         exact H. }
                       pose proof (llist_allows_cmp cv v l_rem' sa Hlla) as HCmp_cv.
                       pose proof (llist_wvalid cv v l_rem' sa Hlla) as HWV_sa.
                       pose proof (wvalid_mono _ _ cv
                         (substate_tran _ hp_ll _
                           (substate_of_partition_l Hpart_sub)
                           (substate_of_partition_r Hpart_full))
                         HWV_sa) as HWV_s.
                       refine (conj HWV_s (conj _ (conj HCmp_cv (conj Pointer.AllowsNull _)))).
                       +++ right; right; reflexivity.
                       +++ intros c Hcmp.
                           assert (Hallow : Pointer.allows cv Operation.Cmp = true).
                           { destruct (Pointer.allows_spec cv Operation.Cmp);
                             [reflexivity | contradiction]. }
                           unfold Pointer.cmp in Hcmp.
                           rewrite Hallow in Hcmp; cbn in Hcmp.
                           inversion Hcmp; subst.
                           assert (Hceqb : Pointer.eqb cv Pointer.NULL = false).
                           { apply Pointer.eqb_neq; exact Hcv_nn. }
                           rewrite Hceqb; cbn. unfold Iw.
                           exact (ex_intro _ cv (ex_intro _ acc
                             (ex_intro _ (v :: l_rem') (ex_intro _ l_acc (ex_intro _ hp_ll
                               (conj (ex_intro _ sa (ex_intro _ sb
                                 (conj Hst_sa (conj Hst_sb (conj Hpart_sub (conj Hlla Hllb))))))
                               (conj Hpart_full (conj eq_refl (conj Hbn (conj Hbnn Hcv_nn)))))))))).
          -- eapply sep_weaken.
             ++ apply sep_read_var_triple.
             ++ intros s (b & curr & acc & l_rem & l_acc & hp_ll & Hll & Hpart_full & Hinv & Hbn & Hbnn & _).
                exact (ex_intro _ curr (conj Hbn
                  (ex_intro _ acc (ex_intro _ l_rem (ex_intro _ l_acc (ex_intro _ hp_ll
                    (conj Hll (conj Hpart_full (conj Hinv (conj Hbn Hbnn)))))))))).
        * eapply sep_bind_rule with (Q := fun nd s =>
            exists acc v l_rem' l_acc hp_ll np on,
              (llist nd (v :: l_rem') ** llist acc l_acc) {|store := store s; heap := hp_ll|} /\
              hp_P $+ hp_ll = Some (heap s) /\
              List.rev l_acc ++ v :: l_rem' = l /\
              BindsTo n_node (encode nd) (store s) /\
              BindsTo n_new_next (encode acc) (store s) /\
              nd <> Pointer.NULL /\
              Pointer.shift_fw nd 1%N = Some np /\
              Heap.Facts.WValid (heap s) np /\
              Pointer.Allows np Operation.Read /\
              Heap.lookup hp_ll np = Some (encode on)).
          -- intro nd.
             eapply sep_bind_rule with (Q := fun np s =>
               exists acc v l_rem' l_acc hp_ll on,
                 (llist nd (v :: l_rem') ** llist acc l_acc) {|store := store s; heap := hp_ll|} /\
                 hp_P $+ hp_ll = Some (heap s) /\
                 List.rev l_acc ++ v :: l_rem' = l /\
                 BindsTo n_node (encode nd) (store s) /\
                 BindsTo n_new_next (encode acc) (store s) /\
                 nd <> Pointer.NULL /\
                 Pointer.shift_fw nd 1%N = Some np /\
                 Heap.Facts.WValid (heap s) np /\
                 Pointer.Allows np Operation.Read /\
                 Heap.lookup hp_ll np = Some (encode on)).
             ++ intro np.
                eapply sep_bind_rule with (Q := fun on s =>
                  exists acc v l_rem' l_acc hp_ll,
                    (llist nd (v :: l_rem') ** llist acc l_acc) {|store := store s; heap := hp_ll|} /\
                    hp_P $+ hp_ll = Some (heap s) /\
                    List.rev l_acc ++ v :: l_rem' = l /\
                    BindsTo n_node (encode nd) (store s) /\
                    BindsTo n_new_next (encode acc) (store s) /\
                    nd <> Pointer.NULL /\
                    Pointer.shift_fw nd 1%N = Some np /\
                    Heap.lookup hp_ll np = Some (encode on)).
                ** intro on.
                   eapply sep_bind_rule with (Q := fun nnv s =>
                     exists v l_rem' l_acc hp_ll,
                       (llist nd (v :: l_rem') ** llist nnv l_acc) {|store := store s; heap := hp_ll|} /\
                       hp_P $+ hp_ll = Some (heap s) /\
                       List.rev l_acc ++ v :: l_rem' = l /\
                       BindsTo n_node (encode nd) (store s) /\
                       BindsTo n_new_next (encode nnv) (store s) /\
                       nd <> Pointer.NULL /\
                       Pointer.shift_fw nd 1%N = Some np /\
                       Heap.lookup hp_ll np = Some (encode on)).
                   --- intro nnv.
                       eapply sep_seq_rule with (Q := fun s =>
                         exists v l_rem' l_acc hp_ll_new,
                           (llist nd (v :: l_acc) ** llist on l_rem') {|store := store s; heap := hp_ll_new|} /\
                           hp_P $+ hp_ll_new = Some (heap s) /\
                           List.rev (v :: l_acc) ++ l_rem' = l /\
                           BindsTo n_node (encode nd) (store s) /\
                           BindsTo n_new_next (encode nnv) (store s)).
                       +++ eapply sep_seq_rule with (Q := fun s =>
                             exists v l_rem' l_acc hp_ll_new,
                               (llist nd (v :: l_acc) ** llist on l_rem') {|store := store s; heap := hp_ll_new|} /\
                               hp_P $+ hp_ll_new = Some (heap s) /\
                               List.rev (v :: l_acc) ++ l_rem' = l /\
                               BindsTo n_node (encode nd) (store s) /\
                               BindsTo n_new_next (encode nd) (store s)).
                           *** eapply sep_weaken.
                               ---- apply sep_write_var_triple.
                               ---- intros s (v & l_rem' & l_acc & hp_ll_new & Hll & Hpart_full & Hrev & Hbn & Hbnn).
                                    exists (encode nd). split. exact Hbn.
                                    destruct Hll as (sa & sb & Hst_sa & Hst_sb & Hpart_sub & Hll_nd & Hll_on).
                                    pose (st'' := Store.mutate_unchecked (store s) n_node (encode on)).
                                    destruct (Pointer.eq_dec on Pointer.NULL) as [Honull | Hnn].
                                    ++++ exists false. unfold Iw.
                                         exists on, nd, l_rem', (v :: l_acc), hp_ll_new.
                                         refine (conj _ (conj Hpart_full (conj Hrev (conj _ (conj _ _))))).
                                         **** exists {|store := st''; heap := heap sb|},
                                                     {|store := st''; heap := heap sa|}.
                                              refine (conj eq_refl (conj eq_refl (conj _ (conj _ _)))).
                                              ----- rewrite op_comm. cbn. exact Hpart_sub.
                                              ----- exact (llist_indep_regs _ _ sb {|store := st''; heap := heap sb|} eq_refl Hll_on).
                                              ----- exact (llist_indep_regs _ _ sa {|store := st''; heap := heap sa|} eq_refl Hll_nd).
                                         **** apply Store.Facts.mutate_unchecked_spec_ll; reflexivity.
                                         **** apply Store.Facts.mutate_unchecked_spec_lr.
                                              intro H; exact (Hn_ne (eq_sym H)). exact Hbnn.
                                         **** exact Honull.
                                    ++++ exists true. unfold Iw.
                                         exists on, nd, l_rem', (v :: l_acc), hp_ll_new.
                                         refine (conj _ (conj Hpart_full (conj Hrev (conj _ (conj _ _))))).
                                         **** exists {|store := st''; heap := heap sb|},
                                                     {|store := st''; heap := heap sa|}.
                                              refine (conj eq_refl (conj eq_refl (conj _ (conj _ _)))).
                                              ----- rewrite op_comm. cbn. exact Hpart_sub.
                                              ----- exact (llist_indep_regs _ _ sb {|store := st''; heap := heap sb|} eq_refl Hll_on).
                                              ----- exact (llist_indep_regs _ _ sa {|store := st''; heap := heap sa|} eq_refl Hll_nd).
                                         **** apply Store.Facts.mutate_unchecked_spec_ll; reflexivity.
                                         **** apply Store.Facts.mutate_unchecked_spec_lr.
                                              intro H; exact (Hn_ne (eq_sym H)). exact Hbnn.
                                         **** exact Hnn.
                           *** eapply sep_weaken.
                               ---- apply sep_write_var_triple.
                               ---- intros s (v & l_rem' & l_acc & hp_ll_new & Hll & Hpart_full & Hrev & Hbn & Hbnn).
                                    exists (encode nnv). split. exact Hbnn.
                                    pose (st' := Store.mutate_unchecked (store s) n_new_next (encode nd)).
                                    destruct Hll as (sa & sb & Hst_sa & Hst_sb & Hpart_sub & Hll_nd & Hll_on).
                                    exists v, l_rem', l_acc, hp_ll_new.
                                    refine (conj _ (conj Hpart_full (conj Hrev (conj _ _)))).
                                    ++++ exists {|store := st'; heap := heap sa|},
                                                {|store := st'; heap := heap sb|}.
                                         refine (conj eq_refl (conj eq_refl (conj Hpart_sub (conj _ _)))).
                                         **** exact (llist_indep_regs _ _ sa {|store := st'; heap := heap sa|} eq_refl Hll_nd).
                                         **** exact (llist_indep_regs _ _ sb {|store := st'; heap := heap sb|} eq_refl Hll_on).
                                    ++++ apply Store.Facts.mutate_unchecked_spec_lr.
                                         intro H; exact (Hn_ne H). exact Hbn.
                                    ++++ apply Store.Facts.mutate_unchecked_spec_ll; reflexivity.
                       +++ eapply sep_weaken.
                           *** apply sep_write_ptr_triple.
                           *** intros s (v & l_rem' & l_acc & hp_ll & Hll & Hpart_full & Hrev & Hbn & Hbnn & _ & Hshift & Hlookup_sub).
                               pose proof (llist_star_mutate nd nnv on v l_rem' l_acc np
                                 {|store := store s; heap := hp_ll|}
                                 Hll Hshift Hlookup_sub) as (h_ll' & Hmut_ll & Hll').
                               pose proof (heap_mutate_frame hp_P hp_ll (heap s) h_ll' np (encode nnv)
                                 Hpart_full Hmut_ll) as (hp' & Hmut_full & Hpart_new).
                               refine (ex_intro _ hp' (conj Hmut_full _)).
                               assert (Hrev' : List.rev (v :: l_acc) ++ l_rem' = l).
                               { cbn [List.rev]. rewrite <- List.app_assoc. exact Hrev. }
                               exists v, l_rem', l_acc, h_ll'.
                               exact (conj Hll' (conj Hpart_new (conj Hrev' (conj Hbn Hbnn)))).
                   --- eapply sep_weaken.
                       +++ apply sep_read_var_triple.
                       +++ intros s (acc & v & l_rem' & l_acc & hp_ll & Hll & Hpart_full & Hrev & Hbn & Hbnn & Hnn & Hshift & Hlookup_sub).
                           exact (ex_intro _ acc (conj Hbnn
                             (ex_intro _ v (ex_intro _ l_rem' (ex_intro _ l_acc (ex_intro _ hp_ll
                               (conj Hll (conj Hpart_full (conj Hrev (conj Hbn (conj Hbnn (conj Hnn (conj Hshift Hlookup_sub))))))))))))).
                ** eapply sep_weaken.
                   --- apply sep_read_ptr_triple.
                   --- intros s (acc & v & l_rem' & l_acc & hp_ll & on & Hll & Hpart_full & Hrev & Hbn & Hbnn & Hnn & Hshift & _ & _ & Hlookup_sub).
                       exact (ex_intro _ on (conj (lookup_mono _ _ _ _ (substate_of_partition_r Hpart_full) Hlookup_sub)
                         (ex_intro _ acc (ex_intro _ v (ex_intro _ l_rem' (ex_intro _ l_acc (ex_intro _ hp_ll
                           (conj Hll (conj Hpart_full (conj Hrev (conj Hbn (conj Hbnn (conj Hnn (conj Hshift Hlookup_sub)))))))))))))).
             ++ eapply sep_weaken.
                ** apply sep_shift_fw_ptr_triple.
                ** intros s (acc & v & l_rem' & l_acc & hp_ll & np & on & Hll & Hpart_full & Hrev & Hbn & Hbnn & Hnn & Hshift & HWVnp & HAlnp & Hlookup_sub).
                   destruct Hll as (sa & sb & Hst_sa & Hst_sb & Hpart_sub & Hlla & Hllb).
                   pose proof (llist_wvalid nd v l_rem' sa Hlla) as HWV_nd_sa.
                   pose proof (wvalid_mono _ _ nd
                     (substate_tran _ hp_ll _
                       (substate_of_partition_l Hpart_sub)
                       (substate_of_partition_r Hpart_full))
                     HWV_nd_sa) as HWV_nd.
                   refine (conj HWV_nd (ex_intro _ np (conj Hshift (conj HWVnp _)))).
                   exact (ex_intro _ acc (ex_intro _ v (ex_intro _ l_rem' (ex_intro _ l_acc (ex_intro _ hp_ll (ex_intro _ on
                     (conj (ex_intro _ sa (ex_intro _ sb
                       (conj Hst_sa (conj Hst_sb (conj Hpart_sub (conj Hlla Hllb))))))
                     (conj Hpart_full (conj Hrev (conj Hbn (conj Hbnn (conj Hnn
                       (conj Hshift (conj HWVnp (conj HAlnp Hlookup_sub))))))))))))))).
          -- eapply sep_weaken.
             ++ apply sep_read_var_triple.
             ++ intros s (curr & acc & l_rem & l_acc & hp_ll & Hll & Hpart_full & Hrev & Hbn & Hbnn & Hnn).
                destruct Hll as (sa & sb & Hst_sa & Hst_sb & Hpart_sub & Hlla & Hllb).
                destruct l_rem as [ | v l_rem'].
                ** cbn in Hlla. destruct Hlla as [Hcurr_null _].
                   exact (False_rect _ (Hnn Hcurr_null)).
                ** pose proof (llist_reach_of_llist curr (v :: l_rem') sa Hlla) as Hreach_sa.
                   cbn in Hreach_sa.
                   destruct Hreach_sa as (_ & _ & _ & _ & addr & np & on & _ & Hshift & HWV_np_sa & HAlnp & _ & Hlookup_sa & _).
                   pose proof (lookup_mono _ _ _ _ (substate_of_partition_l Hpart_sub) Hlookup_sa) as Hlookup_sub.
                   pose proof (wvalid_mono _ _ np
                     (substate_tran _ hp_ll _
                       (substate_of_partition_l Hpart_sub)
                       (substate_of_partition_r Hpart_full))
                     HWV_np_sa) as HWVnp.
                   exact (ex_intro _ curr (conj Hbn
                     (ex_intro _ acc (ex_intro _ v (ex_intro _ l_rem' (ex_intro _ l_acc (ex_intro _ hp_ll
                       (ex_intro _ np (ex_intro _ on
                         (conj (ex_intro _ sa (ex_intro _ sb
                           (conj Hst_sa (conj Hst_sb (conj Hpart_sub (conj Hlla Hllb))))))
                         (conj Hpart_full (conj Hrev (conj Hbn (conj Hbnn (conj Hnn
                           (conj Hshift (conj HWVnp (conj HAlnp Hlookup_sub)))))))))))))))))).
    - eapply sep_weaken.
      + apply sep_write_var_triple.
      + intros s ->.
        pose (st' := Store.mutate_unchecked st2 n_node (encode ptr)).
        exists (encode ptr).
        split. exact Hbn2.
        assert (Hllist0' : llist ptr l {|store := st2; heap := hp_ll_init|}).
        { exact (llist_indep_regs ptr l s_ll {|store := st2; heap := hp_ll_init|} eq_refl Hllist0). }
        destruct l as [ | vh l'].
        * cbn in Hllist0'. destruct Hllist0' as [Hptr_null Hheap0].
          subst ptr.
          exists false. unfold Iw.
          exists Pointer.NULL, Pointer.NULL, (@nil memval), (@nil memval), ($0 : list_heap_carrier)%sep.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
          -- pose (snil := {| store := st'; heap := ($0 : list_heap_carrier)%sep |}).
             exists snil, snil.
             refine (conj eq_refl (conj eq_refl (conj _ (conj _ _)))).
             ++ exact (op_id_l ($0)%sep).
             ++ split; reflexivity.
             ++ split; reflexivity.
          -- change (heap {| store := st2; heap := hp_ll_init |}) with hp_ll_init in Hheap0.
             fold hp_P hp_ll_init in Hpart_init.
             rewrite Hheap0 in Hpart_init. exact Hpart_init.
          -- cbn. reflexivity.
          -- apply Store.Facts.mutate_unchecked_spec_ll; reflexivity.
          -- apply Store.Facts.mutate_unchecked_spec_lr.
             intro H; exact (Hn_ne (eq_sym H)). exact Hbnn1.
          -- reflexivity.
        * pose proof (llist_allows_read ptr vh l' {|store := st2; heap := hp_ll_init|} Hllist0') as HAllRead.
          exists true. unfold Iw.
          exists ptr, Pointer.NULL, (vh :: l'), (@nil memval), hp_ll_init.
          refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
          -- pose (sl  := {| store := st'; heap := hp_ll_init |}).
             pose (snil := {| store := st'; heap := ($0 : list_heap_carrier)%sep |}).
             exists sl, snil.
             refine (conj eq_refl (conj eq_refl (conj _ (conj _ _)))).
             ++ exact (op_id_r hp_ll_init).
             ++ exact (llist_indep_regs _ _ {|store := st2; heap := hp_ll_init|} sl eq_refl Hllist0').
             ++ split; reflexivity.
          -- exact Hpart_init.
          -- cbn. reflexivity.
          -- apply Store.Facts.mutate_unchecked_spec_ll; reflexivity.
          -- apply Store.Facts.mutate_unchecked_spec_lr.
             intro H; exact (Hn_ne (eq_sym H)). exact Hbnn1.
          -- intro Hcontra. subst ptr. inversion HAllRead.
  Qed.

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

  Lemma append_spec (l0 l1: Pointer.t) (la lb: list memval) P
      (HWF: forall s, P s -> Store.WF (store s)) :
  {{ P && (llist l0 la ** llist l1 lb) }}
    append l0 l1 (1%N)
  {{ fun res s' => llist res (la ++ lb) s' }}.

  Proof.
  unfold append.
  destruct la as [ | v la'].
  - eapply sep_bind_rule with
      (Q := fun (is_null : bool) s =>
        match is_null with
        | true  => P s /\ llist l1 lb s
        | false => False
        end).
    + intro is_null; destruct is_null.
      * eapply sep_weaken. apply sep_ret_triple.
        intros s [_ Hllb]. cbn. exact Hllb.
      * exact (fun s H => False_rect _ H).
    + eapply sep_weaken. apply sep_eq_ptr_triple_cmp.
      intros s [HP Hstar].
      destruct Hstar as (sa & sb & _ & _ & Hab & Hlla & Hllb).
      cbn in Hlla. destruct Hlla as [Hl0null Hempty]. subst l0.
      rewrite Hempty in Hab. rewrite op_id_l in Hab. injection Hab as Hheap_sb.
      split. right; right; reflexivity.
      split. right; right; reflexivity.
      split. exact Pointer.AllowsNull.
      split. exact Pointer.AllowsNull.
      intros b Hcmp. cbn in Hcmp. inversion Hcmp; subst.
      exact (conj HP (llist_indep_regs l1 lb sb s Hheap_sb Hllb)).
  - eapply sep_bind_rule with
      (Q := fun (is_null : bool) s =>
        match is_null with
        | true  => False
        | false => P s /\ (llist l0 (v :: la') ** llist l1 lb) s
        end).
    + intro is_null; destruct is_null.
      * exact (fun s H => False_rect _ H).
      * eapply sep_with_var_triple.
        intros s_init n_node st1 [HP Hstar] Hpush_node.
        pose proof (push_spec2 _ _ _ _ (HWF s_init HP) Hpush_node) as Hbn_init.
        destruct (pop_spec Hpush_node) as [st_pop0 [Hpop_st1 _]].
        destruct Hstar as (sa & sb & Hst_sa & Hst_sb & Hab & Hlla & Hllb).
        pose proof (substate_of_partition_l Hab) as Hsub_sa.
        pose proof (llist_reach_of_llist l0 (v :: la') sa Hlla) as Hreach_sa.
        pose proof (llist_reach_monotone _ _ l0 (v :: la') Hsub_sa Hreach_sa)
          as Hreach_init.
        assert (Hstar_init : (llist l0 (v :: la') ** llist l1 lb) s_init)
          by (exists sa, sb; cbn; repeat split; assumption).
        assert (Hne : v :: la' <> []) by discriminate.
        pose (Iw := fun (b : bool) (s : State ListStore list_heap_carrier) =>
          heap s = heap s_init /\
          exists (curr : Pointer.t) (la_pref la_suff : list memval),
            (v :: la') = la_pref ++ la_suff /\
            la_suff <> [] /\
            Store.BindsTo n_node (encode curr) (store s) /\
            llist_path (heap s_init) l0 la_pref curr /\
            llist_reach (heap s_init) curr la_suff /\
            (exists st_pop, Store.pop (store s) = Some st_pop) /\
            (b = true  -> exists vh vx la_rest, la_suff = vh :: vx :: la_rest) /\
            (b = false -> exists v_last, la_suff = [v_last])).
        eapply sep_weaken.
        -- apply sep_seq_rule with (Q := fun s => Iw false s).
          ++ eapply sep_bind_rule with
              (Q := fun (curr : Pointer.t) s =>
                curr <> Pointer.NULL /\
                heap s = heap s_init /\
                exists la_pref v_last,
                  (v :: la') = la_pref ++ [v_last] /\
                  Store.BindsTo n_node (encode curr) (store s) /\
                  llist_path (heap s_init) l0 la_pref curr /\
                  llist_reach (heap s_init) curr [v_last] /\
                  exists st_pop, Store.pop (store s) = Some st_pop).
            ** intro curr.
               eapply sep_bind_rule with
                 (Q := fun (np : Pointer.t) s =>
                   curr <> Pointer.NULL /\
                   heap s = heap s_init /\
                   Pointer.shift_fw curr 1%N = Some np /\
                   exists la_pref v_last,
                     (v :: la') = la_pref ++ [v_last] /\
                     llist_path (heap s_init) l0 la_pref curr /\
                     llist_reach (heap s_init) curr [v_last] /\
                     exists st_pop, Store.pop (store s) = Some st_pop).
               --- intro np.
                   eapply sep_bind_rule with
                     (Q := fun (_ : unit) s =>
                       exists st_pop,
                         Store.pop (store s) = Some st_pop /\
                         llist l0 ((v :: la') ++ lb)
                           {| store := st_pop; heap := heap s |}).
                   +++ intro tt.
                       eapply sep_weaken. apply sep_ret_triple.
                       intros s [st_pop [Hpop Hll]].
                       exact (ex_intro _ st_pop (conj Hpop Hll)).
                   +++ eapply sep_weaken. apply sep_write_ptr_triple.
                       intros s (HNN_c & Hheap & Hshift_np &
                                 la_pref & v_last & Hpart & Hpath_curr &
                                 Hreach_one & [st_pop Hpop]).
                       assert (Hpref_eq : la_pref = removelast (v :: la')).
                       { pose proof (f_equal (@removelast memval) Hpart) as Hrm.
                         rewrite removelast_app in Hrm. 2: discriminate.
                         cbn in Hrm. rewrite app_nil_r in Hrm.
                         exact (eq_sym Hrm). }
                       destruct Hstar_init as (sa' & sb' & _ & _ & Hab' & Hlla' & Hllb').
                       assert (Hstar_s :
                         (llist l0 (v :: la') ** llist l1 lb)
                           {| store := store s; heap := heap s_init |}).
                       { exists {| store := store s; heap := heap sa' |},
                                {| store := store s; heap := heap sb' |}.
                         cbn. repeat split. exact Hab'.
                         exact (llist_indep_regs l0 (v :: la') sa'
                                  {| store := store s; heap := heap sa' |}
                                  eq_refl Hlla').
                         exact (llist_indep_regs l1 lb sb'
                                  {| store := store s; heap := heap sb' |}
                                  eq_refl Hllb'). }
                       destruct (llist_extend_with_path l0 l1 (v :: la') lb
                                   {| store := store s; heap := heap s_init |}
                                   Hne Hstar_s)
                         as (nd & np_ext & h_ext & Hpath_ext & Hshift_ext &
                             Hmut_ext & Hll_ext).
                       cbn in Hpath_ext, Hshift_ext, Hmut_ext, Hll_ext.
                       assert (Hcurr_nd : curr = nd).
                       { apply (llist_path_det (heap s_init) l0 la_pref).
                         exact Hpath_curr. rewrite Hpref_eq. exact Hpath_ext. }
                       subst nd.
                       assert (Hnp_eq : np = np_ext).
                       { injection (eq_trans (eq_sym Hshift_np) Hshift_ext) as Heq.
                         exact Heq. }
                       subst np_ext.
                       exact (ex_intro _ h_ext
                         (conj (eq_ind_r
                                  (fun h => Heap.mutate h np (encode l1) = Some h_ext)
                                  Hmut_ext Hheap)
                         (ex_intro _ st_pop (conj Hpop
                         (llist_indep_regs l0 ((v :: la') ++ lb)
                            {| store := store s; heap := h_ext |}
                            {| store := st_pop; heap := h_ext |}
                            eq_refl Hll_ext))))).
               --- eapply sep_weaken. apply sep_shift_fw_ptr_triple.
                   intros s (HNN_c & Hheap & la_pref & v_last & Hpart & Hbn_s &
                             Hpath_curr & Hreach_one & [st_pop Hpop]).
                   pose proof (llist_reach_unfold (heap s_init) curr v_last [] Hreach_one)
                     as (HNN_c2 & HWV_c & _ & _ & _ & np_c & _ &
                         _ & Hshift_c & HWVnp_c & _ & _ & _ & _).
                   split. rewrite Hheap. exact HWV_c.
                   exists np_c. split. exact Hshift_c.
                   split. rewrite Hheap. exact HWVnp_c.
                   exact (conj HNN_c (conj Hheap (conj Hshift_c (ex_intro _ la_pref
                     (ex_intro _ v_last (conj Hpart (conj Hpath_curr
                       (conj Hreach_one (ex_intro _ st_pop Hpop))))))))).
            ** eapply sep_weaken. apply sep_read_var_triple.
               intros s (Hheap & curr_r & la_pref & la_suff & Hpart & Hne_suff &
                         Hbn_s & Hpath_curr & Hreach_curr & [st_pop Hpop] & _ & Hlast).
               destruct (Hlast eq_refl) as [v_last Hvl]. subst la_suff.
               pose proof (llist_reach_unfold (heap s_init) curr_r v_last [] Hreach_curr)
                 as (HNN_c & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
               exists curr_r. split. exact Hbn_s.
               exact (conj HNN_c (conj Hheap (ex_intro _ la_pref (ex_intro _ v_last
                 (conj Hpart (conj Hbn_s (conj Hpath_curr (conj Hreach_curr
                   (ex_intro _ st_pop Hpop))))))))).
          ++ apply sep_while_rule with (I := Iw).
            ** eapply sep_bind_rule with
                 (Q := fun (nd : Pointer.t) s =>
                   heap s = heap s_init /\
                   exists la_pref la_suff,
                     (v :: la') = la_pref ++ la_suff /\
                     la_suff <> [] /\
                     Store.BindsTo n_node (encode nd) (store s) /\
                     llist_path (heap s_init) l0 la_pref nd /\
                     llist_reach (heap s_init) nd la_suff /\
                     exists st_pop, Store.pop (store s) = Some st_pop).
               --- intro nd.
                   eapply sep_bind_rule with
                     (Q := fun (np : Pointer.t) s =>
                       heap s = heap s_init /\
                       exists la_pref la_suff,
                         (v :: la') = la_pref ++ la_suff /\
                         la_suff <> [] /\
                         Store.BindsTo n_node (encode nd) (store s) /\
                         llist_path (heap s_init) l0 la_pref nd /\
                         llist_reach (heap s_init) nd la_suff /\
                         Pointer.shift_fw nd 1%N = Some np /\
                         exists st_pop, Store.pop (store s) = Some st_pop).
                   +++ intro np.
                       eapply sep_bind_rule with
                         (Q := fun (nxt : Pointer.t) s =>
                           heap s = heap s_init /\
                           exists la_pref la_suff,
                             (v :: la') = la_pref ++ la_suff /\
                             la_suff <> [] /\
                             Store.BindsTo n_node (encode nd) (store s) /\
                             llist_path (heap s_init) l0 la_pref nd /\
                             llist_reach (heap s_init) nd la_suff /\
                             Pointer.shift_fw nd 1%N = Some np /\
                             Heap.lookup (heap s_init) np =
                               Some (StorablePtr.ptr_encode nxt) /\
                             exists st_pop, Store.pop (store s) = Some st_pop).
                       *** intro nxt.
                           eapply sep_bind_rule with
                             (Q := fun (c : bool) s => Iw (negb c) s).
                           ---- intro c. apply sep_ret_triple.
                           ---- eapply sep_weaken. apply sep_eq_ptr_triple_cmp.
                                intros s (Hheap & la_pref & la_suff & Hpart & Hne_suff &
                                          Hbn_s & Hpath_nd & Hreach_nd & Hshift_np &
                                          Hlk_np & [st_pop Hpop]).
                                destruct la_suff as [ | vh la_suff_tail].
                                { exact (False_rect _ (Hne_suff eq_refl)). }
                                pose proof (llist_reach_unfold (heap s_init) nd vh la_suff_tail
                                              Hreach_nd)
                                  as (HNN_nd & HWV_nd & HCmp_nd & _ & _ & np_ref & nxt_ref &
                                      _ & Hshift_ref & HWVnp_ref & _ & _ & Hlk_ref & Htail_ref).
                                assert (Hnp_eq : np = np_ref).
                                { injection (eq_trans (eq_sym Hshift_np) Hshift_ref) as Heq.
                                  exact Heq. }
                                subst np_ref.
                                assert (Hnxt_eq : nxt = nxt_ref).
                                { assert (H : StorablePtr.ptr_encode nxt =
                                             StorablePtr.ptr_encode nxt_ref) by congruence.
                                  cbn in H. injection H as H'. exact H'. }
                                subst nxt_ref.
                                destruct la_suff_tail as [ | vx la_rest].
                                ++++ cbn in Htail_ref. subst nxt.
                                     split. right; right; reflexivity.
                                     split. right; right; reflexivity.
                                     split. exact Pointer.AllowsNull.
                                     split. exact Pointer.AllowsNull.
                                     intros c Hcmp. cbn in Hcmp. inversion Hcmp; subst.
                                     unfold Iw. cbn.
                                     split. exact Hheap.
                                     exists nd, la_pref, [vh].
                                     split. cbn in Hpart |- *. exact Hpart.
                                     split. discriminate.
                                     split. exact Hbn_s.
                                     split. exact Hpath_nd.
                                     split. exact Hreach_nd.
                                     split. exact (ex_intro _ st_pop Hpop).
                                     constructor; [intro H; discriminate |
                                       intros _; exact (ex_intro _ vh eq_refl)].
                                ++++ pose proof (llist_reach_unfold (heap s_init) nxt vx la_rest
                                                   Htail_ref)
                                       as (HNN_nxt & HWV_nxt & HCmp_nxt & _ & _).
                                     split. rewrite Hheap. exact HWV_nxt.
                                     split. right; right; reflexivity.
                                     split. exact HCmp_nxt.
                                     split. exact Pointer.AllowsNull.
                                     intros c Hcmp.
                                     assert (Hallow_nxt :
                                       Pointer.allows nxt Operation.Cmp = true).
                                     { destruct (Pointer.allows_spec nxt Operation.Cmp);
                                       [reflexivity | contradiction]. }
                                     assert (Hallow_null :
                                       Pointer.allows Pointer.NULL Operation.Cmp = true).
                                     { destruct (Pointer.allows_spec Pointer.NULL Operation.Cmp);
                                       [reflexivity |
                                        exact (False_rect _ (n Pointer.AllowsNull))]. }
                                     unfold Pointer.cmp in Hcmp.
                                     rewrite Hallow_nxt, Hallow_null in Hcmp. cbn in Hcmp.
                                     assert (Hceqb : Pointer.eqb nxt Pointer.NULL = false).
                                     { apply Pointer.eqb_neq. exact HNN_nxt. }
                                     rewrite Hceqb in Hcmp. cbn in Hcmp.
                                     inversion Hcmp; subst.
                                     unfold Iw. cbn.
                                     split. exact Hheap.
                                     exists nd, la_pref, (vh :: vx :: la_rest).
                                     split. exact Hpart.
                                     split. discriminate.
                                     split. exact Hbn_s.
                                     split. exact Hpath_nd.
                                     split. exact Hreach_nd.
                                     split. exact (ex_intro _ st_pop Hpop).
                                     constructor; [intros _;
                                       exact (ex_intro _ vh (ex_intro _ vx
                                         (ex_intro _ la_rest eq_refl))) |
                                       intro H; discriminate].
                       *** eapply sep_weaken. apply sep_read_ptr_triple.
                           intros s (Hheap & la_pref & la_suff & Hpart & Hne_suff &
                                     Hbn_s & Hpath_nd & Hreach_nd & Hshift_np & [st_pop Hpop]).
                           destruct la_suff as [ | vh la_suff_tail].
                           { exact (False_rect _ (Hne_suff eq_refl)). }
                           pose proof (llist_reach_unfold (heap s_init) nd vh la_suff_tail
                                         Hreach_nd)
                             as (_ & _ & _ & _ & _ & np_ref & nxt_ref &
                                 _ & Hshift_ref & _ & _ & _ & Hlk_ref & _).
                           assert (Hnp_eq : np = np_ref).
                           { injection (eq_trans (eq_sym Hshift_np) Hshift_ref) as Heq.
                             exact Heq. }
                           subst np_ref.
                           exists nxt_ref. split. rewrite Hheap. exact Hlk_ref.
                           split. exact Hheap.
                           exists la_pref, (vh :: la_suff_tail).
                           split. exact Hpart.
                           split. discriminate.
                           split. exact Hbn_s.
                           split. exact Hpath_nd.
                           split. exact Hreach_nd.
                           split. exact Hshift_np.
                           split. exact Hlk_ref.
                           exact (ex_intro _ st_pop Hpop).
                   +++ eapply sep_weaken. apply sep_shift_fw_ptr_triple.
                       intros s (Hheap & la_pref & la_suff & Hpart & Hne_suff &
                                 Hbn_s & Hpath_nd & Hreach_nd & [st_pop Hpop]).
                       destruct la_suff as [ | vh la_suff_tail].
                       { exact (False_rect _ (Hne_suff eq_refl)). }
                       pose proof (llist_reach_unfold (heap s_init) nd vh la_suff_tail
                                     Hreach_nd)
                         as (_ & HWV_nd & _ & _ & _ & np_ref & _ &
                             _ & Hshift_ref & HWVnp_ref & _ & _ & _ & _).
                       split. rewrite Hheap. exact HWV_nd.
                       exists np_ref. split. exact Hshift_ref.
                       split. rewrite Hheap. exact HWVnp_ref.
                       exact (conj Hheap (ex_intro _ la_pref
                         (ex_intro _ (vh :: la_suff_tail)
                         (conj Hpart (conj Hne_suff (conj Hbn_s (conj Hpath_nd
                           (conj Hreach_nd (conj Hshift_ref
                             (ex_intro _ st_pop Hpop)))))))))).
               --- eapply sep_weaken. apply sep_read_var_triple.
                   intros s [b HIw].
                   destruct HIw as (Hheap & curr & la_pref & la_suff &
                                    Hpart & Hne_suff & Hbn_s & Hpath_curr & Hreach_curr &
                                    Hpop_ex & _ & _).
                   exists curr. split. exact Hbn_s.
                   exact (conj Hheap (ex_intro _ la_pref (ex_intro _ la_suff
                     (conj Hpart (conj Hne_suff (conj Hbn_s (conj Hpath_curr
                       (conj Hreach_curr Hpop_ex)))))))).
            ** eapply sep_bind_rule with
                 (Q := fun (nd : Pointer.t) s =>
                   heap s = heap s_init /\
                   exists la_pref vh vx la_rest,
                     (v :: la') = la_pref ++ (vh :: vx :: la_rest) /\
                     Store.BindsTo n_node (encode nd) (store s) /\
                     llist_path (heap s_init) l0 la_pref nd /\
                     llist_reach (heap s_init) nd (vh :: vx :: la_rest) /\
                     exists st_pop, Store.pop (store s) = Some st_pop).
               --- intro nd.
                   eapply sep_bind_rule with
                     (Q := fun (np : Pointer.t) s =>
                       heap s = heap s_init /\
                       exists la_pref vh vx la_rest,
                         (v :: la') = la_pref ++ (vh :: vx :: la_rest) /\
                         Store.BindsTo n_node (encode nd) (store s) /\
                         llist_path (heap s_init) l0 la_pref nd /\
                         llist_reach (heap s_init) nd (vh :: vx :: la_rest) /\
                         Pointer.shift_fw nd 1%N = Some np /\
                         exists st_pop, Store.pop (store s) = Some st_pop).
                   +++ intro np.
                       eapply sep_bind_rule with
                         (Q := fun (nxt : Pointer.t) s =>
                           heap s = heap s_init /\
                           exists la_pref vh vx la_rest,
                             (v :: la') = la_pref ++ (vh :: vx :: la_rest) /\
                             Store.BindsTo n_node (encode nd) (store s) /\
                             llist_path (heap s_init) l0 la_pref nd /\
                             nd <> Pointer.NULL /\
                             Pointer.shift_fw nd 1%N = Some np /\
                             Heap.lookup (heap s_init) np =
                               Some (StorablePtr.ptr_encode nxt) /\
                             llist_reach (heap s_init) nxt (vx :: la_rest) /\
                             exists st_pop, Store.pop (store s) = Some st_pop).
                       *** intro nxt.
                           eapply sep_weaken. apply sep_write_var_triple.
                           intros s (Hheap & la_pref & vh & vx & la_rest & Hpart &
                                     Hbn_s & Hpath_nd & HNN_nd & Hshift_np & Hlk_np &
                                     Hreach_nxt & [st_pop Hpop]).
                           destruct (pop_mutate_unchecked_fwd (store s) n_node (encode nxt)
                                       (ex_intro _ st_pop Hpop)) as [st_pop' Hpop'].
                           exists (encode nd). split. exact Hbn_s.
                           destruct la_rest as [ | v2 la_rest'].
                           ---- exists false. unfold Iw. cbn [heap store].
                                split. exact Hheap.
                                exists nxt, (la_pref ++ [vh]), [vx].
                                split.
                                { rewrite <- app_assoc. cbn. exact Hpart. }
                                split. discriminate.
                                split.
                                { apply Store.Facts.mutate_unchecked_spec_ll; reflexivity. }
                                split.
                                { exact (llist_path_app_step _ l0 la_pref nd vh np nxt
                                           Hpath_nd HNN_nd Hshift_np Hlk_np). }
                                split. exact Hreach_nxt.
                                split. exact (ex_intro _ st_pop' Hpop').
                                constructor; [intro H; discriminate |
                                  intros _; exact (ex_intro _ vx eq_refl)].
                           ---- exists true. unfold Iw. cbn [heap store].
                                split. exact Hheap.
                                exists nxt, (la_pref ++ [vh]), (vx :: v2 :: la_rest').
                                split.
                                { rewrite <- app_assoc. cbn. exact Hpart. }
                                split. discriminate.
                                split.
                                { apply Store.Facts.mutate_unchecked_spec_ll; reflexivity. }
                                split.
                                { exact (llist_path_app_step _ l0 la_pref nd vh np nxt
                                           Hpath_nd HNN_nd Hshift_np Hlk_np). }
                                split. exact Hreach_nxt.
                                split. exact (ex_intro _ st_pop' Hpop').
                                constructor; [intros _;
                                  exact (ex_intro _ vx (ex_intro _ v2
                                    (ex_intro _ la_rest' eq_refl))) |
                                  intro H; discriminate].
                       *** eapply sep_weaken. apply sep_read_ptr_triple.
                           intros s (Hheap & la_pref & vh & vx & la_rest & Hpart &
                                     Hbn_s & Hpath_nd & Hreach_nd & Hshift_np & [st_pop Hpop]).
                           pose proof (llist_reach_unfold (heap s_init) nd vh (vx :: la_rest)
                                         Hreach_nd)
                             as (HNN_nd & _ & _ & _ & _ & np_ref & nxt_ref &
                                 _ & Hshift_ref & _ & _ & _ & Hlk_ref & Htail_ref).
                           assert (Hnp_eq : np = np_ref).
                           { injection (eq_trans (eq_sym Hshift_np) Hshift_ref) as Heq.
                             exact Heq. }
                           subst np_ref.
                           exists nxt_ref. split. rewrite Hheap. exact Hlk_ref.
                           exact (conj Hheap (ex_intro _ la_pref (ex_intro _ vh
                             (ex_intro _ vx (ex_intro _ la_rest
                             (conj Hpart (conj Hbn_s (conj Hpath_nd (conj HNN_nd (conj Hshift_np
                               (conj Hlk_ref (conj Htail_ref
                                 (ex_intro _ st_pop Hpop))))))))))))).
                   +++ eapply sep_weaken. apply sep_shift_fw_ptr_triple.
                       intros s (Hheap & la_pref & vh & vx & la_rest & Hpart &
                                 Hbn_s & Hpath_nd & Hreach_nd & [st_pop Hpop]).
                       pose proof (llist_reach_unfold (heap s_init) nd vh (vx :: la_rest)
                                     Hreach_nd)
                         as (_ & HWV_nd & _ & _ & _ & np_ref & _ &
                             _ & Hshift_ref & HWVnp_ref & _ & _ & _ & _).
                       split. rewrite Hheap. exact HWV_nd.
                       exists np_ref. split. exact Hshift_ref.
                       split. rewrite Hheap. exact HWVnp_ref.
                       exact (conj Hheap (ex_intro _ la_pref (ex_intro _ vh
                         (ex_intro _ vx (ex_intro _ la_rest
                         (conj Hpart (conj Hbn_s (conj Hpath_nd (conj Hreach_nd
                           (conj Hshift_ref (ex_intro _ st_pop Hpop))))))))))).
               --- eapply sep_weaken. apply sep_read_var_triple.
                   intros s (Hheap & curr & la_pref & la_suff &
                             Hpart & Hne_suff & Hbn_s & Hpath_curr & Hreach_curr &
                             [st_pop Hpop] & Htrue & _).
                   destruct (Htrue eq_refl) as [vh [vx [la_rest Hla_eq]]]. subst la_suff.
                   exists curr. split. exact Hbn_s.
                   exact (conj Hheap (ex_intro _ la_pref (ex_intro _ vh
                     (ex_intro _ vx (ex_intro _ la_rest
                     (conj Hpart (conj Hbn_s (conj Hpath_curr
                       (conj Hreach_curr (ex_intro _ st_pop Hpop)))))))))).
        -- intros s ->.
           destruct la' as [ | vx la''].
           ++ exists false. unfold Iw.
              split. reflexivity.
              exists l0, [], [v].
              split. cbn. reflexivity.
              split. discriminate.
              split. exact Hbn_init.
              split. exact (Path_nil (heap s_init) l0).
              split. exact Hreach_init.
              split. exact (ex_intro _ st_pop0 Hpop_st1).
              split. intro H; discriminate.
              intro . exact (ex_intro _ v eq_refl).
           ++ exists true. unfold Iw.
              split. reflexivity.
              exists l0, [], (v :: vx :: la'').
              split. cbn. reflexivity.
              split. discriminate.
              split. exact Hbn_init.
              split. exact (Path_nil (heap s_init) l0).
              split. exact Hreach_init.
              split. exact (ex_intro _ st_pop0 Hpop_st1).
              split. intro .
                exact (ex_intro _ v (ex_intro _ vx (ex_intro _ la'' eq_refl))).
              intro H; discriminate.
    + eapply sep_weaken. apply sep_eq_ptr_triple_cmp.
      intros s [HP Hstar].
      destruct Hstar as (sa & sb & Hst_sa & Hst_sb & Hab & Hlla & Hllb).
      pose proof (substate_of_partition_l Hab) as Hsub_sa.
      pose proof (llist_reach_of_llist l0 (v :: la') sa Hlla) as Hreach0.
      pose proof (llist_reach_monotone _ _ l0 (v :: la') Hsub_sa Hreach0) as Hreach_s.
      pose proof (llist_reach_unfold _ l0 v la' Hreach_s)
        as (HNN_l0 & HWV_l0 & HCmp_l0 & _ & _).
      split. exact HWV_l0.
      split. right; right; reflexivity.
      split. exact HCmp_l0.
      split. exact Pointer.AllowsNull.
      intros b Hcmp.
      assert (Hallow_l0 : Pointer.allows l0 Operation.Cmp = true).
      { destruct (Pointer.allows_spec l0 Operation.Cmp); [reflexivity | contradiction]. }
      assert (Hallow_null : Pointer.allows Pointer.NULL Operation.Cmp = true).
      { destruct (Pointer.allows_spec Pointer.NULL Operation.Cmp);
        [reflexivity | exact (False_rect _ (n Pointer.AllowsNull))]. }
      unfold Pointer.cmp in Hcmp.
      rewrite Hallow_l0, Hallow_null in Hcmp. cbn in Hcmp.
      assert (Hceqb : Pointer.eqb l0 Pointer.NULL = false).
      { apply Pointer.eqb_neq. exact HNN_l0. }
      rewrite Hceqb in Hcmp. cbn in Hcmp.
      inversion Hcmp; subst.
      exact (conj HP (ex_intro _ sa (ex_intro _ sb
        (conj Hst_sa (conj Hst_sb (conj Hab (conj Hlla Hllb))))))).
  Qed.

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
