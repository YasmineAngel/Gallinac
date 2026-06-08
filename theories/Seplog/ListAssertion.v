From Stdlib Require Import
FunctionalExtensionality PropExtensionality List Psatz Arith NArith.
Import ListNotations.
From GallinaC.Imp Require Export Store Heap Primitives.
Import Heap.Facts.
From GallinaC.Seplog Require Export Pred GenAssertion.

Local Open Scope state_scope.
Local Open Scope heap_scope.
Local Open Scope separation_scope.

Definition One {St Hp} (a: Addr.t) (v: memval): Pred (State St Hp) :=
  fun s => heap s = a |-> v.

Definition Two {St Hp} (a:Addr.t) (v1 v2:memval): Pred (State St Hp) :=
  fun s => heap s = of_list a [v1; v2].

Notation "a ||~> v" :=
  (One a v)
    (at level 35, no associativity).

Notation "a ||~> ( v1 , v2 )" :=
  (Two a v1 v2)
    (at level 35, no associativity).

Lemma Two_star {St Hp}: forall a v1 v2,
    |- ((a ||~> (v1, v2)) <==>
          (a ||~> v1) ** ((Addr.shift_fw a 1%N) ||~> v2): Pred (State St Hp)).
Proof.
  intros a v1 v2.
  unfold One,Two.
  apply impl_antisym_taut.
  - intros s Hs.
    exists
      (mkState (store s) (a |-> v1)),
      (mkState (store s) ((Addr.shift_fw a 1%N) |-> v2)); cbn.
    repeat split; auto.
    unfold of_list in Hs.
    cbn in Hs.
    rewrite op_id_r in Hs.
    destruct ((Addr.shift_fw a 1) |-> v2 $+ a |-> v1) as [ hp | ] eqn:E; [ rewrite op_comm; congruence | ].
    destruct (proj1 (@one_ne_addr Hp (Addr.shift_fw a 1) a v2 v1)).
    intros contra; destruct a; cbn in *; inversion contra; lia.
    congruence.
  - intros s ( s1 & s2 & Hst1 & Hst2 & HPartition & Hfirst & Hsecond ).
Abort.

Fixpoint llist {St Hp} (p:Pointer.t) (l: list memval) : Pred (State St Hp) :=
  match l with
  | [] => [| p = Pointer.NULL |]
  | v :: l' =>
      [| p <> Pointer.NULL /\
         Pointer.Allows p Operation.Read /\
         exists next_ptr,
           Pointer.shift_fw p 1%N = Some next_ptr /\
           Pointer.Allows next_ptr Operation.Read /\
           Pointer.Allows next_ptr Operation.Write |] **
      Exists a p', [| Pointer.References p a |] ** a ||~> (v, VPtr p') ** llist p' l'
  end.

Lemma llist_null {St Hp}: forall l,
    |- @llist St Hp Pointer.NULL l <==> [| l = [] |].
Proof.
  intro l.
  apply impl_antisym_taut; intros s Hm; unfold lift in *.
  -
    (destruct l; cbn in Hm); [ split; auto; now destruct Hm  | ].
    destruct Hm as (s1 & s2 & _ & _ & _ & Hlift & _).
    destruct Hlift as ((HNULL & _) & _).
    contradiction.
  -
    destruct Hm; subst.
    split; auto.
Qed.

Lemma llist_allows_read {St Hp}: forall p v l s,
  @llist St Hp p (v :: l) s -> Pointer.Allows p Operation.Read.
Proof.
  intros p v l s Hll.
  cbn in Hll.
  destruct Hll as (s1 & s2 & _ & _ & _ & ((_ & HAR & _) & _) & _).
  exact HAR.
Qed.

Lemma llist_wvalid {St Hp}: forall p v l s,
  @llist St Hp p (v :: l) s -> Heap.Facts.WValid (heap s) p.
Proof.
  intros p v l s Hll.
  cbn in Hll.
  destruct Hll as (sA & sB & _ & _ & HpartAB & HliftA & HexistsB).
  destruct HliftA as ((HNN & _) & HhA).
  destruct HexistsB as (a & p0 & HexistsB2).
  destruct HexistsB2 as (sC & sD & _ & _ & HpartCD & HliftC & HstarDE).
  destruct HliftC as (HRefState & s2 & HstC1 & HstC2 & HpartRef & Hrefs & Hcell).
  left.
  exists a, v.
  split.
  - destruct Hrefs as [Hrefs _]. exact Hrefs.
  - rewrite HhA, op_id_l in HpartAB.
    injection HpartAB as HhB.
    unfold Two, One in Hcell.
    unfold of_list in Hcell.
    cbn in Hcell.
    rewrite op_id_r in Hcell.
    
    assert (Hsub2 : heap s2 $<= heap sB).
    { eapply substate_tran.
      - apply substate_of_partition_r in HpartRef. exact HpartRef.
      - apply substate_of_partition_l in HpartCD. exact HpartCD. }
    
    rewrite HhB in Hsub2.
    rewrite Hcell in Hsub2.
    
       eapply substate_tran with (b := heap sB).
       -- assert (Hcell_sub : a |-> v $<= heap s2).
    { 
      rewrite Hcell.
      destruct ((Addr.shift_fw a 1) |-> (VPtr p0) $+ a |-> v) eqn:Heqn.
      - cbn.
        apply (proj2 (one_discriminate _ _ _ _ Heqn a v)).
        right. split.
          intros contra. 
          destruct a; cbn in *; inversion contra; lia.
         apply substate_refl.
        - exfalso.
        destruct (proj1 (@one_ne_addr Hp (Addr.shift_fw a 1) a (VPtr p0) v)).
        rewrite op_comm in Heqn.
        * intros contra. 
          destruct a; cbn in *; inversion contra; lia.
        * congruence.
      }
    rewrite <- Hcell in Hsub2. 
    rewrite HhB.
    eapply substate_tran; [exact Hcell_sub | exact Hsub2].
  -- rewrite HhB. apply substate_refl.
Qed.

Lemma llist_allows_cmp {St Hp}: forall p v l s,
  @llist St Hp p (v :: l) s -> Pointer.Allows p Operation.Cmp.
Proof.
  intros p v l s Hll.
  apply llist_allows_read in Hll.
  inversion Hll; subst.
  - apply Pointer.AllowsLive.
    eapply Provenance.allows_tran; [eassumption | constructor].
Qed.

Lemma shift_fw_references: forall p a n next_ptr,
  Pointer.References p a ->
  Pointer.shift_fw p n = Some next_ptr ->
  Pointer.References next_ptr (Addr.shift_fw a n).
Proof.
  intros p a n next_ptr HRef Hshift.
  inversion HRef; subst.
  unfold Pointer.shift_fw in Hshift.
  destruct (Provenance.within a prov && Provenance.within (Addr.shift_fw a n) prov)%bool eqn:Hcond.
  - inversion Hshift; subst. 
    constructor.
  - discriminate Hshift.
Qed.

Lemma llist_shift_fw_next {St Hp}: forall p v l s,
  @llist St Hp p (v :: l) s ->
  exists next_ptr,
    Pointer.shift_fw p 1%N = Some next_ptr /\
    Pointer.Allows next_ptr Operation.Read.
Proof.
  intros p v l s Hll.
  cbn in Hll.
  destruct Hll as (s1 & s2 & _ & _ & _ & ((_ & _ & HsfA) & _) & _).
  destruct HsfA as (next_ptr & HShift & HRead & _).
  exact (ex_intro _ next_ptr (conj HShift HRead)).
Qed.

Lemma llist_allows_write_next {St Hp}: forall p v l s next_ptr,
  @llist St Hp p (v :: l) s ->
  Pointer.shift_fw p 1%N = Some next_ptr ->
  Pointer.Allows next_ptr Operation.Write.
Proof.
  intros p v l s next_ptr Hll Hshift.
  cbn in Hll.
  destruct Hll as (s1 & s2 & _ & _ & _ & ((_ & _ & HsfA) & _) & _).
  destruct HsfA as (next_ptr' & HShift' & _ & HWrite).
  rewrite HShift' in Hshift.
  injection Hshift as <-.
  exact HWrite.
Qed.

Lemma llist_wvalid_next {St Hp}: forall p v l s next_ptr,
  @llist St Hp p (v :: l) s ->
  Pointer.shift_fw p 1%N = Some next_ptr ->
  Heap.Facts.WValid (heap s) next_ptr.
Proof.
  intros p v l s next_ptr Hll Hshift.
  cbn in Hll.
  destruct Hll as (sA & sB & _ & _ & HpartAB & HliftA & HexistsB).
  destruct HliftA as ((HNN & _ & _) & HhA).
  destruct HexistsB as (a & p0 & HexistsB2).
  destruct HexistsB2 as (sC & sD & _ & _ & HpartCD & HliftC & HstarDE).
  destruct HliftC as (HRefState & HhC).
  destruct HhC as [s2 (HstC1 & HstC2 & HpartRef & Hrefs & Hcell)].
  assert (HhB : heap sB = heap s).
  { rewrite HhA, op_id_l in HpartAB. now injection HpartAB. }
  left. exists (Addr.shift_fw a 1%N), (VPtr p0).
  split.
  - destruct Hrefs as [Hrefs _].
    exact (shift_fw_references p a 1%N next_ptr Hrefs Hshift).
  - assert (Hcell_sub : (Addr.shift_fw a 1) |-> (VPtr p0) $<= heap s2).
    {
      unfold Two, One in Hcell. rewrite Hcell.
      pose proof (proj1 (@of_list_spec Hp a [v; VPtr p0] 1 (VPtr p0))) as Hspec.
      cbn in Hspec.
      apply (Hspec eq_refl).
    }
    eapply substate_tran.
    -- exact Hcell_sub.
    -- eapply substate_tran.
      + apply substate_of_partition_r in HpartRef. exact HpartRef.
      + eapply substate_tran.
        * apply substate_of_partition_l in HpartCD. exact HpartCD.
        * rewrite HhB. apply substate_refl.
Qed.

Lemma list_nonnull {St Hp}:
  forall p l,
    |- ([| p <> Pointer.NULL |] : Pred (State St Hp)) ** llist p l
         ===>
         [| p <> Pointer.NULL |]  **
         Exists (v : memval)
         (l' : list memval)
         (a: Addr.t)
         (p' : Pointer.t),
  [| Pointer.References p a |] **
    [| l = v :: l' |] **
    a ||~> (v, VPtr p') **
    llist p' l'.
Proof.
  intros p l.
  apply cond_star_semicancel_l with
    (R := [| p <> Pointer.NULL |])
    (P := llist p l)
    (Q := (Exists (v : memval)
             (l' : list memval)
             (a : Addr.t)
             (p': Pointer.t),
            [| Pointer.References p a |] **
              [|l = v :: l'|] **
              a ||~> (v, VPtr p') **
              llist p' l'));
    [apply heapless_lift | now apply equiv_refl_taut | apply equiv_refl_taut | ].
  destruct l; cbn.
  -
    intros s ( _ & _ & _ & _ & _ & [ H1 _ ] & [ H2 _ ] ).
    contradiction.
  - intros s Hs.
    apply star_assoc in Hs.
    apply Exists_star_right in Hs; destruct Hs as ( a & Hs ).
    apply Exists_star_right in Hs; destruct Hs as ( p' & Hs ).
    destruct Hs as (snull & s' & Hst1 & Hst2 & HPartition1 & HNull &  H ).
    (*apply p_p_p in HNull.*)
    destruct HNull as ( HNull & HEmp ).
    exists m, l, a.
    (* TODO return to after IR *)
    (* destruct Hs as ( ?a & ?H ). *)
    (*     (rewrite <- star_assoc). *)
    (*     rewrite p_p_p. *)
    (*     rewrite <- Exists_star_right. *)
    (*     apply skolem_left. *)
    (*     intro a. *)
    (*     apply Exists_impl. *)
    (*     apply inst_Exists with (x := v). *)
    (*     apply Exists_impl. *)
    (*     apply inst_Exists with (x := l). *)
    (*     apply Exists_impl. *)
    (*     apply inst_Exists with (x := a). *)
    (*     apply star_weaken_l; [apply heapless_lift | apply impl_refl]. *)
    (*     intros s [ p ( s1 & s2 & Hr1 & Hr2 & HPartition & (s3 & s4 & Hr3 & Hr4 & HPartition' & HReferences & HOne) & Hllist ) ]. *)
    (*     exists p. *)
    (*     eexists (mk_state (reg s) (mem s1)); eexists (mk_state (reg s) (mem s2)). *)
    (*     split; [ now rewrite reg_state | ]. *)
    (*     split; [ now rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite mem_state | ]. *)
    (*     split. *)
    (*     eexists (mk_state (reg s) (mem s3)); eexists (mk_state (reg s) (mem s4)). *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite mem_state | split ]. *)
    (*     eexists (mk_state (reg s) (mem s3)); eexists (mk_state (reg s) $0). *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ now repeat rewrite reg_state | ]. *)
    (*     split; [ repeat rewrite mem_state; now apply Partition_is_empty_r | split ]. *)
    (*     rewrite Hr1; rewrite Hr3; rewrite state_reg_mem; assumption. *)
    (*     constructor; try rewrite mem_state; reflexivity. *)
    (*     rewrite Hr1; rewrite Hr4; rewrite state_reg_mem; assumption. *)
    (*     rewrite Hr2; rewrite state_reg_mem; assumption. *)
    (* Qed. *)
Abort.

Lemma cond_list_nonnull {St: Store.Store} {Hp: Heap} (P U V: Pred (State St Hp)):
  forall  r l,
    U =  [|r <> Pointer.NULL|] ** llist r l ** P ->
    |- [|r <> Pointer.NULL|]  **
     (Exists (v : memval)
        (l' : list memval)
        (a: Addr.t)
      (p' : Pointer.t),
       [| Pointer.References r a |] **
       [| l = v :: l' |] **
         a ||~> (v, VPtr p') **
      llist p' l') ** P  ===> V
      ->
     |- U ===> V.
Proof.
  intros r l HU HP;subst.
  (* TODO return to after IR *)
(* apply impl_trans with (Q := [|r <> Pointer.NULL|] ** *)
(*           (Exists (v : memval) *)
(*              (l' : list memval) *)
(*              (a: Addr.t) *)
(*              (p' : Pointer.t), *)
(*             [| Pointer.References r a |] ** *)
(*             [|l = v :: l'|] ** *)
(*               a ||~> (v, VPtr p') ** *)
(*               llist p' l') ** P); auto. *)
(* apply star_cancel_r. *)
(* eapply list_nonnull. *)
(* Qed. *)
Admitted.

Lemma llist_indep_regs {St: Store.Store} {Hp: Heap}: forall p l,
  @indep_store St Hp (llist p l).
Proof.
  intros p l.
  generalize dependent p.
  induction l; intros p s s' Hheap Hll.
  - cbn in Hll |- *.
    destruct Hll as (HNull & Hh).
    split; [exact HNull | congruence].
  - cbn in Hll |- *.
    rename IHl into IHl'.
    cbn in Hll.
    destruct Hll as (sA & sB & HstA & HstB & HpartAB & HliftA & HexistB).
    exists {| store := store s'; heap := heap sA |},
           {| store := store s'; heap := heap sB |}.
    split; [reflexivity | split; [reflexivity | split]].
    + cbn. rewrite <- Hheap. exact HpartAB.
    + split.
      * exact HliftA.
      * cbn in HexistB.
        destruct HexistB as (addr & p0 & sC & sD & HstC & HstD & HpartCD & HliftC & HstarDE).
        exists addr, p0.
        exists {| store := store s'; heap := heap sC |},
               {| store := store s'; heap := heap sD |}.
        split; [reflexivity | split; [reflexivity | split]].
        { cbn. exact HpartCD. }
        split.
        { cbn in HliftC |- *.
          destruct HliftC as (sE & sF & HstE & HstF & HpartEF & HtwoE & HllistF).
          exists {| store := store s'; heap := heap sE |},
                 {| store := store s'; heap := heap sF |}.
          split; [reflexivity | split; [reflexivity | split]].
          - cbn. exact HpartEF.
          - split; [exact HtwoE | exact HllistF]. }
        { apply (IHl' p0 sD {| store := store s'; heap := heap sD |} eq_refl HstarDE). }
Qed.


Fixpoint llist_reach {Hp: Heap} (h: Hp) (p: Pointer.t) (l: list memval) : Prop :=
  match l with
  | [] => p = Pointer.NULL
  | v :: l' =>
      p <> Pointer.NULL /\
      Heap.Facts.WValid h p /\
      Pointer.Allows p Operation.Cmp /\
      Pointer.Allows p Operation.Read /\
      exists a next_ptr p0,
        Pointer.References p a /\
        Pointer.shift_fw p 1%N = Some next_ptr /\
        Heap.Facts.WValid h next_ptr /\
        Pointer.Allows next_ptr Operation.Read /\
        Pointer.Allows next_ptr Operation.Write /\
        Heap.lookup h next_ptr = Some (StorablePtr.ptr_encode p0) /\
        llist_reach h p0 l'
  end.

Lemma wvalid_mono {Hp: Heap}: forall (h h': Hp) p,
  h $<= h' -> Heap.Facts.WValid h p -> Heap.Facts.WValid h' p.
Proof.
  intros h h' p Hsub HWV.
  destruct HWV as [HV | [HPO | HNULL]].
  - left. destruct HV as (addr & v0 & HRefv & HSub0).
    exists addr, v0. exact (conj HRefv (substate_tran _ _ _ HSub0 Hsub)).
  - right; left. destruct HPO as (addr & addr' & v0 & HRefv & HShift & HSub0).
    exists addr, addr', v0. exact (conj HRefv (conj HShift (substate_tran _ _ _ HSub0 Hsub))).
  - right; right. exact HNULL.
Qed.

Lemma lookup_mono {Hp: Heap}: forall (h h': Hp) p v,
  h $<= h' -> Heap.lookup h p = Some v -> Heap.lookup h' p = Some v.
Proof.
  intros h h' p v Hsub HLookup.
  apply (proj1 (Heap.lookup_some h' p v)).
  apply (proj2 (Heap.lookup_some h p v)) in HLookup.
  destruct HLookup as (addr & HRef & HAll & HSub0).
  exact (ex_intro _ addr (conj HRef (conj HAll (substate_tran _ _ _ HSub0 Hsub)))).
Qed.

Lemma llist_reach_monotone {H : Heap}: forall (h h' : H) p l,
  h $<= h' ->
  llist_reach h p l ->
  llist_reach h' p l.
Proof.
  intros h h' p l Hsub.
  revert p.
  induction l; intros p Hreach.
  - exact Hreach.
  - destruct Hreach as (HNN & HWV & HCmp & HRead & addr & next_ptr & p0
                        & HRef & Hshift & HWVnp & HRnp & HWrite & HLookup & Htail).
    cbn.
    repeat split.
  * exact HNN.
  * eapply wvalid_mono; [exact Hsub | exact HWV].
  * exact HCmp.
  * exact HRead.
  * exists addr, next_ptr, p0.
    repeat split.
    + exact HRef.
    + exact Hshift.
    + eapply wvalid_mono; [exact Hsub | exact HWVnp].
    + exact HRnp.
    + exact HWrite.
    + eapply lookup_mono; [exact Hsub | exact HLookup].
    + apply (IHl p0 Htail).
Qed.

Lemma llist_reach_null_iff {Hp: Heap}: forall (h: Hp) p l,
  llist_reach h p l ->
  (p = Pointer.NULL <-> l = []).
Proof.
  intros h p l Hreach.
  split.
  - intros HNull. destruct l as [ | v l']; [ reflexivity | ].
    cbn in Hreach. destruct Hreach as (HNN & _). contradiction.
  - intros Hl. subst. cbn in Hreach. exact Hreach.
Qed.

Lemma llist_reach_of_llist {St Hp}: forall p l s,
  @llist St Hp p l s ->
  llist_reach (heap s) p l.
Proof.
  intros p l.
  revert p.
  induction l.
  - intros p s Hll.
    cbn in Hll |- *.
    destruct Hll as [HNull Hempty].
    exact HNull.
  - intros p s Hll.
    rename l into l'.
    rename IHl into IHl'.
    pose proof (llist_wvalid p a l' s Hll) as HWV_p.
    pose proof (llist_allows_cmp p a l' s Hll) as HCmp_p.
    pose proof (llist_allows_read p a l' s Hll) as HRead_p.
    pose proof (llist_shift_fw_next p a l' s Hll) as [next_ptr_loc [HShift_loc HAll2_loc]].
    cbn in Hll |- *.
    destruct Hll as (sA & sB & HstA & HstB & HpartAB & HliftA & HexistB).
    cbn in HliftA.
    destruct HliftA as [HNN HemptyA].
    destruct HexistB as (addr & p0 & sC & sD & HstC & HstD & HpartCD & HliftC & HstarDE).
    destruct HliftC as (HRefState & HhC).
    destruct HhC as [s2 (HstE & HstF & HpartEF & Hrefs & Hcell_pt)].
    destruct Hrefs as [HRef HemptyE].
    destruct HNN as [HNN_ptr [HAll1 [next_ptr [HShift [HAll2 HWrite]]]]].
    repeat split.
    + exact HNN_ptr.
    + exact HWV_p.
    + exact HCmp_p.
    + exact HRead_p.
    + exists addr, next_ptr, p0.
      repeat split.
      * exact HRef.
      * exact HShift.
      * eapply llist_wvalid_next; [ | exact HShift ].
        cbn. exists sA, sB. repeat split; eauto.
        cbn. repeat split; eauto.
        exists addr, p0, sC, sD. repeat split; eauto.
        exists HRefState, s2. repeat split; eauto.
      * exact HAll2.
      * exact HWrite.
      * apply -> lookup_some.
        exists (Addr.shift_fw addr 1%N).
        repeat split.
        -- eapply shift_fw_references; [ exact HRef | exact HShift ].
        -- exact HAll2.
        -- assert (Hsub2 : heap s2 $<= heap sB).
           { eapply substate_tran.
             - apply substate_of_partition_r in HpartEF. exact HpartEF.
             - apply substate_of_partition_l in HpartCD. exact HpartCD. }
           assert (Hsub_all : heap s2 $<= heap s).
           { eapply substate_tran; [ exact Hsub2 | ].
             apply substate_of_partition_r in HpartAB. exact HpartAB. }
           unfold Two in Hcell_pt.
           assert (H_of_list : (Addr.shift_fw addr 1%N) |-> (StorablePtr.ptr_encode p0) $<= heap s2).
           { rewrite Hcell_pt.
             pose proof (proj1 (Facts.of_list_spec (M := Hp) addr [a; VPtr p0] 1%nat (VPtr p0))) as Hspec.
             cbn in Hspec.
             apply Hspec.
             reflexivity. }
           eapply substate_tran; [ exact H_of_list | exact Hsub_all ].
    * assert (HsubD : heap sD $<= heap s).
      { eapply substate_tran.
        - apply substate_of_partition_r in HpartCD. exact HpartCD.
        - apply substate_of_partition_r in HpartAB. exact HpartAB. }
      eapply llist_reach_monotone; [ exact HsubD | ].
      apply (IHl' p0 sD HstarDE).
Qed.

Lemma llist_tl {St Hp}: forall p v l' s,
  @llist St Hp p (v :: l') s ->
  exists next_ptr p',
    Pointer.shift_fw p 1%N = Some next_ptr /\
    Heap.lookup (heap s) next_ptr = Some (encode p') /\
    llist_reach (heap s) p' l'.
Proof.
  intros p v l' s Hll.
  pose proof (llist_reach_of_llist p (v :: l') s Hll) as Hreach.
  cbn in Hreach.
  destruct Hreach as (_ & _ & _ & _ & _ & next_ptr & p'
                      & _ & Hshift & _ & _ & _ & HLookup & Htail).
  exact (ex_intro _ next_ptr (ex_intro _ p' (conj Hshift (conj HLookup Htail)))).
Qed.

Lemma llist_star_mutate {St Hp}:
  forall (nd acc old_next: Pointer.t) (v: memval) (l_rem l_acc: list memval)
         (node_next_ptr: Pointer.t)
         (s: State St Hp),
  (llist nd (v :: l_rem) ** llist acc l_acc) s ->
  Pointer.shift_fw nd 1%N = Some node_next_ptr ->
  Heap.lookup (heap s) node_next_ptr = Some (encode old_next) ->
  exists h',
    Heap.mutate (heap s) node_next_ptr (encode acc) = Some h' /\
    (llist nd (v :: l_acc) ** llist old_next l_rem)
      {| store := store s; heap := h' |}.
Proof.
  intros nd acc old_next v l_rem l_acc node_next_ptr s H_star H_shift H_lookup.
  destruct H_star as (s_a & s_b & _ & _ & H_ab & H_ll_a & H_ll_b).
  cbn in H_ll_a.
  destruct H_ll_a as (sLift & sRest & _ & _ & H_lr & H_lp & H_re).
  cbn in H_lp.
  destruct H_lp as [[HNN [HRead [np [H_sl [HReadNP HWriteNP]]]]] H_eLift].
  rewrite H_eLift, op_id_l in H_lr. injection H_lr as H_restH.
  destruct H_re as (addr_nd & p0 & sCR & sTL & _ & _ & H_cr_tl & H_cr & H_tl).
  destruct H_cr as (sE & sF & _ & _ & H_ef & H_refE & H_twoF).
  cbn in H_refE.
  destruct H_refE as [H_ref_nd H_eRef].
  rewrite H_eRef, op_id_l in H_ef. injection H_ef as H_fH.
  unfold Two in H_twoF.
  assert (H_hCR : heap sCR = of_list addr_nd [v; VPtr p0]) by congruence.
  rewrite H_restH, H_hCR in H_cr_tl.
  assert (H_ne : Addr.shift_fw addr_nd 1 <> addr_nd).
  { intros c. destruct addr_nd; cbn in c; inversion c; lia. }
  destruct (proj1 (@one_ne_addr Hp (Addr.shift_fw addr_nd 1) addr_nd (VPtr p0) v) H_ne) as (h2old & H2old).
  assert (H_ol_old : of_list addr_nd [v; VPtr p0] = h2old).
  { unfold of_list; cbn; rewrite op_id_r; cbn; now rewrite H2old. }
  destruct (proj1 (@one_ne_addr Hp (Addr.shift_fw addr_nd 1) addr_nd (encode acc) v) H_ne) as (h2new & H2new).
  assert (H_ol_new : of_list addr_nd [v; encode acc] = h2new).
  { unfold of_list; cbn; rewrite op_id_r; cbn.
    change (StorablePtr.ptr_encode acc) with (encode acc).
    rewrite H2new.
    reflexivity. }
  rewrite H_ol_old in H_cr_tl.
  assert (H_E1 : exists h_BC,
    (addr_nd |-> v) $+ heap sTL = Some h_BC /\
    ((Addr.shift_fw addr_nd 1) |-> (VPtr p0)) $+ h_BC = Some (heap s_a)).
  { specialize (op_assc ((Addr.shift_fw addr_nd 1) |-> (VPtr p0)) (addr_nd |-> v) (heap sTL))
      as Eassoc.
    unfold Basics.flip in Eassoc.
    rewrite H2old in Eassoc. cbn in Eassoc. rewrite H_cr_tl in Eassoc.
    destruct ((addr_nd |-> v) $+ heap sTL) eqn:E_BC.
    - cbn in Eassoc. eexists. exact (conj eq_refl (eq_sym Eassoc)).
    - cbn in Eassoc. discriminate. }
  destruct H_E1 as (h_BC & E_BC & E1).
  assert (H_E2 : exists h_BCD,
    h_BC $+ heap s_b = Some h_BCD /\
    ((Addr.shift_fw addr_nd 1) |-> (VPtr p0)) $+ h_BCD = Some (heap s)).
  { specialize (op_assc ((Addr.shift_fw addr_nd 1) |-> (VPtr p0)) h_BC (heap s_b)) as Eassoc.
    unfold Basics.flip in Eassoc.
    rewrite E1 in Eassoc. cbn in Eassoc. rewrite H_ab in Eassoc.
    destruct (h_BC $+ heap s_b) eqn:E_BCD.
    - cbn in Eassoc. eexists. exact (conj eq_refl (eq_sym Eassoc)).
    - cbn in Eassoc. discriminate. }
  destruct H_E2 as (h_BCD & E_BCD & E2).
  assert (H_ref_nnp : Pointer.References node_next_ptr (Addr.shift_fw addr_nd 1)).
  { exact (shift_fw_references nd addr_nd 1%N node_next_ptr H_ref_nd H_shift). }
  assert (H_np : np = node_next_ptr).
  { rewrite H_sl in H_shift. injection H_shift; auto. }
  subst np.
  assert (H_sub_p0 : ((Addr.shift_fw addr_nd 1) |-> (VPtr p0)) $<= heap s).
  { apply (substate_tran _ h2old).
    - exact (substate_of_partition_l H2old).
    - apply (substate_tran _ (heap s_a)).
      + exact (substate_of_partition_l H_cr_tl).
      + exact (substate_of_partition_l H_ab). }
  apply (proj2 (Heap.lookup_some (heap s) node_next_ptr (encode old_next))) in H_lookup.
  destruct H_lookup as (addr_l & H_ref_l & _ & H_sub_old).
  assert (H_al : addr_l = Addr.shift_fw addr_nd 1).
  { inversion H_ref_l; subst. inversion H_ref_nnp; subst. reflexivity. }
  subst addr_l.
  assert (H_veq : VPtr p0 = encode old_next).
  { exact (one_fun (Addr.shift_fw addr_nd 1) (VPtr p0) (encode old_next) (heap s)
             H_sub_p0 H_sub_old). }
  cbn in H_veq. injection H_veq as H_p0eq. subst p0.
  destruct (proj1 (Heap.mutate_some (heap s) node_next_ptr (encode acc))
    (ex_intro _ (Addr.shift_fw addr_nd 1)
      (conj H_ref_nnp (conj HWriteNP (ex_intro _ (VPtr old_next) H_sub_p0)))))
    as (h' & H_mut).
  exists h'. refine (conj H_mut _).
  assert (H_h' : ((Addr.shift_fw addr_nd 1) |-> (encode acc)) $+ h_BCD = Some h').
  { exact (Heap.mutate_mem (heap s) node_next_ptr (encode acc) h'
             (Addr.shift_fw addr_nd 1) (VPtr old_next) h_BCD H_mut H_ref_nnp E2). }
  assert (H_EA : exists h_an,
    ((Addr.shift_fw addr_nd 1) |-> (encode acc)) $+ h_BC = Some h_an /\
    h_an $+ heap s_b = Some h').
  { specialize (op_assc ((Addr.shift_fw addr_nd 1) |-> (encode acc)) h_BC (heap s_b)) as Eassoc.
    unfold Basics.flip in Eassoc.
    rewrite E_BCD in Eassoc.
    case_eq (((Addr.shift_fw addr_nd 1) |-> (encode acc)) $+ h_BC).
    - intros h_an E_an.
      rewrite E_an in Eassoc.
      eexists. exact (conj eq_refl (eq_trans Eassoc H_h')).
    - intros E_an.
      rewrite E_an in Eassoc.
      exfalso.
      assert (contra : None = Some h') by exact (eq_trans Eassoc H_h').
      discriminate. }
  destruct H_EA as (h_an & E_an & EA).
  assert (EB : h2new $+ heap sTL = Some h_an).
  { specialize (op_assc ((Addr.shift_fw addr_nd 1) |-> (encode acc)) (addr_nd |-> v) (heap sTL))
      as Eassoc.
    unfold Basics.flip in Eassoc.
    rewrite H2new in Eassoc.
    rewrite E_BC in Eassoc.
    exact (eq_trans Eassoc E_an). }
  assert (H_EC : exists h_nd,
    h2new $+ heap s_b = Some h_nd /\
    h_nd $+ heap sTL = Some h').
  { specialize (op_assc h2new (heap sTL) (heap s_b)) as Eassoc1.
    unfold Basics.flip in Eassoc1.
    rewrite EB in Eassoc1. cbn in Eassoc1. rewrite EA in Eassoc1.
    specialize (op_assc h2new (heap s_b) (heap sTL)) as Eassoc2.
    unfold Basics.flip in Eassoc2.
    rewrite (op_comm (heap s_b) (heap sTL)) in Eassoc2.
    destruct (heap sTL $+ heap s_b) eqn:E_Ts.
    - cbn in Eassoc1.
      cbn in Eassoc2. rewrite <- Eassoc1 in Eassoc2.
      destruct (h2new $+ heap s_b) eqn:E_nd.
      + cbn in Eassoc2. eexists. exact (conj eq_refl Eassoc2).
      + cbn in Eassoc2. discriminate.
    - cbn in Eassoc1. discriminate. }
  destruct H_EC as (h_nd & E_nd & EC2).
  exists {| store := store s; heap := h_nd |}, {| store := store s; heap := heap sTL |}.
  cbn. split; [reflexivity | split; [reflexivity | split; [exact EC2 | split]]].
  - cbn.
    exists {| store := store s; heap := $0 |}, {| store := store s; heap := h_nd |}.
    cbn. split; [reflexivity | split; [reflexivity | split; [apply op_id_l | split]]].
    + exact (conj (conj HNN (conj HRead
        (ex_intro _ node_next_ptr (conj H_shift (conj HReadNP HWriteNP))))) eq_refl).
    + exists addr_nd, acc,
             {| store := store s; heap := h2new |},
             {| store := store s; heap := heap s_b |}.
      cbn. split; [reflexivity | split; [reflexivity | split; [exact E_nd | split]]].
      * exists {| store := store s; heap := $0 |},
               {| store := store s; heap := h2new |}.
        cbn. split; [reflexivity | split; [reflexivity | split; [apply op_id_l | split]]].
        -- exact (conj H_ref_nd eq_refl).
        -- unfold Two. exact (eq_sym H_ol_new).
      * exact (llist_indep_regs acc l_acc s_b
                 {| store := store s; heap := heap s_b |} eq_refl H_ll_b).
  - exact (llist_indep_regs old_next l_rem sTL
             {| store := store s; heap := heap sTL |} eq_refl H_tl).
Qed.

Lemma mutate_frame {Hp: Heap}: forall (h_cr h_sub h h'_sub: Hp) (p: Pointer.t) (v: memval),
  h_cr $+ h_sub = Some h ->
  Heap.mutate h_sub p v = Some h'_sub ->
  exists h', h_cr $+ h'_sub = Some h' /\ Heap.mutate h p v = Some h'.
Proof.
  intros h_cr h_sub h h'_sub p v H_cr_sub H_mut_sub.
  destruct (proj2 (Heap.mutate_some h_sub p v) (ex_intro _ h'_sub H_mut_sub))
    as (addr & H_ref & H_allow & v_old & H_sub_np).
  destruct H_sub_np as (m_sub & H_m_sub).
  assert (H_sub_new : addr |-> v $+ m_sub = Some h'_sub).
  { exact (Heap.mutate_mem h_sub p v h'_sub addr v_old m_sub H_mut_sub H_ref H_m_sub). }
  assert (H_sub_full : addr |-> v_old $<= h).
  { exact (substate_tran _ _ _ (substate_of_partition_l H_m_sub) (substate_of_partition_r H_cr_sub)). }
  destruct H_sub_full as (m_full & H_m_full).
  destruct (proj1 (Heap.mutate_some h p v)
    (ex_intro _ addr (conj H_ref (conj H_allow (ex_intro _ v_old (substate_of_partition_l H_m_full))))))
    as (h' & H_mut_h).
  assert (H_full_new : addr |-> v $+ m_full = Some h').
  { exact (Heap.mutate_mem h p v h' addr v_old m_full H_mut_h H_ref H_m_full). }
  assert (H_cr_m_sub : h_cr $+ m_sub = Some m_full).
  { specialize (op_assc h_cr (addr |-> v_old) m_sub) as Hassoc.
    unfold Basics.flip in Hassoc.
    rewrite H_m_sub in Hassoc. cbn in Hassoc.
    rewrite H_cr_sub in Hassoc.
    rewrite (op_comm h_cr (addr |-> v_old)) in Hassoc.
    specialize (op_assc (addr |-> v_old) h_cr m_sub) as Hassoc2.
    unfold Basics.flip in Hassoc2.
    rewrite Hassoc2 in Hassoc.
    case_eq (h_cr $+ m_sub).
    - intros m_full_n E_cr_sub. rewrite E_cr_sub in Hassoc. cbn in Hassoc.
      pose proof (canc_mem _ _ _ _ H_m_full Hassoc) as Hmf_eq.
      symmetry in Hmf_eq. subst m_full_n. reflexivity.
    - intro E_cr_sub. rewrite E_cr_sub in Hassoc. cbn in Hassoc. discriminate. }
  exists h'. refine (conj _ H_mut_h).
  specialize (op_assc h_cr (addr |-> v) m_sub) as Hassoc3.
  unfold Basics.flip in Hassoc3.
  rewrite H_sub_new in Hassoc3. cbn in Hassoc3.
  specialize (op_assc (addr |-> v) h_cr m_sub) as Hassoc4.
  unfold Basics.flip in Hassoc4.
  rewrite H_cr_m_sub in Hassoc4. cbn in Hassoc4.
  rewrite (op_comm h_cr (addr |-> v)) in Hassoc3.
  rewrite Hassoc4 in Hassoc3.
  rewrite H_full_new in Hassoc3.
  exact (eq_sym Hassoc3).
Qed.

Lemma llist_extend {St Hp}:
  forall (p q: Pointer.t) (la lb: list memval)
         (s: State St Hp),
  la <> [] ->
  (llist p la ** llist q lb) s ->
  exists (nd np: Pointer.t) (h': Hp),
    Pointer.shift_fw nd 1%N = Some np /\
    Heap.mutate (heap s) np (encode q) = Some h' /\
    llist p (la ++ lb) {| store := store s; heap := h' |}.
Proof.
  intro p. intro q. intro la.
  revert p.
  induction la as [ | v la_tl IH_tl].
  - intros p lb s Hne _. exact (False_rect _ (Hne eq_refl)).
  - intros p lb s _ H_star.
    destruct la_tl as [ | v_n la_r].
    + assert (H_lookup_shift :
        exists np, Pointer.shift_fw p 1%N = Some np /\
                   Heap.lookup (heap s) np = Some (encode Pointer.NULL)).
      { destruct H_star as (sa & sb & _ & _ & H_ab & H_a & _).
        pose proof (llist_tl p v [] sa H_a) as Htl.
        destruct Htl as (np & p0 & H_shift & H_lk & Hreach).
        cbn in Hreach. subst p0.
        exact (ex_intro _ np (conj H_shift
          (lookup_mono _ _ _ _ (substate_of_partition_l H_ab) H_lk))). }
      destruct H_lookup_shift as (np & H_shift & H_lookup).
      destruct (llist_star_mutate p q Pointer.NULL v [] lb np s H_star H_shift H_lookup)
        as (h' & H_mut & H_res).
      destruct H_res as (sa' & sb' & _ & _ & H_ab' & H_a' & H_b').
      cbn in H_b'. destruct H_b' as (_ & Hempty).
      rewrite Hempty, op_id_r in H_ab'. injection H_ab' as Heq.
      exists p, np, h'.
      refine (conj H_shift (conj H_mut _)).
      exact (llist_indep_regs p (v :: lb) sa'
               {| store := store s; heap := h' |} Heq H_a').
    + assert (Hne_tl : v_n :: la_r <> []) by discriminate.
      destruct H_star as (sa & sb & _ & _ & H_ab & Hlla & Hllb).
      cbn in Hlla.
      destruct Hlla as (sLift & sRest & _ & _ & H_lr & HliftA & HexistB).
      cbn in HliftA.
      destruct HliftA as [[HNN [HRead [np_p [H_shift_p [HReadNP HWriteNP]]]]] H_eLift].
      rewrite H_eLift, op_id_l in H_lr. injection H_lr as H_restH.
      destruct HexistB as (addr & p' & sCR & sTL & _ & _ & H_cr_tl & HliftC & HtailD).
      rewrite H_restH in H_cr_tl.
      destruct HliftC as (sE & sF & _ & _ & H_ef & HrefE & HtwoF).
      cbn in HrefE. destruct HrefE as [H_ref_nd H_eRef].
      rewrite H_eRef, op_id_l in H_ef. injection H_ef as H_fH.
      assert (H_hCR : heap sCR = of_list addr [v; VPtr p'])
        by (unfold Two in HtwoF; congruence).
      assert (H_h_sub : exists h_sub,
        heap sTL $+ heap sb = Some h_sub /\
        heap sCR $+ h_sub = Some (heap s)).
      { specialize (op_assc (heap sCR) (heap sTL) (heap sb)) as Hassoc.
        unfold Basics.flip in Hassoc.
        rewrite H_cr_tl in Hassoc. cbn in Hassoc.
        rewrite H_ab in Hassoc.
        case_eq (heap sTL $+ heap sb).
        - intros h_sub E_sub. rewrite E_sub in Hassoc. cbn in Hassoc.
          exact (ex_intro _ h_sub (conj eq_refl (eq_sym Hassoc))).
        - intro E_sub. rewrite E_sub in Hassoc. cbn in Hassoc. discriminate. }
      destruct H_h_sub as (h_sub & H_sub_eq & H_cr_sub).
      assert (H_star_sub : (llist p' (v_n :: la_r) ** llist q lb)
                             {| store := store s; heap := h_sub |}).
      { exists {| store := store s; heap := heap sTL |},
               {| store := store s; heap := heap sb |}.
        cbn. split. reflexivity. split. reflexivity. split. exact H_sub_eq.
        split.
        - exact (llist_indep_regs p' (v_n :: la_r) sTL
                   {| store := store s; heap := heap sTL |} eq_refl HtailD).
        - exact (llist_indep_regs q lb sb
                   {| store := store s; heap := heap sb |} eq_refl Hllb). }
      destruct (IH_tl p' lb {| store := store s; heap := h_sub |}
                  Hne_tl H_star_sub)
        as (nd & np & h'_sub & H_shift_nd & H_mut_sub & H_ext_sub).
      destruct (mutate_frame (heap sCR) h_sub (heap s) h'_sub np (encode q)
                  H_cr_sub H_mut_sub)
        as (h' & H_cr_h'_sub & H_mut_full).
      exists nd, np, h'.
      refine (conj H_shift_nd (conj H_mut_full _)).
      cbn.
      exists {| store := store s; heap := $0 |},
             {| store := store s; heap := h' |}.
      cbn. split. reflexivity. split. reflexivity. split. apply op_id_l.
      split.
      { exact (conj (conj HNN (conj HRead
          (ex_intro _ np_p (conj H_shift_p (conj HReadNP HWriteNP))))) eq_refl). }
      exists addr, p'.
      exists {| store := store s; heap := heap sCR |},
             {| store := store s; heap := h'_sub |}.
      cbn. split. reflexivity. split. reflexivity. split. exact H_cr_h'_sub.
      split.
      { exists {| store := store s; heap := $0 |},
               {| store := store s; heap := heap sCR |}.
        cbn. split. reflexivity. split. reflexivity. split. apply op_id_l.
        split.
        - exact (conj H_ref_nd eq_refl).
        - unfold Two. exact H_hCR. }
      exact H_ext_sub.
Qed.

