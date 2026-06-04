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
           Pointer.Allows next_ptr Operation.Read |] **
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
  exact HsfA.
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
      (* Changed proj2 to proj1 here *)
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
                        & HRef & Hshift & HWVnp & HRnp & HLookup & Htail).
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
    + eapply lookup_mono; [exact Hsub | exact HLookup].
    + apply (IHl p0 Htail).
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
    destruct HNN as [HNN_ptr [HAll1 [next_ptr [HShift HAll2]]]].
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

