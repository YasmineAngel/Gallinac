From Stdlib Require Import Arith List SetoidList Psatz.
Import ListNotations.
From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Memval.
From GallinaC.Utils Require GenId.
From GallinaC.Imp Require Store Heap.

Section ListStore.

  Import Store.

  Record list_store: Type :=
    mkListStore
      {
        ls_bindings : list (Nat.t * memval);
        ls_next_var : Nat.t
      }.

  Definition list_store_emp: list_store := mkListStore [] 0.

  Definition list_store_lookup (s: list_store) n := findA (Nat.eqb n) (ls_bindings s).
  Definition list_store_mutate (s: list_store) n v :=
    match findA (Nat.eqb n) (ls_bindings s) with
    | Some _ => Some (mkListStore (@replace _ _ Nat.eq_dec n v (ls_bindings s)) (ls_next_var s))
    | None => None
    end.
  Definition list_store_push (s: list_store) v :=
    let n := ls_next_var s in
    let next_id := S (ls_next_var s) in
    (mkListStore ((n,v)::(ls_bindings s)) next_id, n).
  Definition list_store_pop (s: list_store) :=
    match ls_bindings s with [] => None | _::s' => Some (mkListStore s' (ls_next_var s)) end.

  Definition list_store_mutate_unchecked (s: list_store) n v :=
    match findA (Nat.eqb n) (ls_bindings s) with
    | Some _ => mkListStore (@replace _ _ Nat.eq_dec n v (ls_bindings s)) (ls_next_var s)
    | None => mkListStore ((n, v):: ls_bindings s) (ls_next_var s)
    end.

  Local Obligation Tactic := cbn; eauto; unfold list_store_lookup, list_store_mutate, list_store_push, list_store_pop, list_store_mutate_unchecked.

  Program Definition ListStore: Store :=
    {|
      store := list_store;
      name := Nat.t;

      name_eq_dec := Nat.eq_dec;

      emp := list_store_emp;

      BindsTo := fun n v s => BindIn n v (ls_bindings s);
      WF := fun s => Forall (fun x => (fst x) < (ls_next_var s)) (ls_bindings s);
      Empty := fun s => ls_bindings s = [];
      Equal := fun s s' => forall n v, BindIn n v (ls_bindings s) <-> BindIn n v (ls_bindings s');

      lookup := list_store_lookup;
      mutate := list_store_mutate;
      push := list_store_push;
      pop := list_store_pop;

      mutate_unchecked := list_store_mutate_unchecked;
      push_unchecked := list_store_mutate_unchecked;
    |}.

  Next Obligation.
    intros n v contra.
    inversion contra.
  Qed.

  Next Obligation.
    cbn; intros s n v w HBindInv HBindInw.
    eapply BindIn_fun; eauto.
  Qed.

  Next Obligation.
    intros s n v Heq contra.
    rewrite Heq in contra.
    inversion contra.
  Qed.

  Next Obligation.
    split; auto.
  Qed.

  Next Obligation.
    intros s n v.
    split.
    - intros HBindIn.
      induction HBindIn as [ n v binds | n v binds n' v' Hneq HBindIn IHBindIn ]; cbn.
      + now rewrite Nat.eqb_refl.
      + apply Nat.eqb_neq in Hneq; now rewrite Hneq.
    - intros HfindA.
      destruct s as [ bindings next_var ].
      induction bindings; cbn in HfindA;
        try discriminate.
      destruct a as [ n' v' ].
      destruct (Nat.eqb_spec n n'); subst.
      + inversion HfindA; subst; left.
      + right; [ auto | now apply IHbindings ].
  Qed.

  Next Obligation.
    intros s n v.
    destruct s as [ binds nvar ];
      cbn;
      split.
    - intros [ v' HBindIn ].
      induction HBindIn as [ n v_old binds | n v_old binds n' v' Hneq HBindIn [ s' IHBindIn ] ].
      + exists (mkListStore ((n,v)::binds)  nvar).
        destruct (findA (Nat.eqb n) ((n, v_old)::binds)) eqn:Efind.
        * cbn.
          destruct (Nat.eq_dec n n); [ clear e | contradiction ].
          reflexivity.
        * cbn in Efind.
          now rewrite Nat.eqb_refl in Efind.
      + exists (mkListStore ((n',v')::ls_bindings s') nvar).
        cbn.
        assert (Hrewrite: n =? n' = false) by (now apply Nat.eqb_neq);
          rewrite Hrewrite; clear Hrewrite.
        destruct (findA (Nat.eqb n) binds) eqn:Efind; try discriminate.
        inversion IHBindIn; subst; clear IHBindIn.
        destruct (Nat.eq_dec n' n); try (congruence).
        reflexivity.
    - induction binds as [ | [ n' v' ] binds IHbinds ];
        intros [ s' HfindA ].
      + destruct (@findA nat memval (Nat.eqb n) []) eqn:Efind;
          cbn in Efind; discriminate.
      + cbn in HfindA.
        destruct (Nat.eqb_spec n' n) as [ Heq | Hneq ]; subst.
        * rewrite (Nat.eqb_refl n) in HfindA.
          destruct (Nat.eq_dec n n) as [ Heq | Hneq ]; [ clear Heq | contradiction ].
          exists v'.
          now constructor.
        * destruct (Nat.eqb_spec n n') as [ Heq | _ ], (Nat.eq_dec n' n); try (congruence).
          destruct (findA (Nat.eqb n) binds) eqn:EfindA; try (discriminate).
          destruct IHbinds as [ v_old HBindIn ].
          eexists; reflexivity.
          exists v_old.
          right; [ congruence | assumption ].
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] Hmutate;
      cbn; cbn in Hmutate.
    destruct (findA (Nat.eqb n) binds) as [ v' | ] eqn:Efind; [ | discriminate ].
    inversion Hmutate; subst; clear Hmutate.
    clear nvar'.
    revert n v v' Efind.
    induction binds as [ | [ n'' v'' ] ]; [ discriminate | ].
    intros.
    cbn.
    destruct (Nat.eq_dec n'' n) as [ Heq | Hneq ]; [ subst; cbn in Efind; rewrite Nat.eqb_refl in Efind; inversion Efind; subst; clear Efind | ].
    constructor; now inversion HForall.
    constructor.
    now symmetry.
    eapply IHbinds; eauto.
    cbn in Efind.
    destruct (Nat.eqb_spec n n''); [ congruence | eauto ].
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] n' v' Hneq Hmutate.
    cbn.
    cbn in Hmutate.
    destruct (findA (Nat.eqb n) binds) eqn:Efind; [ | discriminate ].
    inversion Hmutate; subst; clear Hmutate.
    induction binds as [ | [ n'' v'' ] binds IHbinds ].
    - split; intros H; cbn in H; now inversion H.
    - cbn.
      split; intros HBindIn.
      + destruct (Nat.eq_dec n'' n) as [ Heq | Hneq'' ]; subst.
        cbn in Efind.
        rewrite Nat.eqb_refl in Efind.
        inversion Efind; subst; clear Efind.
        right.
        now symmetry.
        inversion HBindIn; [ congruence | now auto ].
        cbn in Efind.
        destruct (Nat.eqb_spec n n'') as [ Heq | _ ]; [ congruence | ].
        inversion HBindIn; subst.
        left.
        right; auto.
        apply IHbinds; auto.
      + destruct (Nat.eq_dec n'' n) as [ Heq | Hneq'' ]; [ subst | ].
        right; auto.
        inversion HBindIn; [ congruence | auto ].
        inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq HBindIn' ]; [ now left | subst ].
        right; auto.
        apply IHbinds; auto.
        cbn in Efind.
        destruct (Nat.eqb_spec n n''); [ congruence | assumption ].
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] HForall Hmutate.
    cbn; cbn in HForall, Hmutate.
    destruct (findA (Nat.eqb n) binds) as [ v'' | ] eqn:Efind; [ inversion Hmutate; subst; clear Hmutate | discriminate ].
    induction binds as [ | [ n' v' ] binds IHbinds ]; [ constructor | ].
    cbn.
    cbn in Efind.
    destruct (Nat.eqb_spec n n') as [ Heq | Hneq ], (Nat.eq_dec n' n) as [ Heq' | Hneq' ];
      try (subst n'; clear Heq Heq');
      try (congruence);
      try (clear Hneq').
    inversion Efind; subst v''; clear Efind.
    constructor; now inversion HForall.
    constructor.
    now inversion HForall.
    apply IHbinds; auto.
    now inversion HForall.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] v' HForall Hpush contra.
    cbn in HForall, Hpush, contra.
    inversion Hpush; subst; clear Hpush.
    induction binds.
    - inversion contra.
    - inversion HForall as [ | x l Hlt HForall' ]; subst.
      inversion contra; [ subst; cbn in Hlt; lia | subst ].
      apply IHbinds; auto.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] HForall Hpush.
    unfold list_store_push in Hpush;
      cbn; cbn in HForall, Hpush.
    inversion Hpush; subst.
    constructor.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] HForall Hpush.
    cbn; cbn in HForall, Hpush.
    inversion Hpush; subst; clear Hpush.
    constructor; [ cbn; lia | ].
    eapply Forall_impl; [ | apply HForall ].
    cbn; lia.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] Hpush.
    cbn; cbn in Hpush.
    inversion Hpush; subst; clear Hpush.
    eexists; split; [ reflexivity | ].
    intros n' v'; split.
    - intros HBindIn.
      induction HBindIn; now constructor.
    - now cbn.
  Qed.

  Next Obligation.
    intros [ binds nvar ] [ binds' nvar' ] HWF Hpop.
    cbn; cbn in HWF, Hpop.
    destruct binds as [ | [ n v ] binds ]; [ discriminate | ].
    inversion Hpop; subst; clear Hpop.
    now inversion HWF.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v n' v'.
    cbn.
    split.
    - intros [ [ Heqn Heqv ] | [ Hneqn HBindIn ] ]; subst; cbn.
      + induction binds as [ | [ n v ] binds IHbinds ]; cbn.
        * constructor.
        * destruct (findA (Nat.eqb n') binds) eqn:Efind.
          -- cbn in IHbinds.
             destruct (Nat.eqb_spec n n') as [ Heq | Hneq ]; subst;
               repeat (rewrite Nat.eqb_refl); cbn.
             destruct (Nat.eq_dec n' n') as [ H | H ]; [ clear H | contradiction ].
             left.
             destruct (Nat.eqb_spec n' n) as [ H | H ]; [ congruence | clear H ].
             cbn.
             destruct (Nat.eq_dec n n') as [ | H ]; [ congruence | clear H].
             now right.
          -- cbn in IHbinds.
             destruct (Nat.eqb_spec n' n) as [ Heq | Hneq ]; subst;
               repeat (rewrite Nat.eqb_refl);
               cbn.
             destruct (Nat.eq_dec n n) as [ H | H ]; [ now left | contradiction ].
             left.
      + destruct (findA (Nat.eqb n') binds) eqn:Efind.
        * cbn.
          induction binds as [ | [ n'' v'' ] binds ]; [ discriminate | ].
          cbn; cbn in Efind.
          destruct (Nat.eqb_spec n'' n') as [ Heq | Hneq ], (Nat.eq_dec n'' n') as [ Heq' | Hneq' ];
            (try (congruence));
            subst;
            (try clear Heq');
            (try clear Hneq').
          rewrite Nat.eqb_refl in Efind.
          inversion Efind; subst.
          constructor; auto.
          inversion HBindIn; [ contradiction | auto ].
          destruct (Nat.eqb_spec n' n'') as [ Heq | _ ]; [ congruence | ].
          inversion HBindIn; subst.
          constructor.
          right; auto.
        * now constructor.
    - induction binds as [ | [ n'' v'' ] binds ].
      + cbn.
        intros HBindIn.
        inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq ?HBindIn' ]; subst.
        now repeat constructor.
        inversion HBindIn'.
      + cbn.
        intros HBindIn.
        destruct (Nat.eqb_spec n'' n') as [ Heq | Hneq ]; subst.
        * rewrite Nat.eqb_refl in HBindIn.
          cbn in HBindIn.
          destruct (Nat.eq_dec n' n') as [ H | H ]; [ clear H | contradiction ].
          inversion HBindIn; subst.
          left; split; auto.
          right; split; auto.
          right; auto.
        * destruct (Nat.eqb_spec n' n'') as [ Heq | _ ]; [ congruence | ].
          destruct (Nat.eq_dec n'' n') as [ H | _ ]; [ contradiction | ].
          destruct (findA (Nat.eqb n') binds) as [ v''' | ] eqn:Efind; [ | ];
            cbn in HBindIn, IHbinds.
          (inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq HBindIn' ]; subst);
          [
            now repeat constructor
          |
            destruct (IHbinds HBindIn') as [ H | H ];
            [ destruct H; subst; now repeat constructor
            | destruct H; now repeat constructor ]
          ].
          inversion HBindIn as [ | ?x ?y ?l ?x' ?y' ?Hneq HBindIn' ]; subst.
          now repeat constructor.
          right; now split.
  Qed.

  Next Obligation.
    intros n v [ binds nvar ] v_old HBindIn.
    cbn; cbn in HBindIn.
    induction HBindIn.
    - cbn.
      rewrite Nat.eqb_refl.
      reflexivity.
    - cbn.
      destruct (Nat.eqb_spec x x') as [ Heq | _ ]; [ congruence | ].
      destruct (Nat.eq_dec x' x) as [ Heq | _ ]; [ congruence | ].
      destruct (findA (Nat.eqb x) l) eqn:Efind; congruence.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] [ binds'' nvar'' ] v' Hpush Hmutate.
    cbn; cbn in Hpush.
    inversion Hpush; subst; clear Hpush.
    cbn in Hmutate.
    rewrite Nat.eqb_refl in Hmutate.
    destruct (Nat.eq_dec n n) as [ _ | Hneq ]; [ | congruence ].
    inversion Hmutate; subst.
    reflexivity.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ binds' nvar' ] n' v' HForall Hpush HBindIn.
    cbn in *; inversion Hpush; subst; clear Hpush.
    apply BindIn_tl.
    - intros contra; subst n'.
      induction HBindIn.
      + inversion HForall; subst; cbn in *; lia.
      + apply IHHBindIn.
        inversion HForall; subst; assumption.
    - exact HBindIn.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n v [ s' Hpop ].
    cbn in Hpop.
    destruct binds as [ | [ k0 v0 ] binds_rest ]; [ discriminate | clear Hpop ].
    cbn.
    destruct (findA (Nat.eqb n) ((k0, v0) :: binds_rest)) as [ v_old | ] eqn:Efind.
    - destruct (Nat.eq_dec k0 n) as [ Heq | Hneq ]; cbn.
      + subst n.
        rewrite Nat.eqb_refl.
        cbn.
        eexists; reflexivity.
      + cbn in Efind.
        destruct (Nat.eqb_spec n k0) as [ Heqb | Hneqb ]; [ congruence | ].
        rewrite Efind.
        cbn.
        destruct (Nat.eq_dec k0 n); [ congruence | ].
        eexists; reflexivity.
    - cbn in Efind.
      destruct (Nat.eqb_spec n k0); [ discriminate Efind | ].
      rewrite Efind.
      cbn.
      eexists; reflexivity.
  Qed.

  Next Obligation.
  intros [ binds nvar ] [ binds' nvar' ] HEqual [ t Hpop ].
  cbn in HEqual, Hpop.
  destruct binds as [ | [ n v ] binds_rest ]; [ discriminate | clear Hpop ].
  assert (HBI : BindIn n v binds') by (apply HEqual; constructor).
  inversion HBI; subst; cbn; eexists; reflexivity.
  Qed.

  Next Obligation.
    intros [ binds nvar ] n1 v1 n2 v2 Hne HBI1 HBI2.
    cbn in HBI1, HBI2.
    inversion HBI1 as [ ? ? rest1' | ? ? rest1' hd_k' hd_v' Hne1' HBI1'' ]; subst.
    - inversion HBI2 as [ ? ? ? | ? ? ? ? ? Hne2 HBI2' ]; subst.
      + contradiction (Hne eq_refl).
      + destruct rest1' as [ | [ rk rv ] rest2 ].
        * inversion HBI2'.
        * cbn; do 2 eexists; split; reflexivity.
    - destruct rest1' as [ | [ rk rv ] rest2 ].
      + inversion HBI1''.
      + cbn; do 2 eexists; split; reflexivity.
  Qed.

End ListStore.

Canonical ListStore.

Section OptionAllocator.
  Import Algebra Arith GenId ssrfun.Option.

  Local Obligation Tactic := (try (intros [ [x|] ];
                                   (try intros [ [y|] ]);
                                   (try intros [ [z|] ]);
                                   first [ reflexivity | discriminate ])).

  Local Open Scope bool_scope.
  Local Open Scope program_scope.

  Record option_alloc: Set :=
    mkOptAlloc
      {
        next: option nat;
      }.

  Definition option_alloc_unit: option_alloc := mkOptAlloc None.

  Definition option_alloc_sum (l r: option_alloc): option option_alloc :=
    match l, r with
    | mkOptAlloc None, mkOptAlloc None => Some (mkOptAlloc None)
    | mkOptAlloc (Some n), mkOptAlloc None
    | mkOptAlloc None, mkOptAlloc (Some n) => Some (mkOptAlloc (Some n))
    | mkOptAlloc (Some _), mkOptAlloc (Some _) => None
    end.

  Definition option_alloc_get (a: option_alloc): option nat := next a.

  Definition option_alloc_next (a: option_alloc): option_alloc :=
    match a with
    | mkOptAlloc None => mkOptAlloc None
    | mkOptAlloc (Some n) => mkOptAlloc (Some (S n))
    end.

  Program Definition option_alloc_separation: Separation :=
    {|
      Algebra.carrier := option_alloc;
      op := option_alloc_sum;
      id_e := option_alloc_unit;
    |}.

  Program Definition option_alloc_genid: GenId :=
    {|
      GenId.carrier := option_alloc_separation;
      GenId.get := option_alloc_get;
      GenId.next := option_alloc_next;
    |}.
  Next Obligation.
    intros [[id0|] ]; cbn; intros id1 EQ.
    inversion EQ; subst; clear EQ.
    now eexists.
    discriminate.
  Qed.

  Next Obligation.
    intros [[id0'|] ]; cbn; intros id0 id1 EQ1 EQ2.
    inversion EQ1; subst; inversion EQ2; subst; clear EQ1 EQ2; lia.
    discriminate.
  Qed.

  Next Obligation.
    intros [[id0|] ] [[id1|]] ([[id2|]] & EQ); cbn in *;
      unfold "$+" in *; cbn in *;
      first
        [ discriminate
        | left; discriminate
        | auto ].
  Qed.

  Next Obligation.
    intros [[id0|] ] [[id1|] ] ([[id2|]] & EQ);
      cbn in *; unfold "$+" in *; cbn in *;
      first
        [ discriminate
        | eexists; reflexivity
        | auto ].
  Qed.

End OptionAllocator.

Canonical option_alloc_separation.
Canonical option_alloc_genid.

Section ListHeap.

  Import Algebra Heap Arith NArith ssrfun.Option.

  Local Obligation Tactic := idtac.
  Local Open Scope bool_scope.
  Local Open Scope separation_scope.

  Definition memblock: Set := list (option memval).
  Record list_heap_carrier: Set :=
    mkListHeap
      {
        list_heap: list memblock;
        alloc: bool;
      }.

  Fixpoint memblock_sum (l r: memblock): option memblock :=
    match l, r with
    | [], [] => Some []
    | [], ((_::_) as mb)
    | ((_::_) as mb), []
      => Some mb
    | Some vl::l, Some vr::r => None
    | None::l, None::r =>
        match memblock_sum l r with
        | Some mb => Some (None::mb)
        | None => None
        end
    | Some v::l, None::r
    | None::l, Some v::r
      => match memblock_sum l r with
         | Some mb =>  Some ((Some v)::mb)
         | None => None
         end
    end.

  Lemma memblock_sum_id_l (mb: memblock): memblock_sum [] mb = Some mb.
  Proof.
    induction mb as [| [v|] mb]; cbn; auto.
  Qed.

  Lemma memblock_sum_id_r (mb: memblock): memblock_sum mb [] = Some mb.
  Proof.
    induction mb as [| [v|] mb]; cbn; auto.
  Qed.

  Lemma memblock_sum_comm (l r: memblock): memblock_sum l r = memblock_sum r l.
  Proof.
    revert r.
    induction l as [| [vl|] l]; intros.
    - now rewrite memblock_sum_id_r, memblock_sum_id_l.
    - cbn.
      destruct r as [| [vr|] r]; auto.
      now rewrite IHl.
    - cbn.
      destruct r as [| [vr|] r].
      now rewrite memblock_sum_id_l.
      now rewrite IHl.
      now rewrite IHl.
  Qed.

  Lemma memblock_sum_assc (x y z: memblock): bind (Basics.flip memblock_sum z) (memblock_sum x y) = bind (memblock_sum x) (memblock_sum y z).
  Proof.
    revert x z.
    induction y as [| vy y]; intros [| vx x] [| vz z]; auto;
      try (now destruct vx; auto);
      try (now destruct vy; auto).
    - unfold flip, bind, apply;
        rewrite memblock_sum_id_l; cbn -[memblock_sum].
      now destruct (memblock_sum _ _); [ rewrite memblock_sum_id_l | ].
    - unfold flip, bind, apply.
      rewrite memblock_sum_id_r.
      now destruct (memblock_sum _ _); [ rewrite memblock_sum_id_r | ].
    - specialize (IHy x z).
      destruct vx as [vx|], vy as [vy|], vz as [vz|]; auto.
      now cbn; destruct (memblock_sum y z); cbn; auto.
      now cbn; destruct (memblock_sum x y), (memblock_sum y z) eqn:Eyz; cbn; auto.
      cbn; destruct (memblock_sum x y) as [xy|], (memblock_sum y z) as [yz|]; cbn; auto.
      now cbv -[memblock_sum] in IHy; rewrite IHy.
      now cbv -[memblock_sum] in IHy; rewrite IHy.
      now cbn in IHy; rewrite <- IHy.
      now cbn; destruct (memblock_sum x y).
      revert IHy;
        cbn; destruct (memblock_sum x y) as [xy|]; unfold flip; cbn.
      destruct (memblock_sum xy z) as [xyz|]; cbn.
      destruct (memblock_sum y z) as [yz|]; cbn; [ now intros EQ; rewrite <- EQ| discriminate].
      destruct (memblock_sum y z) as [yz|]; cbn; [ now intros EQ; rewrite <- EQ| reflexivity ].
      destruct (memblock_sum y z) as [yz|]; cbn; [ now intros EQ; rewrite <- EQ| reflexivity ].
      revert IHy;
        cbn; destruct (memblock_sum x y) as [xy|]; unfold flip; cbn.
      now destruct (memblock_sum y z) as [yz|]; cbn; intros EQ; rewrite EQ.
      destruct (memblock_sum y z); [ | reflexivity ].
      now cbn; intros EQ; rewrite <- EQ.
      revert IHy; cbn.
      destruct (memblock_sum x y) as [xy|]; unfold flip; cbn;
        destruct (memblock_sum y z) as [yz|]; cbn;
        intros EQ; first [ rewrite EQ | rewrite <- EQ | auto ]; auto.
      now destruct (memblock_sum x yz).
  Qed.

  Fixpoint memblocks_sum (l r: list memblock): option (list memblock) :=
    match l, r with
    | [], mbs | mbs, [] => Some mbs
    | mbl::mbsl, mbr::mbsr =>
        match memblock_sum mbl mbr, memblocks_sum mbsl mbsr with
        | Some mb, Some mbs => Some (mb::mbs)
        | None, _ | _, None => None
        end
    end.

  Lemma memblocks_sum_id_l mbs: memblocks_sum [] mbs = Some mbs.
  Proof.
    induction mbs; auto.
  Qed.

  Lemma memblocks_sum_id_r mbs: memblocks_sum mbs [] = Some mbs.
  Proof.
    induction mbs; auto.
  Qed.

  Lemma memblocks_sum_comm (mbsl mbsr: list memblock): memblocks_sum mbsl mbsr = memblocks_sum mbsr mbsl.
  Proof.
    revert mbsr.
    induction mbsl as [|mbl mbsl]; intros.
    - now rewrite memblocks_sum_id_l, memblocks_sum_id_r.
    - destruct mbsr as [|mbr mbsr]; cbn; auto.
      now rewrite memblock_sum_comm, IHmbsl.
  Qed.

  Lemma memblocks_sum_assc (x y z: list memblock): bind (flip memblocks_sum z) (memblocks_sum x y) = bind (memblocks_sum x) (memblocks_sum y z).
  Proof.
    revert y z.
    induction x as [|mbx x]; intros.
    - unfold flip; rewrite memblocks_sum_id_l; cbn.
      now destruct (memblocks_sum y z).
    - destruct y as [|mby y], z as [|mbz z]; auto.
      unfold flip; rewrite memblocks_sum_id_r; cbn.
      destruct (memblock_sum mbx mby); [ | reflexivity ].
      now destruct (memblocks_sum x y).
      specialize (IHx y z); revert IHx.
      specialize (memblock_sum_assc mbx mby mbz).
      unfold flip; cbn.
      destruct (memblock_sum mbx mby) as [mbxy|]; cbn;
        destruct (memblock_sum mby mbz) as [mbyz|]; cbn;
        destruct (memblocks_sum x y) as [xy|]; cbn;
        destruct (memblocks_sum y z) as [yz|]; cbn;
        auto;
        intros EQmb EQmbs;
        (try (now rewrite EQmb, EQmbs));
        (try now rewrite EQmb);
        (try now rewrite <- EQmb).
      now destruct (memblock_sum mbxy mbz); [ rewrite EQmbs | ].
      now destruct (memblock_sum mbx mbyz); [ rewrite <- EQmbs | ].
  Qed.

  Lemma memblocks_sum_length_max: forall [mbsl mbsr mbs] (EQ: memblocks_sum mbsl mbsr = Some mbs), length mbs = Nat.max (length mbsl) (length mbsr).
  Proof.
    induction mbsl as [|mbl mbsl].
    - intros mbsr mbs; rewrite memblocks_sum_id_l; cbn; congruence.
    - intros [|mbr mbsr] mbs; cbn; intros EQ.
      inversion EQ; subst; clear EQ; auto.
      destruct (memblock_sum mbl mbr); try discriminate.
      destruct (memblocks_sum mbsl mbsr) as [mbs'|] eqn:E;
        inversion EQ; subst; clear EQ.
      cbn.
      f_equal.
      now apply IHmbsl.
  Qed.

  Definition list_heap_sum (l r: list_heap_carrier): option list_heap_carrier :=
    match l, r with
    | mkListHeap mbsl allocl, mkListHeap mbsr allocr =>
        if (allocl && allocr) || (allocl && (length mbsl <? length mbsr)) || (allocr && (length mbsr <? length mbsl))
        then
          None
        else
          match memblocks_sum mbsl mbsr with
          | Some mbs => Some (mkListHeap mbs (allocl || allocr))
          | None => None
          end
    end.

  Definition list_heap_unit: list_heap_carrier := mkListHeap [] false.

  Fixpoint memblock_one (o: nat) (v: memval): memblock :=
    match o with
    | 0 => [Some v]
    | S o => None::(memblock_one o v)
    end.

  Lemma memblock_one_inj (o o': nat) (v v': memval):
    memblock_one o v = memblock_one o' v' <-> o = o' /\ v = v'.
  Proof.
    split; [ intros EQ; split | intros [ EQo EQv ] ].
    - revert o' v v' EQ.
      induction o; intros.
      + destruct o'; [ reflexivity | discriminate ].
      + destruct o'; [ discriminate | cbn in EQ ].
        f_equal; eapply IHo.
        injection EQ; eauto.
    - revert o' v v' EQ.
      induction o; intros;
        destruct o';
        [ now inversion EQ
        | discriminate
        | discriminate
        | eapply IHo; injection EQ; eauto ].
    - now subst.
  Qed.

  Lemma memblock_one_ne_addr o o' v v'
    : o <> o' <-> exists mb', memblock_sum (memblock_one o v) (memblock_one o' v') = Some mb'.
  Proof.
    split; [ intros NE | intros (mb' & EQ)].
    - revert o' NE;
        induction o; intros.
      destruct o';
        [ contradiction |
          cbn; destruct (memblock_one o' v'); eexists; reflexivity].
      destruct o';
        [ cbn; rewrite memblock_sum_id_r; eexists; reflexivity
        | specialize (IHo o' ltac:(apply Nat.succ_inj_wd_neg, NE)) as (mb' & EQ);
          cbn; rewrite EQ; eexists; reflexivity ].
    - intros contra; subst o'.
      revert mb' EQ.
      induction o; intros; [ discriminate | ].
      cbn in EQ; destruct (memblock_sum _ _); [ destruct mb'; [ discriminate | inversion EQ; subst ]; apply (IHo mb'); auto | discriminate ].
  Qed.

  Fixpoint memblocks_one (b o: nat) (v: memval): list memblock :=
    match b with
    | 0 => [memblock_one o v]
    | S b => []::(memblocks_one b o v)
    end.

  Lemma memblocks_one_inj b b' o o' v v':
    memblocks_one b o v = memblocks_one b' o' v' <-> b = b' /\ o = o' /\ v = v'.
  Proof.
    split; [ intros EQ; split; [|split] | now intros ( EQb & EQo & EQv); subst ];
      revert b' o o' v v' EQ; induction b;
      intros.
    - destruct b'; [ reflexivity | cbn in EQ ].
      destruct o; discriminate.
    - destruct b'; [ destruct o, o'; cbn in EQ; discriminate  | cbn in EQ; injection EQ as EQ ].
      f_equal; eapply IHb, EQ.
    - destruct b'; [ cbn in EQ; injection EQ as EQ; eapply memblock_one_inj, EQ | destruct o, o'; discriminate ].
    - destruct b'; [ destruct o, o'; discriminate | ].
      injection EQ as EQ. eapply IHb, EQ.
    - destruct b'; [ injection EQ as EQ; eapply memblock_one_inj, EQ | ].
      destruct o, o'; discriminate.
    - destruct b'; [ destruct o, o'; discriminate | injection EQ; eapply IHb ].
  Qed.

  Lemma memblocks_one_ne_block b b' o o' v v'
    : (b <> b') -> exists mbs', memblocks_sum (memblocks_one b o v) (memblocks_one b' o' v') = Some mbs'.
  Proof.
    intros NE.
    revert b' NE.
    induction b; intros.
    - destruct b'; [ contradiction | clear NE ]; cbn.
      rewrite memblock_sum_id_r; eexists; reflexivity.
    - destruct b'; [ destruct o, o'; cbn; try rewrite memblocks_sum_id_r; eexists; reflexivity | ].
      cbn.
      specialize (IHb b' ltac:(apply Nat.succ_inj_wd_neg, NE)) as (mbs' & EQ).
      now rewrite EQ; eexists.
  Qed.

  Lemma memblocks_one_eq_block_ne_offset b o o' v v'
    : o <> o' <-> exists mbs', memblocks_sum (memblocks_one b o v) (memblocks_one b o' v') = Some mbs'.
  Proof.
    split; [ intros NE | ].
    - revert o o' NE.
      induction b.
      + intros o o' NE; cbn.
        specialize (proj1 (memblock_one_ne_addr o o' v v') NE) as (mb' & EQ).
        rewrite EQ; eexists; reflexivity.
      + intros o o' NE; cbn.
        specialize (IHb o o' NE) as (mbs' & EQ).
        rewrite EQ; eexists; reflexivity.
    - intros (mbs' & EQ).
      revert mbs' EQ; induction b; intros.
      + cbn in EQ.
        destruct (memblock_sum _ _) eqn:E; [ | discriminate].
        eapply memblock_one_ne_addr.
        eexists; apply E.
      + cbn in EQ. destruct (memblocks_sum _ _) eqn:E; [ | discriminate ].
        inversion EQ; subst.
        now eapply IHb.
  Qed.

  Lemma memblocks_one_ne_addr b b' o o' v v'
    : (b <> b' \/ o <> o') <-> exists mbs', memblocks_sum (memblocks_one b o v) (memblocks_one b' o' v') = Some mbs'.
  Proof.
    split; [ intros [ NE | NE ] | intros (mbs' & EQ) ].
    - now apply memblocks_one_ne_block.
    - now destruct (Nat.eq_dec b b'); [ subst; apply memblocks_one_eq_block_ne_offset | apply memblocks_one_ne_block ].
    - destruct (Nat.eq_dec b b'); [ subst b'; right | now left ].
      apply (memblocks_one_eq_block_ne_offset b o o' v v'); eexists mbs'; apply EQ.
  Qed.

  Definition list_heap_one (addr: Addr.t) (v: memval): list_heap_carrier :=
    match addr with
    | Addr.mkAddr b o =>
        mkListHeap (memblocks_one b (N.to_nat o) v) false
    end.

  Lemma list_heap_one_inj addr addr' v v'
    : list_heap_one addr v = list_heap_one addr' v' <-> addr = addr' /\ v = v'.
  Proof.
    split; [ | now intros [EQa EQv]; subst ].
    unfold list_heap_one.
    destruct addr, addr'. intros EQ; injection EQ as EQ.
    apply memblocks_one_inj in EQ as (EQb & EQo & EQv).
    apply N2Nat.inj in EQo; split; f_equal; congruence.
  Qed.

  Lemma list_heap_one_ne_addr a a' v v'
    : a <> a' <-> exists lh', list_heap_sum (list_heap_one a v) (list_heap_one a' v') = Some lh'.
  Proof.
    destruct a as [b o], a' as [b' o'].
    split; [ intros NE | intros (lh' & EQ) ].
    - cbn.
      specialize (proj1 (memblocks_one_ne_addr b b' (N.to_nat o) (N.to_nat o') v v')) as (mbs' & EQ).
      destruct (Nat.eq_dec b b'); [ subst b' | now left].
      destruct (N.eq_dec o o') as [|NEo]; [ subst; contradiction | right; intros contra; apply NEo, N2Nat.inj, contra ].
      rewrite EQ.
      eexists; reflexivity.
    - intros contra.
      cbn in EQ.
      destruct (memblocks_sum _ _) eqn:E; [clear lh' EQ | discriminate ].
      injection contra; intros; subst b' o'; clear contra.
      apply (proj2 (memblocks_one_eq_block_ne_offset b (N.to_nat o) (N.to_nat o) v v')); auto.
      eexists; apply E.
  Qed.

  Fixpoint memblock_with_one (mb: memblock) (o: nat) (v: memval): bool :=
    match o, mb with
    | 0, Some v'::_ => if Memval.eq_dec v v' then true else false
    | S o, _::mb => memblock_with_one mb o v
    | _, _ => false
    end.

  Fixpoint memblocks_with_one (mbs: list memblock) (b o: nat) (v: memval): bool :=
    match b, mbs with
    | 0, mb::_ => memblock_with_one mb o v
    | S b, _::mbs => memblocks_with_one mbs b o v
    | _, _ => false
    end.

  Definition list_heap_with_one (lh: list_heap_carrier) (a: Addr.t) (v: memval): bool :=
    match lh, a with
    | mkListHeap mbs _, Addr.mkAddr b o =>
        memblocks_with_one mbs b (N.to_nat o) v
    end.

  Fixpoint memblock_contains (mb: memblock) (o: nat): bool :=
    match o, mb with
    | 0, Some _::_ => true
    | S o, _::mb => memblock_contains mb o
    | _, _ => false
    end.

  Fixpoint memblocks_contains (mbs: list memblock) (b o: nat): bool :=
    match b, mbs with
    | 0, mb::_ => memblock_contains mb o
    | S b, _::mbs => memblocks_contains mbs b o
    | _, _ => false
    end.

  Definition list_heap_contains (lh: list_heap_carrier) (a: Addr.t): bool :=
    match lh, a with
    | mkListHeap mbs _, Addr.mkAddr b o =>
        memblocks_contains mbs b (N.to_nat o)
    end.

  Lemma list_heap_sum_comm: forall x y, list_heap_sum x y = list_heap_sum y x.
  Proof.
    intros [ mbx allocx ] [ mby allocy ].
    cbn -[Nat.ltb].
    rewrite (Bool.andb_comm allocy allocx).
    destruct (allocx && allocy) eqn:Ealloc; [ reflexivity | cbn -[Nat.ltb] ].
    rewrite (Bool.orb_comm (allocy && _) _).
    destruct (allocx && (length mbx <? length mby)); [ reflexivity | cbn -[Nat.ltb] ].
    destruct (allocy && (length mby <? length mbx)); [ reflexivity | cbn -[Nat.ltb] ].
    rewrite (memblocks_sum_comm mby mbx).
    destruct (memblocks_sum mbx mby); auto.
    destruct allocx, allocy; reflexivity.
  Qed.

  Definition list_heap_emp_with_alc (alc: option_alloc): list_heap_carrier :=
    match alc with
    | mkOptAlloc (Some n) =>
        mkListHeap (List.repeat [] n) true
    | mkOptAlloc None =>
        mkListHeap [] false
    end.

  Fixpoint memblocks_to_allocator (mbs: list memblock) (acc: nat): option_alloc :=
    match mbs with
    | [] => mkOptAlloc (Some acc)
    | _::mbs => memblocks_to_allocator mbs (S acc)
    end.

  Definition list_heap_to_allocator (lh: list_heap_carrier): option_alloc :=
    match lh with
    | mkListHeap mbs true => memblocks_to_allocator mbs 0
    | mkListHeap _ false => mkOptAlloc None
    end.

  Definition memblock_lookup (mb: memblock) (o: nat): option memval :=
    List.nth o mb None.

  Definition memblocks_lookup (mbs: list memblock) (b o: nat): option memval :=
    match List.nth_error mbs b with
    | Some mb => memblock_lookup mb o
    | None => None
    end.

  Definition list_heap_lookup (lh: list_heap_carrier) (p: Pointer.t): option memval :=
    match lh, p with
    | mkListHeap mbs _, Some(Addr.mkAddr b o, prov) =>
        if Pointer.allows p Operation.Read
        then
          memblocks_lookup mbs b (N.to_nat o)
        else
          None
    | _, None => None
    end.

  Fixpoint memblock_mutate (mb: memblock) (o: nat) (v: memval): option memblock :=
    match mb, o with
    | Some _::mb, 0 => Some ((Some v)::mb)
    | vo::mb, S o =>
        match memblock_mutate mb o v with
        | Some mb => Some (vo::mb)
        | None => None
        end
    | None::_, 0 | [], _ => None
    end.


  Fixpoint memblocks_mutate (mbs: list memblock) (b o: nat) (v: memval): option (list memblock) :=
    match mbs, b with
    | mb::mbs, 0 =>
        match memblock_mutate mb o v with
        | Some mb => Some (mb::mbs)
        | None => None
        end
    | mb::mbs, S b =>
        match memblocks_mutate mbs b o v with
        | Some mbs => Some(mb::mbs)
        | None => None
        end
    | [], _ => None
    end.

  Definition list_heap_mutate (lh: list_heap_carrier) (p: Pointer.t) (v: memval): option list_heap_carrier :=
    match lh, p with
    | mkListHeap mbs alloc, Some (Addr.mkAddr b o, prov) =>
        if Pointer.allows p Operation.Write then
          match memblocks_mutate mbs b (N.to_nat o) v with
          | Some mbs => Some (mkListHeap mbs alloc)
          | None => None
          end
        else
          None
    | _, None => None
    end.

  Definition list_heap_alloc (lh: list_heap_carrier) (sz: N.t) (v: memval): option (list_heap_carrier * Pointer.t) :=
    match lh with
    | mkListHeap mbs true =>
        Some (mkListHeap (mbs++[List.repeat (Some v) (N.to_nat sz)]) true, Some(Addr.mkAddr (length mbs) 0%N, Provenance.Allocation (length mbs) 0 sz 0 sz Permission.Free))
    | mkListHeap _ false => None
    end.

  Fixpoint memblocks_free (mbs: list memblock) (b: nat): option (list memblock) :=
    match mbs, b with
    | (_::_)::mbs, 0 => Some ([]::mbs)
    | mb::mbs, S b =>
        match memblocks_free mbs b with
        | Some mbs => Some (mb::mbs)
        | None => None
        end
    (* Double-free *)
    | []::_, _ => None
    (* Heap doesn't contain block *)
    | [], _ => None
    end.

  Definition list_heap_free (lh: list_heap_carrier) (p: Pointer.t): option list_heap_carrier :=
    match lh, p with
    | mkListHeap mbs alloc, Some(Addr.mkAddr b 0, prov) =>
        if Pointer.allows p Operation.Free then
          match memblocks_free mbs b with
          | Some mbs => Some (mkListHeap mbs alloc)
          | None => None
          end
        else
          None
    | _, _ => None
    end.


  Program Definition list_heap_separation: Separation :=
    {|
      Algebra.carrier := list_heap_carrier;
      op := list_heap_sum;
      id_e := list_heap_unit;
      op_comm := list_heap_sum_comm;
    |}.

  Local Opaque Nat.ltb.

  Next Obligation.
    intros [ mbx allocx ] [ mby allocy ] [ mbz allocz ].
    specialize (memblocks_sum_assc mbx mby mbz).
    unfold flip, list_heap_sum; cbn.
    destruct allocx, allocy, allocz;
      cbn.
    now destruct (Nat.ltb_spec (length mby) (length mbz)).
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    now destruct (memblocks_sum mby mbz).
    destruct (Nat.ltb_spec (length mbx) (length mby)); cbn.
    destruct (Nat.ltb_spec (length mbz) (length mby)); cbn.
    now destruct (memblocks_sum mby mbz).
    now destruct (memblocks_sum mby mbz).
    destruct (memblocks_sum mbx mby); cbn.
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | ].
    now destruct (memblocks_sum mby mbz).
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | cbn ].
    now destruct (memblocks_sum mby mbz).
    destruct (Nat.ltb_spec (length mbx) (length mby)); cbn.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mbyz) as [mbxyz|] eqn:Exyz; auto.
    specialize (memblocks_sum_length_max Eyz); lia.
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; cbn.
    destruct (Nat.ltb_spec (length mbxy) (length mbz)); cbn.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mbyz); [ | reflexivity ].
    specialize (memblocks_sum_length_max Exy);
    specialize (memblocks_sum_length_max Eyz);
      lia.
    destruct (memblocks_sum mbxy mbz) as [mbxyz|] eqn:Exyz; cbn.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | discriminate ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); cbn.
    intros Ex_yz.
    specialize (memblocks_sum_length_max Exy);
      specialize (memblocks_sum_length_max Exy).
    specialize (memblocks_sum_length_max Exyz);
      specialize (memblocks_sum_length_max Exyz).
    specialize (memblocks_sum_length_max Eyz);
      specialize (memblocks_sum_length_max Eyz).
    symmetry in Ex_yz;
      specialize (memblocks_sum_length_max Ex_yz);
      specialize (memblocks_sum_length_max Ex_yz).
    lia.
    destruct (memblocks_sum mbx mbyz); congruence.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mbyz) as [mbxyz|] eqn:Ex_yz; [ discriminate | reflexivity ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbx) (length mbyz)); [ reflexivity | cbn ].
    now intros EQ; rewrite <- EQ.
    destruct (Nat.ltb_spec (length mby) (length mbx)); [ reflexivity | ].
    destruct (memblocks_sum mbx mby) as [mb_x_y|] eqn:E_x_y; [ reflexivity | reflexivity ].
    destruct (Nat.ltb_spec (length mby) (length mbx)); cbn.
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mby mbz) as [mb_y_z|] eqn:E_y_z; [ cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mb_y_z) (length mbx)); [ reflexivity | cbn ].
    destruct (memblocks_sum mbx mb_y_z); [ | reflexivity ].
    specialize (memblocks_sum_length_max E_y_z); lia.
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; cbn.
    destruct (Nat.ltb_spec (length mbxy) (length mbz)); cbn.
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    specialize (memblocks_sum_length_max Exy); lia.
    destruct (Nat.ltb_spec (length mby) (length mbz)); cbn.
    destruct (memblocks_sum mbxy mbz) as [mbxyz|] eqn:Exyz; [ | reflexivity ].
    apply memblocks_sum_length_max in Exyz, Exy; lia.
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; cbn.
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ | now intros EQ; rewrite EQ ].
    apply memblocks_sum_length_max in Exy, Eyz; lia.
    now intros EQ; rewrite EQ.
    destruct (Nat.ltb_spec (length mby) (length mbz)); [ reflexivity | cbn ].
    destruct (memblocks_sum mby mbz) as [mbyz|]; [now cbn; intros EQ; rewrite <- EQ; destruct (Nat.ltb _ _) |reflexivity ].
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; [apply memblocks_sum_length_max in Exy|];
      cbn.
    destruct (Nat.ltb_spec (length mbz) (length mbxy)); cbn.
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ apply memblocks_sum_length_max in Eyz; cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ reflexivity | lia ].
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ lia | cbn ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ apply memblocks_sum_length_max in Eyz; cbn | now intros EQ; rewrite EQ].
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ lia | now intros EQ; rewrite EQ ].
    destruct (Nat.ltb_spec (length mbz) (length mby)); [ reflexivity | ].
    destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; [ apply memblocks_sum_length_max in Eyz; cbn | reflexivity ].
    destruct (Nat.ltb_spec (length mbyz) (length mbx)); [ reflexivity | now intros EQ; rewrite <- EQ ].
    destruct (memblocks_sum mbx mby) as [mbxy|] eqn:Exy; [ apply memblocks_sum_length_max in Exy; cbn | now cbn; destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz; auto; cbn; intros EQ; rewrite <- EQ ].
    intros EQ; rewrite EQ; clear EQ.
    now destruct (memblocks_sum mby mbz) as [mbyz|] eqn:Eyz.
  Qed.

  Next Obligation.
    intros [ mb alloc ]; cbn.
    now destruct (Nat.ltb_spec (length mb) 0); [ lia | rewrite Bool.andb_false_r].
  Qed.

  Next Obligation.
    intros [ mb alloc ]; cbn.
    destruct (Nat.ltb_spec (length mb) 0); [ lia | rewrite Bool.andb_false_r; cbn ].
    now rewrite Bool.orb_false_r, memblocks_sum_id_r.
  Qed.

  Canonical list_heap_separation.

  Program Definition list_heap_memory: Memory :=
    {|
      mem := list_heap_separation;
      one := list_heap_one;
      with_one := list_heap_with_one;
      contains := list_heap_contains;
      one_inj := list_heap_one_inj;
      one_ne_addr := list_heap_one_ne_addr;
    |}.

  Next Obligation.
    intros [ b o ] v [ [ mbs alloc ] EQ].
    revert EQ.
    unfold "$+", "$0"; cbn;
      unfold list_heap_unit.
    destruct alloc;
      [ destruct (Nat.ltb_spec (length mbs) (length (memblocks_one b (N.to_nat o) v))); [ discriminate | cbn; destruct (memblocks_sum _ _); congruence ]| cbn ].
    destruct (memblocks_sum _ _) eqn:Embs; [ intros EQ; inversion EQ; subst; clear EQ | discriminate ].
    apply memblocks_sum_length_max in Embs.
    cbn in Embs.
    destruct b; cbn in Embs;
      destruct (length mbs); lia.
  Qed.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Canonical list_heap_memory.

  Program Definition list_heap_heap: Heap :=
    {|
      Heap.heap := list_heap_memory;
      heap_alc := option_alloc_genid;
      emp_with_alc := list_heap_emp_with_alc;
      to_allocator := list_heap_to_allocator;
      lookup := list_heap_lookup;
      mutate := list_heap_mutate;
      Heap.alloc := list_heap_alloc;
      free := list_heap_free;
    |}.

  Next Obligation.
    reflexivity.
  Qed.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Admitted.

  Canonical list_heap_heap.

  Lemma memblocks_one_length b o v : length (memblocks_one b o v) = S b.
  Proof. induction b; cbn; lia. Qed.

  Fixpoint memblock_clear (mb: memblock) (o: nat): memblock :=
    match o, mb with
    | 0, _::mb => None::mb
    | S o, x::mb => x::(memblock_clear mb o)
    | _, [] => []
    end.

  Fixpoint memblocks_clear (mbs: list memblock) (b o: nat): list memblock :=
    match b, mbs with
    | 0, mb::mbs => (memblock_clear mb o)::mbs
    | S b, mb::mbs => mb::(memblocks_clear mbs b o)
    | _, [] => []
    end.

  Lemma memblocks_clear_length mbs b o :
    length (memblocks_clear mbs b o) = length mbs.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b]; cbn; auto.
  Qed.

  Lemma memblock_sum_one_l o v r result :
    memblock_sum (memblock_one o v) r = Some result ->
    memblock_with_one result o v = true.
  Proof.
    revert r result.
    induction o as [|o' IHo].
    intros [|[w|] r] result EQ; cbn in *; try discriminate.
    inversion EQ; subst; cbn.
    destruct (Memval.eq_dec v v) as [Heq | Hneq].
    reflexivity.
    exfalso; apply Hneq; reflexivity.
    destruct r; cbn in EQ; inversion EQ; subst; cbn.
    destruct (Memval.eq_dec v v) as [Heq | Hneq].
    reflexivity.
    exfalso; apply Hneq; reflexivity.
    destruct (Memval.eq_dec v v) as [Heq | Hneq].
    reflexivity.
    exfalso; apply Hneq; reflexivity.
    intros [|[w|] r] result EQ; cbn in *; try discriminate.
    inversion EQ; subst; cbn.
    eapply IHo; apply memblock_sum_id_r.
    destruct (memblock_sum (memblock_one o' v) r) eqn:E; [ | discriminate ].
    inversion EQ; subst; cbn.
    eapply IHo; exact E.
    destruct (memblock_sum (memblock_one o' v) r) eqn:E; [ | discriminate ].
    inversion EQ; subst; cbn.
    eapply IHo; exact E.
  Qed.


  Lemma memblocks_sum_one_l b o v rest result :
    memblocks_sum (memblocks_one b o v) rest = Some result ->
    memblocks_with_one result b o v = true.
  Proof.
    revert rest result.
    induction b as [|b IHb]; intros rest result EQ; cbn in *.
    - destruct rest as [|mb rest]; cbn in *.
      + inversion EQ; subst; cbn.
        eapply memblock_sum_one_l.
        apply memblock_sum_id_r.
      + destruct (memblock_sum (memblock_one o v) mb) eqn:Em; [ | discriminate ].
        destruct (memblocks_sum [] rest) eqn:Er; [ | discriminate ].
        inversion EQ; subst; cbn.
        eapply memblock_sum_one_l.
        exact Em.
    - destruct rest as [|mb rest]; cbn in *.
      + inversion EQ; subst; cbn.
        eapply IHb. 
        apply memblocks_sum_id_r.
      + destruct mb; cbn in EQ.
        * destruct (memblocks_sum (memblocks_one b o v) rest) eqn:Er; [ | discriminate ].
          inversion EQ; subst; cbn.
          eapply IHb; exact Er.
        * destruct (memblocks_sum (memblocks_one b o v) rest) eqn:Er; [ | discriminate ].
          inversion EQ; subst; cbn.
          eapply IHb; exact Er.
  Qed.

  Lemma memblock_clear_sum mb o v :
    memblock_with_one mb o v = true ->
    memblock_sum (memblock_one o v) (memblock_clear mb o) = Some mb.
  Proof.
    revert o.
    induction mb as [|[w|] mb]; intros [|o] EQ; cbn in *; try discriminate.
    - destruct (Memval.eq_dec v w); [ subst | discriminate ].
      destruct mb; reflexivity.
    - specialize (IHmb o EQ).
      rewrite IHmb.
      reflexivity.      
    - specialize (IHmb o EQ).
      rewrite IHmb.
      reflexivity.
  Qed.

  Lemma memblocks_clear_sum mbs b o v :
    memblocks_with_one mbs b o v = true ->
    memblocks_sum (memblocks_one b o v) (memblocks_clear mbs b o) = Some mbs.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b] EQ; cbn in *; try discriminate.
    - rewrite memblock_clear_sum; auto; rewrite memblocks_sum_id_r; reflexivity.
    - destruct (memblocks_sum (memblocks_one b o v) (memblocks_clear mbs b o)) eqn:E.
      + specialize (IHmbs b EQ); rewrite IHmbs in E; inversion E; subst.
        destruct mb; reflexivity.
      + specialize (IHmbs b EQ); rewrite IHmbs in E; discriminate.
  Qed.

  Lemma memblock_with_one_fun mb o v1 v2 :
    memblock_with_one mb o v1 = true ->
    memblock_with_one mb o v2 = true ->
    v1 = v2.
  Proof.
    revert o.
    induction mb as [|[w|] mb]; intros [|o] H1 H2; cbn in *; try discriminate.
    - destruct (Memval.eq_dec v1 w), (Memval.eq_dec v2 w); subst; auto; discriminate.
    - eapply IHmb; eassumption.
    - eapply IHmb; eassumption.
  Qed.

  Lemma memblocks_with_one_fun mbs b o v1 v2 :
    memblocks_with_one mbs b o v1 = true ->
    memblocks_with_one mbs b o v2 = true ->
    v1 = v2.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b] H1 H2; cbn in *; try discriminate.
    - eapply memblock_with_one_fun; eassumption.
    - eapply IHmbs; eassumption.
  Qed.

  Lemma memblock_contains_iff mb o :
    memblock_contains mb o = true <-> exists v, memblock_with_one mb o v = true.
  Proof.
    revert o.
    induction mb as [|[w|] mb]; intros [|o]; cbn; split; try discriminate.
    - intros (v & Hv); discriminate.
    - intros (v & Hv); discriminate.
    - intros _; exists w; now rewrite Memval.eq_dec_refl.
    - intros (v & Hv). destruct (Memval.eq_dec v w); auto; discriminate.
    - intros H. apply IHmb. exact H.
    - intros H. apply IHmb. exact H.
    - intros (v & Hv); discriminate.
    - specialize (IHmb o).
      destruct IHmb as [H_fwd H_bwd].
      intros H.
      apply H_fwd.
      exact H.
      -specialize (IHmb o).
      destruct IHmb as [H_fwd H_bwd].
      intros H.
      apply H_bwd.
      exact H.
  Qed.

  Lemma memblocks_contains_iff mbs b o :
    memblocks_contains mbs b o = true <-> exists v, memblocks_with_one mbs b o v = true.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b]; cbn; split; try (intros (v & Hv); discriminate).
    - intros H; discriminate H.
    - intros H; discriminate H.
    - intros H. apply memblock_contains_iff in H.
      destruct H as [v Hv]. exists v. exact Hv.
    - intros (v & Hv). apply memblock_contains_iff.
      exists v. exact Hv.
    - specialize (IHmbs b). destruct IHmbs as [H_fwd H_bwd].
      intros H. apply H_fwd. exact H.
    - specialize (IHmbs b). destruct IHmbs as [H_fwd H_bwd].
      intros H. apply H_bwd. exact H.
  Qed.

  Lemma memblocks_sum_one_conflict b o v mbs :
    memblocks_sum (memblocks_one b o v) mbs = None ->
    exists v', memblocks_with_one mbs b o v' = true.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b] EQ; cbn in *; try discriminate.
    - destruct (memblock_sum (memblock_one o v) mb) eqn:Em.
      + destruct (memblocks_sum [] mbs) eqn:Er; discriminate.
      + clear EQ IHmbs mbs.
        generalize dependent o.
        induction mb as [|[w|] mb]; intros [|o] Em; cbn in Em.
        discriminate Em.
        discriminate Em.
        cbn.
        exists w.
        destruct (eq_dec w w); [ reflexivity | contradiction ].
        destruct (memblock_sum (memblock_one o v) mb) eqn:E.
        discriminate Em.
        specialize (IHmb o E) as (v' & Hv').
        exists v'.
        cbn; exact Hv'.
        destruct mb; cbn in Em; discriminate Em.
        destruct (memblock_sum (memblock_one o v) mb) eqn:E.
        discriminate Em.
        specialize (IHmb o E) as (v' & Hv').
        exists v'.
        cbn; exact Hv'.
        - destruct (memblocks_sum (memblocks_one b o v) mbs) eqn:Er.
          cbn in EQ.
          destruct mb; cbn in EQ; discriminate EQ.
          specialize (IHmbs b Er) as (v' & Hv').
          exists v'.
          exact Hv'.
  Qed.


  Lemma memblock_with_one_conflict mb o v v' :
    memblock_with_one mb o v' = true ->
    memblock_sum (memblock_one o v) mb = None.
  Proof.
    revert o.
    induction mb as [|[w|] mb]; intros [|o] H; cbn in *; try discriminate.
    - destruct (Memval.eq_dec v' w); [ subst; reflexivity | discriminate ].
    - destruct (memblock_sum (memblock_one o v) mb) eqn:E; [ | reflexivity ].
      now rewrite (IHmb o H) in E.
    - destruct (memblock_sum (memblock_one o v) mb) eqn:E; [ | reflexivity ].
      now rewrite (IHmb o H) in E.
  Qed.


  Lemma memblocks_with_one_conflict mbs b o v v' :
    memblocks_with_one mbs b o v' = true ->
    memblocks_sum (memblocks_one b o v) mbs = None.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b] H; cbn in *; try discriminate.
    - rewrite (memblock_with_one_conflict mb o v v' H).
      now destruct (memblocks_sum [] mbs).
    - rewrite (IHmbs b H).
      destruct mb; reflexivity.
  Qed.

  Lemma memblock_with_one_one_false o v o' w :
    o' <> o ->
    memblock_with_one (memblock_one o v) o' w = false.
  Proof.
      revert o'.
      induction o as [|o IHo]; intros [|o'] H.
      - contradiction.
      - destruct o';  reflexivity.
      - cbn. reflexivity.
      - cbn. apply IHo.
        lia.
    Qed.

  Lemma memblocks_with_one_one_false_blk b o v b' o' w :
    b' <> b ->
    memblocks_with_one (memblocks_one b o v) b' o' w = false.
  Proof.
    revert b'.
    induction b as [|b IHb]; intros [|b'] H.
    - contradiction.
    - cbn. destruct b'; reflexivity.
    - cbn. destruct o'; reflexivity.
    - cbn. apply IHb.
      lia.
  Qed.

  Lemma memblock_sum_one_neq o v mb mb' o' w :
    memblock_sum (memblock_one o v) mb = Some mb' ->
    o' <> o ->
    memblock_with_one mb' o' w = memblock_with_one mb o' w.
  Proof.
    revert mb mb' o'.
    induction o as [|o IHo]; intros mb mb' [|o'] H Hneq.
    - contradiction.
    - destruct mb as [|[vm|] mb]; cbn in *.
      + inversion H; subst; cbn; destruct o'; reflexivity.
      + discriminate.
      + destruct mb; cbn in H; inversion H; subst; cbn.
        * reflexivity.
        * reflexivity.
    - destruct mb as [|[vm|] mb]; cbn in *; inversion H; subst; cbn.
      reflexivity.
      destruct (memblock_sum (memblock_one o v) mb) eqn:E; try discriminate.
      inversion H; subst; cbn. reflexivity.
      destruct (memblock_sum (memblock_one o v) mb) eqn:E; try discriminate.
      inversion H; subst; cbn. reflexivity.
    - destruct mb as [|[vm|] mb]; cbn in H.
      + inversion H; subst; cbn.
      apply memblock_with_one_one_false.
        lia.
      + destruct (memblock_sum (memblock_one o v) mb) eqn:E; try discriminate.
        inversion H; subst; cbn.
        apply IHo; [ exact E | lia ].
      + destruct (memblock_sum (memblock_one o v) mb) eqn:E; try discriminate.
        inversion H; subst; cbn.
        apply IHo; [ exact E | lia ].
  Qed.

  Lemma memblocks_sum_one_neq b o v mbs mbs' b' o' w :
    memblocks_sum (memblocks_one b o v) mbs = Some mbs' ->
    (b' <> b \/ o' <> o) ->
    memblocks_with_one mbs' b' o' w = memblocks_with_one mbs b' o' w.
  Proof.
    revert mbs mbs' b' o' w.
    induction b as [|b IHb]; intros mbs mbs' b' o' w H Hneq.
    - cbn [memblocks_one] in H.
      destruct mbs as [|mb mbs_rest]; cbn in H.
      + inversion H; subst; cbn.
      destruct b' as [|b'].
        * destruct Hneq as [Hneq | Hneq].
          -- contradiction.
          -- cbn. apply memblock_with_one_one_false. exact Hneq.
        * cbn. destruct b'; reflexivity.
      + destruct (memblock_sum (memblock_one o v) mb) eqn:Em; try discriminate.
    inversion H; subst; cbn.
    destruct b' as [|b'].
    * destruct Hneq as [Hneq | Hneq].
      -- contradiction.
      -- cbn. apply memblock_sum_one_neq with (o := o) (v := v) (mb := mb) (mb' := m); [ exact Em | exact Hneq ].
      * reflexivity.
    - destruct mbs as [|mb mbs_rest]; cbn in H.
  + inversion H; subst; cbn.
    destruct b' as [|b'].
    * destruct o'; reflexivity.
    * assert (Hempty : memblocks_with_one [] b' o' w = false) by (destruct b'; reflexivity).
      rewrite <- Hempty.
      apply IHb with (mbs' := memblocks_one b o v).
      -- apply memblocks_sum_id_r.
      -- destruct Hneq as [Hneq | Hneq]; [ left; lia | right; exact Hneq ].
    + destruct (memblocks_sum (memblocks_one b o v) mbs_rest) eqn:E; try discriminate.
    destruct mb; cbn in H; inversion H; subst; cbn.
    * destruct b' as [|b0].
      -- destruct o'; reflexivity.
      -- cbn. apply IHb with (mbs' := l); [ exact E | ].
         destruct Hneq as [Hneq | Hneq]; [ left; lia | right; exact Hneq ].
    * destruct b' as [|b0].
      -- destruct o' as [|o']; [ destruct o0; reflexivity | reflexivity ].
      -- cbn. apply IHb with (mbs' := l); [ exact E | ].
         destruct Hneq as [Hneq | Hneq]; [ left; lia | right; exact Hneq ].
         * destruct mb; cbn in H; discriminate H.
  Qed.

  Lemma memblock_with_one_iff_nth mb o v :
    memblock_with_one mb o v = true <-> List.nth o mb None = Some v.
  Proof.
    revert o.
    induction mb as [|[w|] mb]; intros [|o]; cbn; split; try discriminate.
    - intros H.
      destruct (Memval.eq_dec v w) as [Heq|Hneq]; [ subst; reflexivity | discriminate ].
    - intros H. inversion H; subst.
      destruct (Memval.eq_dec v v) as [|Hneq]; [ reflexivity | exfalso; apply Hneq; reflexivity ].
    - apply IHmb.
    - apply IHmb.
    - apply IHmb.
    - apply IHmb.
  Qed.

  Lemma memblocks_with_one_iff_lookup mbs b o v :
    memblocks_with_one mbs b o v = true <-> memblocks_lookup mbs b o = Some v.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b]; cbn; split; try discriminate.
    - apply memblock_with_one_iff_nth.
    - apply memblock_with_one_iff_nth.
    - apply IHmbs.
    - apply IHmbs.
  Qed.

  Lemma memblock_mutate_one_self o v' v :
    memblock_mutate (memblock_one o v') o v = Some (memblock_one o v).
  Proof.
    induction o as [|o]; cbn; [ reflexivity | rewrite IHo; reflexivity ].
  Qed.

  Lemma memblock_mutate_some_iff mb o v :
    (exists v0, memblock_with_one mb o v0 = true) <-> exists mb', memblock_mutate mb o v = Some mb'.
    Proof.
      revert o.
      induction mb as [|[w|] mb]; intros [|o]; cbn; split;
        try (intros (? & H); discriminate);
        try (intros (? & H); discriminate).
      - intros _; exists (Some v :: mb); reflexivity.
      - intros _; exists w;
          destruct (Memval.eq_dec w w) as [|Hneq]; [ reflexivity | exfalso; apply Hneq; reflexivity ].
      - intros (mb'0 & Hmut).
      destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst.
      + exists (Some w :: m). reflexivity.
      + destruct (IHmb o) as [Hforward _].
        assert (Hexist : exists v0 : memval, memblock_with_one mb o v0 = true) by (exists mb'0; exact Hmut).
        apply Hforward in Hexist as [mb_tail Hmut_eq].
        rewrite Hmut_eq in E.
        discriminate E.
      - intros (mb' & Hmut).
      destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst.
      destruct (IHmb o) as [_ Hbackward].
      assert (Hexist : exists mb' : memblock, memblock_mutate mb o v = Some mb') by (exists m; exact E).
      apply Hbackward in Hexist as (v0 & Hv).
      exists v0. exact Hv.
      - intros (v0 & Hv).
      destruct (IHmb o) as [Hforward _].
      assert (Hexist : exists v1 : memval, memblock_with_one mb o v1 = true) by (exists v0; exact Hv).
      apply Hforward in Hexist as [mb_tail Hmut].
      rewrite Hmut.
      exists (None :: mb_tail).
      reflexivity.
    - intros (mb' & Hmut).
      destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst.
      destruct (IHmb o) as [_ Hbackward].
      assert (Hexist : exists mb' : memblock, memblock_mutate mb o v = Some mb') by (exists m; exact E).
      apply Hbackward in Hexist as (v0 & Hv).
      exists v0. exact Hv.
  Qed.

  Lemma memblocks_mutate_some_iff mbs b o v :
    (exists v0, memblocks_with_one mbs b o v0 = true) <-> exists mbs', memblocks_mutate mbs b o v = Some mbs'.
  Proof.
    revert b.
    induction mbs as [|mb mbs]; intros [|b]; cbn; split;
      try (intros (? & H); discriminate);
      try (intros (? & H); discriminate).
    - intros (v0 & H).
      destruct (proj1 (memblock_mutate_some_iff mb o v) (ex_intro _ v0 H)) as (mb' & Hmb').
      rewrite Hmb'; eauto.
    - intros (mbs' & H).
      destruct (memblock_mutate mb o v) eqn:E; [ | discriminate ].
      exact (proj2 (memblock_mutate_some_iff mb o v) (ex_intro _ m E)).
    - intros (v0 & H).
      destruct (proj1 (IHmbs b) (ex_intro _ v0 H)) as (mbs' & Hmbs').
      rewrite Hmbs'; eauto.
    - intros (mbs' & H).
      destruct (memblocks_mutate mbs b o v) eqn:E; [ | discriminate ].
      exact (proj2 (IHmbs b) (ex_intro _ l E)).
  Qed.

  Lemma memblock_mutate_one_sum o v' mb m v mb_new :
    memblock_sum (memblock_one o v') mb = Some m ->
    memblock_mutate m o v = Some mb_new ->
    memblock_sum (memblock_one o v) mb = Some mb_new.
  Proof.
    revert mb m mb_new.
    induction o as [|o IHo]; intros mb m mb_new H Hmut.
    - destruct mb as [|[w|] mb].
      + rewrite memblock_sum_id_r in H; inversion H; subst.
        cbn [memblock_mutate] in Hmut; inversion Hmut; subst.
        rewrite memblock_sum_id_r; reflexivity.
      + cbn [memblock_sum] in H; discriminate.
      + cbn [memblock_sum] in H.
        cbn in H. inversion H; subst; clear H.
        cbn in Hmut. inversion Hmut; subst; clear Hmut.
        rewrite H0.
        destruct mb as [|m0 mb_rest]; cbn in *; inversion H1; subst.
        * cbn in H0. inversion H0; subst. reflexivity.
        * cbn in H0. inversion H0; subst. reflexivity.
    - destruct mb as [| vo mb_tail].
      + cbn in H. inversion H; subst.
        cbn in Hmut.
        rewrite memblock_mutate_one_self in Hmut.
        inversion Hmut; subst.
        cbn. reflexivity.
      + destruct vo as [w|]; cbn in H.
        * destruct (memblock_sum (memblock_one o v') mb_tail) eqn:E; try discriminate.
          inversion H; subst; clear H.
          cbn in Hmut. destruct (memblock_mutate m0 o v) eqn:Emut; try discriminate.
          inversion Hmut; subst; clear Hmut.
          cbn. rewrite (IHo mb_tail m0 m E Emut). reflexivity.
        * destruct (memblock_sum (memblock_one o v') mb_tail) eqn:E; try discriminate.
          inversion H; subst; clear H.
          cbn in Hmut. destruct (memblock_mutate m0 o v) eqn:Emut; try discriminate.
          inversion Hmut; subst; clear Hmut.
          cbn. rewrite (IHo mb_tail m0 m E Emut). reflexivity.
  Qed.

  Lemma memblocks_sum_mutate b o v' rmbs mbs_old v mbs_new :
    memblocks_sum (memblocks_one b o v') rmbs = Some mbs_old ->
    memblocks_mutate mbs_old b o v = Some mbs_new ->
    memblocks_sum (memblocks_one b o v) rmbs = Some mbs_new.
  Proof.
    revert rmbs mbs_old mbs_new.
    induction b as [|b IHb]; intros rmbs mbs_old mbs_new H Hmut.
    - destruct rmbs as [|rb rmbs_rest].
      + rewrite memblocks_sum_id_r in H; inversion H; subst; cbn in Hmut.
        rewrite memblock_mutate_one_self in Hmut; inversion Hmut; subst.
        rewrite memblocks_sum_id_r; reflexivity.
      + cbn in H.
        destruct (memblock_sum (memblock_one o v') rb) as [m_inner|] eqn:Em; [ | discriminate ].
        inversion H; subst; cbn in Hmut.
        destruct (memblock_mutate m_inner o v) as [mb_inner|] eqn:E2; [ | discriminate ].
        inversion Hmut; subst; cbn.
        rewrite (memblock_mutate_one_sum o v' rb m_inner v mb_inner Em E2); reflexivity.
    - destruct rmbs as [|rb rmbs_rest].
      + rewrite memblocks_sum_id_r in H; inversion H; subst; cbn in Hmut.
        destruct (memblocks_mutate (memblocks_one b o v') b o v) as [mbs_inner|] eqn:E2; [ | discriminate ].
        inversion Hmut; subst.
        specialize (IHb [] (memblocks_one b o v') mbs_inner (memblocks_sum_id_r _) E2) as IH.
        rewrite memblocks_sum_id_r in IH; inversion IH; subst.
        cbn [memblocks_one memblocks_sum]; reflexivity.
      + cbn [memblocks_one memblocks_sum] in H.
        rewrite memblock_sum_id_l in H; cbn in H.
        destruct (memblocks_sum (memblocks_one b o v') rmbs_rest) as [mbs_inner|] eqn:Er; [ | discriminate ].
        inversion H; subst; cbn in Hmut.
        destruct (memblocks_mutate mbs_inner b o v) as [mbs_inner_new|] eqn:E2; [ | discriminate ].
        inversion Hmut; subst.
        cbn [memblocks_one memblocks_sum].
        rewrite memblock_sum_id_l; cbn.
        rewrite (IHb rmbs_rest mbs_inner mbs_inner_new Er E2); reflexivity.
  Qed.

  Lemma memblocks_mutate_length mbs b o v mbs' :
    memblocks_mutate mbs b o v = Some mbs' -> length mbs' = length mbs.
  Proof.
    revert b mbs'.
    induction mbs as [|mb mbs IHmbs]; intros [|b] mbs' H; cbn in *; try discriminate.
    - destruct (memblock_mutate mb o v) eqn:E; [ | discriminate ].
      inversion H; subst; reflexivity.
    - destruct (memblocks_mutate mbs b o v) eqn:E; [ | discriminate ].
      inversion H; subst; cbn.
      f_equal.
      apply (IHmbs b l E).
  Qed.

  Lemma alloc_shift_fw_succeeds mbs alloc sz v lh' p o :
    list_heap_alloc (mkListHeap mbs alloc) sz v = Some (lh', p) ->
    (o < sz)%N ->
    exists p', Pointer.shift_fw p o = Some p'.
  Proof.
    intros H_alc Ho.
    unfold list_heap_alloc in H_alc.
    inversion H_alc.
    destruct alloc; [ | discriminate ].
    inversion H_alc; subst lh' p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw].
    unfold Provenance.within, Provenance.wf.
    rewrite !Nat.eqb_refl.
    rewrite !N.add_0_l.
    destruct (N.leb_spec0 0 0); [| lia ].
    destruct (N.leb_spec0 sz sz); [| lia ].
    destruct (N.leb_spec0 0 sz); [| lia ].
    destruct (N.leb_spec0 0 o); [| lia ].
    destruct (N.leb_spec0 o sz); [| lia ].
    cbn.
    eexists.
    reflexivity.
  Qed.

  Lemma alloc_write_allows mbs alloc sz v lh' p o :
    list_heap_alloc (mkListHeap mbs alloc) sz v = Some (lh', p) ->
    (o < sz)%N ->
    Pointer.allows (match Pointer.shift_fw p o with Some p' => p' | None => Pointer.NULL end) Operation.Write = true.
  Proof.
    intros H_alc Ho.
    specialize (alloc_shift_fw_succeeds mbs alloc sz v lh' p o H_alc Ho) as [p' Hp'].
    rewrite Hp'.
    unfold list_heap_alloc in H_alc.
    destruct alloc; [ | discriminate ].
    inversion H_alc; subst lh' p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw] in Hp'.
    rewrite !N.add_0_l in Hp'.
    unfold Provenance.within, Provenance.wf in Hp'.
    rewrite !Nat.eqb_refl in Hp'.
    destruct (N.leb_spec0 0 0) in Hp'; [| lia ].
    destruct (N.leb_spec0 sz sz) in Hp'; [| lia ].
    destruct (N.leb_spec0 0 sz) in Hp'; [| lia ].
    destruct (N.leb_spec0 0 o) in Hp'; [| lia ].
    destruct (N.leb_spec0 o sz) in Hp'; [| lia ].
    cbn in Hp'.
    inversion Hp'; subst p'; clear Hp'.
    cbn [Pointer.allows Provenance.allows].
    unfold Provenance.within, Provenance.wf.
    rewrite !Nat.eqb_refl.
    destruct (N.leb_spec0 0 0); [| lia ].
    destruct (N.leb_spec0 sz sz); [| lia ].
    destruct (N.leb_spec0 0 o); [| lia ].
    destruct (N.leb_spec0 o sz); [| lia ].
    destruct (N.ltb_spec0 o sz); [| lia ].
    cbn.
    reflexivity.
  Qed.

  Lemma memblocks_mutate_alloc_succeeds mbs sz v o v_new :
    (N.to_nat o < N.to_nat sz)%nat ->
    exists mbs', memblocks_mutate (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o) v_new = Some mbs'.
  Proof.
    intros Ho.
    induction mbs as [|mb mbs' IHmbs]; cbn.
    - generalize dependent (N.to_nat o).
      induction (N.to_nat sz) as [|k IHk]; intros idx Hidx.
      + lia.
      + destruct idx as [|idx]; cbn.
      * eexists; reflexivity.
        * assert (Hidx_tail: idx < k) by lia.
          specialize (IHk idx Hidx_tail) as [mbs_tail Hmb].
          destruct (memblock_mutate (repeat (Some v) k) idx v_new) eqn:Emut; try discriminate.
          inversion Hmb; subst mbs_tail; clear Hmb.
          eexists; reflexivity.
    - destruct IHmbs as [mbs_tail IH].
      rewrite IH.
      eexists; reflexivity.
  Qed.

  Lemma memblock_with_one_repeat k o v :
    o < k ->
    memblock_with_one (List.repeat (Some v) k) o v = true.
  Proof.
    generalize dependent o.
    induction k as [|k IHk]; intros o Ho.
    - lia.
    - destruct o as [|o]; cbn.
      + now rewrite Memval.eq_dec_refl.
      + apply IHk.
        lia.
  Qed.

  Lemma memblocks_with_one_append_block mbs sz o v :
    (N.to_nat o < N.to_nat sz)%nat ->
    memblocks_with_one (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o) v = true.
  Proof.
    intros Ho.
    induction mbs as [|mb mbs IH]; cbn.
    - apply memblock_with_one_repeat; exact Ho.
    - exact IH.
  Qed.

  Lemma memblock_contains_after_mutate mb o v mb' o' :
    memblock_mutate mb o v = Some mb' ->
    memblock_contains mb o' = true ->
    memblock_contains mb' o' = true.
    Proof.
    revert o o' mb'.
    induction mb as [|[w|] mb IH]; intros [|o] [|o'] mb' Hmut Hcont;
      cbn in *; try discriminate.
    - inversion Hmut; subst; reflexivity.
    - inversion Hmut; subst; exact Hcont.
    - destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst; reflexivity.
    - destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst.
      cbn.
      eapply IH; [ exact E | exact Hcont ].
    - destruct (memblock_mutate mb o v) eqn:E; try discriminate.
    inversion Hmut; subst.
    cbn.
    eapply IH; [ exact E | exact Hcont ].
  Qed.

  Lemma memblocks_contains_after_mutate mbs b o v mbs' b' o' :
    memblocks_mutate mbs b o v = Some mbs' ->
    memblocks_contains mbs b' o' = true ->
    memblocks_contains mbs' b' o' = true.
    Proof.
    revert b b' mbs'.
    induction mbs as [|mb mbs IH]; intros [|b] [|b'] mbs' Hmut Hcont;
      cbn in *; try discriminate.
    - destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst.
      eapply memblock_contains_after_mutate; [ exact E | exact Hcont ].
    - destruct (memblock_mutate mb o v) eqn:E; try discriminate.
      inversion Hmut; subst; exact Hcont.
    - destruct (memblocks_mutate mbs b o v) eqn:E; try discriminate.
      inversion Hmut; subst; exact Hcont.
    - destruct (memblocks_mutate mbs b o v) eqn:E; try discriminate.
      inversion Hmut; subst.
      cbn.
      eapply IH; [ exact E | exact Hcont ].
  Qed.

  Lemma memblocks_contains_alloc_append mbs sz o v :
    (N.to_nat o < N.to_nat sz)%nat ->
    memblocks_contains (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o) = true.
  Proof.
    intros Ho.
    apply (proj2 (memblocks_contains_iff _ _ _)).
    exists v.
    apply memblocks_with_one_append_block; exact Ho.
  Qed.

  Lemma alloc_shift_wvalid mbs alloc sz v lh' p o p' :
    list_heap_alloc (mkListHeap mbs alloc) sz v = Some (lh', p) ->
    (o < sz)%N ->
    Pointer.shift_fw p o = Some p' ->
    Heap.Facts.WValid lh' p'.
  Proof.
    intros H_alc Ho Hshift.
    unfold list_heap_alloc in H_alc.
    destruct alloc; [|discriminate].
    inversion H_alc; subst lh' p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw] in Hshift.
    unfold Provenance.within, Provenance.wf in Hshift.
    rewrite !Nat.eqb_refl, !N.add_0_l in Hshift.
    destruct (N.leb_spec0 0 0) in Hshift; [|lia].
    destruct (N.leb_spec0 sz sz) in Hshift; [|lia].
    destruct (N.leb_spec0 0 sz) in Hshift; [|lia].
    destruct (N.leb_spec0 0 o) in Hshift; [|lia].
    destruct (N.leb_spec0 o sz) in Hshift; [|lia].
    cbn in Hshift.
    inversion Hshift; subst p'; clear Hshift.
    left.
    unfold Heap.Facts.Valid.
    exists (Addr.mkAddr (length mbs) o), v.
    split.
    - constructor.
    - unfold Substate.
      exists (mkListHeap (memblocks_clear (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o)) true).
      unfold list_heap_sum; cbn.
      assert (H_sum : memblocks_sum (memblocks_one (length mbs) (N.to_nat o) v)
                        (memblocks_clear (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o)) =
                      Some (mbs ++ [List.repeat (Some v) (N.to_nat sz)])).
      { apply memblocks_clear_sum.
        - induction mbs as [|mb mbs' IH]; cbn.
          + apply memblock_with_one_repeat.
            destruct o, sz; cbn; try lia; try discriminate.
          + exact IH. }
      cbn.
      unfold "$+"; unfold list_heap_sum; cbn.
      rewrite memblocks_clear_length, memblocks_one_length.
      rewrite length_app; cbn; try lia.
      rewrite H_sum.
      cbn.
      replace (length mbs + 1) with (S (length mbs)) by lia.
      cbn.
      destruct (S (length mbs) <? S (length mbs)) eqn:H_lt.
      apply Nat.ltb_lt in H_lt. lia.
      reflexivity.
  Qed.

  Lemma alloc_shift_wvalid_after_mut mbs sz v lh' p o p' lh'' ptr_m v_m :
    list_heap_alloc (mkListHeap mbs true) sz v = Some (lh', p) ->
    (o < sz)%N ->
    Pointer.shift_fw p o = Some p' ->
    list_heap_mutate lh' ptr_m v_m = Some lh'' ->
    Heap.Facts.WValid lh'' p'.
  Proof.
    intros H_alc Ho Hshift Hmut.
    unfold list_heap_alloc in H_alc.
    inversion H_alc; subst lh' p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw] in Hshift.
    unfold Provenance.within, Provenance.wf in Hshift.
    rewrite !Nat.eqb_refl, !N.add_0_l in Hshift.
    destruct (N.leb_spec0 0 0) in Hshift; [|lia].
    destruct (N.leb_spec0 sz sz) in Hshift; [|lia].
    destruct (N.leb_spec0 0 sz) in Hshift; [|lia].
    destruct (N.leb_spec0 0 o) in Hshift; [|lia].
    destruct (N.leb_spec0 o sz) in Hshift; [|lia].
    cbn in Hshift. inversion Hshift; subst p'; clear Hshift.
    unfold list_heap_mutate in Hmut.
    destruct ptr_m as [[[b_m o_m] prov_m]|]; [|discriminate].
    destruct (Pointer.allows _ Operation.Write); [|discriminate].
    destruct (memblocks_mutate (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) b_m (N.to_nat o_m) v_m)
      as [mbs''|] eqn:Emut; [|discriminate].
    inversion Hmut; subst lh''; clear Hmut.
    assert (Hcont : memblocks_contains mbs'' (length mbs) (N.to_nat o) = true).
    { apply (memblocks_contains_after_mutate _ b_m (N.to_nat o_m) v_m _ _ (N.to_nat o) Emut).
      apply memblocks_contains_alloc_append.
      destruct o, sz; cbn; try lia; try discriminate. }
    left.
    unfold Heap.Facts.Valid.
    apply memblocks_contains_iff in Hcont. destruct Hcont as [mv Hw1].
    exists {| Addr.block := length mbs; Addr.offset := o |}, mv.
    split.
    - constructor.
    - unfold Substate. unfold "$<=". unfold "$+"; unfold list_heap_sum; cbn.
    exists {| list_heap := memblocks_clear mbs'' (length mbs) (N.to_nat o); alloc := true |}.
    cbn.
    rewrite memblocks_one_length.
    replace (S (length mbs) <? 1) with false by reflexivity.
    rewrite memblocks_clear_length.
    assert (Hlen : length mbs'' = S (length mbs)).
    { apply memblocks_mutate_length in Emut. rewrite Emut. rewrite length_app; cbn; lia. }
    rewrite Hlen.
    destruct (S (length mbs) <? S (length mbs)) eqn:H_lt; [apply Nat.ltb_lt in H_lt; lia |].
    assert (H_sum : memblocks_sum (memblocks_one (length mbs) (N.to_nat o) mv)
                      (memblocks_clear mbs'' (length mbs) (N.to_nat o)) = Some mbs'').
    cbn in Hw1.
    apply memblocks_clear_sum.
    exact Hw1.
    rewrite H_sum.
    reflexivity.
  Qed.

  Lemma alloc_mutate_succeeds mbs alloc sz v lh' p o p' val :
    list_heap_alloc (mkListHeap mbs alloc) sz v = Some (lh', p) ->
    (o < sz)%N ->
    Pointer.shift_fw p o = Some p' ->
    exists lh'', list_heap_mutate lh' p' val = Some lh''.
  Proof.
    intros H_alc Ho Hshift.
    unfold list_heap_alloc in H_alc.
    destruct alloc; [|discriminate].
    inversion H_alc; subst lh' p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw] in Hshift.
    unfold Provenance.within, Provenance.wf in Hshift.
    rewrite !Nat.eqb_refl, !N.add_0_l in Hshift.
    destruct (N.leb_spec0 0 0) in Hshift; [|lia].
    destruct (N.leb_spec0 sz sz) in Hshift; [|lia].
    destruct (N.leb_spec0 0 sz) in Hshift; [|lia].
    destruct (N.leb_spec0 0 o) in Hshift; [|lia].
    destruct (N.leb_spec0 o sz) in Hshift; [|lia].
    cbn in Hshift. inversion Hshift; subst p'; clear Hshift.
    unfold list_heap_mutate.
    cbn [Pointer.allows Provenance.allows Provenance.within Provenance.wf].
    rewrite !Nat.eqb_refl.
    destruct (N.leb_spec0 0 0); [|lia].
    destruct (N.leb_spec0 sz sz); [|lia].
    destruct (N.leb_spec0 0 o); [|lia].
    destruct (N.leb_spec0 o sz); [|lia].
    destruct (N.ltb_spec0 o sz); [|lia].
    cbn.
    destruct (memblocks_mutate_alloc_succeeds mbs sz v o val) as [mbs' Emut].
    { destruct o, sz; cbn; try lia; try discriminate. }
    exists {| list_heap := mbs'; alloc := true |}.
    pattern (memblocks_mutate (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o) val).
    rewrite Emut.
    reflexivity.
  Qed.

  Lemma alloc_mutate_mutate_succeeds mbs alloc sz v lh' p o1 p1 o2 p2 lh1 val1 val2 :
    list_heap_alloc (mkListHeap mbs alloc) sz v = Some (lh', p) ->
    (o1 < sz)%N ->
    Pointer.shift_fw p o1 = Some p1 ->
    list_heap_mutate lh' p1 val1 = Some lh1 ->
    (o2 < sz)%N ->
    Pointer.shift_fw p o2 = Some p2 ->
    exists lh2, list_heap_mutate lh1 p2 val2 = Some lh2.
  Proof.
    intros H_alc Ho1 Hshift1 Hmut1 Ho2 Hshift2.
    unfold list_heap_alloc in H_alc.
    destruct alloc; [|discriminate].
    inversion H_alc; subst lh' p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw] in Hshift1.
    unfold Provenance.within, Provenance.wf in Hshift1.
    rewrite !Nat.eqb_refl, !N.add_0_l in Hshift1.
    destruct (N.leb_spec0 0 0) in Hshift1; [|lia].
    destruct (N.leb_spec0 sz sz) in Hshift1; [|lia].
    destruct (N.leb_spec0 0 sz) in Hshift1; [|lia].
    destruct (N.leb_spec0 0 o1) in Hshift1; [|lia].
    destruct (N.leb_spec0 o1 sz) in Hshift1; [|lia].
    cbn in Hshift1. inversion Hshift1; subst p1; clear Hshift1.
    cbn [Pointer.shift_fw Addr.shift_fw] in Hshift2.
    unfold Provenance.within, Provenance.wf in Hshift2.
    rewrite !Nat.eqb_refl, !N.add_0_l in Hshift2.
    destruct (N.leb_spec0 0 0) in Hshift2; [|lia].
    destruct (N.leb_spec0 sz sz) in Hshift2; [|lia].
    destruct (N.leb_spec0 0 sz) in Hshift2; [|lia].
    destruct (N.leb_spec0 0 o2) in Hshift2; [|lia].
    destruct (N.leb_spec0 o2 sz) in Hshift2; [|lia].
    cbn in Hshift2. inversion Hshift2; subst p2; clear Hshift2.
    unfold list_heap_mutate in Hmut1.
    cbn [Pointer.allows Provenance.allows Provenance.within Provenance.wf] in Hmut1.
    rewrite !Nat.eqb_refl in Hmut1.
    destruct (N.leb_spec0 0 0) in Hmut1; [|lia].
    destruct (N.leb_spec0 sz sz) in Hmut1; [|lia].
    destruct (N.leb_spec0 0 o1) in Hmut1; [|lia].
    destruct (N.leb_spec0 o1 sz) in Hmut1; [|lia].
    destruct (N.ltb_spec0 o1 sz) in Hmut1; [|lia].
    cbn in Hmut1.
    destruct (memblocks_mutate (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) (length mbs) (N.to_nat o1) val1)
      as [mbs1|] eqn:Emut1; [|discriminate].
    inversion Hmut1; subst lh1; clear Hmut1.
    unfold list_heap_mutate.
    cbn [Pointer.allows Provenance.allows Provenance.within Provenance.wf].
    rewrite !Nat.eqb_refl.
    destruct (N.leb_spec0 0 0); [|lia].
    destruct (N.leb_spec0 sz sz); [|lia].
    destruct (N.leb_spec0 0 o2); [|lia].
    destruct (N.leb_spec0 o2 sz); [|lia].
    destruct (N.ltb_spec0 o2 sz); [|lia].
    cbn.
    assert (Hcont : memblocks_contains mbs1 (length mbs) (N.to_nat o2) = true).
    { apply (memblocks_contains_after_mutate _ (length mbs) (N.to_nat o1) val1 _ _ (N.to_nat o2) Emut1).
      apply memblocks_contains_alloc_append.
      destruct o2, sz; cbn; try lia; try discriminate. }
    apply memblocks_contains_iff in Hcont.
    rewrite memblocks_mutate_some_iff in Hcont.
    destruct Hcont as [mbs2 Emut2].
    exists {| list_heap := mbs2; alloc := true |}.
    pattern (memblocks_mutate mbs1 (length mbs) (N.to_nat o2) val2).
    rewrite Emut2.
    reflexivity.
  Qed.

  Lemma alloc_heap_neq_orig mbs sz v lh' p p1 p2 lh1 lh2 v1 v2 :
    list_heap_alloc (mkListHeap mbs true) sz v = Some (lh', p) ->
    list_heap_mutate lh' p1 v1 = Some lh1 ->
    list_heap_mutate lh1 p2 v2 = Some lh2 ->
    lh2 <> mkListHeap mbs true.
  Proof.
    intros H_alc Hmut1 Hmut2.
    unfold list_heap_alloc in H_alc.
    inversion H_alc; subst lh' p; clear H_alc.
    unfold list_heap_mutate in Hmut1.
    destruct p1 as [[[b1 o1] prov1]|]; [|discriminate].
    destruct (Pointer.allows _ Operation.Write); [|discriminate].
    destruct (memblocks_mutate (mbs ++ [List.repeat (Some v) (N.to_nat sz)]) b1 (N.to_nat o1) v1)
      as [mbs1|] eqn:Emut1; [|discriminate].
    inversion Hmut1; subst lh1; clear Hmut1.
    unfold list_heap_mutate in Hmut2.
    destruct p2 as [[[b2 o2] prov2]|]; [|discriminate].
    destruct (Pointer.allows _ Operation.Write); [|discriminate].
    destruct (memblocks_mutate mbs1 b2 (N.to_nat o2) v2)
      as [mbs2|] eqn:Emut2; [|discriminate].
    inversion Hmut2; subst lh2; clear Hmut2.
    intros contra.
    pose proof (memblocks_mutate_length _ _ _ _ _ Emut2) as Hlen2.
    pose proof (memblocks_mutate_length _ _ _ _ _ Emut1) as Hlen1.
    rewrite length_app in Hlen1; cbn [length] in Hlen1.
    assert (Hmbs_len : length mbs2 = length mbs).
    { exact (f_equal (fun lh => length (list_heap lh)) contra). }
    lia.
  Qed.

  Lemma list_heap_alloc_true (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) :
      list_heap_alloc h sz v = Some (lh', p) -> alloc h = true.
  Proof.
    destruct h as [mbs [|]]; cbn; intros H; [reflexivity | discriminate].
  Qed.

    Lemma alloc_shift_fw_0_self mbs sz v lh' p :
      list_heap_alloc (mkListHeap mbs true) sz v = Some (lh', p) ->
      (0 < sz)%N ->
      Pointer.shift_fw p 0%N = Some p.
  Proof.
    intros H_alc Ho.
    unfold list_heap_alloc in H_alc.
    inversion H_alc; subst p; clear H_alc.
    cbn [Pointer.shift_fw Addr.shift_fw].
    rewrite N.add_0_r.
    unfold Provenance.within, Provenance.wf.
    rewrite !Nat.eqb_refl.
    destruct (N.leb_spec0 0 0); [|lia].
    destruct (N.leb_spec0 sz sz); [|lia].
    destruct (N.leb_spec0 0 sz); [|lia].
    cbn. reflexivity.
  Qed.

  Lemma alloc_wvalid_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) :
      Heap.alloc h sz v = Some (lh', p) ->
      (0 < sz)%N ->
      Heap.Facts.WValid lh' p.
  Proof.
    destruct h as [mbs [|]]; intros H_alc Ho.
    - eapply alloc_shift_wvalid with (o := 0%N) (p' := p); eauto.
      + eapply alloc_shift_fw_0_self; eauto.
    - cbn in H_alc; discriminate H_alc.
  Qed.

  Lemma alloc_shift_fw_succeeds_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) (o : N.t) :
      Heap.alloc h sz v = Some (lh', p) ->
      (o < sz)%N ->
      exists p', Pointer.shift_fw p o = Some p'.
  Proof.
    destruct h as [mbs [|]]; intros H Ho;
      [exact (alloc_shift_fw_succeeds mbs true sz v lh' p o H Ho) | cbn in H; discriminate].
  Qed.

  Lemma alloc_shift_wvalid_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) (o : N.t) (p' : Pointer.t) :
      Heap.alloc h sz v = Some (lh', p) ->
      (o < sz)%N ->
      Pointer.shift_fw p o = Some p' ->
      Heap.Facts.WValid lh' p'.
  Proof.
    destruct h as [mbs [|]]; intros H Ho Hs;
      [exact (alloc_shift_wvalid mbs true sz v lh' p o p' H Ho Hs) | cbn in H; discriminate].
  Qed.

  Lemma alloc_mutate_succeeds_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) (o : N.t) (p' : Pointer.t) (val : memval) :
      Heap.alloc h sz v = Some (lh', p) ->
      (o < sz)%N ->
      Pointer.shift_fw p o = Some p' ->
      exists lh'', Heap.mutate lh' p' val = Some lh''.
  Proof.
    destruct h as [mbs [|]]; intros H Ho Hs;
      [exact (alloc_mutate_succeeds mbs true sz v lh' p o p' val H Ho Hs) | cbn in H; discriminate].
  Qed.

  Lemma alloc_shift_wvalid_after_mut_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) (o : N.t) (p' : Pointer.t) (lh'' : list_heap_carrier) (ptr_m : Pointer.t) (v_m : memval) :
      Heap.alloc h sz v = Some (lh', p) ->
      (o < sz)%N ->
      Pointer.shift_fw p o = Some p' ->
      Heap.mutate lh' ptr_m v_m = Some lh'' ->
      Heap.Facts.WValid lh'' p'.
  Proof.
    destruct h as [mbs [|]]; intros H Ho Hs Hm;
      [exact (alloc_shift_wvalid_after_mut mbs sz v lh' p o p' lh'' ptr_m v_m H Ho Hs Hm) | cbn in H; discriminate].
  Qed.

  Lemma alloc_wvalid_after_mut_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) (lh'' : list_heap_carrier) (ptr_m : Pointer.t) (v_m : memval) :
      Heap.alloc h sz v = Some (lh', p) ->
      (0 < sz)%N ->
      Heap.mutate lh' ptr_m v_m = Some lh'' ->
      Heap.Facts.WValid lh'' p.
  Proof.
  destruct h as [mbs [|]]; intros H_alc Ho H_mut; cbn in *.
  - injection H_alc as H_lh' H_p.
    subst lh' p.
    
    assert (H_fw0: Pointer.shift_fw (Some ({| Addr.block := length mbs; Addr.offset := 0 |},
        {| Provenance.prov_block := length mbs; Provenance.prov_bofst := 0;
           Provenance.prov_eofst := sz; Provenance.prov_mbofst := 0;
           Provenance.prov_meofst := sz; Provenance.prov_perm := Permission.Free |})) 0%N = 
        Some (Some ({| Addr.block := length mbs; Addr.offset := 0 |},
        {| Provenance.prov_block := length mbs; Provenance.prov_bofst := 0;
           Provenance.prov_eofst := sz; Provenance.prov_mbofst := 0;
           Provenance.prov_meofst := sz; Provenance.prov_perm := Permission.Free |}))).
    { cbn [Pointer.shift_fw Addr.shift_fw].
      rewrite N.add_0_r.
      unfold Provenance.within, Provenance.wf.
      rewrite !Nat.eqb_refl.
      destruct (N.leb_spec0 0 0); [| lia ].
      destruct (N.leb_spec0 sz sz); [| lia ].
      destruct (N.leb_spec0 0 sz); [| lia ].
      reflexivity. }
      
    eapply alloc_shift_wvalid_after_mut with (o := 0%N); eauto.
    cbn. reflexivity.
  - discriminate H_alc.
Qed.

  Lemma alloc_mutate_mutate_succeeds_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p : Pointer.t) (o1 : N.t) (p1 : Pointer.t) (o2 : N.t) (p2 : Pointer.t) (lh1 : list_heap_carrier) (val1 val2 : memval) :
      Heap.alloc h sz v = Some (lh', p) ->
      (o1 < sz)%N ->
      Pointer.shift_fw p o1 = Some p1 ->
      Heap.mutate lh' p1 val1 = Some lh1 ->
      (o2 < sz)%N ->
      Pointer.shift_fw p o2 = Some p2 ->
      exists lh2, Heap.mutate lh1 p2 val2 = Some lh2.
  Proof.
    destruct h as [mbs [|]]; intros H Ho1 Hs1 Hm1 Ho2 Hs2;
      [exact (alloc_mutate_mutate_succeeds mbs true sz v lh' p o1 p1 o2 p2 lh1 val1 val2 H Ho1 Hs1 Hm1 Ho2 Hs2) | cbn in H; discriminate].
  Qed.

  Lemma alloc_heap_neq_orig_gen (h : list_heap_carrier) (sz : N.t) (v : memval) (lh' : list_heap_carrier) (p p1 p2 : Pointer.t) (lh1 lh2 : list_heap_carrier) (v1 v2 : memval) :
      Heap.alloc h sz v = Some (lh', p) ->
      Heap.mutate lh' p1 v1 = Some lh1 ->
      Heap.mutate lh1 p2 v2 = Some lh2 ->
      lh2 <> h.
  Proof.
    destruct h as [mbs [|]]; intros H Hm1 Hm2;
      [exact (alloc_heap_neq_orig mbs sz v lh' p p1 p2 lh1 lh2 v1 v2 H Hm1 Hm2) | cbn in H; discriminate].
  Qed.

  Lemma alloc_wvalid mbs sz v lh' p :
      list_heap_alloc (mkListHeap mbs true) sz v = Some (lh', p) ->
      (0 < sz)%N ->
      Heap.Facts.WValid lh' p.
  Proof.
    intros H_alc Ho.
    exact (alloc_shift_wvalid mbs true sz v lh' p 0%N p H_alc Ho
             (alloc_shift_fw_0_self mbs sz v lh' p H_alc Ho)).
  Qed.

  Lemma alloc_wvalid_after_mut mbs sz v lh' p lh'' ptr_m v_m :
      list_heap_alloc (mkListHeap mbs true) sz v = Some (lh', p) ->
      (0 < sz)%N ->
      list_heap_mutate lh' ptr_m v_m = Some lh'' ->
      Heap.Facts.WValid lh'' p.
  Proof.
    intros H_alc Ho H_mut.
    exact (alloc_shift_wvalid_after_mut mbs sz v lh' p 0%N p lh'' ptr_m v_m
             H_alc Ho (alloc_shift_fw_0_self mbs sz v lh' p H_alc Ho) H_mut).
  Qed.

End ListHeap.


