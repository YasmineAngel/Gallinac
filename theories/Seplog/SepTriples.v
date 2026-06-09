From Stdlib Require Import FunctionalExtensionality PropExtensionality Nat Lia NArith.
From GallinaC.Seplog Require Export PrimitivesTriples StateAssertion.
Local Open Scope state_scope.


Lemma sep_weaken : forall (S A : Type) (m : program S A)
         (P Q : Pred S) (R : A -> Pred S),
       {{ Q }} m {{ R }} ->
       (|- P ===> Q) -> {{ P }} m {{ R }}.
Proof.
intros.
eapply weaken; eauto.
Qed.


Lemma sep_strengthen
  {S A : Type} (m : program S A) (P : Pred S) (Q R : A -> Pred S) :
{{ P }} m {{ Q }} -> (forall a, |- Q a ===> R a ) -> {{ P }} m {{ R }}.
Proof.
intros.
eapply strengthen; eauto.
Qed.


Local Open Scope program_scope.

Lemma  sep_bind_rule
  {S A B : Type} (m : program S A) (f : A -> program S B)
  (P : S -> Prop) (Q : A -> Pred S) (R : B -> Pred S) :
(forall a, {{ Q a }} f a {{ R }}) -> {{ P }} m {{ Q }} ->
{{ P }} do x <- m; f x {{ R }}.
Proof.
eapply bind_rule; eauto.
Qed.



Lemma sep_seq_rule
  {S A B : Type} (m1 : program S A) (m2 : program S B)
  (P : Pred S) (Q : Pred S) (R : B -> Pred S) :
{{ Q }} m2 {{ R }} -> {{ P }} m1 {{ fun _ s => Q s }} ->
{{ P }} m1;; m2 {{ R }}.
Proof.
eapply seq_rule; eauto.
Qed.


Lemma sep_ret_triple {S A : Type} (a : A) (P : A -> Pred S) :
{{ P a }} ret a {{ P }}.
Proof.
apply ret_triple.
Qed.

Lemma sep_fail_triple{S A: Type}(P: A -> Pred S):
{{ fun _ => False}} fail {{P}}.
Proof.
apply fail_triple.
Qed.

Lemma sep_eq_ptr_triple
  {St: Store} {Hp: Heap}
  (ptr_l ptr_r : Pointer.t)
  (Q : bool -> Pred (State St Hp)) :
  {{ fun s =>
       Facts.WValid (heap s) ptr_l /\
         Facts.WValid (heap s) ptr_r /\
         Pointer.Allows ptr_l Operation.Cmp /\
         Pointer.Allows ptr_r Operation.Cmp /\
         forall b, Q b s }}
    eq_ptr ptr_l ptr_r
    {{ Q }}.
Proof.
  intros s (HWValid_l & HWValid_r & HAllows_l & HAllows_r & HQ).
  unfold eq_ptr, partial_exception_hoare. cbn.
  destruct (Facts.weakly_valid_spec (heap s) ptr_l) as [Hwv_l | Hnwv_l].
  2: contradiction.
  destruct (Pointer.allows_spec ptr_l Operation.Cmp) as [Ha_l | Hna_l].
  2: contradiction.
  destruct (Facts.weakly_valid_spec (heap s) ptr_r) as [Hwv_r | Hnwv_r].
  2: contradiction.
  destruct (Pointer.allows_spec ptr_r Operation.Cmp) as [Ha_r | Hna_r].
  2: contradiction.
  cbn.
  destruct (Pointer.cmp ptr_l ptr_r) eqn:Ecmp.
  - cbn. apply HQ.
  - exfalso.
    unfold Pointer.cmp in Ecmp.
    destruct (Pointer.allows_spec ptr_l Operation.Cmp); [ | contradiction ].
    destruct (Pointer.allows_spec ptr_r Operation.Cmp); [ | contradiction ].
    discriminate Ecmp.
Qed.

Lemma sep_shift_fw_ptr_triple
  {St: Store} {Hp: Heap}
  (ptr: Pointer.t) (shift: N.t)
  (Q: Pointer.t -> Pred (State St Hp)) :
  {{ fun s =>
       Facts.WValid (heap s) ptr /\
       exists ptr', Pointer.shift_fw ptr shift = Some ptr' /\
       Facts.WValid (heap s) ptr' /\
       Q ptr' s }}
    shift_fw_ptr ptr shift
  {{ Q }}.
Proof.
  intros s (HWValid & ptr' & Hshift & HWValid' & HQ).
  unfold shift_fw_ptr, partial_exception_hoare. cbn.
  destruct (Facts.weakly_valid_spec (heap s) ptr) as [Hwv | Hnwv].
  2: contradiction.
  rewrite Hshift.
  destruct (Facts.weakly_valid_spec (heap s) ptr') as [Hwv' | Hnwv'].
  2: contradiction.
  cbn. exact HQ.
Qed.

Lemma sep_read_ptr_triple
  {St: Store} {Hp: Heap} {MS: MemStorable}
  (ptr: Pointer.t)
  (Q: obj MS -> Pred (State St Hp)) :
  {{ fun s => exists v, Heap.lookup (heap s) ptr = Some (encode v) /\ Q v s }}
    read_ptr ptr
  {{ Q }}.
Proof.
  intros s (v & Hlookup & HQ).
  unfold read_ptr, partial_exception_hoare. cbn.
  rewrite Hlookup. rewrite encode_decode. cbn. exact HQ.
Qed.

Lemma sep_write_ptr_triple
  {St: Store} {Hp: Heap} {MS: MemStorable}
  (ptr: Pointer.t) (val: obj MS)
  (Q: unit -> Pred (State St Hp)) :
  {{ fun s => exists h', Heap.mutate (heap s) ptr (encode val) = Some h' /\
              Q tt {| store := store s; heap := h' |} }}
    write_ptr ptr val
  {{ Q }}.
Proof.
  intros s (h' & Hmutate & HQ).
  unfold write_ptr, partial_exception_hoare. cbn.
  rewrite Hmutate. cbn. exact HQ.
Qed.

Lemma sep_alloc_ptr_triple
  {St: Store} {Hp: Heap} {MS: MemStorable}
  (n: N.t) (val: obj MS)
  (Q: Pointer.t -> Pred (State St Hp)) :
  {{ fun s =>
       (exists hp' ptr', Heap.alloc (heap s) n (encode val) = Some (hp', ptr')) /\
       forall hp ptr, Heap.alloc (heap s) n (encode val) = Some (hp, ptr) ->
       Q ptr {| store := store s; heap := hp |} }}
    alloc_ptr n val
  {{ Q }}.
Proof.
  intros s ((hp_ex & ptr_ex & Hex) & HQ).
  unfold alloc_ptr, partial_exception_hoare. cbn.
  rewrite Hex. cbn. exact (HQ hp_ex ptr_ex Hex).
Qed.

Lemma sep_eq_ptr_triple_cmp
    {St: Store} {Hp: Heap}
    (ptr_l ptr_r: Pointer.t)
    (Q: bool -> Pred (State St Hp)):
    {{ fun s =>
         Facts.WValid (heap s) ptr_l /\
         Facts.WValid (heap s) ptr_r /\
         Pointer.Allows ptr_l Operation.Cmp /\
         Pointer.Allows ptr_r Operation.Cmp /\
         forall b, Pointer.cmp ptr_l ptr_r = Some b -> Q b s }}
      eq_ptr ptr_l ptr_r
      {{ Q }}.
  Proof.
    intros s (HWValid_l & HWValid_r & HAllows_l & HAllows_r & HQ).
    unfold eq_ptr, partial_exception_hoare. cbn.
    destruct (Facts.weakly_valid_spec (heap s) ptr_l) as [Hwv_l | Hnwv_l].
    2: contradiction.
    destruct (Pointer.allows_spec ptr_l Operation.Cmp) as [Ha_l | Hna_l].
    2: contradiction.
    destruct (Facts.weakly_valid_spec (heap s) ptr_r) as [Hwv_r | Hnwv_r].
    2: contradiction.
    destruct (Pointer.allows_spec ptr_r Operation.Cmp) as [Ha_r | Hna_r].
    2: contradiction.
    cbn.
    destruct (Pointer.cmp ptr_l ptr_r) eqn:Ecmp.
    - cbn. apply HQ. reflexivity.
    - exfalso.
      unfold Pointer.cmp in Ecmp.
      destruct (Pointer.allows_spec ptr_l Operation.Cmp); [ | contradiction ].
      destruct (Pointer.allows_spec ptr_r Operation.Cmp); [ | contradiction ].
      discriminate Ecmp.
  Qed.

Lemma sep_read_var_triple
  {St: Store} {Hp: Heap} {MS: MemStorable}
  (varname: name)
  (Q: obj MS -> Pred (State St Hp)) :
  {{ fun s => exists v, Store.BindsTo varname (encode v) (store s) /\ Q v s }}
    read_var varname
  {{ Q }}.
Proof. apply read_var_triple. Qed.


Lemma sep_write_var_triple
  {St: Store} {Hp: Heap} {MS: MemStorable}
  (varname: name) (val: obj MS)
  (Q: unit -> Pred (State St Hp)) :
  {{ fun s => exists v_old, Store.BindsTo varname v_old (store s) /\
              Q tt {| store := Store.mutate_unchecked (store s) varname (encode val);
                      heap  := heap s |} }}
    write_var varname val
  {{ Q }}.
Proof. apply write_var_triple. Qed.

Lemma sep_with_var_triple
  {A: Type} {St: Store} {Hp: Heap} {MS: MemStorable}
  (e_var: obj MS) (p_cont: name -> program (State St Hp) A)
  (P: Pred (State St Hp)) (Q: A -> Pred (State St Hp)) :
  (forall s n st,
    P s ->
    Store.push (store s) (encode e_var) = (st, n) ->
    {{ fun s' => s' = {| store := st; heap := heap s |} }}
      p_cont n
    {{ fun a s_after =>
         exists st_pop,
           Store.pop (store s_after) = Some st_pop /\
           Q a {| store := st_pop; heap := heap s_after |}
    }}) ->
  {{ P }} with_var e_var p_cont {{ Q }}.
Proof.
  intros Hcont s HP.
  unfold with_var, partial_exception_hoare.
  destruct (Store.push (store s) (encode e_var)) as [st n] eqn:Epush.
  specialize (Hcont s n st HP Epush).
  unfold partial_exception_hoare in Hcont.
  specialize (Hcont {| store := st; heap := heap s |} ltac:(reflexivity)).
  destruct (p_cont n {| store := st; heap := heap s |}) as [ [ (v & s2) | ] | ] eqn:Epcont.
  - destruct Hcont as (st_pop & Hpop & HQ).
    unfold bind, get, put.
    cbn.
    rewrite Epush.
    rewrite Epcont.
    trivial.
    rewrite Hpop.
    cbn.
    exact HQ.
  - cbn in Hcont. contradiction.
  - unfold bind, get, put.
    cbn.
    rewrite Epush.
    rewrite Epcont.
    trivial.
Qed.


Lemma sep_alloc_concrete_triple {St: Store} {Hp: Heap} {MS: MemStorable} 
  (n: N.t) (val: obj MS) (alloc_func : Hp -> N.t -> memval -> option (Hp * Pointer.t))
  (Q: Pointer.t -> Pred (State St Hp)) :
  (forall h n' v', Heap.alloc h n' v' = alloc_func h n' v') ->
  {{ fun s =>
       (exists hp' ptr', alloc_func (heap s) n (encode val) = Some (hp', ptr')) /\
       forall hp ptr, alloc_func (heap s) n (encode val) = Some (hp, ptr) ->
       Q ptr {| store := store s; heap := hp |} }}
    alloc_ptr n val
  {{ Q }}.
Proof.
  intros Halloc_eq s ((hp_ex & ptr_ex & Hex) & HQ).
  unfold alloc_ptr, partial_exception_hoare. cbn.
  assert (H_heap_alloc: Heap.alloc (heap s) n (encode val) = Some (hp_ex, ptr_ex)).
  { rewrite Halloc_eq. exact Hex. }
  rewrite H_heap_alloc. cbn.
  exact (HQ hp_ex ptr_ex Hex).
Qed.


Section GenTriples.
Context {St: Store} {Hp: Heap} {MS: MemStorable}.

Lemma sep_alloc_gen (n: N.t) (val: obj MS) (alloc_func : Hp -> N.t -> memval -> option (Hp * Pointer.t))
  (Q: Pointer.t -> Pred (State St Hp)) :
  (forall h n' v', Heap.alloc h n' v' = alloc_func h n' v') ->
  {{ fun s => (exists hp' ptr', alloc_func (heap s) n (encode val) = Some (hp', ptr')) /\
              (forall hp ptr, alloc_func (heap s) n (encode val) = Some (hp, ptr) -> Q ptr {| store := store s; heap := hp |}) }}
    alloc_ptr n val
  {{ Q }}.
Proof.
  intros Halloc_eq s ((hp_ex & ptr_ex & Hex) & HQ).
  unfold alloc_ptr, partial_exception_hoare. cbn.
  assert (H_alloc: Heap.alloc (heap s) n (encode val) = Some (hp_ex, ptr_ex)) by (rewrite Halloc_eq; exact Hex).
  rewrite H_alloc. cbn. exact (HQ hp_ex ptr_ex Hex).
Qed.


Lemma sep_write_gen (ptr: Pointer.t) (val: obj MS) (mutate_func : Hp -> Pointer.t -> memval -> option Hp)
  (Q: unit -> Pred (State St Hp)) :
  (forall h p v, Heap.mutate h p v = mutate_func h p v) ->
  {{ fun s => (exists h', mutate_func (heap s) ptr (encode val) = Some h') /\
              (forall h', mutate_func (heap s) ptr (encode val) = Some h' -> Q tt {| store := store s; heap := h' |}) }}
    write_ptr ptr val
  {{ Q }}.
Proof.
  intros Hmut_eq s ((h'_ex & Hex) & HQ).
  unfold write_ptr, partial_exception_hoare. cbn.
  assert (H_mut: Heap.mutate (heap s) ptr (encode val) = Some h'_ex) by (rewrite Hmut_eq; exact Hex).
  rewrite H_mut. cbn. exact (HQ h'_ex Hex).
Qed.

End GenTriples.

Lemma sep_if_rule
  {S A : Type} (cond : program S bool) (m1 m2 : program S A)
  (P : Pred S) (Q : bool -> Pred S) (R : A -> Pred S) :
{{ P }} cond {{ Q }} -> {{ Q true}} m1 {{ R }} -> {{ Q false}} m2 {{ R }} ->
{{ P }} If cond then m1 else m2 {{ R }}.
Proof.
eapply if_rule; eauto.
Qed.


Local Open Scope state_scope.

Lemma sep_while_rule {S}
   (cond : program S bool) (body : program S unit)
  (I : bool -> Pred S) :
{{ Exists b, I b }}
 cond
{{ I }} ->
{{ I true }}
  body
{{ fun _ => Exists b, I b }} ->
{{ Exists b, I b }}
  while cond body
{{ fun _ => I false }}.
Proof.
eapply while_rule; eauto.
Qed.

(* Lemma sep_read_reg1_triple {S} (P : nat -> Pred S) : *)
(* {{Exists r, (reg1= r) ** (P r)}} read_reg1 {{ P }}. *)
(* Proof. *)
(* rewrite pre_read_reg1_eq. *)
(* apply read_reg1_triple. *)
(* Qed. *)


(* Lemma sep_read_reg2_triple (P : nat -> Pred State) : *)
(* {{ Exists r, (reg2= r) ** (P r)}} read_reg2 {{ P }}. *)
(* Proof. *)
(* rewrite pre_read_reg2_eq. *)
(* apply read_reg2_triple. *)
(* Qed. *)


(* Lemma sep_write_reg1_triple(r:nat) *)
(* (Q: unit -> Pred State): *)
(* {{ *)
(* [reg1=r]-* (Q tt) *)
(* }} *)
(* write_reg1 r *)
(* {{ *)
(*  Q *)
(* }}. *)
(* Proof. *)
(* apply write_reg1_triple. *)
(* Qed. *)


(* Lemma sep_write_reg2_triple(r:nat) *)
(* (Q: unit -> Pred State): *)
(* {{ *)
(* [reg2=r]-* (Q tt) *)
(* }} *)
(* write_reg2 r *)
(* {{ *)
(*  Q *)
(* }}. *)
(* Proof. *)
(* apply write_reg2_triple. *)
(* Qed. *)

(**
Lemma fw_write_reg2_triple(r:nat)
(P: Pred State):
{{
P
}}
write_reg2 r
{{
fun _ => (reg2= r) ** P
}}.
Proof.
 eapply  sep_weaken;  [apply sep_write_reg2_triple| ].
cbn.
Admitted.
*)

(* Lemma sep_read_addr_triple (addr : nat) (P : nat -> Pred S) : *)
(*   {{ *)
(*     Exists a, (addr ---> a) && (P a) *)
(*      }} *)
(*    read_addr addr *)
(*    {{ P }}. *)
(* Proof. *)
(* rewrite pre_read_addr_eq. *)
(* apply read_addr_triple. *)
(* Qed. *)


(* Lemma sep_write_addr_triple (a:addr) (v : nat) (P : unit -> Pred State) : *)
(* {{ *)
(* (Exists x, (a |~> x))**((a |~> v) -* (P tt)) *)
(* }} *)
(* write_addr a v *)
(* {{ P }}. *)
(* Proof. *)
(* rewrite  write_addr_wp_eq. *)
(* apply write_addr_triple. *)
(* Qed. *)


(* Lemma sep_deref_succ_reg1_triple (P : nat -> Pred State) : *)
(* {{ (Exists (a r:nat), (reg1= r) ** *)
(*                         ((r + 1) ---> a && P a)) }} *)
(*   deref_succ_reg1 *)
(* {{ P }}. *)
(* Proof. *)
(* unfold deref_succ_reg1. *)
(* eapply bind_rule. *)
(* - intro x. *)
(*   apply sep_read_addr_triple. *)
(* - eapply sep_weaken; [apply read_reg1_triple | ]. *)
(*   rewrite <-  wp_deref_succ_reg1_eq. *)
(*   now intros s Hm. *)
(* Qed. *)
