From iris.base_logic.lib Require Import invariants.
From iris.program_logic Require Export weakestpre.
From iris.algebra Require Import auth excl.
From iris.heap_lang Require Import lang adequacy notation tactics proofmode.
From iris_string_ident Require Import ltac2_string_ident.

Definition clock_loop : val :=
  rec: "loop" "l" :=
    (if: !"l" = #23 then
      "l" <- #0
    else
      "l" <- !"l" + #1) ;;
    "loop" "l".

Definition clock : val :=
  λ: <>,
    let: "l" := ref #0 in
    clock_loop "l".

Record clockSt := MkClock { hour: nat }.

Definition initSt := MkClock 0.

Definition nextSt (st : clockSt) : clockSt :=
  MkClock (st.(hour) + 1).

Lemma nextSt_plus1 (st : clockSt) :
  (nextSt st).(hour) = st.(hour) + 1.
Proof. reflexivity. Qed.

Inductive tick : relation clockSt :=
| tick_next st : st.(hour) < 23 -> tick st (nextSt st)
| tick_wrap st : st.(hour) = 23 -> tick st initSt.

Definition tick_star := rtc tick.

Definition valid_st (st : clockSt) : Prop := st.(hour) <= 23.

Lemma init_valid : valid_st initSt.
Proof. Admitted.

Lemma tick_preserves_validity st st':
  tick st st' -> valid_st st -> valid_st st'.
Proof. Admitted.

Lemma tick_star_preserves_validity st st':
  tick_star st st' -> valid_st st -> valid_st st'.
Proof. Admitted.

Lemma next_tick_star st :
  valid_st st ->
  tick_star initSt st ->
  hour st ≠ 23 ->
  tick_star initSt (nextSt st).
Proof.
  intros Hvalid Hst Hne.
  eapply rtc_r; [eauto|].
  apply tick_next.
  unfold valid_st in Hvalid; lia.
Qed.

Section clock_specs.

  Context `{!heapG Σ}.

  Notation HSO := (leibnizO clockSt).

  Context `{!inG Σ (authUR (optionUR (exclR HSO)))} (γst : gname).

  Definition StateAuth s := own γst (● Excl' s).
  Definition StateFrag s := own γst (◯ Excl' s).

  Lemma State_agree s s' : StateAuth s ⊢ StateFrag s' -∗ ⌜s = s'⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as
        %[->%Excl_included%leibniz_equiv ?]%auth_both_valid; done.
  Qed.

  Lemma State_update s1 s2 s :
    StateAuth s1 ⊢ StateFrag s2 ==∗ StateAuth s ∗ StateFrag s.
  Proof.
    iIntros "H1 H2".
    iMod (own_update_2 _ _ _ (● Excl' s ⋅ ◯ Excl' s) with "H1 H2") as "[$ $]";
      last done.
    apply auth_update.
    apply option_local_update, exclusive_local_update; done.
  Qed.

  Definition invN := nroot.@"H".

  Definition clock_sts_invariant ℓ : iProp Σ :=
    inv invN
        (∃ s,
            StateAuth s ∗
            ⌜tick_star initSt s⌝ ∗
            ℓ ↦ #s.(hour)).

  Lemma clock_sts_state_valid ℓ s E :
    ↑invN ⊆ E →
    clock_sts_invariant ℓ ⊢
      StateFrag s ={E}=∗ StateFrag s ∗ ⌜valid_st s⌝.
  Proof.
    iIntros (HE) "#Hi Hsf".
    iInv invN as "> Hinv". iDestruct "Hinv" as (s') "(Hsa & %Htick & Hℓ)".
    iDestruct (State_agree with "Hsa Hsf") as %->.
    iModIntro; iFrame "Hsf".
    iSplitL.
    { iNext; iExists _; iFrame; done. }
    iModIntro; iPureIntro.
    eapply tick_star_preserves_validity; eauto.
    apply init_valid.
  Qed.

  Lemma silly n :
     n ≠ 23 ->
     #n ≠ #23.
  Proof. Admitted.

  Lemma clock_loop_spec (s : clockSt) ℓ :
    {{{ clock_sts_invariant ℓ ∗
        StateFrag s }}}
      clock_loop #ℓ
    {{{ RET #(); False }}}.
  Proof.
    iIntros (ϕ) "[#Hinv Hfrag] Hcont".
    rewrite /clock_loop.
    iLöb as "IH" forall (s).
    wp_pures.
    wp_bind (!_)%E.
    iInv invN as "> HI" "Hclose".
    iDestruct "HI" as (s1) "(Hsa & %Htick1 & Hℓ)".
    wp_load.
    iDestruct (State_agree with "Hsa Hfrag") as %->.
    iMod ("Hclose" with "[Hℓ Hsa]") as "_".
    { iNext. iExists s. iFrame. by iPureIntro. }
    iModIntro.
    destruct (decide (s.(hour) = 23)) as [->| Hne].
    - wp_pures. wp_bind (_ <- _)%E.
      iInv invN as "> HI" "Hclose".
      iDestruct "HI" as (s2) "(Hsa & %Htick2 & Hℓ)".
      wp_store.
      iMod (State_update _ _ initSt with "Hsa Hfrag") as "[Hia Hif]".
      iMod ("Hclose" with "[Hℓ Hia]") as "_".
      { iNext.
        iExists initSt. simpl.
        iFrame. eauto. }
      iModIntro.
      do 2 wp_pure _.
      by iApply ("IH" with "Hif").
    - wp_pures.
      rewrite /= bool_decide_eq_false_2 //; last first.
      { by apply silly. }
      wp_pures. wp_bind (! _)%E.
      iInv invN as "> HI" "Hclose".
      iDestruct "HI" as (s2) "(Hsa & _ & Hℓ)".
      wp_load.
      iDestruct (State_agree with "Hsa Hfrag") as %->.
      iMod ("Hclose" with "[Hℓ Hsa]") as "_".
      { iNext. iExists s. iFrame. by iPureIntro. }
      iModIntro.
      wp_pures.
      wp_bind (_ <- _)%E.
      iMod (clock_sts_state_valid with "Hinv Hfrag") as "[Hfrag %Hvalid]"; [done |].
      iInv invN as "> HI" "Hclose".
      iDestruct "HI" as (s3) "(Hsa & _ & Hℓ)".
      wp_store.
      iDestruct (State_agree with "Hsa Hfrag") as %->.
      iMod (State_update _ _ (nextSt s) with "Hsa Hfrag") as "[Hna Hnf]".
      iMod ("Hclose" with "[Hℓ Hna]") as "_".
      { iNext. iExists (nextSt s). rewrite nextSt_plus1.
        assert (Z.of_nat (hour s + 1)%nat = (hour s + 1)%Z) as ->; [by lia|].
        iFrame. iPureIntro.
        apply next_tick_star; auto. }
      iModIntro. do 2 wp_pure _.
      iApply ("IH" with "Hnf").
      done.
  Qed.
  
Open Scope Z.

Lemma Zeven_add_2 n : Z.even n -> Z.even (n + 2).
Proof.
  rewrite (ltac:(lia): n + 2 = Z.succ (Z.succ n))
          Z.even_succ_succ //.
Qed.

Section S.
  Context `{!heapG Σ} `{!spawnG Σ} (N : namespace).

  Lemma incr2_spec (ℓ: loc) :
    {{{ inv N (∃ (x:Z), ℓ ↦ #x ∗ ⌜Z.even x⌝)%I }}}
      incr2 #ℓ
    {{{ RET #(); True }}}.
  Proof.
    iIntros (φ) "#Hi Hφ". iLöb as "IH".
    wp_lam. wp_bind (_ ||| _)%E. wp_pures.
    (* specification for the two threads *)
    iAssert (WP #ℓ <- ! #ℓ + #2 {{ _, True }})%I with "[Hi]" as "Ht".
    { wp_bind (!#ℓ)%E. iInv N as (x) ">[Hℓ %]" "Hclose". wp_load.
      iMod ("Hclose" with "[Hℓ]"). now eauto.
      iModIntro. wp_pures.
      iInv N as (x') ">[Hℓ %]" "Hclose". wp_store.
      iMod ("Hclose" with "[Hℓ]"); eauto.
      iNext. iExists (x+2). iFrame. eauto using Zeven_add_2. }
    iApply (wp_par (fun _ => ⌜True⌝)%I (fun _ => ⌜True⌝)%I);
      [ iApply "Ht" .. |].
    iIntros. iNext. wp_pures. iApply "IH". eauto.
  Qed.
End S.

Class heapPreG Σ := HeapPreG {
  heap_preG_iris :> invPreG Σ;
  heap_preG_heap :> gen_heapPreG loc (option val) Σ;
  heap_preG_inv_heap :> inv_heapPreG loc (option val) Σ;
  heap_preG_proph :> proph_mapPreG proph_id (val * val) Σ;
}.

Section S.
  Context (N: namespace).
  Context `{!spawnG Σ}.
  Context `{heapPreG Σ}.

  Lemma invariant_adequacy :
    forall (ℓ : loc) (σ1 σ2 : state) (es: list expr),
      let φ := (fun (σ: state) => ∃ (x:Z),
                  heap σ !! ℓ = Some (Some (#x)) ∧ Z.even x) in
      rtc erased_step ([incr2 #ℓ], σ1) (es, σ2) →
      φ σ1 →
      φ σ2.
  Proof.
    intros * Hstep Hσ1.
    pose proof (@incr2_spec Σ) as S.

    pose proof (wp_invariance Σ heap_lang NotStuck) as L. cbn in L.
    specialize (L (incr2 #ℓ) σ1 es σ2 (φ σ2)).
    eapply L; eauto. intros Hinv κs. clear L.

    (* Allocate heap resources corresponding to (heap σ1) *)
    iMod (gen_heap_init (delete ℓ (heap σ1))) as (Hheap) "Hσ1".
    (* Also allocate the prophecy-related resources, that appear in the standard
       state interpretation in heapG_irisG (this is needed for things to match
       later on). *)
    iMod (proph_map_init κs (used_proph_id σ1)) as (Hproph) "Hpr1".

    iMod (inv_heap_init loc (option val)) as (Hi) ">Hi1".
    (* /!\ do not use 'pose proof', as [heapG_invG HeapΣ] needs to
       stay convertible to Hinv for things to typecheck later on. *)
    set (HeapΣ := HeapG Σ Hinv Hheap Hi Hproph).

    (* Add ℓ back to the heap, so that we get a corresponding points-to *)
    destruct Hσ1 as [v1 [Hσ1 E1]].
    iMod (gen_heap_alloc (delete ℓ (heap σ1)) ℓ (Some #v1) with "Hσ1")
      as "(Hσ1 & Hℓ & ?)".
    by rewrite lookup_delete.

    (* Allocate the same invariant as in [incr2_spec], so that we can feed it to
       [S] *)
    iPoseProof (@inv_alloc Σ Hinv N ⊤
      (∃ (x:Z), ℓ ↦ #x ∗ ⌜Z.even x⌝)%I with "[Hℓ]") as ">#HI".
    by iExists v1; eauto.

    rewrite insert_delete insert_id //.
    specialize (S HeapΣ spawnG0 N ℓ (fun _ => True%I)).
    iPoseProof (S with "HI") as "S".

    iModIntro.

    (* /!\ this has to match exactly the state_interp of heapG_irisG *)
    iExists (fun σ 𝜅s _ =>
      gen_heap_ctx (heap σ) ∗ proph_map_ctx 𝜅s (used_proph_id σ))%I.
    iExists (fun _ => True%I).
    iSplitL "Hσ1 Hpr1"; [ by iFrame |].
    iSplitL "S". by iApply "S".
    iIntros "[Hheap ?]". iExists (⊤ ∖ ↑N).
    iInv N as (x) ">[Hℓ %]" "Hclose".
    iDestruct (gen_heap_valid with "Hheap Hℓ") as "%".
    iModIntro. iPureIntro. unfold φ. eauto.
  Qed.
End S.

Theorem invariant_adequacy' (ℓ : loc) (σ1 σ2 : state) (es: list expr) :
  let φ := (fun (σ: state) =>
              ∃ (x:Z), heap σ !! ℓ = Some (Some (#x)) ∧ Z.even x) in
  φ σ1 →
  rtc erased_step ([incr2 #ℓ], σ1) (es, σ2) →
  φ σ2.
Proof.
  set (Σ := #[invΣ; gen_heapΣ loc (option val); inv_heapΣ loc (option val); proph_mapΣ proph_id (val * val); spawnΣ]).
  set (HG := HeapPreG Σ _ _ _ _).
  intros. eapply (@invariant_adequacy nroot Σ); eauto.
  typeclasses eauto.
Qed.
