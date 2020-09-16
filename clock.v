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

  (* TODO: spec for closed program *)
End clock_specs.

Definition clockΣ :=
  #[heapΣ; GFunctor (authUR (optionUR (exclR (leibnizO clockSt))))].

Local Instance subG_heapPreG {Σ} :
  subG clockΣ Σ → inG Σ (authUR (optionUR (exclR (leibnizO clockSt)))).
Proof. solve_inG. Qed.

Lemma clock_loop_correctness (ℓ : loc) :
  ∀ (t2 : list expr) (σ1 σ2 : state),
    σ1.(heap) !! ℓ = Some (Some #0) →
    rtc erased_step ([clock_loop #ℓ], σ1) (t2, σ2) →
    (∀ e2, e2 ∈ t2 → not_stuck e2 σ2) ∧
    ∃ s : clockSt,
      tick_star initSt s ∧
      σ2.(heap) !! ℓ = Some (Some #s.(hour)).
Proof. Admitted.

(* TODO: correctness of closed program *)
