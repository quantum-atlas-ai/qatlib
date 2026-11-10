/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdaptiveTest26.MainResults.AdaptiveFidelityTestingDefs
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.AdversaryBounds.AdvDuality.InstrumentLoopBudget
import QuantumInfo.Channels.Dual
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.AdaptiveTest26.MainResults

set_option autoImplicit false

open Qatlib.Papers.AdaptiveTest26.MainResults Matrix
open scoped BigOperators ComplexOrder MatrixOrder

variable {D O : ℕ}

theorem schattenOne_nonneg (A : Operator D) : 0 ≤ SchattenOne A := by
  rw [Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm]
  exact Matrix.traceNorm_nonneg A

theorem schattenOne_zero : SchattenOne (0 : Operator D) = 0 := by
  rw [Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm,
      Matrix.traceNorm_zero]

theorem rootFidelity_nonneg (ρ σ : Operator D) : 0 ≤ RootFidelity ρ σ :=
  schattenOne_nonneg _

theorem rootFidelity_self {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    RootFidelity ρ ρ = 1 := by
  have hnn : (0 : Operator D) ≤ ρ := hρ.1.nonneg
  have hsqrt : CFC.sqrt ρ = cfc Real.sqrt ρ := by
    rw [CFC.sqrt_eq_real_sqrt ρ hnn, cfcₙ_eq_cfc]
  have hsq : cfc Real.sqrt ρ * cfc Real.sqrt ρ = ρ := by
    rw [← hsqrt]
    exact CFC.sqrt_mul_sqrt_self ρ hnn
  rw [RootFidelity, hsq, schattenOne_eq_re_trace hρ.1, hρ.2, Complex.one_re]

theorem rootFidelity_self_pos {ρ : Operator D} (hρ : IsDensityOperator ρ) :
    0 < RootFidelity ρ ρ := by
  rw [rootFidelity_self hρ]
  exact Real.zero_lt_one

theorem not_isH1_self {ρ : Operator D} (hρ : IsDensityOperator ρ) {ε : ℝ}
    (hε : 0 < ε) : ¬ IsH1 ε ρ ρ := by
  intro h
  have h1 : RootFidelity ρ ρ ≤ 1 - ε := h
  rw [rootFidelity_self hρ] at h1
  exact absurd h1 (by linarith)

theorem isH1_le_one {ε : ℝ} {ρ σ : Operator D} (h : IsH1 ε ρ σ) : ε ≤ 1 := by
  have h0 : (0 : ℝ) ≤ RootFidelity ρ σ := rootFidelity_nonneg ρ σ
  have h1 : RootFidelity ρ σ ≤ 1 - ε := h
  linarith

theorem successFloor_pos : 0 < SuccessFloor := by
  norm_num [SuccessFloor]

theorem successFloor_lt_one : SuccessFloor < 1 := by
  norm_num [SuccessFloor]

theorem outcomeProb_nonneg {E : PovmEffects D O} {ρ : Operator D}
    (hE : ∀ i : Fin O, (E i).PosSemidef) (hρ : ρ.PosSemidef) (i : Fin O) :
    0 ≤ outcomeProb E ρ i := by
  have h := Matrix.PosSemidef.trace_mul_nonneg (hE i) hρ
  exact (RCLike.nonneg_iff.mp h).1

theorem sum_outcomeProb_eq_one {E : PovmEffects D O} {ρ : Operator D}
    (hE : IsPovmEffects E) (hρ : IsDensityOperator ρ) :
    ∑ i : Fin O, outcomeProb E ρ i = 1 := by
  have htrace : (∑ i : Fin O, ((E i * ρ).trace)).re
      = ((∑ i : Fin O, E i) * ρ).trace.re := by
    rw [Finset.sum_mul, Matrix.trace_sum]
  have h1 : ((∑ i : Fin O, E i) * ρ).trace = 1 := by
    rw [hE.2, one_mul, hρ.2]
  calc ∑ i : Fin O, outcomeProb E ρ i
      = (∑ i : Fin O, ((E i * ρ).trace)).re := by
        simp only [outcomeProb, Complex.re_sum]
    _ = ((∑ i : Fin O, E i) * ρ).trace.re := htrace
    _ = (1 : ℂ).re := by rw [h1]
    _ = 1 := Complex.one_re

theorem outcomeProb_le_one {E : PovmEffects D O} {ρ : Operator D}
    (hE : IsPovmEffects E) (hρ : IsDensityOperator ρ) (i : Fin O) :
    outcomeProb E ρ i ≤ 1 := by
  have hnonneg : ∀ j : Fin O, (0 : ℝ) ≤ outcomeProb E ρ j :=
    fun j => outcomeProb_nonneg (fun k => (hE.1 k)) hρ.1 j
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin O)))
    (f := fun j : Fin O => outcomeProb E ρ j) (fun j _ => hnonneg j) (Finset.mem_univ i)
  rw [sum_outcomeProb_eq_one hE hρ] at h
  exact h

theorem sum_prod_outcomeProb_eq_one {steps : ℕ}
    (povm : Fin steps → PovmEffects D O) (stream : Fin steps → StreamTag)
    (ρ σ : Operator D) (hp : ∀ t : Fin steps, IsPovmEffects (povm t))
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    ∑ h : OutcomeRecord O steps,
      ∏ t : Fin steps, outcomeProb (povm t) (stateFor (stream t) ρ σ) (h t) = 1 := by
  have hstate : ∀ t : Fin steps, IsDensityOperator (stateFor (stream t) ρ σ) := by
    intro t
    rcases h : stream t with _ | _
    · simpa [stateFor, h] using hρ
    · simpa [stateFor, h] using hσ
  have hsingle : ∀ t : Fin steps,
      ∑ j : Fin O, outcomeProb (povm t) (stateFor (stream t) ρ σ) j = 1 :=
    fun t => sum_outcomeProb_eq_one (hp t) (hstate t)
  set f : Fin steps → Fin O → ℝ :=
    fun t j => outcomeProb (povm t) (stateFor (stream t) ρ σ) j with hf
  have hswap : (∑ h : OutcomeRecord O steps, ∏ t, f t (h t))
      = ∑ h ∈ Fintype.piFinset (fun _ : Fin steps => (Finset.univ : Finset (Fin O))),
        ∏ t, f t (h t) :=
    Finset.sum_congr rfl (fun ω _ => rfl)
  rw [hswap, ← Finset.prod_univ_sum (t := fun _ : Fin steps => (Finset.univ : Finset (Fin O)))
      (f := f)]
  have hprod : (∏ t : Fin steps, ∑ j : Fin O, f t j) = 1 := by
    rw [Finset.prod_congr rfl (fun t _ => hsingle t), Finset.prod_const_one]
  exact hprod

theorem nonAdaptiveAcceptProb_of_decide_eq_true (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) (hp : ∀ t : Fin S.steps, IsPovmEffects (S.povm t))
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hdec : ∀ h : OutcomeRecord O S.steps, S.decide h = true) :
    nonAdaptiveAcceptProb S ρ σ = 1 := by
  have hkey : ∀ h : OutcomeRecord O S.steps,
      (if S.decide h then (1 : ℝ) else 0) *
        ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)
      = ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t) := by
    intro h
    rw [if_pos (hdec h), one_mul]
  show (∑ h : OutcomeRecord O S.steps,
      (if S.decide h then (1 : ℝ) else 0) *
        ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)) = 1
  exact (Finset.sum_congr rfl (fun h _ => hkey h)).trans
    (sum_prod_outcomeProb_eq_one S.povm S.stream ρ σ hp hρ hσ)

theorem nonAdaptiveAcceptProb_of_decide_eq_false (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D)
    (hdec : ∀ h : OutcomeRecord O S.steps, S.decide h = false) :
    nonAdaptiveAcceptProb S ρ σ = 0 := by
  have hkey : ∀ h : OutcomeRecord O S.steps,
      (if S.decide h then (1 : ℝ) else 0) *
        ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t) = 0 := by
    intro h
    have hc : ¬ (S.decide h = true) := by
      intro he
      rw [hdec h] at he
      exact Bool.noConfusion he
    rw [if_neg hc, zero_mul]
  show (∑ h : OutcomeRecord O S.steps,
      (if S.decide h then (1 : ℝ) else 0) *
        ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)) = 0
  exact (Finset.sum_congr rfl (fun h _ => hkey h)).trans (Finset.sum_const_zero)

theorem nonAdaptiveAcceptProb_nonneg (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) (hp : ∀ t : Fin S.steps, IsPovmEffects (S.povm t))
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    0 ≤ nonAdaptiveAcceptProb S ρ σ := by
  have hstate : ∀ t : Fin S.steps,
      (stateFor (S.stream t) ρ σ).PosSemidef := by
    intro t
    rcases hh : S.stream t with _ | _
    · simpa [stateFor, hh] using hρ.1
    · simpa [stateFor, hh] using hσ.1
  have hprod : ∀ h : OutcomeRecord O S.steps,
      (0 : ℝ) ≤ ∏ t : Fin S.steps,
        outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t) := by
    intro h
    apply Finset.prod_nonneg
    intro t _
    exact outcomeProb_nonneg (fun i => (hp t).1 i) (hstate t) (h t)
  apply Finset.sum_nonneg
  intro h _
  by_cases hc : S.decide h = true
  · rw [if_pos hc, one_mul]
    exact hprod h
  · rw [if_neg hc, zero_mul]

theorem nonAdaptiveAcceptProb_le_one (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) (hp : ∀ t : Fin S.steps, IsPovmEffects (S.povm t))
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    nonAdaptiveAcceptProb S ρ σ ≤ 1 := by
  have hstate : ∀ t : Fin S.steps,
      (stateFor (S.stream t) ρ σ).PosSemidef := by
    intro t
    rcases hh : S.stream t with _ | _
    · simpa [stateFor, hh] using hρ.1
    · simpa [stateFor, hh] using hσ.1
  have hprod_nonneg : ∀ h : OutcomeRecord O S.steps,
      (0 : ℝ) ≤ ∏ t : Fin S.steps,
        outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t) := by
    intro h
    apply Finset.prod_nonneg
    intro t _
    exact outcomeProb_nonneg (fun i => (hp t).1 i) (hstate t) (h t)
  have hterm : ∀ h : OutcomeRecord O S.steps,
      (if S.decide h then (1 : ℝ) else 0) *
        ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)
      ≤ ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t) := by
    intro h
    by_cases hc : S.decide h = true
    · rw [if_pos hc, one_mul]
    · rw [if_neg hc, zero_mul]
      exact hprod_nonneg h
  have htotal : (∑ h : OutcomeRecord O S.steps,
      ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)) = 1 :=
    sum_prod_outcomeProb_eq_one S.povm S.stream ρ σ hp hρ hσ
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (OutcomeRecord O S.steps)))
    (fun h _ => hterm h)
  show (∑ h : OutcomeRecord O S.steps,
      (if S.decide h then (1 : ℝ) else 0) *
        ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)) ≤ 1
  rw [htotal] at hsum
  exact hsum

theorem randomizedAcceptProb_nonneg (S : RandomizedNonAdaptiveStrategy D O)
    (ρ σ : Operator D) (hp : IsAdmissibleRandomizedNonAdaptive S)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    0 ≤ randomizedAcceptProb S ρ σ := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (S.weight_nonneg i)
    (nonAdaptiveAcceptProb_nonneg (S.component i) ρ σ (fun t => (hp i) t) hρ hσ)

theorem randomizedAcceptProb_le_one (S : RandomizedNonAdaptiveStrategy D O)
    (ρ σ : Operator D) (hp : IsAdmissibleRandomizedNonAdaptive S)
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    randomizedAcceptProb S ρ σ ≤ 1 := by
  have hle : ∀ i : Fin S.support,
      S.weight i * nonAdaptiveAcceptProb (S.component i) ρ σ ≤ S.weight i * 1 := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (nonAdaptiveAcceptProb_le_one (S.component i) ρ σ (fun t => (hp i) t) hρ hσ)
      (S.weight_nonneg i)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin S.support)))
    (fun i _ => hle i)
  simp only [randomizedAcceptProb]
  rw [← Finset.sum_mul, S.weight_sum, one_mul] at hsum
  exact hsum

theorem streamTag_eq_rho_or_sigma (t : StreamTag) : t = StreamTag.rho ∨ t = StreamTag.sigma := by
  rcases t with _ | _ <;> simp

theorem nonAdaptive_ledger_rho_add_sigma (S : NonAdaptiveStrategy D O) :
    S.ledger.rho + S.ledger.sigma = S.steps := by
  have hsplit : ∀ t : Fin S.steps,
      (if S.stream t = StreamTag.rho then (1 : ℕ) else 0)
        + (if S.stream t = StreamTag.sigma then 1 else 0) = 1 := by
    intro t
    rcases h : S.stream t with _ | _ <;> simp_all
  simp only [NonAdaptiveStrategy.ledger, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  simp_rw [hsplit]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem nonAdaptive_ledger_total (S : NonAdaptiveStrategy D O) :
    CopyLedger.total S.ledger = S.steps := by
  simp only [CopyLedger.total]
  exact nonAdaptive_ledger_rho_add_sigma S

theorem nonAdaptive_ledger_rho_le_steps (S : NonAdaptiveStrategy D O) :
    S.ledger.rho ≤ S.steps :=
  Nat.le.intro (nonAdaptive_ledger_rho_add_sigma S)

theorem nonAdaptive_ledger_sigma_le_steps (S : NonAdaptiveStrategy D O) :
    S.ledger.sigma ≤ S.steps := by
  have h := nonAdaptive_ledger_rho_add_sigma S
  omega

theorem le_worstLedger_rho (S : RandomizedNonAdaptiveStrategy D O) (i : Fin S.support) :
    (S.component i).ledger.rho ≤ S.worstLedger.rho :=
  Finset.le_sup (f := fun j : Fin S.support => (S.component j).ledger.rho) (Finset.mem_univ i)

theorem le_worstLedger_sigma (S : RandomizedNonAdaptiveStrategy D O) (i : Fin S.support) :
    (S.component i).ledger.sigma ≤ S.worstLedger.sigma :=
  Finset.le_sup (f := fun j : Fin S.support => (S.component j).ledger.sigma) (Finset.mem_univ i)

theorem le_worstTotalCopies (S : RandomizedNonAdaptiveStrategy D O) (i : Fin S.support) :
    (S.component i).steps ≤ S.worstTotalCopies :=
  Finset.le_sup (f := fun j : Fin S.support => (S.component j).steps) (Finset.mem_univ i)

theorem worstLedger_rho_le_worstTotalCopies (S : RandomizedNonAdaptiveStrategy D O) :
    S.worstLedger.rho ≤ S.worstTotalCopies := by
  show (Finset.univ.sup fun j : Fin S.support => (S.component j).ledger.rho) ≤
    (Finset.univ.sup fun j : Fin S.support => (S.component j).steps)
  exact Finset.sup_le (fun i _ =>
    (nonAdaptive_ledger_rho_le_steps (S.component i)).trans (le_worstTotalCopies S i))

theorem worstLedger_sigma_le_worstTotalCopies (S : RandomizedNonAdaptiveStrategy D O) :
    S.worstLedger.sigma ≤ S.worstTotalCopies := by
  show (Finset.univ.sup fun j : Fin S.support => (S.component j).ledger.sigma) ≤
    (Finset.univ.sup fun j : Fin S.support => (S.component j).steps)
  exact Finset.sup_le (fun i _ =>
    (nonAdaptive_ledger_sigma_le_steps (S.component i)).trans (le_worstTotalCopies S i))

theorem worstTotalCopies_le_worstLedger_sum (S : RandomizedNonAdaptiveStrategy D O) :
    S.worstTotalCopies ≤ S.worstLedger.rho + S.worstLedger.sigma :=
  Finset.sup_le (fun i _ => by
    have h := nonAdaptive_ledger_rho_add_sigma (S.component i)
    calc (S.component i).steps
        = (S.component i).ledger.rho + (S.component i).ledger.sigma := h.symm
      _ ≤ S.worstLedger.rho + S.worstLedger.sigma :=
        add_le_add (le_worstLedger_rho S i) (le_worstLedger_sigma S i))

theorem adaptive_rhoUses_add_sigmaUses (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) :
    S.rhoUses h + S.sigmaUses h = S.steps := by
  have hsplit : ∀ t : Fin S.steps,
      (if S.stream t (recordPrefix h t) = StreamTag.rho then (1 : ℕ) else 0)
        + (if S.stream t (recordPrefix h t) = StreamTag.sigma then 1 else 0) = 1 := by
    intro t
    rcases hh : S.stream t (recordPrefix h t) with _ | _ <;> simp_all
  simp only [AdaptiveStrategy.rhoUses, AdaptiveStrategy.sigmaUses,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  simp_rw [hsplit]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

theorem adaptive_rhoUses_le_steps (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : S.rhoUses h ≤ S.steps :=
  Nat.le.intro (adaptive_rhoUses_add_sigmaUses S h)

theorem adaptive_sigmaUses_le_steps (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : S.sigmaUses h ≤ S.steps := by
  have hh := adaptive_rhoUses_add_sigmaUses S h
  omega

theorem rhoUses_le_worstLedger_rho (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : S.rhoUses h ≤ S.worstLedger.rho :=
  Finset.le_sup (f := fun g : OutcomeRecord O S.steps => S.rhoUses g) (Finset.mem_univ h)

theorem sigmaUses_le_worstLedger_sigma (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : S.sigmaUses h ≤ S.worstLedger.sigma :=
  Finset.le_sup (f := fun g : OutcomeRecord O S.steps => S.sigmaUses g) (Finset.mem_univ h)

theorem adaptive_worstLedger_rho_le_steps (S : AdaptiveStrategy D O) :
    S.worstLedger.rho ≤ S.steps :=
  Finset.sup_le (fun h _ => adaptive_rhoUses_le_steps S h)

theorem adaptive_worstLedger_sigma_le_steps (S : AdaptiveStrategy D O) :
    S.worstLedger.sigma ≤ S.steps :=
  Finset.sup_le (fun h _ => adaptive_sigmaUses_le_steps S h)

theorem adaptive_steps_le_worstLedger_sum (S : AdaptiveStrategy D O)
    (hne : Nonempty (OutcomeRecord O S.steps)) :
    S.steps ≤ S.worstLedger.rho + S.worstLedger.sigma := by
  obtain ⟨h⟩ := hne
  have hkey := adaptive_rhoUses_add_sigmaUses S h
  calc S.steps
      = S.rhoUses h + S.sigmaUses h := hkey.symm
    _ ≤ S.worstLedger.rho + S.worstLedger.sigma :=
      add_le_add (rhoUses_le_worstLedger_rho S h) (sigmaUses_le_worstLedger_sigma S h)

theorem nonAdaptiveAcceptProb_eq_of_all_streams_rho (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) (h : ∀ t : Fin S.steps, S.stream t = StreamTag.rho) :
    nonAdaptiveAcceptProb S ρ σ = nonAdaptiveAcceptProb S ρ ρ := by
  simp only [nonAdaptiveAcceptProb]
  refine Finset.sum_congr rfl (fun hh _ => ?_)
  have hprod : (∏ t : Fin S.steps,
      outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (hh t))
      = ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) ρ ρ) (hh t) := by
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [h t]
    rfl
  rw [hprod]

theorem nonAdaptiveAcceptProb_eq_of_all_streams_sigma (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) (h : ∀ t : Fin S.steps, S.stream t = StreamTag.sigma) :
    nonAdaptiveAcceptProb S ρ σ = nonAdaptiveAcceptProb S σ σ := by
  simp only [nonAdaptiveAcceptProb]
  refine Finset.sum_congr rfl (fun hh _ => ?_)
  have hprod : (∏ t : Fin S.steps,
      outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (hh t))
      = ∏ t : Fin S.steps, outcomeProb (S.povm t) (stateFor (S.stream t) σ σ) (hh t) := by
    refine Finset.prod_congr rfl (fun t _ => ?_)
    rw [h t]
    rfl
  rw [hprod]

theorem stream_const_of_steps_le_one (S : NonAdaptiveStrategy D O) (h : S.steps ≤ 1) :
    (∀ t : Fin S.steps, S.stream t = StreamTag.rho) ∨
      (∀ t : Fin S.steps, S.stream t = StreamTag.sigma) := by
  by_cases h0 : S.steps = 0
  · left
    intro t
    have hlt : (t.val : ℕ) < 0 := by
      rw [← h0]
      exact t.isLt
    omega
  · have hi : 0 < S.steps := by omega
    have hval : ∀ t : Fin S.steps, t.val = 0 := by
      intro t
      have := t.isLt
      omega
    have heq : ∀ t u : Fin S.steps, t = u := by
      intro t u
      apply Fin.ext
      rw [hval t, hval u]
    obtain hstr := streamTag_eq_rho_or_sigma (S.stream ⟨0, hi⟩)
    cases hstr with
    | inl hr =>
      left
      intro t
      rw [heq t ⟨0, hi⟩]
      exact hr
    | inr hs =>
      right
      intro t
      rw [heq t ⟨0, hi⟩]
      exact hs

theorem accept_swap_add_of_steps_le_one (S : NonAdaptiveStrategy D O) (ρ σ : Operator D)
    (h : S.steps ≤ 1) :
    nonAdaptiveAcceptProb S ρ ρ + nonAdaptiveAcceptProb S σ σ
      = nonAdaptiveAcceptProb S ρ σ + nonAdaptiveAcceptProb S σ ρ := by
  rcases stream_const_of_steps_le_one S h with hr | hs
  · rw [nonAdaptiveAcceptProb_eq_of_all_streams_rho S ρ σ hr,
      nonAdaptiveAcceptProb_eq_of_all_streams_rho S σ ρ hr]
  · rw [nonAdaptiveAcceptProb_eq_of_all_streams_sigma S σ ρ hs,
      nonAdaptiveAcceptProb_eq_of_all_streams_sigma S ρ σ hs]
    exact add_comm _ _

theorem randomizedAccept_swap_add_of_worstTotalCopies_le_one
    (S : RandomizedNonAdaptiveStrategy D O) (ρ σ : Operator D)
    (h : S.worstTotalCopies ≤ 1) :
    randomizedAcceptProb S ρ ρ + randomizedAcceptProb S σ σ
      = randomizedAcceptProb S ρ σ + randomizedAcceptProb S σ ρ := by
  have hsteps : ∀ i : Fin S.support, (S.component i).steps ≤ 1 := by
    intro i
    have hi := le_worstTotalCopies S i
    omega
  have hi : ∀ i : Fin S.support,
      nonAdaptiveAcceptProb (S.component i) ρ ρ + nonAdaptiveAcceptProb (S.component i) σ σ
        = nonAdaptiveAcceptProb (S.component i) ρ σ
          + nonAdaptiveAcceptProb (S.component i) σ ρ :=
    fun i => accept_swap_add_of_steps_le_one (S.component i) ρ σ (hsteps i)
  simp only [randomizedAcceptProb]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← mul_add, ← mul_add, hi i]

def basisProj (D : ℕ) (i : Fin D) : Operator D :=
  Matrix.diagonal (fun j : Fin D => if j = i then (1 : ℂ) else 0)

theorem basisProj_posSemidef {D : ℕ} (i : Fin D) : (basisProj D i).PosSemidef := by
  unfold basisProj
  rw [Matrix.posSemidef_diagonal_iff]
  intro j
  by_cases hj : j = i
  · rw [if_pos hj]
    exact zero_le_one
  · rw [if_neg hj]

theorem isDensityOperator_basisProj {D : ℕ} (i : Fin D) :
    IsDensityOperator (basisProj D i) := by
  refine ⟨basisProj_posSemidef i, ?_⟩
  unfold basisProj
  rw [Matrix.trace_diagonal]
  simp

theorem basisProj_mul_self {D : ℕ} (i : Fin D) :
    basisProj D i * basisProj D i = basisProj D i := by
  unfold basisProj
  rw [Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem basisProj_mul_basisProj_eq_zero {D : ℕ} {i k : Fin D} (hik : i ≠ k) :
    basisProj D i * basisProj D k = 0 := by
  have hfun : (fun j : Fin D =>
      (if j = i then (1 : ℂ) else 0) * (if j = k then (1 : ℂ) else 0))
      = fun _ => (0 : ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hik]
    · simp [hj]
  unfold basisProj
  rw [Matrix.diagonal_mul_diagonal, hfun, Matrix.diagonal_zero]

theorem rootFidelity_basisProj {D : ℕ} {i k : Fin D} (hik : i ≠ k) :
    RootFidelity (basisProj D i) (basisProj D k) = 0 := by
  have hsq : ∀ j : Fin D, cfc Real.sqrt (basisProj D j) = basisProj D j := by
    intro j
    have hnn : (0 : Operator D) ≤ basisProj D j := (basisProj_posSemidef j).nonneg
    have h1 : CFC.sqrt (basisProj D j) = cfc Real.sqrt (basisProj D j) := by
      rw [CFC.sqrt_eq_real_sqrt _ hnn, cfcₙ_eq_cfc]
    rw [← h1]
    exact CFC.sqrt_unique (basisProj_mul_self j) hnn
  rw [RootFidelity, hsq i, hsq k, basisProj_mul_basisProj_eq_zero hik, schattenOne_zero]

theorem exists_isH1_pair {D : ℕ} (hD : 2 ≤ D) {ε : ℝ} (hε : ε ≤ 1) :
    ∃ ρ σ : Operator D, IsDensityOperator ρ ∧ IsDensityOperator σ ∧ IsH1 ε ρ σ := by
  have hi : 0 < D := by omega
  have hk : 1 < D := by omega
  refine ⟨basisProj D ⟨0, hi⟩, basisProj D ⟨1, hk⟩,
    isDensityOperator_basisProj _, isDensityOperator_basisProj _, ?_⟩
  have hik : (⟨0, hi⟩ : Fin D) ≠ ⟨1, hk⟩ := by
    intro h
    have hval : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hF := rootFidelity_basisProj hik
  show RootFidelity (basisProj D ⟨0, hi⟩) (basisProj D ⟨1, hk⟩) ≤ 1 - ε
  rw [hF]
  linarith

theorem not_correct_of_worstTotalCopies_le_one
    (S : RandomizedNonAdaptiveStrategy D O) {ε : ℝ} (hε : ε ≤ 1) (hD : 2 ≤ D)
    (hcopies : S.worstTotalCopies ≤ 1)
    (hc : IsCorrectNonAdaptiveEquivalenceTester S ε) : False := by
  obtain ⟨hadm, hnull, halt⟩ := hc
  obtain ⟨ρ, σ, hρ, hσ, hh1⟩ := exists_isH1_pair hD hε
  have hswap := randomizedAccept_swap_add_of_worstTotalCopies_le_one S ρ σ hcopies
  have h0ρ : SuccessFloor ≤ randomizedAcceptProb S ρ ρ := hnull ρ hρ
  have h0σ : SuccessFloor ≤ randomizedAcceptProb S σ σ := hnull σ hσ
  have h1 : randomizedAcceptProb S ρ σ ≤ 1 - SuccessFloor := halt ρ σ hρ hσ hh1
  have hle : randomizedAcceptProb S σ ρ ≤ 1 :=
    randomizedAcceptProb_le_one S σ ρ hadm hσ hρ
  have hSF : SuccessFloor = (99 : ℝ) / 100 := rfl
  linarith

theorem worstTotalCopies_two_le_of_correct
    (S : RandomizedNonAdaptiveStrategy D O) {ε : ℝ} (hε : ε ≤ 1) (hD : 2 ≤ D)
    (hc : IsCorrectNonAdaptiveEquivalenceTester S ε) :
    2 ≤ S.worstTotalCopies := by
  by_contra hlt
  exact not_correct_of_worstTotalCopies_le_one S hε hD (by omega) hc

end Qatlib.Papers.AdaptiveTest26.MainResults
