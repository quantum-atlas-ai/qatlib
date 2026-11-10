/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StabilizerAlg.NearUniformGen.AbelianStabilizerDefs
set_option warningAsError false
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Concepts.StabilizerAlg.NearUniformGen.AspBisectionState
open Qatlib.Concepts.StabilizerAlg.NearUniformGen.AspRecordKernel

set_option autoImplicit false

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped BigOperators Classical

theorem asp_composite_probability_formula {Ω G : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype G] [DecidableEq G] (k : AspRecordKernel Ω G) (y : G) :
    k.marginal.prob y = ∑ V, k.joint V y := rfl

theorem asp_composite_probability_formula_set {Ω G : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype G] [DecidableEq G] (k : AspRecordKernel Ω G) (S : Finset G) :
    (∑ y ∈ S, k.marginal.prob y)
        = ∑ V : Ω, k.branchLaw.prob V * ∑ y ∈ S, (k.conditional V).prob y := by
  calc
    (∑ y ∈ S, k.marginal.prob y)
        = ∑ y ∈ S, ∑ V : Ω, k.branchLaw.prob V * (k.conditional V).prob y := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rfl
    _ = ∑ V : Ω, ∑ y ∈ S, k.branchLaw.prob V * (k.conditional V).prob y := Finset.sum_comm
    _ = ∑ V : Ω, k.branchLaw.prob V * ∑ y ∈ S, (k.conditional V).prob y := by
        refine Finset.sum_congr rfl fun V _ => ?_
        rw [Finset.mul_sum]

theorem asp_joint_law_marginal {Ω G : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype G]
    [DecidableEq G] (k : AspRecordKernel Ω G) (y : G) :
    (∑ V : Ω, (k.jointLaw).prob (V, y)) = k.marginal.prob y := by
  rw [AspRecordKernel.jointLaw]
  simp only [AspRecordKernel.joint]
  rfl

theorem asp_uniform_mixture_identity {Ω G : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq Ω] [Fintype G] [DecidableEq G] (k : AspRecordKernel Ω G)
    (hbr : ∀ V, k.branchLaw.prob V = (Fintype.card Ω : ℝ)⁻¹) (y : G) :
    k.marginal.prob y = (Fintype.card Ω : ℝ)⁻¹ * ∑ V, (k.conditional V).prob y := by
  calc
    k.marginal.prob y = ∑ V, k.branchLaw.prob V * (k.conditional V).prob y := rfl
    _ = ∑ V, (Fintype.card Ω : ℝ)⁻¹ * (k.conditional V).prob y := by
        refine Finset.sum_congr rfl fun V _ => ?_
        rw [hbr V]
    _ = (Fintype.card Ω : ℝ)⁻¹ * ∑ V, (k.conditional V).prob y := by
        rw [Finset.mul_sum]

noncomputable def aspOrbitRecordKernel {G : Type*} [Fintype G] [DecidableEq G]
    (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (cond : AddChar E ℂ → FinDist G) : AspRecordKernel (AddChar E ℂ) G where
  branchLaw := aspOrbitBranchLaw E
  conditional := cond

theorem asp_orbit_uniform_mixture_identity {G : Type*} [Fintype G] [DecidableEq G]
    (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (cond : AddChar E ℂ → FinDist G) (g : G) :
    (aspOrbitRecordKernel E cond).marginal.prob g
      = (Fintype.card (AddChar E ℂ) : ℝ)⁻¹ * ∑ χ : AddChar E ℂ, (cond χ).prob g := by
  refine asp_uniform_mixture_identity (aspOrbitRecordKernel E cond) ?_ g
  intro χ
  change (aspOrbitBranchLaw E).prob χ = (Fintype.card (AddChar E ℂ) : ℝ)⁻¹
  rw [aspOrbitBranchLaw_uniform, ← aspCharacterGroup_card E]

theorem asp_orbit_uniform_mixture_identity_q {G : Type*} [Fintype G] [DecidableEq G]
    (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (cond : AddChar E ℂ → FinDist G) (g : G) :
    (aspOrbitRecordKernel E cond).marginal.prob g
      = (Fintype.card E : ℝ)⁻¹ * ∑ χ : AddChar E ℂ, (cond χ).prob g := by
  rw [asp_orbit_uniform_mixture_identity, ← aspCharacterGroup_card E]

theorem asp_product_record_law_is_distribution {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) :
    (∑ ω : Fin l → G, (aspProductRecordLaw μ l).prob ω) = 1 :=
  (aspProductRecordLaw μ l).sum_one

theorem asp_product_record_mass_eq {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) (ω : Fin l → G) :
    (aspProductRecordLaw μ l).prob ω = μ.probOf ω := rfl

theorem asp_product_record_event_eq {G : Type*} [Fintype G] [DecidableEq G]
    (μ : FinDist G) (l : ℕ) (E : (Fin l → G) → Prop) [DecidablePred E] :
    (∑ ω ∈ Finset.univ.filter E, (aspProductRecordLaw μ l).prob ω)
      = FinDist.probEvent (L := l) μ E := by
  unfold FinDist.probEvent aspProductRecordLaw
  rfl

theorem asp_marginal_near_uniform {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) (k : AspRecordKernel (↥H) G) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hmix : ∀ g : G, k.marginal.prob g
      = (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (k.conditional h').prob g)
    (hacc : ∀ h' : ↥H, 1 - δ ≤ (k.conditional h').prob (h' : G)) :
    ∀ L : Finset ↥H,
      |(∑ g ∈ L, k.marginal.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ := by
  intro L
  exact compositeMeasurementNearUniformSubgoal G H k.marginal k.conditional δ hδ hmix hacc L

theorem asp_uniform_branch_near_uniform {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (H : AddSubgroup G) (k : AspRecordKernel (↥H) G) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hbr : ∀ h' : ↥H, k.branchLaw.prob h' = (Fintype.card ↥H : ℝ)⁻¹)
    (hacc : ∀ h' : ↥H, 1 - δ ≤ (k.conditional h').prob (h' : G)) :
    ∀ L : Finset ↥H,
      |(∑ g ∈ L, k.marginal.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ :=
  asp_marginal_near_uniform H k δ hδ
    (fun g => asp_uniform_mixture_identity k hbr g) hacc

theorem asp_constructed_generation {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (n : ℕ) (hn : 0 < n) (H : AddSubgroup G)
    (hcard : Fintype.card ↥H ≤ 2 ^ n) (k : AspRecordKernel (↥H) G) (δ : ℝ) (_hδ : 0 ≤ δ)
    (hnear : ∀ L : Finset ↥H,
      |(∑ g ∈ L, k.marginal.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ δ)
    (hbudget : δ ≤ 1 / ((6 : ℝ) * ↑(n + 4))) :
    FinDist.probEvent (L := n + 4) k.marginal
        (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G)) ≤ 1 / 3 := by
  refine abelianStabilizerWideGenerationSubgoal n hn G H hcard k.marginal ?_
  intro L
  exact le_trans (hnear L) (by linarith)

theorem asp_uniform_branch_generation {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (n : ℕ) (hn : 0 < n) (H : AddSubgroup G)
    (hcard : Fintype.card ↥H ≤ 2 ^ n) (k : AspRecordKernel (↥H) G)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hbr : ∀ h' : ↥H, k.branchLaw.prob h' = (Fintype.card ↥H : ℝ)⁻¹)
    (hacc : ∀ h' : ↥H, 1 - δ ≤ (k.conditional h').prob (h' : G))
    (hbudget : δ ≤ 1 / ((6 : ℝ) * ↑(n + 4))) :
    FinDist.probEvent (L := n + 4) k.marginal
        (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G)) ≤ 1 / 3 :=
  asp_constructed_generation n hn H hcard k δ hδ
    (asp_uniform_branch_near_uniform H k δ hδ hbr hacc) hbudget

theorem asp_bounded_error_accuracy {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (H : AddSubgroup G) (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (h' : ↥H) :
    1 - ε ≤ (aspBoundedErrorConditional (fun h : ↥H => (h : G)) ε hε hε1 h').prob (h' : G) := by
  have hpoint : (aspPointConditional (fun h : ↥H => (h : G)) h').prob (h' : G) = 1 := by
    simp [aspPointConditional]
  have hmix : (aspBoundedErrorConditional (fun h : ↥H => (h : G)) ε hε hε1 h').prob (h' : G)
      = (1 - ε) * (aspPointConditional (fun h : ↥H => (h : G)) h').prob (h' : G)
        + ε * (aspUniformLaw G).prob (h' : G) := by
    simp only [aspBoundedErrorConditional, finDistMix]
    ring
  rw [hmix, hpoint]
  have hunif : (0 : ℝ) ≤ (aspUniformLaw G).prob (h' : G) := (aspUniformLaw G).nonneg _
  have hmul : (0 : ℝ) ≤ ε * (aspUniformLaw G).prob (h' : G) := mul_nonneg hε hunif
  linarith

theorem asp_bounded_error_near_uniform {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (H : AddSubgroup G) (ε : ℝ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    let k : AspRecordKernel (↥H) G :=
      { branchLaw := aspUniformGroupBranchLaw G H
        conditional := aspBoundedErrorConditional (fun h : ↥H => (h : G)) ε hε hε1 }
    ∀ L : Finset ↥H,
      |(∑ g ∈ L, k.marginal.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)| ≤ ε := by
  (try dsimp only)
  refine asp_uniform_branch_near_uniform H _ ε hε ?_ ?_
  · intro h'
    rfl
  · intro h'
    exact asp_bounded_error_accuracy H ε hε hε1 h'

theorem asp_bounded_error_generation {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] [Nonempty G] (n : ℕ) (hn : 0 < n) (H : AddSubgroup G)
    (hcard : Fintype.card ↥H ≤ 2 ^ n) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbudget : ε ≤ 1 / ((6 : ℝ) * ↑(n + 4))) :
    FinDist.probEvent (L := n + 4)
        ({ branchLaw := aspUniformGroupBranchLaw G H
           conditional := aspBoundedErrorConditional (fun h : ↥H => (h : G)) ε hε hε1 } :
          AspRecordKernel (↥H) G).marginal
        (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G)) ≤ 1 / 3 := by
  refine asp_uniform_branch_generation n hn H hcard _ ε hε ?_ ?_ hbudget
  · intro h'
    rfl
  · intro h'
    exact asp_bounded_error_accuracy H ε hε hε1 h'

theorem asp_gate_is_paper_U_pow {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (l : ℕ) :
    ControlledPowers U (2 ^ l) = BlockDiag (fun x : Fin (2 ^ l) => U ^ (x.val : ℕ)) := rfl

theorem asp_gate_exponent_range (l : ℕ) (x : Fin (2 ^ l)) : x.val ≤ 2 ^ l - 1 := by
  have h : x.val < 2 ^ l := x.isLt
  omega

theorem asp_gate_provides_localisation_powers (l : ℕ) (j : ℕ) (hj : j < l) :
    2 ^ j ≤ 2 ^ l - 1 := by
  have h : 2 ^ j ≤ 2 ^ (l - 1) :=
    Nat.pow_le_pow_right (n := 2) (by omega) (i := j) (j := l - 1) (by omega)
  have h2 : 2 ^ (l - 1) < 2 ^ l :=
    Nat.pow_lt_pow_right (a := 2) (by omega) (m := l - 1) (n := l) (by omega)
  omega

theorem asp_gate_localisation_block (l : ℕ) (j : ℕ) (hj : j < l) : (2 ^ j : ℕ) < 2 ^ l := by
  exact Nat.pow_lt_pow_right (a := 2) (by omega) (m := j) (n := l) hj

theorem aspBisectionStateAt_level (o : ℕ → Bool) (k : ℕ) :
    (aspBisectionStateAt o k).level = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show ((aspBisectionStateAt o k).step (o k)).level = k + 1
      have hstep : ((aspBisectionStateAt o k).step (o k)).level
          = (aspBisectionStateAt o k).level + 1 := rfl
      rw [hstep, ih]

theorem aspBisectionStateAt_queries (o : ℕ → Bool) (k : ℕ) :
    (aspBisectionStateAt o k).queries = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show ((aspBisectionStateAt o k).step (o k)).queries = k + 1
      have hstep : ((aspBisectionStateAt o k).step (o k)).queries
          = (aspBisectionStateAt o k).queries + 1 := rfl
      rw [hstep, ih]

theorem AspBisectionState.step_width (s : AspBisectionState) (b : Bool) :
    (s.step b).width = s.width / 2 := by
  have hpow : (2 : ℝ) ^ (s.level + 1) = 2 ^ s.level * 2 := pow_succ _ _
  have hne : (2 : ℝ) ^ s.level ≠ 0 := by positivity
  rw [show (s.step b).width = 1 / 2 ^ (s.level + 1) from rfl]
  rw [show s.width = 1 / 2 ^ s.level from rfl]
  rw [hpow]
  field_simp

theorem AspBisectionState.step_lower (s : AspBisectionState) (b : Bool) :
    (s.step b).lower = (if b = true then s.mid else s.lower) := by
  have hpow : (2 : ℝ) ^ (s.level + 1) = 2 ^ s.level * 2 := pow_succ _ _
  have hne : (2 : ℝ) ^ s.level ≠ 0 := by positivity
  cases b with
  | false =>
      show ((s.step false).bits : ℝ) / 2 ^ (s.level + 1)
          = (s.bits : ℝ) / 2 ^ s.level
      rw [show (s.step false).bits = 2 * s.bits by rfl]
      rw [hpow]
      field_simp
      push_cast
      ring
  | true =>
      show ((s.step true).bits : ℝ) / 2 ^ (s.level + 1)
          = (s.bits : ℝ) / 2 ^ s.level + (1 / 2 ^ s.level) / 2
      rw [show (s.step true).bits = 2 * s.bits + 1 by rfl]
      rw [hpow]
      field_simp
      push_cast
      ring

theorem aspBisectionStateAt_width (o : ℕ → Bool) (k : ℕ) :
    (aspBisectionStateAt o k).width = 1 / 2 ^ k := by
  induction k with
  | zero =>
      show (aspBisectionInitial.width) = 1 / 2 ^ 0
      simp [AspBisectionState.width, aspBisectionInitial]
  | succ k ih =>
      show ((aspBisectionStateAt o k).step (o k)).width = 1 / 2 ^ (k + 1)
      rw [AspBisectionState.step_width, ih]
      rw [pow_succ]
      field_simp

theorem aspBisectionRun_queries (l : ℕ) (o : ℕ → Bool) :
    (aspBisectionRun l o).queries = l + 2 := by
  rw [aspBisectionRun, aspBisectionStateAt_queries]

theorem aspBisectionRun_level (l : ℕ) (o : ℕ → Bool) :
    (aspBisectionRun l o).level = l + 2 := by
  rw [aspBisectionRun, aspBisectionStateAt_level]

theorem aspBisectionRun_width (l : ℕ) (o : ℕ → Bool) :
    (aspBisectionRun l o).width = 1 / 2 ^ (l + 2) := by
  rw [aspBisectionRun, aspBisectionStateAt_width]

def AspBisectionOracleCorrect (o : ℕ → Bool) (φ : ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n →
    (o k = true ↔ ((aspBisectionStateAt o k).mid ≤ φ ∧
      φ < (aspBisectionStateAt o k).lower + (aspBisectionStateAt o k).width))

theorem aspBisectionStateAt_contains (o : ℕ → Bool) (φ : ℝ) (n : ℕ)
    (horacle : AspBisectionOracleCorrect o φ n) (hφ : 0 ≤ φ ∧ φ < 1) :
    ∀ k : ℕ, k ≤ n →
      (aspBisectionStateAt o k).lower ≤ φ ∧
        φ < (aspBisectionStateAt o k).lower + (aspBisectionStateAt o k).width := by
  intro k hk
  unfold AspBisectionOracleCorrect at horacle
  induction k with
  | zero =>
      have h0 : (aspBisectionStateAt o 0).lower = 0 := by
        simp [aspBisectionStateAt, aspBisectionInitial, AspBisectionState.lower]
      have w0 : (aspBisectionStateAt o 0).width = 1 := by
        simp [aspBisectionStateAt, aspBisectionInitial, AspBisectionState.width]
      rw [h0, w0]
      exact ⟨hφ.1, by linarith⟩
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have hinv := ih hk'
      have hor := horacle k (by omega)
      rw [show aspBisectionStateAt o (k + 1) = (aspBisectionStateAt o k).step (o k) from rfl]
      by_cases hb : o k = true
      · have hmid : (aspBisectionStateAt o k).mid ≤ φ ∧
            φ < (aspBisectionStateAt o k).lower + (aspBisectionStateAt o k).width :=
          hor.mp hb
        rw [AspBisectionState.step_lower, AspBisectionState.step_width]
        simp [hb]
        constructor
        · exact hmid.1
        · have hid : (aspBisectionStateAt o k).mid + (aspBisectionStateAt o k).width / 2
              = (aspBisectionStateAt o k).lower + (aspBisectionStateAt o k).width := by
            simp [AspBisectionState.mid]
            ring
          linarith
      · have hnot : ¬ ((aspBisectionStateAt o k).mid ≤ φ ∧
            φ < (aspBisectionStateAt o k).lower + (aspBisectionStateAt o k).width) := by
          intro h
          exact hb (hor.mpr h)
        rw [AspBisectionState.step_lower, AspBisectionState.step_width]
        simp [hb]
        constructor
        · exact hinv.1
        · have hmidlt : φ < (aspBisectionStateAt o k).mid := by
            by_contra hc
            exact hnot ⟨not_lt.mp hc, hinv.2⟩
          have hid : (aspBisectionStateAt o k).mid
              = (aspBisectionStateAt o k).lower + (aspBisectionStateAt o k).width / 2 := by
            simp [AspBisectionState.mid]
          linarith

theorem aspBisection_contains (l : ℕ) (o : ℕ → Bool) (φ : ℝ) (hφ : 0 ≤ φ ∧ φ < 1)
    (horacle : AspBisectionOracleCorrect o φ (l + 2)) :
    (aspBisectionRun l o).lower ≤ φ ∧
      φ < (aspBisectionRun l o).lower + (aspBisectionRun l o).width :=
  aspBisectionStateAt_contains o φ (l + 2) horacle hφ (l + 2) (by omega)

end Qatlib.Concepts.FourierRecovery.ModularFourier
