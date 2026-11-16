/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Thermalize11.MainResults.SourceModel.SourceMicrocanonical
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section


/-!
# Thermalize11 reviewed Corollary

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.Thermalize11.MainResults.Corollary1

open Qatlib.Papers.Thermalize11.MainResults.SourceModel

/-- The numerical data shared by both halves of Corollary 1: subsystem
dimension `d_S`, the support dimensions `Ω_min`, `Ω_max`, the boundary count
`Ω_ε`, the coupling norm `‖V‖∞`, the window parameters `ε`, `Δ`, and the slack
`ε'` of Eq. (5). -/
structure Settings where
  /-- Dimension of the thermalized subsystem `S` (number of qubits `n` below). -/
  dS : ℕ
  /-- Minimal support dimension `Ω_min = min(rank G, rank F)`. -/
  OmegaMin : ℕ
  /-- Maximal support dimension `Ω_max = max(rank G, rank F)`. -/
  OmegaMax : ℕ
  /-- Boundary count `Ω_ε`, i.e. the total number of eigenstates in the two
  `ε`-boundary windows. -/
  OmegaE : ℕ
  /-- `‖V‖∞`, the operator norm of the coupling. -/
  couplingNorm : ℝ
  /-- The energy window width `Δ`. -/
  Delta : ℝ
  /-- The boundary width `ε`. -/
  eps : ℝ
  /-- `ΔΩ = Ω_max − Ω_min`. -/
  DeltaOmega : ℝ
  /-- The slack `ε'` of Eq. (5). -/
  eps' : ℝ

namespace Settings

variable (S : Settings)

/-- The Theorem-1 right-hand side `‖V‖∞/ε + (ΔΩ + Ω_ε)/(2Ω_max)`, shared by
Eqs. (5) and (6). -/
def theorem1Term : ℝ :=
  theorem1Bound S.couplingNorm S.eps (S.OmegaMax : ℝ) (S.OmegaMin : ℝ) (S.OmegaE : ℝ)

/-- The extra kinematic term `2 d_S/√Ω_min` of Eq. (5). -/
def kinematicExtra : ℝ := 2 * (S.dS : ℝ) / Real.sqrt (S.OmegaMin : ℝ)

/-- The extra dynamic term `d_S/(2√Ω_min)` of Eq. (6). -/
def dynamicExtra : ℝ := (S.dS : ℝ) / (2 * Real.sqrt (S.OmegaMin : ℝ))

/-- The full threshold of Eq. (5):
`2d_S/√Ω_min + ‖V‖∞/ε + (ΔΩ+Ω_ε)/(2Ω_max) + ε'`. -/
def kinematicThreshold : ℝ := S.theorem1Term + S.kinematicExtra + S.eps'

/-- The right-hand side of Eq. (6):
`d_S/(2√Ω_min) + ‖V‖∞/ε + (ΔΩ+Ω_ε)/(2Ω_max)`. -/
def dynamicBound : ℝ := S.theorem1Term + S.dynamicExtra

end Settings

/-- **Arithmetic identity behind Corollary 1.** The Eq. (5) threshold is the
Eq. (6) bound plus `3d_S/(2√Ω_min)` plus the slack `ε'`. This is the exact
difference between the two displayed right-hand sides on p. 3. -/
theorem kinematicThreshold_eq_dynamicBound_add (S : Settings) :
    S.kinematicThreshold =
      S.dynamicBound + 3 * (S.dS : ℝ) / (2 * Real.sqrt (S.OmegaMin : ℝ)) + S.eps' := by
  unfold Settings.kinematicThreshold Settings.dynamicBound Settings.kinematicExtra
    Settings.dynamicExtra
  ring

/-- **`Ω_min > 0` makes `√Ω_min` positive** (used for the sign of the extra
correction terms). -/
theorem sqrt_OmegaMin_pos (S : Settings) (hΩ : 0 < S.OmegaMin) :
    0 < Real.sqrt (S.OmegaMin : ℝ) := by
  exact Real.sqrt_pos.mpr (by exact_mod_cast hΩ)

/-- The dynamic correction `d_S/(2√Ω_min)` is nonnegative. -/
theorem dynamicExtra_nonneg (S : Settings) (_hΩ : 0 < S.OmegaMin) :
    0 ≤ S.dynamicExtra := by
  unfold Settings.dynamicExtra
  exact div_nonneg (by positivity) (by positivity)

/-- The kinematic correction `2d_S/√Ω_min` is nonnegative. -/
theorem kinematicExtra_nonneg (S : Settings) (_hΩ : 0 < S.OmegaMin) :
    0 ≤ S.kinematicExtra := by
  unfold Settings.kinematicExtra
  exact div_nonneg (by positivity) (by positivity)

/-- The Theorem-1 term is nonnegative under the paper's numerical hypotheses. -/
theorem theorem1Term_nonneg (S : Settings) (hV : 0 ≤ S.couplingNorm)
    (heps : 0 < S.eps) (hΩmax : 0 < (S.OmegaMax : ℝ))
    (hΩE : 0 ≤ (S.OmegaE : ℝ)) (hminmax : (S.OmegaMin : ℝ) ≤ (S.OmegaMax : ℝ)) :
    0 ≤ S.theorem1Term := by
  unfold Settings.theorem1Term
  exact theorem1Bound_nonneg hV heps hΩmax hΩE hminmax

/-- **The dynamic bound of Eq. (6) is nonnegative** under the paper's
hypotheses. -/
theorem dynamicBound_nonneg (S : Settings) (hV : 0 ≤ S.couplingNorm)
    (heps : 0 < S.eps) (hΩmax : 0 < (S.OmegaMax : ℝ))
    (hΩE : 0 ≤ (S.OmegaE : ℝ)) (hminmax : (S.OmegaMin : ℝ) ≤ (S.OmegaMax : ℝ))
    (hΩ : 0 < S.OmegaMin) :
    0 ≤ S.dynamicBound := by
  unfold Settings.dynamicBound
  exact add_nonneg (theorem1Term_nonneg S hV heps hΩmax hΩE hminmax)
    (dynamicExtra_nonneg S hΩ)

/-- **The kinematic threshold dominates the dynamic bound.** For every
`ε' ≥ 0` the right-hand side of Eq. (5) is at least that of Eq. (6); this is
why (5) is the stronger, probabilistic statement of the two. -/
theorem dynamicBound_le_kinematicThreshold (S : Settings) (hΩ : 0 < S.OmegaMin)
    (heps' : 0 ≤ S.eps') :
    S.dynamicBound ≤ S.kinematicThreshold := by
  have hsqrt := sqrt_OmegaMin_pos S hΩ
  have hnonneg : 0 ≤ 3 * (S.dS : ℝ) / (2 * Real.sqrt (S.OmegaMin : ℝ)) := by
    positivity
  rw [kinematicThreshold_eq_dynamicBound_add]
  linarith

/-- Probabilistic data of the kinematic half of Corollary 1: the (normalized)
Haar measure of the set of pure states of the microcanonical subspace that
violate Eq. (5). `badProbability` is a probability, so `0 ≤ badProbability ≤ 1`;
these fields are the definition of being a probability, not extra physical
assumptions. -/
structure KinematicOutcome (S : Settings) where
  /-- Uniform (Haar) measure of `{ψ : 𝒟(ψ^S, ω_Π^{S(0)}) ≥ threshold}`,
  normalized to a probability. -/
  badProbability : ℝ
  /-- Probabilities are nonnegative. -/
  badProbability_nonneg : 0 ≤ badProbability
  /-- Probabilities are at most one. -/
  badProbability_le_one : badProbability ≤ 1

/-- Time-averaged data of the dynamic half of Corollary 1: the averaged
subsystem distance `𝒟̄(ψ^S_{u,t}, ω_Π^{S(0)})`, and the Hamiltonian's
nondegenerate-gap hypothesis of Ref. [5], carried as a proposition. -/
structure DynamicOutcome (S : Settings) where
  /-- The time-averaged distance appearing on the left of Eq. (6). -/
  timeAveragedDistance : ℝ
  /-- The nondegenerate-energy-gap hypothesis of Ref. [5]. -/
  nondegenerateGaps : Prop




/-- A true gap proposition does not restrict the free averaged-distance field. -/
theorem freeDynamic_refutes (S : Settings) :
    ∃ D : DynamicOutcome S, D.nondegenerateGaps ∧
      ¬ D.timeAveragedDistance ≤ S.dynamicBound := by
  refine ⟨⟨S.dynamicBound + 1, True⟩, trivial, ?_⟩
  dsimp
  linarith

/-- A valid probability can violate the unconstrained exponential assertion. -/
theorem freeKinematic_refutes (S : Settings) (hΩ : 0 < S.OmegaMin)
    (heps : 0 < S.eps') :
    ∃ K : KinematicOutcome S,
      ¬ K.badProbability ≤ Real.exp (-(S.OmegaMin : ℝ) * S.eps' ^ 2) := by
  refine ⟨⟨1, by norm_num, by norm_num⟩, ?_⟩
  have ho : (0 : ℝ) < S.OmegaMin := by exact_mod_cast hΩ
  have hn : -(S.OmegaMin : ℝ) * S.eps' ^ 2 < 0 := by
    have := sq_pos_of_pos heps
    nlinarith
  have hb : Real.exp (-(S.OmegaMin : ℝ) * S.eps' ^ 2) < 1 := Real.exp_lt_one_iff.2 hn
  dsimp
  linarith

end Qatlib.Papers.Thermalize11.MainResults.Corollary1
