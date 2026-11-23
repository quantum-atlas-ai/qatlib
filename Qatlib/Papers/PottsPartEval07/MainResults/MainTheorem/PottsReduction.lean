/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.GraphOutput
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.QueryReduction

@[expose] public section

/-!
# The phase-query reduction to exact graph partition values

The output is computed from observed phase labels, lattice rounding, and the
compressed enumerator. Its correctness is derived from the actual code's
McEliece weight identity and divisibility, rather than assumed as an output
field. The probability comes from independent counted QPE observations.

This conditional reduction leaves the construction of McEliece certificates
for every ICCC input and the finite-gate implementation of the Gauss-sum
primitive as separate obligations. It does not claim the full paper runtime.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.ExactRecovery
open Qatlib.Concepts.AmplitudeCore.PhaseEstimation

variable {q : ℕ} [NeZero q] {V E : Type*}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The actual weight list obtained from the recorded QPE labels. -/
def recordedWeights {classes terms : ℕ} (M spacing : ℕ) (base scale : ℝ)
    (coefficient : Fin classes → Fin terms → ℂ) (record : Fin terms → Fin M) :
    Fin classes → ℕ :=
  fun i => observedWeight spacing base scale (coefficient i)
    (fun a => (record a).val / (M : ℝ))

/-- The partition value computed from the actual label record. -/
def recordedPotts {classes terms : ℕ} (ends : E → V × V)
    (codeSize classSize M spacing : ℕ) (base scale : ℝ)
    (coefficient : Fin classes → Fin terms → ℂ) (record : Fin terms → Fin M)
    (y : ℝ) : ℂ :=
  compressedPotts (q := q) ends codeSize classSize
    (recordedWeights M spacing base scale coefficient record) y

/-- Correct phase observations imply the exact graph value after actual decoding. -/
theorem recordedPotts_correct {classes terms classSize : ℕ} (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (k : ℕ) (hcard : Fintype.card C = q ^ k)
    (M spacing : ℕ) (hspacing : 0 < spacing) (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin classes → Fin terms → ℂ) (hc : ∀ i a, ‖coefficient i a‖ ≤ 1)
    (phase : Fin terms → ℝ)
    (hformula : ∀ i, turnWeight base scale (coefficient i) phase =
      hammingWeight (partition.representative i).val)
    (hdiv : ∀ i, spacing ∣ hammingWeight (partition.representative i).val)
    (radius : ℝ) (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2)
    (record : Fin terms → Fin M)
    (hgood : ∀ a, bhmt11CircleDist ((record a).val / (M : ℝ)) (phase a) ≤ radius)
    (y : ℝ) (hy : y ≠ 0) :
    recordedPotts (q := q) ends (q ^ k) classSize M spacing base scale coefficient record y =
      (Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ q ends y : ℂ) := by
  unfold recordedPotts
  rw [← hcard]
  refine compressedPotts_recovered ends C partition hdual _ ?_ y hy
  intro i
  apply observedWeight_eq spacing hspacing base scale hs (coefficient i) (hc i) phase
    (fun a => (record a).val / (M : ℝ)) radius
    (fun a => by
      rw [bhmt_phase_estimation_theorem11_distance_symm]
      exact hgood a) hp _ (hdiv i) (hformula i)

/-- Sum the true observation masses of records that compute the exact partition value. -/
def exactMass {classes terms : ℕ} (ends : E → V × V)
    (codeSize classSize M spacing : ℕ) (base scale : ℝ)
    (coefficient : Fin classes → Fin terms → ℂ) (phase : Fin terms → ℝ) (y : ℝ) : ℝ :=
  ∑ record : Fin terms → Fin M,
    if recordedPotts (q := q) ends codeSize classSize M spacing base scale coefficient record y =
      (Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ q ends y : ℂ)
    then batchMass M phase record else 0

/-- The actual all-accurate observation event is contained in exact output success. -/
theorem exactMass_ge {classes terms classSize : ℕ} (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (k : ℕ) (hcard : Fintype.card C = q ^ k)
    (M spacing : ℕ) (hspacing : 0 < spacing) (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin classes → Fin terms → ℂ) (hc : ∀ i a, ‖coefficient i a‖ ≤ 1)
    (phase : Fin terms → ℝ)
    (hformula : ∀ i, turnWeight base scale (coefficient i) phase =
      hammingWeight (partition.representative i).val)
    (hdiv : ∀ i, spacing ∣ hammingWeight (partition.representative i).val)
    (radius : ℝ) (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2)
    (y : ℝ) (hy : y ≠ 0) :
    batchGoodMass M phase radius ≤
      exactMass (q := q) ends (q ^ k) classSize M spacing base scale coefficient phase y := by
  classical
  unfold batchGoodMass exactMass
  apply Finset.sum_le_sum
  intro record _
  by_cases hg : ∀ a, bhmt11CircleDist ((record a).val / (M : ℝ)) (phase a) ≤ radius
  · rw [ite_eq_left hg, ite_eq_left (recordedPotts_correct ends C partition hdual k hcard
      M spacing hspacing base scale hs coefficient hc phase hformula hdiv radius hp record hg y hy)]
  · rw [ite_eq_right hg]
    split_ifs
    · exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)
    · exact le_rfl

/-- The actual decoder succeeds with probability at least three quarters at the chosen query budget.
This is a certified-code Gauss-phase query reduction, not the original full runtime theorem. -/
theorem query_reduction {classes terms classSize : ℕ} (hd : 0 < terms) (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (k : ℕ) (hcard : Fintype.card C = q ^ k)
    (spacing : ℕ) (hspacing : 0 < spacing) (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin classes → Fin terms → ℂ) (hc : ∀ i a, ‖coefficient i a‖ ≤ 1)
    (phase : Fin terms → ℝ)
    (hformula : ∀ i, turnWeight base scale (coefficient i) phase =
      hammingWeight (partition.representative i).val)
    (hdiv : ∀ i, spacing ∣ hammingWeight (partition.representative i).val)
    (radius : ℝ) (hr : 0 < radius)
    (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2)
    (y : ℝ) (hy : y ≠ 0) :
    3 / 4 ≤ exactMass (q := q) ends (q ^ k) classSize (sampleSize terms radius) spacing
      base scale coefficient phase y ∧
      (batchQueries terms (sampleSize terms radius) : ℝ) ≤ 3 * (terms : ℝ) ^ 2 / radius := by
  exact ⟨(batch_three_quarters hd phase radius hr).trans
    (exactMass_ge ends C partition hdual k hcard (sampleSize terms radius) spacing hspacing
      base scale hs coefficient hc phase hformula hdiv radius hp y hy),
    batch_query_bound hd radius hr⟩

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
