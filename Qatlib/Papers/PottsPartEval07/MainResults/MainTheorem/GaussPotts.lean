/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.GaussReadout
public import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem.PottsReduction

@[expose] public section

/-!
# Exact Potts values from actual Gauss-query observation traces

This theorem composes the constructed Gauss unitaries, counted QPE, observed
label decoder and graph/code identity. Every sampled phase comes from the
actual finite-field Gauss sum and every probability from actual circuit
execution. The algebraic ICCC/McEliece certificates remain explicit inputs.
This reduction does not discharge the full paper's bit-operation runtime goal.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators
open Qatlib.Papers.PottsPartEval07.ExactRecovery

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {q : ℕ} [NeZero q] {V E : Type*}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Exact-output probability computed directly from actual Gauss-QPE executions. -/
def actualExactMass {classes terms : ℕ} (batch : GaussBatch F terms)
    (ends : E → V × V) (codeSize classSize M spacing : ℕ) (hM : 0 < M)
    (base scale : ℝ) (coefficient : Fin classes → Fin terms → ℂ) (y : ℝ) : ℝ :=
  ∑ record : Fin terms → Fin M,
    if recordedPotts (q := q) ends codeSize classSize M spacing base scale coefficient record y =
      (Qatlib.Papers.PottsPartEval07.PottsBridge.pottsZ q ends y : ℂ)
    then ∏ a, gaussMarginal M hM (batch.character a) batch.additive batch.frequency (record a)
    else 0

omit [DecidableEq E] in
/-- The actual observation probability equals the probability used by the certified decoder. -/
theorem actualExactMass_eq {classes terms : ℕ} (batch : GaussBatch F terms)
    (ends : E → V × V) (codeSize classSize M spacing : ℕ) (hM : 0 < M)
    (base scale : ℝ) (coefficient : Fin classes → Fin terms → ℂ) (y : ℝ) :
    actualExactMass (q := q) batch ends codeSize classSize M spacing hM base scale coefficient y =
      exactMass (q := q) ends codeSize classSize M spacing base scale coefficient (gaussPhases batch) y := by
  unfold actualExactMass exactMass
  apply Finset.sum_congr rfl
  intro record _
  rw [gauss_record_law batch M hM record]

/-- Subunit circular precision forces every nonempty batch to use positive actual queries. -/
theorem sampleSize_gt_one {terms : ℕ} (hd : 0 < terms) (radius : ℝ)
    (hr : 0 < radius) (hr1 : radius < 1) : 1 < sampleSize terms radius := by
  have hdR : (1 : ℝ) ≤ terms := by exact_mod_cast hd
  have hc := Nat.le_ceil (((2 : ℝ) * terms + 1) / radius)
  have hx : 1 < ((2 : ℝ) * terms + 1) / radius := by
    apply (lt_div_iff₀ hr).mpr
    linarith
  have hm : (1 : ℝ) < sampleSize terms radius := lt_of_lt_of_le hx hc
  exact_mod_cast hm

/-- The actual Gauss-query algorithm has positive query cost and derives exact graph output
with probability at least three quarters under certified code/phase identities. -/
theorem gauss_potts_reduction {classes terms classSize : ℕ} (batch : GaussBatch F terms)
    (hd : 0 < terms) (ends : E → V × V)
    (C : Submodule (ZMod q) (E → ZMod q)) (partition : WeightClasses C classes classSize)
    (hdual : dualCode C = graphCode ends) (k : ℕ) (hcard : Fintype.card C = q ^ k)
    (spacing : ℕ) (hspacing : 0 < spacing) (base scale : ℝ) (hs : 0 ≤ scale)
    (coefficient : Fin classes → Fin terms → ℂ) (hc : ∀ i a, ‖coefficient i a‖ ≤ 1)
    (hformula : ∀ i, turnWeight base scale (coefficient i) (gaussPhases batch) =
      hammingWeight (partition.representative i).val)
    (hdiv : ∀ i, spacing ∣ hammingWeight (partition.representative i).val)
    (radius : ℝ) (hr : 0 < radius) (hr1 : radius < 1)
    (hp : scale * (terms * (2 * Real.pi * radius)) < spacing / 2)
    (y : ℝ) (hy : y ≠ 0) :
    ∃ hM : 0 < sampleSize terms radius,
      0 < batchQueries terms (sampleSize terms radius) ∧
      3 / 4 ≤ actualExactMass (q := q) batch ends (q ^ k) classSize
        (sampleSize terms radius) spacing hM base scale coefficient y ∧
      (batchQueries terms (sampleSize terms radius) : ℝ) ≤ 3 * (terms : ℝ) ^ 2 / radius := by
  have hM1 := sampleSize_gt_one hd radius hr hr1
  have hM : 0 < sampleSize terms radius := by omega
  refine ⟨hM, batchQueries_pos hd hM1, ?_⟩
  rw [actualExactMass_eq]
  exact query_reduction hd ends C partition hdual k hcard spacing hspacing base scale hs
    coefficient hc (gaussPhases batch) hformula hdiv radius hr hp y hy

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
