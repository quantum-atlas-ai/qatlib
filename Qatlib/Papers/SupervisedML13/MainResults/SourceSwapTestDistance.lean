/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SupervisedML13.MainResults.SourceModel

@[expose] public section


/-! Preserved legacy scalar model and closed lemmas. Fixed source: arXiv:1307.0411v2.
The scalar overlap is not a system-vector projection; the fidelity expression is a
budget, not an operational fidelity. Counterexamples diagnose legacy contracts only. -/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SupervisedML13.MainResults

open Qatlib.Papers.SupervisedML13.MainResults

/-! ## Preserved legacy scalar coefficients -/

/-- The retained level-zero scalar coefficient `|u| / sqrt Z`. -/
def paperAncillaLevelZero {M N : ℕ} (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ) : ℝ :=
  vecNorm u / Real.sqrt (swapNormalizer u v)

/-- The retained legacy sample coefficient. The source joint-state projection
has additional branch factors; this isolated scalar is not its amplitude. -/
def paperAncillaLevelSample {M N : ℕ} (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ)
    (j : Fin M) : ℝ :=
  -(vecNorm (v j)) / Real.sqrt (swapNormalizer u v)

/-- The preserved legacy scalar overlap expression. It replaces vector branches
by their norms and uses the old relative coefficients. The fixed source's
normalized joint state retains vector inner products and a common factor of
`1 / sqrt 2`; this scalar expression is not that projection amplitude. -/
def paperSwapOverlap {M N : ℕ} (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ) : ℝ :=
  (1 / Real.sqrt (swapNormalizer u v)) *
    (vecNorm u / Real.sqrt 2 - (1 / Real.sqrt (M : ℝ)) * ∑ j, vecNorm (v j))

/-- The square of the legacy scalar overlap; no Born-law interpretation is claimed. -/
def paperSwapProbability {M N : ℕ} (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ) : ℝ :=
  paperSwapOverlap u v ^ 2

/-! ## Exact scalar algebra and contract refutation -/

/-- The exact algebraic closed form of the retained legacy scalar square.
This preserves the closed computation without treating it as a source protocol. -/
theorem paper_swap_probability_closed_form {M N : ℕ} (u : Fin N → ℝ)
    (v : Fin M → Fin N → ℝ) (hZ : 0 < swapNormalizer u v) :
    paperSwapProbability u v
      = (1 / swapNormalizer u v) *
          (vecNorm u / Real.sqrt 2 - (1 / Real.sqrt (M : ℝ)) * ∑ j, vecNorm (v j)) ^ 2 := by
  unfold paperSwapProbability paperSwapOverlap
  rw [mul_pow, div_pow, one_pow]
  have hsZ : (Real.sqrt (swapNormalizer u v)) ^ 2 = swapNormalizer u v :=
    Real.sq_sqrt hZ.le
  rw [hsZ]


/-- Equal one-dimensional vectors refute the legacy scalar-overlap distance identity.
The legacy overlap discards system-vector inner products; this diagnoses that model. -/
theorem scalarSwapRefuted :
    distanceToMeanSq (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) ≠
      swapNormalizer (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) *
      paperSwapProbability (fun _ : Fin 1 => (1 : ℝ))
        (fun _ : Fin 1 => fun _ : Fin 1 => (1 : ℝ)) := by
  norm_num [distanceToMeanSq, meanVector, normSq, swapNormalizer,
    paperSwapProbability, paperSwapOverlap, vecNorm]
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hne : 1 / Real.sqrt (2 : ℝ) - 1 ≠ 0 := by
    intro h
    have hdiv : 1 / Real.sqrt (2 : ℝ) = 1 := by linarith
    have he := (div_eq_iff (ne_of_gt hs)).mp hdiv
    nlinarith
  simpa only [one_div] using hne

/-- The original universally quantified scalar distance identity is false. -/
theorem legacySwapFalse :
    ¬ (∀ (M N : ℕ) (u : Fin N → ℝ) (v : Fin M → Fin N → ℝ), 0 < M →
      distanceToMeanSq u v = swapNormalizer u v * paperSwapProbability u v) := by
  intro h
  exact scalarSwapRefuted (h 1 1 (fun _ => 1) (fun _ _ => 1) (by decide))

end Qatlib.Papers.SupervisedML13.MainResults
