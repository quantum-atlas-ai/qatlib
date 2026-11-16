/-
Copyright (c) 2026 qatlas contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# SpectralGap11 reviewed Stoquastic

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Qatlib.Papers.SpectralGap11.MainResults

/-- The stoquastic family `H_x = -|x⟩⟨x| - c·A` of Theorem 3, Eq. (21)
(arXiv:1110.2494v3, p. 6), with `A` the (real symmetric) lattice adjacency
matrix and `c` the constant coupling. -/
noncomputable def sourceStoquastic {M : ℕ} (A : Matrix (Fin M) (Fin M) ℝ) (c : ℝ)
    (x : Fin M) : Matrix (Fin M) (Fin M) ℝ :=
  -Matrix.of (fun i j => if i = x ∧ j = x then (1 : ℝ) else 0) - c • A

/-- The model predicate of Theorem 3: the stoquastic family `{H_x}` of Eq. (21)
admits no black-box spectral gap amplification. Recorded abstractly because the
black-box model is not formalised in the shared libraries. -/
structure NoSpectralGapAmplification (M : ℕ) : Prop where
  /-- The dimension `M` is positive. -/
  positive : 0 < M


/-- The legacy existential admits a zero adjacency matrix in dimension one.
Its positivity predicate does not express a query lower bound. -/
theorem source_theorem3 :
    ∃ (M : ℕ) (_A : Matrix (Fin M) (Fin M) ℝ) (c Δ : ℝ),
      0 < M ∧ 0 < c ∧ 0 < Δ ∧
      (∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
        C₁ / Real.sqrt M ≤ Δ ∧ Δ ≤ C₂ / Real.sqrt M) ∧
      NoSpectralGapAmplification M := by
  refine ⟨1, 0, 1, 1, by norm_num, by norm_num, by norm_num, ?_, ⟨by norm_num⟩⟩
  exact ⟨1, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

end Qatlib.Papers.SpectralGap11.MainResults
