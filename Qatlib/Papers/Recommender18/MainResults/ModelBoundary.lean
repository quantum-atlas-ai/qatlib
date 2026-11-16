/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Recommender18.MainResults.SourceDefinitions
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! Counterexamples to missing rank and threshold conditions in the legacy contracts. -/

set_option autoImplicit false

namespace Qatlib.Papers.Recommender18.MainResults

open scoped BigOperators
open Qatlib.Papers.Recommender18.MainResults

/-- A zero singular value makes the original non-strict zero-threshold filter inconsistent. -/
theorem zero_filter {m n : ℕ} {A : Fin m → Fin n → ℝ} (S : IsSVD A)
    (t : Fin S.N) (ht : S.σ t = 0) (η : ℝ) :
    ¬ ∃ c : Fin S.N → ℝ, IsSpectralFilter S 0 η c := by
  rintro ⟨c, hc⟩
  have h1 := hc.1 t (by simp [ht])
  have h0 := hc.2.1 t (by simp [ht])
  linarith

/-- The zero-dimensional near-isometry input satisfies the old Gram-error assumptions. -/
theorem empty_gram :
    (∀ t s : Fin 1, t ≠ s →
      |∑ _i : Fin 0, (0 : ℝ) * 0| ≤ (1 : ℝ) / Real.sqrt 1) ∧
    (∀ _t : Fin 1, |1 - ∑ _i : Fin 0, (0 : ℝ) ^ 2| ≤ (1 : ℝ) / Real.sqrt 1) := by
  constructor <;> intros <;> norm_num

/-- A zero-dimensional space has no unit column, refuting the old near-isometry conclusion. -/
theorem empty_no_frame :
    ¬ ∃ L : Fin 0 → Fin 1 → ℝ,
      ∀ t s : Fin 1, (∑ i, L i t * L i s) = if t = s then 1 else 0 := by
  rintro ⟨L, hL⟩
  have h := hL 0 0
  norm_num at h

end Qatlib.Papers.Recommender18.MainResults
