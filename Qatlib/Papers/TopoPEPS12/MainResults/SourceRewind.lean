/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TopoPEPS12.MainResults.SourceTheorem4
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-!
# The PEPS rewinding repetition count

Choose the least integer rounding up the repetition budget after Eq. (11)
of arXiv:1211.4050v1 and feed that same number to the success-probability
and phase-estimation cost bounds.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TopoPEPS12.MainResults

/-- The source's least natural repetition count, rounded upward. -/
noncomputable def rewindCount (N : ℕ) (κ ε : ℝ) : ℕ :=
  ⌈(N : ℝ) * κ ^ 2 / (2 * ε)⌉₊

/-- When the real budget is at least one, the natural witness satisfies both bounds used
in the source's success and runtime calculation. -/
theorem rewindCount_bounds (N : ℕ) (κ ε : ℝ) (hε : 0 < ε)
    (hx : 1 ≤ (N : ℝ) * κ ^ 2 / (2 * ε)) :
    1 ≤ rewindCount N κ ε ∧ (N : ℝ) * κ ^ 2 / (2 * ε) ≤ (rewindCount N κ ε : ℝ) ∧
      (rewindCount N κ ε : ℝ) ≤ (N : ℝ) * κ ^ 2 / ε := by
  unfold rewindCount
  let x := (N : ℝ) * κ ^ 2 / (2 * ε)
  change 1 ≤ ⌈x⌉₊ ∧ x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) ≤ (N : ℝ) * κ ^ 2 / ε
  have hlo : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hpos : (1 : ℝ) ≤ (⌈x⌉₊ : ℝ) := hx.trans hlo
  have hscale : 2 * x = (N : ℝ) * κ ^ 2 / ε := by
    dsimp [x]
    field_simp [hε.ne']
  refine ⟨by exact_mod_cast hpos, hlo, ?_⟩
  rw [← hscale]
  linarith [Nat.ceil_lt_add_one (zero_le_one.trans hx)]

/-- The explicit source witness simultaneously meets the probability and runtime bounds
when the assumed per-step failure bound holds at that witness. -/
theorem theorem4_at_rewindCount
    (N : ℕ) (p κ dmin Δ ε d : ℝ) (hN : 1 ≤ N)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : p ≤ 1 / (2 * (rewindCount N κ ε : ℝ) * dmin))
    (hκ : 1 ≤ κ) (hdmin : 0 < dmin) (hκ₂ : (κ ^ 2)⁻¹ ≤ dmin)
    (hΔ : 0 < Δ) (hε : 0 < ε) (hx : 1 ≤ (N : ℝ) * κ ^ 2 / (2 * ε)) :
    1 - ε ≤ (1 - p) ^ N ∧
      (N : ℝ) * (rewindCount N κ ε : ℝ) * ((N : ℝ) ^ 2 / Δ) ≤
        (N : ℝ) ^ 4 * κ ^ 2 / (Δ * ε) ∧
      Qatlib.Papers.TopoPEPS12.MainResults.classicalProcessingCost N d = (N : ℝ) * d ^ 6 := by
  obtain ⟨hm, hlo, hhi⟩ := rewindCount_bounds N κ ε hε hx
  exact Qatlib.Papers.TopoPEPS12.MainResults.theorem4_runtime N (rewindCount N κ ε)
    p κ dmin Δ ε d hN hm hp0 hp1 hp hκ hdmin hκ₂ hΔ hε hlo hhi

end Qatlib.Papers.TopoPEPS12.MainResults
