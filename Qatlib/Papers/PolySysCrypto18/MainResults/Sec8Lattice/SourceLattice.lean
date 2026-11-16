/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PolySysCrypto18.MainResults.SourceModel
public import Mathlib.Tactic

@[expose] public section


/-! Closed source mathematics; paper algorithm claims retain their separate obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.PolySysCrypto18.MainResults.Sec8Lattice
open Qatlib.Papers.PolySysCrypto18.MainResults

/-- **Lemma 8.1 (p.24), numerical core.**  If every coordinate of `v ∈ R^m` has
`|v_i| ≤ c` (in particular `c = ‖B‖∞` for a lattice vector bounded by the basis
height), then `‖v‖₂ ≤ √m · c`.

Paper proof: `‖v‖₂² = Σ v_i² ≤ Σ c² = m·c²`, so `‖v‖₂ ≤ √m·c`. -/
theorem lemma_8_1 {m : ℕ} (v : Fin m → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, |v i| ≤ c) : l2Norm v ≤ Real.sqrt (m : ℝ) * c := by
  unfold l2Norm
  have hsq : sqNorm v ≤ (m : ℝ) * c ^ 2 := by
    unfold sqNorm
    have h1 : ∀ i, (v i) ^ 2 ≤ c ^ 2 := by
      intro i
      have := h i
      calc (v i) ^ 2 = |v i| ^ 2 := (sq_abs (v i)).symm
        _ ≤ c ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    calc ∑ i : Fin m, (v i) ^ 2 ≤ ∑ i : Fin m, c ^ 2 := Finset.sum_le_sum (fun i _ => h1 i)
      _ = (m : ℝ) * c ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb : 0 ≤ Real.sqrt (m : ℝ) * c := by positivity
  calc Real.sqrt (sqNorm v) ≤ Real.sqrt ((Real.sqrt (m : ℝ) * c) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [mul_pow, Real.sq_sqrt (by positivity)]; exact hsq)
    _ = Real.sqrt (m : ℝ) * c := Real.sqrt_sq hb

end Qatlib.Papers.PolySysCrypto18.MainResults.Sec8Lattice
