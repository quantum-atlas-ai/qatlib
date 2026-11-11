/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# RmSearch.GroverPlane.Radius — Lemma 9: lower bound for the accepted radius

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Lemma 9, Eq. (B20), p. 19–21.

Before entering the Newton region (`e_k > r_N`) the trial step is measured by the
Grover-plane radius `R := t γ_k ξ_k`.  In terms of `R` the Armijo condition becomes
`Q_U(R) ≥ q + c (R/ξ) ‖g‖²`, and with `Q_U(R) - q = A Φ_U(R)` (`A = q₀(1-q₀)q(1-q)`,
`Φ_U(0)=0`, `Φ_U'(0)=2`) it is equivalent to `Φ_U(R) ≥ 2cR`.

The paper proves that the normalized trial objective `Φ_U` belongs to a compactly
parametrized family, so there is `R* > 0` (with `R* ≤ 1/64`) independent of the iterate such
that `Φ_U(R) ≥ R ≥ 2cR` for every `0 ≤ R ≤ R*`.  Hence every radius not exceeding `R*` is
accepted, and since backtracking multiplies by `ρ`, the first accepted radius satisfies
`R_k ≥ ρ R*` (Eq. (B20)).

This file formalizes the second, combinatorial part: uniform Armijo acceptance on `[0,R*]`
forces the smallest accepted radius to be at least `ρ R*`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.GroverPlane.Radius

/-- **Lemma 9, accepted-radius bound** (arXiv:2603.26039v3, Eq. (B20), p. 19–21).  Let
`Φ k : ℝ → ℝ` be the normalized trial objective at iterate `k`, `R_k = ρ^{m_k}` the first
accepted trial radius (the smallest `m_k` for which `2c·ρ^{m_k} ≤ Φ k (ρ^{m_k})`, the Armijo
condition in radius variables).  Assume the uniform acceptance property
`2cR ≤ Φ k R` for all `0 ≤ R ≤ R*` (obtained in the paper from the compactness of
`(R,q,s) ↦ Φ(R;q,s)` and Taylor's formula).  Then, for every iterate,
`R_k ≥ ρ R*`.
-/
theorem lemma9_accepted_radius_lower_bound
    (c ρ Rstar : ℝ) (hc : 0 < c) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hRstar0 : 0 < Rstar) (hRstar1 : Rstar < 1)
    (Phi : ℕ → ℝ → ℝ) (m : ℕ → ℕ)
    (hPhi : ∀ k R, 0 ≤ R → R ≤ Rstar → 2 * c * R ≤ Phi k R)
    (hMin : ∀ k j, j < m k → ¬ (2 * c * ρ ^ j ≤ Phi k (ρ ^ j))) :
    ∀ k, ρ ^ (m k) ≥ ρ * Rstar := by
  intro k
  by_contra hcon
  push_neg at hcon
  rcases Nat.eq_zero_or_pos (m k) with h0 | hpos
  · -- `m_k = 0`: the radius is `1`, which already exceeds `ρ R*` since `R* < 1`.
    rw [h0] at hcon
    simp only [pow_zero] at hcon
    nlinarith [hcon, hRstar1, hρ1, hρ0, hRstar0]
  · -- `m_k ≥ 1`: the previous trial radius lies in `[0,R*]` and is therefore accepted.
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    have hlt : ρ ^ j < Rstar := by
      have hmk : ρ ^ (m k) = ρ * ρ ^ j := by
        rw [hj, pow_succ]
        ring
      have h1 : ρ * ρ ^ j < ρ * Rstar := by
        rw [hmk] at hcon
        exact hcon
      exact (mul_lt_mul_iff_of_pos_left hρ0).mp h1
    have hacc : 2 * c * ρ ^ j ≤ Phi k (ρ ^ j) :=
      hPhi k (ρ ^ j) (le_of_lt (pow_pos hρ0 j)) (le_of_lt hlt)
    have hmin : ¬ (2 * c * ρ ^ j ≤ Phi k (ρ ^ j)) :=
      hMin k j (by rw [hj]; exact Nat.lt_succ_self j)
    exact hmin hacc

end Qatlib.Papers.QSearchPrec26.RmSearch.GroverPlane.Radius
