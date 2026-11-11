/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux2

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 12 of `QLinearODE17`: the integrated source polynomial

Source: arXiv:1701.03684v2, Appendix A, printed Lemma 12 (`lem:taylor3`).
For `|z| ≤ 1` the integrated truncated exponential
`S_k(z) = ∑_{j=1}^{k} z^{j-1}/j!` approximates `(exp z - 1)/z`.

The printed proof reuses the integral remainder of Lemma 10 and divides by `z`;
its bound `|S_k(z) - (exp z - 1)/z| ≤ |z|^k/(k+1)!` needs
`|exp (e^{iφ} t)| ≤ 1`, i.e. the half-plane hypothesis `Re z ≤ 0` that the
printed statement omits. The printed statement is in fact false without it: for
`z = 1` and `k = 1` one has `S_1(1) = 1` while `exp 1 - 1 = 1.718…`, so the
defect exceeds `1/2!`. `QLinearODE17` only ever applies the lemma at
`z = h λ` with `Re λ ≤ 0`, where the missing hypothesis holds, so the
formalization below carries `Re z ≤ 0` explicitly and is otherwise the printed
statement.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Qatlib.Papers.QLinearODE17.TaylorAnalysis

/-- Printed Lemma 12: the integrated truncated exponential
`S_k(z) = ∑_{j=1}^{k} z^{j-1}/j!`. -/
noncomputable def taylorShiftPoly (k : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 k, z ^ (j - 1) / ((Nat.factorial j : ℕ) : ℂ)

/-- Multiplying the integrated polynomial by `z` removes the shift:
`z S_k(z) = T_k(z) - 1`. -/
theorem taylorShiftPoly_mul (k : ℕ) (z : ℂ) :
    z * taylorShiftPoly k z = taylorPoly k z - 1 := by
  have hrange : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : 0 ∉ Finset.Icc 1 k := by simp
  have hterm : ∀ j ∈ Finset.Icc 1 k,
      z * (z ^ (j - 1) / ((Nat.factorial j : ℕ) : ℂ)) =
        z ^ j / ((Nat.factorial j : ℕ) : ℂ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hp : z ^ j = z * z ^ (j - 1) := by
      rw [← pow_succ' z (j - 1), show j - 1 + 1 = j from by omega]
    rw [hp, mul_div_assoc]
  rw [taylorPoly, hrange, Finset.sum_insert h0, taylorShiftPoly, Finset.mul_sum,
    Finset.sum_congr rfl hterm]
  simp

/-- Printed Lemma 12 with the half-plane hypothesis that the printed proof uses:
for `z ≠ 0`, `|z| ≤ 1` and `Re z ≤ 0`,
`‖S_k(z) - (exp z - 1)/z‖ ≤ 1/(k+1)!`. -/
theorem taylorShiftPoly_defect {k : ℕ} {z : ℂ} (hz : z ≠ 0) (h1 : ‖z‖ ≤ 1)
    (hre : z.re ≤ 0) :
    ‖taylorShiftPoly k z - (Complex.exp z - 1) * z⁻¹‖ ≤
      1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
  have hid := taylorShiftPoly_mul k z
  have hzsplit : z * ((Complex.exp z - 1) * z⁻¹) = Complex.exp z - 1 := by
    calc z * ((Complex.exp z - 1) * z⁻¹)
        = (z * (Complex.exp z - 1)) * z⁻¹ := by rw [mul_assoc]
      _ = (z * z⁻¹) * (Complex.exp z - 1) := by rw [mul_right_comm]
      _ = Complex.exp z - 1 := by rw [mul_inv_cancel₀ hz, one_mul]
  have hmul : z * (taylorShiftPoly k z - (Complex.exp z - 1) * z⁻¹) =
      taylorPoly k z - Complex.exp z := by
    rw [mul_sub, hid, hzsplit]
    ring
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hF : (0 : ℝ) < ((Nat.factorial (k + 1) : ℕ) : ℝ) := by positivity
  have hnorm : ‖taylorShiftPoly k z - (Complex.exp z - 1) * z⁻¹‖ =
      ‖taylorPoly k z - Complex.exp z‖ / ‖z‖ := by
    rw [eq_div_iff hzpos.ne']
    rw [mul_comm, ← norm_mul, hmul]
  rw [hnorm, show ‖taylorPoly k z - Complex.exp z‖ = ‖Complex.exp z - taylorPoly k z‖
    from norm_sub_rev _ _]
  calc ‖Complex.exp z - taylorPoly k z‖ / ‖z‖
      ≤ (‖z‖ ^ (k + 1) / ((Nat.factorial (k + 1) : ℕ) : ℝ)) / ‖z‖ := by
        gcongr
        exact taylorPoly_defect_halfPlane k z hre
    _ = ‖z‖ ^ k / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
        rw [pow_succ, div_div, mul_div_mul_right _ _ hzpos.ne']
    _ ≤ 1 / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
        gcongr
        exact pow_le_one₀ (norm_nonneg z) h1

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
