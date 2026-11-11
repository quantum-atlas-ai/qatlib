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
# RmSearch.NewtonRegion — Proposition 2: Newton region and local quadratic convergence

Fixed source: arXiv:2603.26039v3, "Achieving double-logarithmic precision dependence in
optimization-based quantum unstructured search", Proposition 2, Eqs. (B12)/(B13), p. 17–19.

The paper defines the constants
`C_N := 64 L_Rie²`, `r_N := 1/(128 L_Rie²) = 1/(2 C_N)`
and proves that once the success-probability error `e_k = 1 - q_k` enters the Newton region
`e_k ≤ r_N`, the Armijo line search accepts the full Newton step `t_k = 1`, and
`e_{k+1} ≤ C_N e_k² ≤ e_k/2` (Eq. (B13)); the region is invariant, giving local quadratic
convergence.

This file formalizes the scalar core: the quadratic-step estimate `C_N e² ≤ e/2` inside the
region, and the induction that keeps the iterate in the region with the halving bound.  The
geometric input (Lemma 6's residual bound implies `e_{k+1} ≤ C_N e_k²` and `t_k = 1`) enters
as the hypothesis `hNewton`, matching Eq. (B13).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSearchPrec26.RmSearch.NewtonRegion

/-- The constant `C_N = 64 L_Rie²` of Eq. (B12). -/
def CN (L : ℝ) : ℝ := 64 * L ^ 2

/-- The Newton-region radius `r_N = 1/(128 L_Rie²) = 1/(2 C_N)` of Eq. (B12). -/
def rN (L : ℝ) : ℝ := 1 / (2 * CN L)

/-- Eq. (B12): `r_N = 1/(2 C_N)`, i.e. the Newton-region threshold is the reciprocal of
twice the quadratic-convergence constant. -/
theorem rN_eq_inv_two_CN (L : ℝ) : rN L = 1 / (2 * CN L) := rfl

/-- **Proposition 2, quadratic decay** (arXiv:2603.26039v3, Eq. (B13), p. 17–19).  Inside the
Newton region `e ≤ r_N = 1/(2C_N)` with `C_N = 64 L_Rie²`, the quadratic step satisfies
`C_N e² ≤ e/2`. -/
theorem newton_quadratic_decay {L e : ℝ} (hL : 0 < L) (he : 0 ≤ e) (hregion : e ≤ rN L) :
    CN L * e ^ 2 ≤ e / 2 := by
  have hC : 0 < CN L := by unfold CN; positivity
  have hCe : CN L * e ≤ CN L * rN L := mul_le_mul_of_nonneg_left hregion hC.le
  have hr : CN L * rN L = 1 / 2 := by
    unfold rN
    field_simp
  have hkey : CN L * e ^ 2 ≤ e * (CN L * rN L) := by
    have h := mul_le_mul_of_nonneg_left hCe he
    nlinarith [h]
  rw [hr] at hkey
  nlinarith [hkey]

/-- **Proposition 2, local quadratic convergence** (arXiv:2603.26039v3, Proposition 2,
p. 17–19).  Let `e_k = 1 - q_k` be the success-probability errors of Algorithm 2 with the
5-factor retraction, and suppose that from some iterate `k₀` on, whenever `e_k ≤ r_N` the
Armijo line search accepts the full step and `e_{k+1} ≤ C_N e_k²` (Eq. (B13), obtained in the
paper from Lemma 6 and Eq. (B15)–(B17)).  If `e_{k₀} ≤ r_N`, then for every `j`,
`e_{k₀+j} ≤ e_{k₀}/2^j` and the iterate stays in the Newton region `e_{k₀+j} ≤ r_N`. -/
theorem proposition2_local_quadratic_convergence
    (L : ℝ) (hL : 0 < L) (e : ℕ → ℝ) (k0 : ℕ)
    (he0 : ∀ k, 0 ≤ e k)
    (hstart : e k0 ≤ rN L)
    (hNewton : ∀ k, e k ≤ rN L → e (k + 1) ≤ CN L * (e k) ^ 2) :
    (∀ j, e (k0 + j) ≤ e k0 / 2 ^ j) ∧ (∀ j, e (k0 + j) ≤ rN L) := by
  have hC : 0 < CN L := by unfold CN; positivity
  have hrN : 0 < rN L := by unfold rN; positivity
  have hmain : ∀ j, e (k0 + j) ≤ e k0 / 2 ^ j ∧ e (k0 + j) ≤ rN L := by
    intro j
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      have hk : e (k0 + j) ≤ rN L := ih.2
      have hstep : e (k0 + j + 1) ≤ CN L * (e (k0 + j)) ^ 2 := hNewton (k0 + j) hk
      have hdec : CN L * (e (k0 + j)) ^ 2 ≤ e (k0 + j) / 2 :=
        newton_quadratic_decay hL (he0 _) hk
      have hhalf : e (k0 + j + 1) ≤ e (k0 + j) / 2 := le_trans hstep hdec
      have hpow : e (k0 + j + 1) ≤ e k0 / 2 ^ (j + 1) := by
        have hih : e (k0 + j) ≤ e k0 / 2 ^ j := ih.1
        have h2 : e (k0 + j) / 2 ≤ (e k0 / 2 ^ j) / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hih
        have heq : (e k0 / 2 ^ j) / 2 = e k0 / 2 ^ (j + 1) := by
          rw [pow_succ]
          field_simp
        linarith [hhalf, h2, heq.le, heq.ge]
      have hr : e (k0 + j + 1) ≤ rN L := by
        have h2 : e (k0 + j) / 2 ≤ rN L / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr hk
        have h3 : rN L / 2 ≤ rN L := by linarith [hrN]
        linarith [hhalf, h2, h3]
      refine ⟨?_, ?_⟩
      · -- reindex `k0 + (j+1) = k0 + j + 1`
        rw [← Nat.add_assoc]
        exact hpow
      · rw [← Nat.add_assoc]
        exact hr
  exact ⟨fun j => (hmain j).1, fun j => (hmain j).2⟩

end Qatlib.Papers.QSearchPrec26.RmSearch.NewtonRegion
