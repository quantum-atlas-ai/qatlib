/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDirectProd11.MainResults.Model.PaperModel

set_option backward.isDefEq.respectTransparency false

/-!
# Classical moment inequalities of arXiv:1104.4468, Section 3.3

Fixed source: arXiv:1104.4468 (2011), Lemma 3.11 (p.11) and Claim 3.12 (p.11).
These are purely classical statements about finite probability distributions; the
proofs below follow the paper's proofs (Cauchy–Schwarz for Lemma 3.11, and the
pointwise dual-feasible bound for Claim 3.12) and are complete.

The paper states Lemma 3.11 for a discrete variable `A` with values in `R₀⁺`, so
`E_p(A⁻¹)` is `+∞` when a zero atom carries `p`-mass; the Lean statement encodes
the substantive (finite) branch by requiring `p i ≠ 0 → 0 < A i`.  On the
degenerate branch the paper's right-hand side is `0` and the claim is vacuous.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QDirectProd11.MainResults.Classical

open scoped BigOperators

/-- **Lemma 3.11** (p.11).  For distributions `p,q` of a nonnegative random
variable `A`, if the classical fidelity `F(p,q) = ∑ᵢ √(pᵢ qᵢ)` is at least `√δ`,
then `E_q(A) ≥ δ · [E_p(A⁻¹)]⁻¹`.

Proof (paper, p.11): Cauchy–Schwarz in the form
`(∑ᵢ √(pᵢ qᵢ))² ≤ (∑ᵢ qᵢ Aᵢ)(∑ᵢ pᵢ/Aᵢ)`, together with `δ ≤ (∑ᵢ √(pᵢ qᵢ))²`. -/
theorem lemma_3_11 {ι : Type} [Fintype ι]
    (p q A : ι → ℝ) (δ : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (_hq0 : ∀ i, 0 ≤ q i)
    (_hp1 : ∑ i, p i = 1) (_hq1 : ∑ i, q i = 1)
    (hA0 : ∀ i, 0 ≤ A i) (hAp : ∀ i, p i ≠ 0 → 0 < A i)
    (hδ0 : 0 ≤ δ)
    (hF : Real.sqrt δ ≤ ∑ i, Real.sqrt (p i * q i)) :
    δ * (∑ i, p i * (A i)⁻¹)⁻¹ ≤ ∑ i, q i * A i := by
  classical
  set S : ℝ := ∑ i, Real.sqrt (p i * q i) with hS
  set Y : ℝ := ∑ i, p i * (A i)⁻¹ with hY
  set X : ℝ := ∑ i, q i * A i with hX
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => mul_nonneg (_hq0 i) (hA0 i))
  have hY0 : 0 ≤ Y :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp0 i) (inv_nonneg.mpr (hA0 i)))
  have hδS : δ ≤ S ^ 2 := by
    calc δ = (Real.sqrt δ) ^ 2 := (Real.sq_sqrt hδ0).symm
      _ ≤ S ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hF 2
  have hcs : S ^ 2 ≤ X * Y := by
    rw [hS, hX, hY]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (f := fun i => q i * A i) (g := fun i => p i * (A i)⁻¹)
      (r := fun i => Real.sqrt (p i * q i)) ?_ ?_ ?_
    · intro i _; exact mul_nonneg (_hq0 i) (hA0 i)
    · intro i _; exact mul_nonneg (hp0 i) (inv_nonneg.mpr (hA0 i))
    · intro i _
      rw [Real.sq_sqrt (mul_nonneg (hp0 i) (_hq0 i))]
      by_cases hpi : p i = 0
      · simp [hpi]
      · have hAi : 0 < A i := hAp i hpi
        have : (q i * A i) * (p i * (A i)⁻¹) = p i * q i := by
          field_simp [hAi.ne']
        exact this.ge
  have hδXY : δ ≤ X * Y := le_trans hδS hcs
  change δ * Y⁻¹ ≤ X
  by_cases hYzero : Y = 0
  · rw [hYzero, inv_zero, mul_zero]
    exact hX0
  · have hYpos : 0 < Y := lt_of_le_of_ne hY0 (Ne.symm hYzero)
    calc δ * Y⁻¹ ≤ (X * Y) * Y⁻¹ :=
          mul_le_mul_of_nonneg_right hδXY (inv_nonneg.mpr hYpos.le)
      _ = X := by rw [mul_assoc, mul_inv_cancel₀ hYzero, mul_one]

/-- **Claim 3.12** (p.11).  If `A` takes values in `[a₀,a₁]` with `0 < a₀ ≤ a₁`
and `E_p(A) = ā`, then `E_p(A⁻¹) ≤ (a₀+a₁-ā)/(a₀a₁)`.

Proof (paper, p.11): the pointwise dual-feasible bound
`1/a ≤ (a₀+a₁-a)/(a₀a₁)` for `a ∈ [a₀,a₁]`, obtained from
`0 ≤ (a-a₀)(a₁-a)`, summed against `p`. -/
theorem claim_3_12 {ι : Type} [Fintype ι]
    (p A : ι → ℝ) (a0 a1 ā : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (_hp1 : ∑ i, p i = 1)
    (ha0 : 0 < a0) (h01 : a0 ≤ a1)
    (hA : ∀ i, a0 ≤ A i ∧ A i ≤ a1)
    (hmean : ∑ i, p i * A i = ā) :
    ∑ i, p i * (A i)⁻¹ ≤ (a0 + a1 - ā) / (a0 * a1) := by
  classical
  have hden : 0 < a0 * a1 := mul_pos ha0 (lt_of_lt_of_le ha0 h01)
  have hApos : ∀ i, 0 < A i := fun i => lt_of_lt_of_le ha0 (hA i).1
  have hpoint : ∀ i, (A i)⁻¹ ≤ (a0 + a1 - A i) / (a0 * a1) := by
    intro i
    have h1 : (1 : ℝ) / A i ≤ (a0 + a1 - A i) / (a0 * a1) := by
      rw [div_le_div_iff₀ (hApos i) hden]
      have hprod : 0 ≤ (A i - a0) * (a1 - A i) :=
        mul_nonneg (by linarith [(hA i).1]) (by linarith [(hA i).2])
      nlinarith [hprod]
    simpa [one_div] using h1
  have hsum : ∑ i, p i * (a0 + a1 - A i) = a0 + a1 - ā := by
    calc ∑ i, p i * (a0 + a1 - A i) = (a0 + a1) * ∑ i, p i - ∑ i, p i * A i := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = a0 + a1 - ā := by rw [_hp1, hmean]; ring
  calc ∑ i, p i * (A i)⁻¹
      ≤ ∑ i, p i * ((a0 + a1 - A i) / (a0 * a1)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp0 i))
    _ = (∑ i, p i * (a0 + a1 - A i)) / (a0 * a1) := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun i _ => by rw [div_eq_mul_inv]; ring)
    _ = (a0 + a1 - ā) / (a0 * a1) := by rw [hsum]

end Qatlib.Papers.QDirectProd11.MainResults.Classical
