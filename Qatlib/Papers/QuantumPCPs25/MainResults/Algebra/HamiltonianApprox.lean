/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.MixedState
public import Qatlib.Papers.QuantumPCPs25.MainResults.Algebra.PauliBasisExpansion

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Error bounds for learning weighted Hamiltonians (Lemma 20)

Source: Buhrman--Helsen--Weggemans, *Quantum PCPs: on Adaptivity, Multiple
Provers and Reductions to Local Hamiltonians*, arXiv:2403.04841v3 (Quantum 9,
1791 (2025)), Lemma 20, pp. 50--51 (Appendix B).

Statement: if `H = Σ_i p_i H_i` with `p_i ∈ [0,1]`, `Σ p_i = 1` and
`‖H_i‖ ≤ 1`, and `H̃ = Σ_i p̃_i H̃_i` is an estimate with `H̃_i` PSD,
`|p̃_i - p_i| ≤ ε₀` and `‖H_i - H̃_i‖ ≤ ε₁`, then the renormalised
`Ĥ = Σ_i p̂_i Ĥ_i` with `p̂_i = p̃_i/W̃`, `W̃ = Σ p̃_i` and
`Ĥ_i = H̃_i / max{‖H̃_i‖,1}` satisfies `‖H - Ĥ‖ ≤ ε` provided
`ε₀ ≤ ε/(8m²)`, `ε₁ ≤ ε/6`, and `ε ≤ 1`.

The formal premises include nonnegative exact weights. Without that condition,
arbitrarily large positive and negative weights amplify the term errors.
The small-error condition keeps the estimated total weight away from zero.
Positivity of the estimated terms is unnecessary for this norm estimate.
The condition `ε ≤ 1` is an added sufficient restriction of this mathematical
repair, not an explicit premise in the source's printed Lemma 20. The norm-clipping
formula below also resolves the source's denominator and tilde/hat notation; this
module does not claim literal equivalence to every printed expression or construct
the paper's Hamiltonian-learning algorithm.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumPCPs25.MainResults.Algebra

open Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Qatlib.Foundations.PureStateMath

/-- **Lemma 20** (arXiv:2403.04841v3, pp. 50--51).
With `H = Σ_i p_i H_i`, `p_i ∈ [0,1]`, `Σ_i p_i = 1`, `‖H_i‖ ≤ 1`, and an
estimate `H̃ = Σ_i p̃_i H̃_i` with `H̃_i` PSD, `|p̃_i - p_i| ≤ ε₀`,
`‖H_i - H̃_i‖ ≤ ε₁`, the renormalised Hamiltonian
`Ĥ = Σ_i (p̃_i/W̃) (H̃_i / max{‖H̃_i‖,1})`, `W̃ = Σ_i p̃_i`, satisfies
`‖H - Ĥ‖ ≤ ε` whenever the exact weights are nonnegative,
`ε₀ ≤ ε/(8m²)`, `ε₁ ≤ ε/6`, and `ε ≤ 1`. Positivity of the estimated
terms is not needed for the clipping estimate. -/
theorem lemma_20_hamiltonian_estimation_error {D m : ℕ} (W ε0 ε1 ε : ℝ)
    (H Ĥ : Operator D) (p ptilde : Fin m → ℝ)
    (Hterm HtildeTerm : Fin m → Operator D)
    (hm : 0 < m) (hW : W = ∑ i, ptilde i)
    (hH : H = ∑ i, p i • Hterm i)
    (hHhat : Ĥ = ∑ i, (ptilde i / W) •
      ((max (OperatorSpectralNorm (HtildeTerm i)) 1)⁻¹ • HtildeTerm i))
    (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1)
    (hpdiff : ∀ i, |ptilde i - p i| ≤ ε0)
    (hnorm : ∀ i, OperatorSpectralNorm (Hterm i) ≤ 1)
    (hhterm : ∀ i, OperatorSpectralNorm (HtildeTerm i - Hterm i) ≤ ε1)
    (hε0 : ε0 ≤ ε / (8 * (m : ℝ) ^ 2)) (hε1 : ε1 ≤ ε / 6)
    (hε : ε ≤ 1) :
    OperatorSpectralNorm (H - Ĥ) ≤ ε := by
  classical
  change ‖H - Ĥ‖ ≤ ε
  change ∀ i, ‖Hterm i‖ ≤ 1 at hnorm
  change ∀ i, ‖HtildeTerm i - Hterm i‖ ≤ ε1 at hhterm
  change Ĥ = ∑ i, (ptilde i / W) •
    ((max ‖HtildeTerm i‖ 1)⁻¹ • HtildeTerm i) at hHhat
  have hmR : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hmpos : 0 < (m : ℝ) := by positivity
  have he0 : 0 ≤ ε0 := (abs_nonneg _).trans (hpdiff ⟨0, hm⟩)
  have he1 : 0 ≤ ε1 := (norm_nonneg _).trans (hhterm ⟨0, hm⟩)
  have he : 0 ≤ ε := by linarith
  have hme : (m : ℝ) * ε0 ≤ ε / 8 := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 8 * (m : ℝ) ^ 2)).mp hε0
    nlinarith [mul_nonneg (mul_nonneg hmpos.le he0) (sub_nonneg.mpr hmR)]
  have hWdiff : |W - 1| ≤ (m : ℝ) * ε0 := by
    rw [hW, ← hpsum, ← Finset.sum_sub_distrib]
    calc
      |∑ i, (ptilde i - p i)| ≤ ∑ i, |ptilde i - p i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin m, ε0 := Finset.sum_le_sum (fun i _ => hpdiff i)
      _ = (m : ℝ) * ε0 := by simp
  have hWlower : 1 / 2 ≤ W := by
    have := (abs_le.mp hWdiff).1
    linarith
  have hWpos : 0 < W := by linarith
  let T : Fin m → Operator D := fun i => (max ‖HtildeTerm i‖ 1)⁻¹ • HtildeTerm i
  have hTnorm (i : Fin m) : ‖T i‖ ≤ 1 := by
    have hmax : 0 < max ‖HtildeTerm i‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    simp only [T, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hmax.le)]
    rw [← div_eq_inv_mul, div_le_iff₀ hmax]
    simp
  have hTdiff (i : Fin m) : ‖Hterm i - T i‖ ≤ 2 * ε1 := by
    have hclip : ‖HtildeTerm i - T i‖ ≤ ε1 := by
      by_cases hi : ‖HtildeTerm i‖ ≤ 1
      · simp [T, max_eq_right hi, he1]
      · have hip : 0 < ‖HtildeTerm i‖ := lt_trans zero_lt_one (lt_of_not_ge hi)
        have hinv : ‖HtildeTerm i‖⁻¹ ≤ 1 := (inv_le_one₀ hip).mpr (le_of_not_ge hi)
        calc
          ‖HtildeTerm i - T i‖ = ‖(1 - ‖HtildeTerm i‖⁻¹) • HtildeTerm i‖ := by
            congr 1
            simp [T, max_eq_left (le_of_not_ge hi), sub_smul]
          _ = ‖HtildeTerm i‖ - 1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hinv)]
            field_simp [ne_of_gt hip]
          _ ≤ ε1 := by
            have := norm_sub_norm_le (HtildeTerm i) (Hterm i)
            linarith [hhterm i, hnorm i]
    calc
      ‖Hterm i - T i‖ ≤ ‖Hterm i - HtildeTerm i‖ + ‖HtildeTerm i - T i‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * ε1 := by rw [norm_sub_rev]; linarith [hhterm i]
  have hcoeff (i : Fin m) : |p i - ptilde i / W| ≤
      (|W - 1| * p i + ε0) / W := by
    have hid : p i - ptilde i / W = ((W - 1) * p i - (ptilde i - p i)) / W := by
      field_simp [ne_of_gt hWpos]
      ring
    rw [hid, abs_div, abs_of_pos hWpos]
    apply div_le_div_of_nonneg_right _ hWpos.le
    calc
      |(W - 1) * p i - (ptilde i - p i)| ≤ |(W - 1) * p i| + |ptilde i - p i| :=
        abs_sub _ _
      _ ≤ |W - 1| * p i + ε0 := by
        rw [abs_mul, abs_of_nonneg (hp i)]
        linarith [hpdiff i]
  have hcoeffsum : (∑ i, |p i - ptilde i / W|) ≤ 4 * (m : ℝ) * ε0 := by
    calc
      (∑ i, |p i - ptilde i / W|) ≤ ∑ i, (|W - 1| * p i + ε0) / W :=
        Finset.sum_le_sum (fun i _ => hcoeff i)
      _ = (|W - 1| + (m : ℝ) * ε0) / W := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hpsum]
        simp
      _ ≤ (2 * (m : ℝ) * ε0) / W := by
        apply div_le_div_of_nonneg_right _ hWpos.le
        linarith
      _ ≤ 4 * (m : ℝ) * ε0 := by
        apply (div_le_iff₀ hWpos).mpr
        nlinarith [mul_nonneg (mul_nonneg hmpos.le he0) (sub_nonneg.mpr hWlower)]
  have hidentity : H - Ĥ = ∑ i, (p i • (Hterm i - T i) +
      (p i - ptilde i / W) • T i) := by
    rw [hH, hHhat, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [T]
    rw [smul_sub, sub_smul, sub_add_sub_cancel]
  rw [hidentity]
  calc
    ‖∑ i, (p i • (Hterm i - T i) + (p i - ptilde i / W) • T i)‖ ≤
        ∑ i, ‖p i • (Hterm i - T i) + (p i - ptilde i / W) • T i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (p i * (2 * ε1) + |p i - ptilde i / W|) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        ‖p i • (Hterm i - T i) + (p i - ptilde i / W) • T i‖ ≤
            ‖p i • (Hterm i - T i)‖ + ‖(p i - ptilde i / W) • T i‖ := norm_add_le _ _
        _ ≤ p i * (2 * ε1) + |p i - ptilde i / W| := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (hp i)]
          exact add_le_add (mul_le_mul_of_nonneg_left (hTdiff i) (hp i))
            (by
              simpa only [mul_one] using
                (mul_le_mul_of_nonneg_left (hTnorm i) (abs_nonneg (p i - ptilde i / W))))
    _ = 2 * ε1 + ∑ i, |p i - ptilde i / W| := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hpsum, one_mul]
    _ ≤ ε := by linarith

/-- Exact unit weights and a nonzero identity Hamiltonian satisfy the repaired
normalization contract, with zero perturbation and target precision `1/2`. -/
theorem normalized_identity_example :
    OperatorSpectralNorm ((1 : Operator 1) - 1) ≤ (1 / 2 : ℝ) := by
  exact lemma_20_hamiltonian_estimation_error 1 0 0 (1 / 2) 1 1
    (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => 1) (fun _ : Fin 1 => 1)
    (by norm_num) (by simp) (by simp) (by simp [OperatorSpectralNorm])
    (by intro i; norm_num) (by simp) (by intro i; norm_num)
    (by intro i; simp [OperatorSpectralNorm])
    (by intro i; simp [OperatorSpectralNorm])
    (by norm_num) (by norm_num) (by norm_num)

/-- In the negative-weight counterexample `p = ptilde = (100,-99)`, exact terms
zero and estimated terms `(I/6,0)`, the normalized estimate has error greater than one.
Here `m=2`, `W=1`, `ε0=0`, `ε1=1/6`, `ε=1`; the old PSD and error bounds hold. -/
theorem negative_weight_error_example :
    (1 : ℝ) < OperatorSpectralNorm ((0 : Operator 1) - (100 / 6 : ℝ) • 1) := by
  change (1 : ℝ) < ‖(0 : Operator 1) - (100 / 6 : ℝ) • 1‖
  simp only [zero_sub, norm_neg, norm_smul, norm_one, mul_one, Real.norm_eq_abs]
  norm_num

end Qatlib.Papers.QuantumPCPs25.MainResults.Algebra
