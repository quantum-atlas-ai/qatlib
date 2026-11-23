/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Heralded dilation of a singular-value filter step

Appendix D of [FillionGourdeauMacLeanLaflamme2017] implements the non-unitary filter update
non-deterministically: after the singular-value decomposition of the scaled shear matrix, the
diagonal factor `Σᵢ = diag (1, aᵢ)` with `0 ≤ aᵢ ≤ 1` (Eq. (D11)) is realized by the two-qubit
controlled rotation `c-Pᵢ` of Eq. (D13),

```
c-Pᵢ = [ 1  0        0        0;
         0  aᵢ       0        sᵢ;
         0  0        1        0;
         0  -sᵢ      0        aᵢ     ],   sᵢ = √(1 - aᵢ²),
```

followed by a projective `|0⟩⟨0|` measurement of the upper (ancilla) qubit. This module proves
that `c-Pᵢ` is unitary for every singular value `0 ≤ aᵢ ≤ 1`, that its successful branch
transports the scaled contraction `diag (1, aᵢ)` while the failure branch carries the amplitude
`√(1 - aᵢ²)`, and that postselected success happens with probability at least `aᵢ²`.

The register order is the paper's two-qubit order: index `0 = (0,0)`, `1 = (0,1)`, `2 = (1,0)`,
`3 = (1,1)` in `Fin 4`, with the ancilla as the first qubit.

## Main statements

* `heraldedDilation_unitary`: `c-Pᵢ` is a unitary matrix for `0 ≤ aᵢ ≤ 1`.
* `heraldedDilation_opNorm`: its L2-operator norm is one.
* `heraldedDilation_success_apply`: the `|0⟩`-ancilla output components agree with
  `diag (1, aᵢ) *ᵥ φ`.
* `heraldedDilation_failure_apply_zero` / `heraldedDilation_failure_apply_one`: the failure
  components, carrying amplitude `√(1 - aᵢ²)`.
* `heraldedDilation_success_probability`: the postselected success probability equals
  `‖φ 0‖² + aᵢ² ‖φ 1‖²`, hence is at least `aᵢ²`.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiracEquation16.FilterCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

/-- The heralded two-qubit dilation `c-Pᵢ` of Eq. (D13) of
[FillionGourdeauMacLeanLaflamme2017], with `sᵢ = √(1 - aᵢ²)`, acting on `Fin 4` in the order
`(0,0), (0,1), (1,0), (1,1)`. -/
noncomputable def heraldedDilation (a : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, (a : ℂ), 0, ((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ);
     0, 0, 1, 0;
     0, -((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ), 0, (a : ℂ)]

/-- The singular-value window `0 ≤ a ≤ 1` makes `1 - a²` nonnegative, so the failure amplitude
`√(1 - a²)` is well-defined. -/
theorem heraldedDilation_sqrt_nonneg {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) : (0:ℝ) ≤ 1 - a ^ 2 := by
  nlinarith [sq_nonneg (a - 1), ha.1, ha.2]

/-- The square of the failure amplitude is `1 - a²` (complex form). -/
theorem heraldedDilation_sqr (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) :
    ((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) * ((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) = (1 - a ^ 2 : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (heraldedDilation_sqrt_nonneg ha)]
  push_cast
  ring

private theorem sum_fin_four (f : Fin 4 → ℂ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 := by
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp

/-- The dilation `c-Pᵢ` of Eq. (D13) is unitary for every singular value `0 ≤ aᵢ ≤ 1`. -/
theorem heraldedDilation_unitary {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) :
    heraldedDilation a ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, heraldedDilation, Complex.conj_ofReal,
      sum_fin_four, heraldedDilation_sqr _ ha] <;>
    ring

/-- The L2-operator norm of the unitary dilation is one. -/
theorem heraldedDilation_opNorm {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) : ‖heraldedDilation a‖ = 1 := by
  have hU := heraldedDilation_unitary ha
  apply le_antisymm
  · rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [one_mul]
    exact le_of_eq (norm_toEuclideanCLM_of_mem_unitaryGroup hU x)
  · have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin 4) (Fin 4) ℂ ≃⋆ₐ[ℂ]
        (EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))) (heraldedDilation a)
        (toEuclidean_fromVec (Ket (0 : Fin 4)))‖ = 1 := by
      rw [toEuclideanCLM_applyGate]
      have hcol : ApplyGate (heraldedDilation a) (Ket (0 : Fin 4)) = Ket (0 : Fin 4) := by
        funext j
        rw [ApplyGate]
        show ∑ k : Fin 4, heraldedDilation a j k * Ket (0 : Fin 4) k = Ket (0 : Fin 4) j
        rw [Finset.sum_eq_single 0]
        · simp only [Ket]
          fin_cases j <;> simp [heraldedDilation, Matrix.cons_val]
        · intro k _ hk
          simp [Ket, hk]
        · intro h
          exact absurd (Finset.mem_univ 0) h
      rw [hcol]
      exact (normalized_iff_norm_toEuclidean_fromVec (Ket (0 : Fin 4))).mp (normalized_ket _)
    have h2 : ‖(toEuclidean_fromVec (Ket (0 : Fin 4)) : EuclideanSpace ℂ (Fin 4))‖ = 1 :=
      (normalized_iff_norm_toEuclidean_fromVec (Ket (0 : Fin 4))).mp (normalized_ket _)
    have h3 := (Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Fin 4) (Fin 4) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))) (heraldedDilation a) |>.le_opNorm
      (toEuclidean_fromVec (Ket (0 : Fin 4)))
    rw [h1, h2, mul_one] at h3
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    exact h3

/-- The input register embedding: the ancilla qubit is prepared in `|0⟩`, so only the first two
components `(0,0)` and `(0,1)` carry the system amplitudes `φ 0` and `φ 1`. -/
def dilatedInput (φ : QState (Fin 2)) : QState (Fin 4) :=
  fun k => if k = 0 then φ 0 else if k = 1 then φ 1 else 0

/-- On the successful branch the ancilla stays in `|0⟩` and the system component `(0,0)` is
transported identically, matching the first singular value `1` of `Σᵢ = diag (1, aᵢ)`. -/
theorem heraldedDilation_success_apply_zero {a : ℝ} (φ : QState (Fin 2)) :
    (heraldedDilation a *ᵥ dilatedInput φ) 0 = φ 0 := by
  show ∑ k : Fin 4, heraldedDilation a 0 k * dilatedInput φ k = φ 0
  rw [sum_fin_four]
  simp only [heraldedDilation,
     dilatedInput]
  simp

/-- On the successful branch the system component `(0,1)` is transported by the second singular
value `aᵢ` of `Σᵢ = diag (1, aᵢ)`. -/
theorem heraldedDilation_success_apply_one {a : ℝ} (φ : QState (Fin 2)) :
    (heraldedDilation a *ᵥ dilatedInput φ) 1 = (a : ℂ) * φ 1 := by
  show ∑ k : Fin 4, heraldedDilation a 1 k * dilatedInput φ k = (a : ℂ) * φ 1
  rw [sum_fin_four]
  simp only [heraldedDilation,
     dilatedInput]
  simp

/-- The successful branch of `c-Pᵢ` on `|0⟩ ⊗ φ` agrees exactly with the scaled contraction
`Σᵢ *ᵥ φ = diag (1, aᵢ) *ᵥ φ` of Eq. (D11). -/
theorem diagonal_filter_mulVec_apply_zero {a : ℝ} (φ : QState (Fin 2)) :
    (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) *ᵥ φ) 0 = φ 0 := by
  show ∑ j : Fin 2, (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ))) 0 j * φ j
      = φ 0
  rw [Fin.sum_univ_two]
  simp []

/-- The second singular value `aᵢ` appears on the `(0,1)` component. -/
theorem diagonal_filter_mulVec_apply_one {a : ℝ} (φ : QState (Fin 2)) :
    (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) *ᵥ φ) 1
      = (a : ℂ) * φ 1 := by
  show ∑ j : Fin 2, (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ))) 1 j * φ j
      = (a : ℂ) * φ 1
  rw [Fin.sum_univ_two]
  simp []

/-- The successful branch of `c-Pᵢ` on `|0⟩ ⊗ φ` agrees exactly with the scaled contraction
`Σᵢ *ᵥ φ = diag (1, aᵢ) *ᵥ φ` of Eq. (D11). -/
theorem heraldedDilation_success_apply {a : ℝ} (φ : QState (Fin 2)) (i : Fin 2) :
    (heraldedDilation a *ᵥ dilatedInput φ) (Fin.castLE (by norm_num) i)
      = (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) *ᵥ φ) i := by
  fin_cases i
  · show (heraldedDilation a *ᵥ dilatedInput φ) 0
      = (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) *ᵥ φ) 0
    rw [diagonal_filter_mulVec_apply_zero]
    exact heraldedDilation_success_apply_zero φ
  · show (heraldedDilation a *ᵥ dilatedInput φ) 1
      = (Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) *ᵥ φ) 1
    rw [diagonal_filter_mulVec_apply_one]
    exact heraldedDilation_success_apply_one φ

/-- On the failure branch the `(1,0)` component vanishes. -/
theorem heraldedDilation_failure_apply_zero {a : ℝ} (φ : QState (Fin 2)) :
    (heraldedDilation a *ᵥ dilatedInput φ) 2 = 0 := by
  show ∑ k : Fin 4, heraldedDilation a 2 k * dilatedInput φ k = 0
  rw [sum_fin_four]
  simp only [heraldedDilation,
     dilatedInput]
  simp

/-- On the failure branch the `(1,1)` component carries the failure amplitude `√(1 - aᵢ²)` of
Eq. (D13). -/
theorem heraldedDilation_failure_apply_one {a : ℝ} (φ : QState (Fin 2)) :
    (heraldedDilation a *ᵥ dilatedInput φ) 3 = -((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) * φ 1 := by
  show ∑ k : Fin 4, heraldedDilation a 3 k * dilatedInput φ k
    = -((Real.sqrt (1 - a ^ 2) : ℝ) : ℂ) * φ 1
  rw [sum_fin_four]
  simp only [heraldedDilation,
     dilatedInput]
  simp

/-- The norm of the failure amplitude on the `(1,1)` component is `√(1 - aᵢ²) * ‖φ 1‖`. -/
theorem heraldedDilation_failure_norm {a : ℝ} (φ : QState (Fin 2)) :
    ‖(heraldedDilation a *ᵥ dilatedInput φ) 3‖
      = Real.sqrt (1 - a ^ 2) * ‖φ 1‖ := by
  rw [heraldedDilation_failure_apply_one]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (Real.sqrt_nonneg (1 - a ^ 2))]

/-- The scaled diagonal contraction `Σᵢ = diag (1, aᵢ)` of Eq. (D11) has operator norm exactly
one for `0 ≤ aᵢ ≤ 1`, witnessing that the scaling makes the update a contraction. -/
theorem diag_filter_opNorm {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) :
    ‖(Matrix.diagonal (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ)‖ = 1 := by
  -- For a diagonal operator, Mathlib's exact L2 operator norm formula is the
  -- maximum modulus of the diagonal entries.
  rw [Matrix.l2_opNorm_diagonal]
  have h1 : ‖(fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ))‖ ≤ 1 := by
    refine pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr fun j => ?_
    fin_cases j
    · simp
    · simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha.1, ha.2]
  have h2 : (1 : ℝ) ≤ ‖(fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ))‖ := by
    have hge := norm_le_pi_norm (fun j : Fin 2 => if j = 0 then (1 : ℂ) else (a : ℂ)) (0 : Fin 2)
    have h0 : (if (0 : Fin 2) = 0 then (1 : ℂ) else (a : ℂ)) = (1 : ℂ) := by simp
    rw [h0] at hge
    simpa using hge
  linarith

/-- The postselected success probability of the dilation on a normalized input equals
`‖φ 0‖² + aᵢ² ‖φ 1‖²`; in particular it is at least `aᵢ²` with equality when `φ` is supported on
the second component. -/
theorem heraldedDilation_success_probability {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (φ : QState (Fin 2))
    (_hφ : Normalized φ) :
    ‖toEuclidean_fromVec (fun k : Fin 4 => if k = 0 ∨ k = 1 then
        (heraldedDilation a *ᵥ dilatedInput φ) k else 0)‖ ^ 2
      = ‖φ 0‖ ^ 2 + a ^ 2 * ‖φ 1‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp [ heraldedDilation_success_apply_zero,
    heraldedDilation_success_apply_one, abs_of_nonneg ha.1,
    mul_pow]

/-- The postselected success probability is at least `aᵢ²`, so the heralded filtering step
succeeds with probability bounded below by the squared smallest kept singular value. -/
theorem heraldedDilation_success_probability_ge {a : ℝ} (ha : 0 ≤ a ∧ a ≤ 1) (φ : QState (Fin 2))
    (hφ : Normalized φ) :
    a ^ 2 ≤ ‖toEuclidean_fromVec (fun k : Fin 4 => if k = 0 ∨ k = 1 then
        (heraldedDilation a *ᵥ dilatedInput φ) k else 0)‖ ^ 2 := by
  rw [heraldedDilation_success_probability ha φ hφ]
  have hsum : ‖φ 0‖ ^ 2 + ‖φ 1‖ ^ 2 = 1 := by
    simpa [Normalized, Fin.sum_univ_two] using hφ
  have h1m : (0:ℝ) ≤ 1 - a ^ 2 := heraldedDilation_sqrt_nonneg ha
  nlinarith [h1m, sq_nonneg ‖φ 0‖, sq_nonneg ‖φ 1‖, ha.1, ha.2, hsum]

end Qatlib.Papers.DiracEquation16.FilterCore
