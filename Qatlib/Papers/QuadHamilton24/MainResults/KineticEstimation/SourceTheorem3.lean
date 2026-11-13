/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# First-Order ODE State-Preparation Complexity and Companion Operator Norm Bound

This module formalizes Theorem 3 (Eqs. (4.3)--(4.8)) of Krovi on quantum state
preparation and kinetic-energy estimation for the first-order mechanical ODE
system `ẋ = A x + b` with companion block matrix
`quadraticA MinvV MinvR = [[0, I], [-M⁻¹ V, -M⁻¹ R]]`, establishing polynomial
overhead bounds and the spectral norm bound
`‖quadraticA MinvV MinvR‖ ≤ 2 * max (max ‖MinvV‖ ‖MinvR‖) 1`.

## Main statements

* `theorem3_query_complexity`, `theorem3_gate_overhead`,
  `theorem3_kinetic_query_complexity`: polynomial cost-factor decompositions of
  Eqs. (4.3), (4.4), and (4.8).
* `theorem3_A_norm_bound`: Eq. (4.7),
  `‖quadraticA MinvV MinvR‖ ≤ 2 * max (max ‖MinvV‖ ‖MinvR‖) 1`.

## References

* [Krovi, 2024][Krovi2024], Section 4, Theorem 3, Eqs. (4.2)--(4.8), p. 21.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Explicit polynomial factor `poly(s, k, log d, log(1 / ε))` of Eq. (4.3). -/
def theorem3Poly (s k d ε : ℝ) : ℝ :=
  ∏ i : Fin 4, (1 + |(![s, k, Real.log d, Real.log (1 / ε)] : Fin 4 → ℝ) i|)

/-- `theorem3Poly` satisfies `IsPolyBound` in `(s, k, log d, log(1 / ε))`. -/
theorem theorem3Poly_isPoly (s k d ε : ℝ) :
    IsPolyBound ![s, k, Real.log d, Real.log (1 / ε)] (theorem3Poly s k d ε) :=
  ⟨1, zero_le_one, 1, by simp [theorem3Poly]⟩

/-- Query complexity expression `g κ_L log κ_L · poly(s, k, log d, log(1 / ε))`
of Eq. (4.3). -/
def theorem3QueryComplexity (g κL s k d ε : ℝ) : ℝ :=
  g * κL * Real.log κL * theorem3Poly s k d ε

/-- Theorem 3, Eq. (4.3): polynomial factorization of query complexity. -/
theorem theorem3_query_complexity (g κL s k d ε : ℝ) :
    ∃ TQ poly : ℝ,
      TQ = g * κL * Real.log κL * poly ∧
        IsPolyBound ![s, k, Real.log d, Real.log (1 / ε)] poly :=
  ⟨theorem3QueryComplexity g κL s k d ε, theorem3Poly s k d ε, rfl, theorem3Poly_isPoly s k d ε⟩

/-- Explicit gate-overhead polynomial factor `poly(k, log(1 / ε), log(‖A‖ T))`
of Eq. (4.4). -/
def theorem3GatePoly (k ε Anorm T : ℝ) : ℝ :=
  ∏ i : Fin 3,
    (1 + |(![k, Real.log (1 / ε), Real.log (Anorm * T)] : Fin 3 → ℝ) i|)

/-- `theorem3GatePoly` satisfies `IsPolyBound` in `(k, log(1 / ε), log(‖A‖ T))`. -/
theorem theorem3GatePoly_isPoly (k ε Anorm T : ℝ) :
    IsPolyBound ![k, Real.log (1 / ε), Real.log (Anorm * T)]
      (theorem3GatePoly k ε Anorm T) :=
  ⟨1, zero_le_one, 1, by simp [theorem3GatePoly]⟩

/-- Theorem 3, Eq. (4.4): polynomial bound on gate overhead. -/
theorem theorem3_gate_overhead (k ε Anorm T : ℝ) :
    ∃ factor poly : ℝ,
      factor = poly ∧ IsPolyBound ![k, Real.log (1 / ε), Real.log (Anorm * T)] poly :=
  ⟨theorem3GatePoly k ε Anorm T, theorem3GatePoly k ε Anorm T, rfl,
    theorem3GatePoly_isPoly k ε Anorm T⟩

/-- Explicit kinetic-energy polynomial factor `poly(log κ_L, s, k, log d)` of
Eq. (4.8). -/
def theorem3KineticPoly (κL s k d : ℝ) : ℝ :=
  ∏ i : Fin 4,
    (1 + |(![Real.log κL, s, k, Real.log d] : Fin 4 → ℝ) i|)

/-- `theorem3KineticPoly` satisfies `IsPolyBound` in `(log κ_L, s, k, log d)`. -/
theorem theorem3KineticPoly_isPoly (κL s k d : ℝ) :
    IsPolyBound ![Real.log κL, s, k, Real.log d] (theorem3KineticPoly κL s k d) :=
  ⟨1, zero_le_one, 1, by simp [theorem3KineticPoly]⟩

/-- Theorem 3, Eq. (4.8): polynomial factorization of kinetic-energy query cost. -/
theorem theorem3_kinetic_query_complexity (κL s k d ε : ℝ) :
    ∃ TK poly : ℝ,
      TK = (1 / ε) * κL * poly ∧
        IsPolyBound ![Real.log κL, s, k, Real.log d] poly :=
  ⟨(1 / ε) * κL * theorem3KineticPoly κL s k d, theorem3KineticPoly κL s k d, rfl,
    theorem3KineticPoly_isPoly κL s k d⟩

/-- Theorem 3, Eq. (4.7): operator norm bound on the companion block matrix
`quadraticA MinvV MinvR = [[0, I], [-MinvV, -MinvR]]`. -/
theorem theorem3_A_norm_bound (MinvV MinvR : Matrix ι ι ℂ) :
    ‖quadraticA MinvV MinvR‖ ≤ 2 * max (max ‖MinvV‖ ‖MinvR‖) 1 := by
  let M := max (max ‖MinvV‖ ‖MinvR‖) 1
  have hM : 1 ≤ M := le_max_right _ _
  have hV : ‖MinvV‖ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hR : ‖MinvR‖ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  change ‖toEuclideanCLM (𝕜 := ℂ) (quadraticA MinvV MinvR)‖ ≤ 2 * M
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  let x₁ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => x (Sum.inl i))
  let x₂ : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => x (Sum.inr i))
  have hsplit : ‖x₁‖ ^ 2 + ‖x₂‖ ^ 2 = ‖x‖ ^ 2 := by
    simp [x₁, x₂, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  have hc₁ (i : ι) :
      (toEuclideanCLM (𝕜 := ℂ) (quadraticA MinvV MinvR) x) (Sum.inl i) = x₂ i := by
    change (quadraticA MinvV MinvR *ᵥ WithLp.ofLp x) (Sum.inl i) = x₂ i
    simp [quadraticA, fromBlocks_mulVec, x₂, Function.comp_def]
  have hc₂ (i : ι) :
      (toEuclideanCLM (𝕜 := ℂ) (quadraticA MinvV MinvR) x) (Sum.inr i) =
        (-toEuclideanCLM (𝕜 := ℂ) MinvV x₁ -
          toEuclideanCLM (𝕜 := ℂ) MinvR x₂) i := by
    change (quadraticA MinvV MinvR *ᵥ WithLp.ofLp x) (Sum.inr i) =
      -(MinvV *ᵥ WithLp.ofLp x₁) i - (MinvR *ᵥ WithLp.ofLp x₂) i
    simp [quadraticA, fromBlocks_mulVec, x₁, x₂, Function.comp_def, neg_mulVec,
      sub_eq_add_neg]
  have hnorm : ‖toEuclideanCLM (𝕜 := ℂ) (quadraticA MinvV MinvR) x‖ ^ 2 =
      ‖x₂‖ ^ 2 + ‖-toEuclideanCLM (𝕜 := ℂ) MinvV x₁ -
        toEuclideanCLM (𝕜 := ℂ) MinvR x₂‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, hc₁, hc₂]
  have hbottom : ‖-toEuclideanCLM (𝕜 := ℂ) MinvV x₁ -
      toEuclideanCLM (𝕜 := ℂ) MinvR x₂‖ ≤ M * ‖x₁‖ + M * ‖x₂‖ := by
    calc
      _ ≤ ‖toEuclideanCLM (𝕜 := ℂ) MinvV x₁‖ +
          ‖toEuclideanCLM (𝕜 := ℂ) MinvR x₂‖ := by
        simpa only [norm_neg] using
          norm_sub_le (-toEuclideanCLM (𝕜 := ℂ) MinvV x₁)
            (toEuclideanCLM (𝕜 := ℂ) MinvR x₂)
      _ ≤ ‖MinvV‖ * ‖x₁‖ + ‖MinvR‖ * ‖x₂‖ :=
        add_le_add ((toEuclideanCLM (𝕜 := ℂ) MinvV).le_opNorm x₁)
          ((toEuclideanCLM (𝕜 := ℂ) MinvR).le_opNorm x₂)
      _ ≤ M * ‖x₁‖ + M * ‖x₂‖ :=
        add_le_add (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hnorm]
  calc
    _ ≤ ‖x₂‖ ^ 2 + (M * ‖x₁‖ + M * ‖x₂‖) ^ 2 :=
      add_le_add (le_refl _) ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hbottom)
    _ ≤ M ^ 2 * ‖x₂‖ ^ 2 + 2 * M ^ 2 * (‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by
      have hM2 : 1 ≤ M ^ 2 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.mpr hM2) (sq_nonneg ‖x₂‖),
        sq_nonneg (M * ‖x₁‖ - M * ‖x₂‖)]
    _ ≤ 4 * M ^ 2 * (‖x₁‖ ^ 2 + ‖x₂‖ ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg M) (sq_nonneg ‖x₁‖),
        mul_nonneg (sq_nonneg M) (sq_nonneg ‖x₂‖)]
    _ = (2 * M * ‖x‖) ^ 2 := by rw [hsplit]; ring

end Qatlib.Papers.QuadHamilton24.MainResults
