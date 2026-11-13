/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5Aux3

/-!
# Transporting Taylor-system inverses by similarity

The blockwise lift `taylorV2Conj` applies a change of basis independently at each history label.
Its multiplication and norm properties transport a diagonal Taylor-system inverse to a similar
system, with the factor `‖V‖ * ‖V⁻¹‖`. See [BerryEtAl2017ODE] for the paper's setting.

## Main statements

* `taylor_opNorm_le_of_vec_sq`: A nonnegative constant bounding the squared Euclidean norm of
  every matrix-vector product also bounds the matrix operator norm.
* `taylorV2_inverse_norm_transport`: Under the intertwining and inverse hypotheses, the
  inverse-system norm for `A` is at most `‖V‖ * ‖V⁻¹‖` times that for `D`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

/-- A nonnegative constant bounding the squared Euclidean norm of every matrix-vector product
also bounds the matrix operator norm. -/
theorem taylor_opNorm_le_of_vec_sq {I : Type} [Fintype I] [DecidableEq I]
    {M : Matrix I I ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : I → ℂ, ∑ i, ‖(M *ᵥ x) i‖ ^ 2 ≤ c ^ 2 * ∑ i, ‖x i‖ ^ 2) : ‖M‖ ≤ c := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun y => ?_
  have hy : y = toEuclidean_fromVec (WithLp.ofLp y) := rfl
  rw [hy, toEuclideanCLM_applyGate]
  change ‖toEuclidean_fromVec (M *ᵥ WithLp.ofLp y)‖ ≤ c * ‖toEuclidean_fromVec (WithLp.ofLp y)‖
  have hin := h (WithLp.ofLp y)
  have hs : ‖toEuclidean_fromVec (M *ᵥ WithLp.ofLp y)‖ ^ 2 ≤
      (c * ‖toEuclidean_fromVec (WithLp.ofLp y)‖) ^ 2 := by
    rw [mul_pow, norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq]
    exact hin
  have hnn : 0 ≤ c * ‖toEuclidean_fromVec (WithLp.ofLp y)‖ := by positivity
  nlinarith [norm_nonneg (toEuclidean_fromVec (M *ᵥ WithLp.ofLp y))]

/-- The squared Euclidean norm of `M *ᵥ v` is at most `‖M‖²` times that of `v`. -/
theorem taylor_mulVec_sq_le {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (v : I → ℂ) :
    ∑ i, ‖(M *ᵥ v) i‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  have hle := stateVector_mulVec_norm_le M v
  have hs := mul_self_le_mul_self (norm_nonneg (stateVector (M *ᵥ v))) hle
  rw [← pow_two, ← pow_two, mul_pow, stateVector_norm_sq, stateVector_norm_sq] at hs
  exact hs

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The block diagonal lift of `V` acting identically on every history label. -/
def taylorV2Conj (m k p : ℕ) (V : Matrix N N ℂ) :
    Matrix (Fin (m * (k + 1) + p + 1) × N) (Fin (m * (k + 1) + p + 1) × N) ℂ :=
  fun r c => if r.1 = c.1 then V r.2 c.2 else 0

omit [DecidableEq N] in

/-- Multiplication by `taylorV2Conj` applies `V` separately to each label block. -/
theorem taylorV2Conj_mulVec (m k p : ℕ) (V : Matrix N N ℂ)
    (x : QState (Fin (m * (k + 1) + p + 1) × N))
    (l : Fin (m * (k + 1) + p + 1)) (n : N) :
    (taylorV2Conj m k p V *ᵥ x) (l, n) = (V *ᵥ taylorBlock x l) n := by
  simp [taylorV2Conj, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ite_mul,
    Finset.sum_ite_irrel, taylorBlock]

/-- The operator norm of the blockwise lift of `V` is at most `‖V‖`. -/
theorem taylorV2Conj_norm_le (m k p : ℕ) (V : Matrix N N ℂ) :
    ‖taylorV2Conj m k p V‖ ≤ ‖V‖ := by
  apply taylor_opNorm_le_of_vec_sq (norm_nonneg _)
  intro x
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  simp_rw [taylorV2Conj_mulVec]
  exact taylor_mulVec_sq_le V (taylorBlock x l)

omit [DecidableEq N] in

/-- The blockwise lift preserves matrix multiplication. -/
theorem taylorV2Conj_mul (m k p : ℕ) (V W : Matrix N N ℂ) :
    taylorV2Conj m k p V * taylorV2Conj m k p W = taylorV2Conj m k p (V * W) := by
  ext r c
  simp [Matrix.mul_apply, taylorV2Conj, Fintype.sum_prod_type,
    ite_mul, mul_ite, Finset.sum_ite_irrel]

/-- If `V⁻¹` is a two-sided inverse of `V`, their blockwise lifts are also two-sided inverses. -/
theorem taylorV2Conj_inverse (m k p : ℕ) (V : Matrix N N ℂ)
    (h1 : V * V⁻¹ = 1) (h2 : V⁻¹ * V = 1) :
    taylorV2Conj m k p V * taylorV2Conj m k p V⁻¹ = 1 ∧
      taylorV2Conj m k p V⁻¹ * taylorV2Conj m k p V = 1 := by
  have heq : taylorV2Conj m k p (1 : Matrix N N ℂ) = 1 := by
    ext r c
    simp [taylorV2Conj, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  rw [taylorV2Conj_mul, taylorV2Conj_mul, h1, h2, heq]
  exact ⟨rfl, rfl⟩

/-- The relation `A * V = V * D` lifts to the corresponding intertwining relation between the V2
Taylor matrices. -/
theorem taylorStepMatrixV2_conj_mul (m k p : ℕ) (A V D : Matrix N N ℂ)
    (hAV : A * V = V * D) :
    taylorStepMatrixV2 m k p A * taylorV2Conj m k p V =
      taylorV2Conj m k p V * taylorStepMatrixV2 m k p D := by
  ext r c
  simp [Matrix.mul_apply, taylorV2Conj, taylorStepMatrixV2, Fintype.sum_prod_type,
    Prod.ext_iff, ite_mul, mul_ite, Finset.sum_ite_irrel]
  simp only [sub_mul, mul_sub, ite_mul, mul_ite, Finset.sum_sub_distrib,
    Finset.sum_ite_irrel, div_mul_eq_mul_div, ← mul_div_assoc, ← Finset.sum_div]
  have he : (∑ n, A r.2 n * V n c.2) = ∑ n, V r.2 n * D n c.2 :=
    congrArg (fun M : Matrix N N ℂ => M r.2 c.2) hAV
  rw [he]
  by_cases hl : r.1 = c.1 <;> simp [hl]

/-- Under the intertwining relation and invertibility of `V`, the inverse V2 Taylor matrix is
the conjugate of the inverse system for `D`. -/
theorem taylorV2_inverse_eq_conj (m k p : ℕ) (A V D : Matrix N N ℂ)
    (hAV : A * V = V * D) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1) :
    (taylorStepMatrixV2 m k p A)⁻¹ =
      taylorV2Conj m k p V * (taylorStepMatrixV2 m k p D)⁻¹ * taylorV2Conj m k p V⁻¹ := by
  apply Matrix.inv_eq_right_inv
  calc taylorStepMatrixV2 m k p A *
        (taylorV2Conj m k p V * (taylorStepMatrixV2 m k p D)⁻¹ * taylorV2Conj m k p V⁻¹)
      = (taylorStepMatrixV2 m k p A * taylorV2Conj m k p V) *
          (taylorStepMatrixV2 m k p D)⁻¹ * taylorV2Conj m k p V⁻¹ := by noncomm_ring
    _ = (taylorV2Conj m k p V * taylorStepMatrixV2 m k p D) *
          (taylorStepMatrixV2 m k p D)⁻¹ * taylorV2Conj m k p V⁻¹ := by
          rw [taylorStepMatrixV2_conj_mul m k p A V D hAV]
    _ = taylorV2Conj m k p V *
          (taylorStepMatrixV2 m k p D * (taylorStepMatrixV2 m k p D)⁻¹) *
          taylorV2Conj m k p V⁻¹ := by noncomm_ring
    _ = taylorV2Conj m k p V * taylorV2Conj m k p V⁻¹ := by
          rw [(taylorStepMatrixV2_inverse m k p D).1, mul_one]
    _ = 1 := (taylorV2Conj_inverse m k p V hV1 hV2).1

/-- Under the intertwining and inverse hypotheses, the inverse-system norm for `A` is at most
`‖V‖ * ‖V⁻¹‖` times that for `D`. -/
theorem taylorV2_inverse_norm_transport (m k p : ℕ) (A V D : Matrix N N ℂ)
    (hAV : A * V = V * D) (hV1 : V * V⁻¹ = 1) (hV2 : V⁻¹ * V = 1) :
    ‖(taylorStepMatrixV2 m k p A)⁻¹‖ ≤
      (‖V‖ * ‖V⁻¹‖) * ‖(taylorStepMatrixV2 m k p D)⁻¹‖ := by
  rw [taylorV2_inverse_eq_conj m k p A V D hAV hV1 hV2]
  calc ‖taylorV2Conj m k p V * (taylorStepMatrixV2 m k p D)⁻¹ * taylorV2Conj m k p V⁻¹‖
      ≤ ‖taylorV2Conj m k p V * (taylorStepMatrixV2 m k p D)⁻¹‖ * ‖taylorV2Conj m k p V⁻¹‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖taylorV2Conj m k p V‖ * ‖(taylorStepMatrixV2 m k p D)⁻¹‖) * ‖taylorV2Conj m k p V⁻¹‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
    _ ≤ (‖V‖ * ‖(taylorStepMatrixV2 m k p D)⁻¹‖) * ‖V⁻¹‖ := by
        gcongr
        · exact taylorV2Conj_norm_le m k p V
        · exact taylorV2Conj_norm_le m k p V⁻¹
    _ = _ := by ring

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
