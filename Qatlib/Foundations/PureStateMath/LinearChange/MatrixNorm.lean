/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # The actual complex unit-ball supremum and the Euclidean operator norm

Demand: LinearOptics10 Lemma 64 and Corollary 65. The historical norm
definition is retained, and its full finite-dimensional Euclidean norm
transport is proved rather than substituting the entrywise matrix norm.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Qatlib.Foundations.PureStateMath.LinearChange.MatrixNorm

/-- The exact historical spectral norm as the supremum over the actual squared-mass unit ball. -/
def matOpNorm {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin n → ℂ, (∑ i, Complex.normSq (v i)) ≤ 1 ∧
    r = Real.sqrt (∑ i, Complex.normSq ((V *ᵥ v) i))}

/-- The actual complex coefficient-vector norm is the square root of its squared-mass sum. -/
theorem vectorNorm {n : ℕ} (v : Fin n → ℂ) :
    ‖WithLp.toLp 2 v‖ = Real.sqrt (∑ i, Complex.normSq (v i)) := by
  simp only [PiLp.norm_eq_of_L2, Complex.normSq_eq_norm_sq]

/-- The actual source unit-ball condition is exactly the closed Euclidean unit-ball condition. -/
theorem unitBall {n : ℕ} (v : Fin n → ℂ) :
    (∑ i, Complex.normSq (v i)) ≤ 1 ↔ ‖WithLp.toLp 2 v‖ ≤ 1 := by
  rw [vectorNorm, Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

/-- The entire actual supremum definition equals the genuine Euclidean continuous operator norm. -/
theorem asNorm {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) :
    matOpNorm V = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) V‖ := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) V
  have hs : {r : ℝ | ∃ v : Fin n → ℂ, (∑ i, Complex.normSq (v i)) ≤ 1 ∧
      r = Real.sqrt (∑ i, Complex.normSq ((V *ᵥ v) i))} =
      (fun x : EuclideanSpace ℂ (Fin n) => ‖A x‖) '' Metric.closedBall 0 1 := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨WithLp.toLp 2 v, ?_, ?_⟩
      · exact mem_closedBall_zero_iff.mpr ((unitBall v).mp hv)
      · simp only [A, Matrix.toEuclideanCLM_toLp, vectorNorm]
    · rintro ⟨v, hv, rfl⟩
      refine ⟨WithLp.ofLp v, (unitBall _).mpr ?_, ?_⟩
      · simpa only [WithLp.toLp_ofLp] using mem_closedBall_zero_iff.mp hv
      · have he := vectorNorm (V *ᵥ WithLp.ofLp v)
        simpa only [A, ← Matrix.ofLp_toEuclideanCLM, WithLp.toLp_ofLp] using he
  unfold matOpNorm
  rw [hs]
  exact A.sSup_unitClosedBall_eq_norm

/-- The actual source operator norm is nonnegative in every finite dimension. -/
theorem normNonneg {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ matOpNorm V := by
  rw [asNorm]
  exact norm_nonneg _

/-- The actual source operator norm controls every actual complex matrix-vector action. -/
theorem actionBound {n : ℕ} (V : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    Real.sqrt (∑ i, Complex.normSq ((V *ᵥ v) i)) ≤
      matOpNorm V * Real.sqrt (∑ i, Complex.normSq (v i)) := by
  rw [asNorm, ← vectorNorm v, ← vectorNorm (V *ᵥ v), ← Matrix.toEuclideanCLM_toLp]
  exact ContinuousLinearMap.le_opNorm _ _

end Qatlib.Foundations.PureStateMath.LinearChange.MatrixNorm
