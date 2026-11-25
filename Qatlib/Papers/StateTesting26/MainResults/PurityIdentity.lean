/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.Model.StateModel
public import Qatlib.Papers.StateTesting26.MainResults.SwapObservable

@[expose] public section

/-!
# Purity as the maximally mixed purity plus a Hilbert--Schmidt distance

Equation (1.8) of the paper decomposes the purity of a `d`-level state as
`tr(ρ²) = 1/d + ‖ρ − ρ_mm‖₂²`, where `ρ_mm = I/d` is the maximally mixed state and
`‖ρ − ρ_mm‖₂² = tr((ρ − ρ_mm)²)` is the squared Hilbert--Schmidt distance of the model layer
(`Qatlib.Papers.StateTesting26.MainResults.Model.hsSqDist`).

The two ingredients are the trace normalisation `tr ρ = 1` of a density matrix and the elementary
matrix identity `tr((ρ − I/d)²) = tr(ρ²) − 2/d + 1/d`. Both are proved here at the level of the
matrices of the model layer, so the statement is a genuine identity about states and not a
restatement of its own right-hand side. No positivity of `ρ` is used beyond the packaged trace
normalisation of `MState`.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Eqs. (1.8) and (4.4)–(4.8).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.StateTesting26.MainResults
open Qatlib.Papers.StateTesting26.MainResults

open Qatlib.Papers.StateTesting26.MainResults.Model

/-- Purity `tr ρ²` read in the reals is the real part of the complex trace `tr(ρ²)`. -/
theorem purityReal_eq_re_trace_mul {d : ℕ} (ρ : QState d) :
    purityReal ρ = ((ρ.m * ρ.m).trace).re := by
  rw [purityReal, MState.purity, MState.val_inner, HermitianMat.inner_eq_re_trace]
  rfl

/-- **Two-copy trace**: `tr(ρ ⊗ ρ) = (tr ρ)²` for the model layer's `tensorPowerMat`. -/
theorem trace_tensorPowerMat_two {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) :
    (tensorPowerMat A 2).trace = A.trace * A.trace := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, tensorPowerMat, Fin.prod_univ_two]
  rw [sum_finTwoArrow_eq_sum_prod (f := fun p : Fin d × Fin d => A p.1 p.1 * A p.2 p.2)]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- The maximally mixed state of the model layer is the scalar matrix `I/d`. -/
theorem maximallyMixed_m_eq_scalar (d : ℕ) (hd : 0 < d) :
    (maximallyMixed d hd).m = Matrix.scalar (Fin d) ((d : ℝ)⁻¹ : ℂ) := by
  simp only [maximallyMixed, MState.uniform, MState.m, MState.coe_ofClassical,
    HermitianMat.diagonal_mat]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal, ProbDistribution.uniform_def, Fintype.card_fin,
    one_div]

/-- `1/d` and `d` are inverse to each other in `ℂ` for a positive dimension. -/
theorem inv_card_mul_card (d : ℕ) (hd : 0 < d) :
    ((d : ℝ)⁻¹ : ℂ) * (d : ℂ) = 1 := by
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
  have h : ((d : ℝ)⁻¹ * (d : ℝ) : ℝ) = 1 := inv_mul_cancel₀ hdR
  calc ((d : ℝ)⁻¹ : ℂ) * (d : ℂ)
      = (((d : ℝ)⁻¹ * (d : ℝ) : ℝ) : ℂ) := by push_cast; ring
    _ = 1 := by rw [h, Complex.ofReal_one]

/-- Right multiplication by `ρ_mm = I/d` rescales a matrix by `1/d`. -/
theorem mul_maximallyMixed {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    A * (maximallyMixed d hd).m = ((d : ℝ)⁻¹ : ℂ) • A := by
  rw [maximallyMixed_m_eq_scalar, Matrix.scalar_apply]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
  simp [mul_comm]

/-- Left multiplication by `ρ_mm = I/d` rescales a matrix by `1/d`. -/
theorem maximallyMixed_mul {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℂ) :
    (maximallyMixed d hd).m * A = ((d : ℝ)⁻¹ : ℂ) • A := by
  rw [maximallyMixed_m_eq_scalar, Matrix.scalar_apply]
  ext i j
  rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]

/-- The square of `ρ_mm = I/d` is the scalar matrix `I/d²`. -/
theorem maximallyMixed_mul_self (d : ℕ) (hd : 0 < d) :
    (maximallyMixed d hd).m * (maximallyMixed d hd).m
      = Matrix.scalar (Fin d) (((d : ℝ)⁻¹ : ℂ) * ((d : ℝ)⁻¹ : ℂ)) := by
  rw [maximallyMixed_m_eq_scalar]
  exact (map_mul (Matrix.scalar (Fin d)) ((d : ℝ)⁻¹ : ℂ) ((d : ℝ)⁻¹ : ℂ)).symm

/-- The trace of the scalar matrix `I/d²` is `1/d`. -/
theorem trace_scalar_inv_sq (d : ℕ) (hd : 0 < d) :
    (Matrix.scalar (Fin d) (((d : ℝ)⁻¹ : ℂ) * ((d : ℝ)⁻¹ : ℂ))).trace = ((d : ℝ)⁻¹ : ℂ) := by
  rw [Matrix.scalar_apply, Matrix.trace_diagonal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_comm (d : ℂ) ((d : ℝ)⁻¹ : ℂ), inv_card_mul_card d hd, one_mul]

/-- The squared difference to `I/d` in trace form: `tr((ρ − I/d)²) = tr(ρ²) − 1/d`. -/
theorem trace_sq_sub_maximallyMixed {d : ℕ} (hd : 0 < d) (ρ : QState d) :
    ((ρ.m - (maximallyMixed d hd).m) * (ρ.m - (maximallyMixed d hd).m)).trace
      = (ρ.m * ρ.m).trace - ((d : ℝ)⁻¹ : ℂ) := by
  have htr : ρ.m.trace = 1 := MState.tr' ρ
  have hexp : (ρ.m - (maximallyMixed d hd).m) * (ρ.m - (maximallyMixed d hd).m)
      = ρ.m * ρ.m - ((d : ℝ)⁻¹ : ℂ) • ρ.m - ((d : ℝ)⁻¹ : ℂ) • ρ.m
        + Matrix.scalar (Fin d) (((d : ℝ)⁻¹ : ℂ) * ((d : ℝ)⁻¹ : ℂ)) := by
    rw [sub_mul, mul_sub, mul_sub, mul_maximallyMixed hd, maximallyMixed_mul hd,
      maximallyMixed_mul_self]
    module
  rw [hexp]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul, htr,
    trace_scalar_inv_sq d hd, smul_eq_mul, mul_one]
  ring

/-- **Equation (1.8)**: `tr ρ² = 1/d + ‖ρ − ρ_mm‖₂²`, the purity of a `d`-level state written as
the maximally mixed purity plus the squared Hilbert--Schmidt distance to `ρ_mm = I/d`. -/
theorem purityReal_eq_inv_card_add_hsSqDist {d : ℕ} (hd : 0 < d) (ρ : QState d) :
    purityReal ρ = (d : ℝ)⁻¹ + hsSqDist ρ (maximallyMixed d hd) := by
  have hre : hsSqDist ρ (maximallyMixed d hd) = ((ρ.m * ρ.m).trace).re - (d : ℝ)⁻¹ := by
    rw [hsSqDist, trace_sq_sub_maximallyMixed hd ρ]
    simp
  rw [hre, purityReal_eq_re_trace_mul]
  ring

end Qatlib.Papers.StateTesting26.MainResults
