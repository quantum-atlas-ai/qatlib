/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.KernelLift
public import Qatlib.Papers.SpectralGap11.MainResults.InvariantBlocks

/-!
# Global compression and the numerical gap implication

The compressed square identity reduces an eigenvalue of the actual full
penalty operator to the input Hamiltonian's spectral coordinates. The real
inequality gives a gap around zero, rather than the distance between the
two lowest ordered eigenvalues.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.GapReduction

open Matrix
open InvariantBlocks

noncomputable section

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- Compression of the squared difference of the actual two projections. -/
theorem compressed_square (J : Matrix R I ℂ) (U : Matrix R R ℂ)
    (hJ : Jᴴ * J = 1) (hU : U * U = 1) :
    Jᴴ * ((J * Jᴴ - U * (J * Jᴴ) * U) *
        (J * Jᴴ - U * (J * Jᴴ) * U)) =
      (1 - (Jᴴ * U * J) * (Jᴴ * U * J)) * Jᴴ := by
  let P := J * Jᴴ
  let Q := U * P * U
  let A := Jᴴ * U * J
  have hP : P * P = P := by
    dsimp [P]
    calc
      (J * Jᴴ) * (J * Jᴴ) = J * (Jᴴ * J) * Jᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.mul_one]
  have hQ : Q * Q = Q := by
    dsimp [Q]
    calc
      (U * P * U) * (U * P * U) = U * P * (U * U) * P * U := by
        simp only [Matrix.mul_assoc]
      _ = U * (P * P) * U := by
        rw [hU, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP]
  have hJP : Jᴴ * P = Jᴴ := by
    dsimp [P]
    rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have hJPQ : Jᴴ * (P * Q) = Jᴴ * Q := by
    rw [← Matrix.mul_assoc, hJP]
  have hJQP : Jᴴ * (Q * P) = (A * A) * Jᴴ := by
    dsimp [Q, P, A]
    simp only [Matrix.mul_assoc]
  have hdiff : (P - Q) * (P - Q) = P - P * Q - Q * P + Q := by
    simp only [sub_mul, mul_sub, hP, hQ]
    module
  change Jᴴ * ((P - Q) * (P - Q)) = (1 - A * A) * Jᴴ
  rw [hdiff, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_sub, hJP, hJPQ, hJQP,
    Matrix.sub_mul, Matrix.one_mul]
  module

/-- The characteristic equation of every positive-input block forces the
same square-root gap, with a fixed constant independent of that eigenvalue. -/
theorem characteristic_gap (lambda L delta mu : ℝ) (hL : 0 < L)
    (hlambda : 0 < lambda) (hmax : lambda ≤ L) (hd : 0 ≤ delta)
    (hsmall : delta ^ 2 ≤ lambda * L)
    (hpoly : mu ^ 2 - delta * mu =
      L * (L + delta) * (1 - (1 - lambda / L) ^ 2)) :
    Real.sqrt (lambda * L) / 2 ≤ |mu| := by
  have hnorm := lazy_norm lambda L hL hlambda.le hmax
  have hsine : 1 - lazyCos lambda L ^ 2 = lazySin lambda L ^ 2 := by linarith
  change mu ^ 2 - delta * mu =
    L * (L + delta) * (1 - lazyCos lambda L ^ 2) at hpoly
  rw [hsine] at hpoly
  have hg := (div_le_iff₀ hL).1 (lazy_gain lambda L hL hlambda.le hmax)
  have hcoef : lambda * L ≤ L * (L + delta) * lazySin lambda L ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hg hL.le
    have hp : 0 ≤ L * delta * lazySin lambda L ^ 2 := by positivity
    nlinarith only [hm, hp]
  have hmu : lambda * L ≤ mu ^ 2 - delta * mu := by linarith
  have hrpos : 0 < Real.sqrt (lambda * L) := Real.sqrt_pos.2 (mul_pos hlambda hL)
  have hrsq := Real.sq_sqrt (mul_pos hlambda hL).le
  have hdelta : delta ≤ Real.sqrt (lambda * L) := by
    nlinarith only [hsmall, hrsq, hd, hrpos]
  by_contra hnot
  have habs : |mu| < Real.sqrt (lambda * L) / 2 := lt_of_not_ge hnot
  have hmul := mul_le_mul_of_nonneg_left (neg_abs_le mu) hd
  have hmul2 := mul_le_mul_of_nonneg_right hdelta (abs_nonneg mu)
  have hmusq : mu ^ 2 = |mu| ^ 2 := (sq_abs mu).symm
  nlinarith [abs_nonneg mu]

end

end Qatlib.Papers.SpectralGap11.MainResults.GapReduction
