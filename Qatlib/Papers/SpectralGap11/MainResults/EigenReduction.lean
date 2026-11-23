/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.GapReduction

/-!
# The full operator eigenvalue reduction

An eigenvector of the actual full penalty matrix gives the characteristic
equation on its compressed input coordinates. No completeness of a list of
candidate output eigenvectors is assumed.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.EigenReduction

open Matrix
open KernelLift

noncomputable section

variable {I R : Type*} [Fintype I] [DecidableEq I] [Fintype R] [DecidableEq R]

/-- Projection onto the actual image of the input register embedding. -/
def imageP (J : Matrix R I ℂ) : Matrix R R ℂ := J * Jᴴ

/-- Its actual conjugate by the oracle involution. -/
def imageQ (J : Matrix R I ℂ) (U : Matrix R R ℂ) : Matrix R R ℂ :=
  U * imageP J * U

/-- The full penalty matrix associated to the actual embedding and oracle. -/
def fullPenalty (J : Matrix R I ℂ) (U : Matrix R R ℂ) (L delta : ℂ) : Matrix R R ℂ :=
  pairH (imageP J) (imageQ J U) L delta

omit [DecidableEq R] in
/-- Isometric input embedding gives a genuine projection. -/
theorem imageP_sq (J : Matrix R I ℂ) (hJ : Jᴴ * J = 1) :
    imageP J * imageP J = imageP J := by
  dsimp [imageP]
  calc
    (J * Jᴴ) * (J * Jᴴ) = J * (Jᴴ * J) * Jᴴ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ, Matrix.mul_one]

/-- Conjugating the physical projection by an involution preserves idempotence. -/
theorem imageQ_sq (J : Matrix R I ℂ) (U : Matrix R R ℂ)
    (hJ : Jᴴ * J = 1) (hU : U * U = 1) : imageQ J U * imageQ J U = imageQ J U := by
  let P := imageP J
  have hP : P * P = P := imageP_sq J hJ
  dsimp [imageQ]
  calc
    (U * imageP J * U) * (U * imageP J * U) =
        U * imageP J * (U * U) * imageP J * U := by simp only [Matrix.mul_assoc]
    _ = U * (imageP J * imageP J) * U := by
      rw [hU, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hP]

/-- The full penalty polynomial compresses to the input operator polynomial. -/
theorem compressed_penalty (J : Matrix R I ℂ) (U : Matrix R R ℂ)
    (L delta : ℂ) (hJ : Jᴴ * J = 1) (hU : U * U = 1) :
    Jᴴ * (fullPenalty J U L delta * fullPenalty J U L delta -
        delta • fullPenalty J U L delta) =
      (L * (L + delta)) •
        ((1 - (Jᴴ * U * J) * (Jᴴ * U * J)) * Jᴴ) := by
  rw [fullPenalty, pairH_square _ _ L delta (imageP_sq J hJ) (imageQ_sq J U hJ hU),
    Matrix.mul_smul]
  exact congrArg (fun A => (L * (L + delta)) • A)
    (GapReduction.compressed_square J U hJ hU)

/-- Every actual full-operator eigenvector obeys the reduced polynomial on
its actual compressed input state. -/
theorem eigen_polynomial (J : Matrix R I ℂ) (U : Matrix R R ℂ)
    (L delta mu : ℂ) (hJ : Jᴴ * J = 1) (hU : U * U = 1)
    (v : R → ℂ) (heigen : fullPenalty J U L delta *ᵥ v = mu • v) :
    (mu ^ 2 - delta * mu) • (Jᴴ *ᵥ v) =
      (L * (L + delta)) •
        ((1 - (Jᴴ * U * J) * (Jᴴ * U * J)) *ᵥ (Jᴴ *ᵥ v)) := by
  let B := fullPenalty J U L delta
  have hb2 : (B * B) *ᵥ v = mu ^ 2 • v := by
    rw [← Matrix.mulVec_mulVec, heigen, Matrix.mulVec_smul, heigen]
    simp only [smul_smul, pow_two]
  have hleft : Jᴴ *ᵥ ((B * B - delta • B) *ᵥ v) =
      (mu ^ 2 - delta * mu) • (Jᴴ *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hb2, heigen,
      Matrix.mulVec_sub, Matrix.mulVec_smul]
    simp only [Matrix.mulVec_smul]
    module
  have h := congrArg (fun A : Matrix I R ℂ => A *ᵥ v)
    (compressed_penalty J U L delta hJ hU)
  rw [← Matrix.mulVec_mulVec, hleft, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec] at h
  exact h

/-- Diagonalizing the actual compression turns every full-operator
eigenvector into the claimed characteristic equation in each input coordinate. -/
theorem eigen_coordinate (J : Matrix R I ℂ) (U : Matrix R R ℂ)
    (L delta mu : ℂ) (hJ : Jᴴ * J = 1) (hU : U * U = 1)
    (V : Matrix I I ℂ) (gamma : I → ℂ) (hVV : V * Vᴴ = 1)
    (hdiag : Vᴴ * (Jᴴ * U * J) * V = Matrix.diagonal gamma)
    (v : R → ℂ) (heigen : fullPenalty J U L delta *ᵥ v = mu • v) (j : I) :
    (mu ^ 2 - delta * mu) * (Vᴴ *ᵥ (Jᴴ *ᵥ v)) j =
      L * (L + delta) * (1 - gamma j ^ 2) * (Vᴴ *ᵥ (Jᴴ *ᵥ v)) j := by
  let A := Jᴴ * U * J
  let D := Matrix.diagonal gamma
  have hVA : Vᴴ * A = D * Vᴴ := by
    calc
      Vᴴ * A = (Vᴴ * A) * (V * Vᴴ) := by rw [hVV, Matrix.mul_one]
      _ = (Vᴴ * A * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = D * Vᴴ := by rw [hdiag]
  have hVAA : Vᴴ * (A * A) = (D * D) * Vᴴ := by
    calc
      Vᴴ * (A * A) = (Vᴴ * A) * A := (Matrix.mul_assoc Vᴴ A A).symm
      _ = (D * Vᴴ) * A := by rw [hVA]
      _ = D * (Vᴴ * A) := Matrix.mul_assoc D Vᴴ A
      _ = D * (D * Vᴴ) := by rw [hVA]
      _ = _ := (Matrix.mul_assoc D D Vᴴ).symm
  have hVpoly : Vᴴ * (1 - A * A) = (1 - D * D) * Vᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, hVAA, Matrix.sub_mul, Matrix.one_mul]
  have h := congrArg (fun x : I → ℂ => Vᴴ *ᵥ x)
    (eigen_polynomial J U L delta mu hJ hU v heigen)
  have haction (psi : I → ℂ) : Vᴴ *ᵥ ((1 - A * A) *ᵥ psi) =
      (1 - D * D) *ᵥ (Vᴴ *ᵥ psi) := by
    calc
      Vᴴ *ᵥ ((1 - A * A) *ᵥ psi) = (Vᴴ * (1 - A * A)) *ᵥ psi :=
        Matrix.mulVec_mulVec psi Vᴴ _
      _ = ((1 - D * D) * Vᴴ) *ᵥ psi := by rw [hVpoly]
      _ = _ := (Matrix.mulVec_mulVec psi _ Vᴴ).symm
  simp only [Matrix.mulVec_smul] at h
  rw [haction] at h
  have hj := congrFun h j
  simp only [D, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.diagonal_mul_diagonal, Matrix.mulVec_diagonal,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj
  convert hj using 1
  ring

/-- A full eigenvector with zero input compression belongs to one of the
two penalty-only sectors. Thus it cannot create an arbitrarily small gap. -/
theorem complementary_eigenvalue (J : Matrix R I ℂ) (U : Matrix R R ℂ)
    (L delta mu : ℂ) (hJ : Jᴴ * J = 1) (hU : U * U = 1) (hL : L ≠ 0)
    (v : R → ℂ) (hv : v ≠ 0) (hcompress : Jᴴ *ᵥ v = 0)
    (heigen : fullPenalty J U L delta *ᵥ v = mu • v) :
    mu = delta ∨ mu = L + delta := by
  let Q := imageQ J U
  have hQ : Q * Q = Q := imageQ_sq J U hJ hU
  have hPv : imageP J *ᵥ v = 0 := by
    rw [imageP, ← Matrix.mulVec_mulVec, hcompress, Matrix.mulVec_zero]
  have heq : L • (Q *ᵥ v) + delta • v = mu • v := by
    simpa only [fullPenalty, pairH, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, hPv, Matrix.one_mulVec, sub_zero] using heigen
  have hscaled : L • (Q *ᵥ v) = (mu - delta) • v := by
    calc
      L • (Q *ᵥ v) = (L • (Q *ᵥ v) + delta • v) - delta • v := by module
      _ = mu • v - delta • v := by rw [heq]
      _ = _ := by module
  let q := L⁻¹ * (mu - delta)
  have hQv : Q *ᵥ v = q • v := by
    have h := congrArg (fun x : R → ℂ => L⁻¹ • x) hscaled
    simpa only [smul_smul, inv_mul_cancel₀ hL, one_smul] using h
  have hid := congrArg (fun x : R → ℂ => Q *ᵥ x) hQv
  rw [Matrix.mulVec_mulVec, hQ, hQv, Matrix.mulVec_smul, hQv,
    smul_smul] at hid
  have hzero : (q * q - q) • v = 0 := by rw [sub_smul, ← hid, sub_self]
  have hq : q * q - q = 0 := (smul_eq_zero.1 hzero).resolve_right hv
  have hfactor : q * (q - 1) = 0 := by
    calc q * (q - 1) = q * q - q := by ring
      _ = 0 := hq
  rcases mul_eq_zero.1 hfactor with hq0 | hq1
  · left
    have hmu := (mul_eq_zero.1 hq0).resolve_left (inv_ne_zero hL)
    exact sub_eq_zero.1 hmu
  · right
    have hqone : q = 1 := sub_eq_zero.1 hq1
    have h := congrArg (fun x : ℂ => L * x) hqone
    dsimp [q] at h
    rw [← mul_assoc, mul_inv_cancel₀ hL, one_mul, mul_one] at h
    exact sub_eq_iff_eq_add.1 h

end

end Qatlib.Papers.SpectralGap11.MainResults.EigenReduction
