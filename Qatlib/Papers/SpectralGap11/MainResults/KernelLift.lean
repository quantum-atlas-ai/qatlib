/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralGap11.MainResults.GroundLift
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The zero eigenspace of the actual penalty construction

The identity `B^2-delta*B=L(L+delta)(P-Q)^2` determines the kernel of
the two-projection penalty without assuming a simple ground eigenvalue.
-/

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Papers.SpectralGap11.MainResults.KernelLift

open Matrix
open scoped ComplexOrder

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The penalty matrix for an actual pair of ancilla projections. -/
def pairH (P Q : Matrix I I ℂ) (L delta : ℂ) : Matrix I I ℂ :=
  L • (Q - P) + delta • (1 - P)

/-- The exact polynomial identity that detects all zero modes of the penalty. -/
theorem pairH_square (P Q : Matrix I I ℂ) (L delta : ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q) :
    pairH P Q L delta * pairH P Q L delta - delta • pairH P Q L delta =
      (L * (L + delta)) • ((P - Q) * (P - Q)) := by
  simp only [pairH, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, one_mul, mul_one, hP, hQ]
  module

/-- The global kernel is precisely the intersection of the two projection
ranges. This handles arbitrarily degenerate ground spaces. -/
theorem pairH_kernel (P Q : Matrix I I ℂ) (L delta : ℂ)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (hPH : P.IsHermitian) (hQH : Q.IsHermitian)
    (hL : L ≠ 0) (hd : delta ≠ 0) (hLd : L + delta ≠ 0) (v : I → ℂ) :
    pairH P Q L delta *ᵥ v = 0 ↔ P *ᵥ v = v ∧ Q *ᵥ v = v := by
  constructor
  · intro hzero
    have hpoly := congrArg (fun A : Matrix I I ℂ => A *ᵥ v)
      (pairH_square P Q L delta hP hQ)
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hzero, Matrix.mulVec_zero,
      Matrix.smul_mulVec, hzero, smul_zero, sub_self, Matrix.smul_mulVec] at hpoly
    have hsquare : ((P - Q) * (P - Q)) *ᵥ v = 0 :=
      (smul_eq_zero.1 hpoly.symm).resolve_left (mul_ne_zero hL hLd)
    have hdiff : (P - Q) *ᵥ v = 0 :=
      (Matrix.conjTranspose_mul_self_mulVec_eq_zero (P - Q) v).1 (by
        rw [(hPH.sub hQH).eq]
        exact hsquare)
    have hpq : P *ᵥ v = Q *ᵥ v := by
      rw [Matrix.sub_mulVec] at hdiff
      exact sub_eq_zero.1 hdiff
    have hpen : delta • (v - P *ᵥ v) = 0 := by
      simpa only [pairH, Matrix.add_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, ← hpq, sub_self,
        smul_zero, zero_add] using hzero
    have hp : P *ᵥ v = v := (sub_eq_zero.1
      ((smul_eq_zero.1 hpen).resolve_left hd)).symm
    exact ⟨hp, hpq.symm.trans hp⟩
  · rintro ⟨hp, hq⟩
    simp only [pairH, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hp, hq, sub_self, smul_zero, add_zero]

end

end Qatlib.Papers.SpectralGap11.MainResults.KernelLift
