/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

set_option autoImplicit false

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- For invertible `G` and `C` with `C` commuting with `P`, the kernel of `Gi * P * Gi` is the
image of the kernel of `P` under `G * C`. -/
theorem correctedLocal_zero_iff
    (P G Gi C Ci : Matrix n n ℂ)
    (hGGi : G * Gi = 1) (hGiG : Gi * G = 1)
    (hCCi : C * Ci = 1) (hCiC : Ci * C = 1)
    (hCP : Commute C P) (x : n → ℂ) :
    (Gi * P * Gi) *ᵥ x = 0 ↔
      ∃ y : n → ℂ, P *ᵥ y = 0 ∧ (G * C) *ᵥ y = x := by
  have hPCi : P * Ci = Ci * P := by
    calc
      P * Ci = Ci * (C * P) * Ci := by
        simp only [← mul_assoc, hCiC, one_mul]
      _ = Ci * (P * C) * Ci := by rw [hCP.eq]
      _ = Ci * P := by simp only [mul_assoc, hCCi, mul_one]
  constructor
  · intro hx
    have hP : P *ᵥ (Gi *ᵥ x) = 0 := by
      have hx' := congrArg (fun v : n → ℂ => G *ᵥ v) hx
      simpa only [Matrix.mulVec_mulVec, ← mul_assoc, hGGi, one_mul,
        Matrix.mulVec_zero] using hx'
    refine ⟨Ci *ᵥ (Gi *ᵥ x), ?_, ?_⟩
    · calc
        P *ᵥ (Ci *ᵥ (Gi *ᵥ x)) = (P * Ci) *ᵥ (Gi *ᵥ x) :=
          Matrix.mulVec_mulVec (Gi *ᵥ x) P Ci
        _ = (Ci * P) *ᵥ (Gi *ᵥ x) := by rw [hPCi]
        _ = Ci *ᵥ (P *ᵥ (Gi *ᵥ x)) :=
          (Matrix.mulVec_mulVec (Gi *ᵥ x) Ci P).symm
        _ = 0 := by rw [hP, Matrix.mulVec_zero]
    · calc
        (G * C) *ᵥ (Ci *ᵥ (Gi *ᵥ x)) =
            G *ᵥ ((C * Ci) *ᵥ (Gi *ᵥ x)) := by
          simp only [Matrix.mulVec_mulVec, mul_assoc]
        _ = G *ᵥ (Gi *ᵥ x) := by rw [hCCi, Matrix.one_mulVec]
        _ = x := by rw [Matrix.mulVec_mulVec, hGGi, Matrix.one_mulVec]
  · rintro ⟨y, hy, hxy⟩
    calc
      (Gi * P * Gi) *ᵥ x = (Gi * P * Gi) *ᵥ ((G * C) *ᵥ y) := by
        rw [hxy]
      _ = (Gi * P) *ᵥ ((Gi * G) *ᵥ (C *ᵥ y)) := by
        simp only [Matrix.mulVec_mulVec, mul_assoc]
      _ = (Gi * P) *ᵥ (C *ᵥ y) := by rw [hGiG, Matrix.one_mulVec]
      _ = Gi *ᵥ ((C * P) *ᵥ y) := by
        simp only [Matrix.mulVec_mulVec, mul_assoc, hCP.eq]
      _ = Gi *ᵥ (C *ᵥ (P *ᵥ y)) := by rw [Matrix.mulVec_mulVec y C P]
      _ = 0 := by rw [hy, Matrix.mulVec_zero, Matrix.mulVec_zero]

end Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels
