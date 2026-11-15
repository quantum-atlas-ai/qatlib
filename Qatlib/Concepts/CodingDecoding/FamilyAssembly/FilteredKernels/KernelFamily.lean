/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels.KernelTransport

@[expose] public section

set_option autoImplicit false

set_option autoImplicit false

namespace Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels

open scoped Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Under the stated invertibility, commutation, and common factorization assumptions, the
common kernel of the corrected operators is the image under `F` of the common kernel of `P`. -/
theorem correctedFamily_zero_iff {ι : Type*}
    (P G Gi C Ci : ι → Matrix n n ℂ) (F Fi : Matrix n n ℂ)
    (hGGi : ∀ i, G i * Gi i = 1) (hGiG : ∀ i, Gi i * G i = 1)
    (hCCi : ∀ i, C i * Ci i = 1) (hCiC : ∀ i, Ci i * C i = 1)
    (hCP : ∀ i, Commute (C i) (P i))
    (hFactor : ∀ i, G i * C i = F)
    (hFFi : F * Fi = 1) (hFiF : Fi * F = 1) (x : n → ℂ) :
    (∀ i, (Gi i * P i * Gi i) *ᵥ x = 0) ↔
      ∃ y : n → ℂ, (∀ i, P i *ᵥ y = 0) ∧ F *ᵥ y = x := by
  constructor
  · intro hx
    refine ⟨Fi *ᵥ x, ?_, ?_⟩
    · intro i
      rcases (correctedLocal_zero_iff (P i) (G i) (Gi i) (C i) (Ci i)
        (hGGi i) (hGiG i) (hCCi i) (hCiC i) (hCP i) x).mp (hx i) with
        ⟨y, hy, hxy⟩
      have hFy : F *ᵥ y = x := by simpa only [hFactor i] using hxy
      have hy_eq : Fi *ᵥ x = y := by
        rw [← hFy, Matrix.mulVec_mulVec, hFiF, Matrix.one_mulVec]
      rw [hy_eq]
      exact hy
    · rw [Matrix.mulVec_mulVec, hFFi, Matrix.one_mulVec]
  · rintro ⟨y, hy, hFy⟩ i
    apply (correctedLocal_zero_iff (P i) (G i) (Gi i) (C i) (Ci i)
      (hGGi i) (hGiG i) (hCCi i) (hCiC i) (hCP i) x).mpr
    refine ⟨y, hy i, ?_⟩
    rw [hFactor i]
    exact hFy

end Qatlib.Concepts.CodingDecoding.FamilyAssembly.FilteredKernels
