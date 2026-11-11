/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Tactic

/-!
# Eigenvalue closure under cyclic block shifts

`cyclicSucc` indexes a cyclic shift of a finite family of vector spaces. For a linear
equivalence that sends each summand into its successor, `lemma4_2_eigenvalue_cyclic_closure`
proves that multiplication by an `n`th root of unity preserves eigenvalues.

This is the cyclic eigenvalue argument associated with Lemma 4.2 of [FreedmanLarsenWang2000].

## Main statements

* `pow_cyclicSucc`: Relate consecutive root-of-unity powers across the cyclic boundary.
* `lemma4_2_eigenvalue_cyclic_closure`: Rotate eigenvalues of a cyclic block-shifting
  equivalence.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Density

open DirectSum Module.End

/-- The successor of an index in `Fin n`, wrapping the last index to zero. -/
def cyclicSucc {n : ℕ} [NeZero n] (i : Fin n) : Fin n :=
  if h : (i : ℕ) + 1 < n then ⟨(i : ℕ) + 1, h⟩ else ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- Away from the cyclic boundary, the value of `cyclicSucc i` is `i + 1`. -/
@[simp] lemma cyclicSucc_val_of_lt {n : ℕ} [NeZero n] (i : Fin n)
    (h : (i : ℕ) + 1 < n) : (cyclicSucc i : ℕ) = (i : ℕ) + 1 := by
  simp [cyclicSucc, dif_pos h]

/-- At the cyclic boundary, the value of `cyclicSucc i` is zero. -/
@[simp] lemma cyclicSucc_val_of_not_lt {n : ℕ} [NeZero n] (i : Fin n)
    (h : ¬ (i : ℕ) + 1 < n) : (cyclicSucc i : ℕ) = 0 := by
  simp [cyclicSucc, dif_neg h]

/-- If `c^n = 1`, incrementing the exponent cyclically multiplies `c^i` by `c`. -/
lemma pow_cyclicSucc {n : ℕ} [NeZero n] {c : ℂ} (hc : c ^ n = 1) (i : Fin n) :
    c ^ (cyclicSucc i : ℕ) = c * c ^ (i : ℕ) := by
  by_cases h : (i : ℕ) + 1 < n
  · rw [cyclicSucc_val_of_lt i h, pow_succ]
    ring
  · rw [cyclicSucc_val_of_not_lt i h, pow_zero,
      show (i : ℕ) = n - 1 by have := i.isLt; omega, ← pow_succ',
      Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n)), hc]

/-- For a linear equivalence cyclically shifting `n` direct summands, multiplication by any
`n`th root of unity preserves eigenvalues, as in [Freedman et al., Lemma
4.2][FreedmanLarsenWang2000]. -/
theorem lemma4_2_eigenvalue_cyclic_closure {n : ℕ} [NeZero n]
    (W : Fin n → Type*) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (T : (⨁ i, W i) ≃ₗ[ℂ] (⨁ i, W i))
    (hT : ∀ (i : Fin n) (x : W i), ∃ y : W (cyclicSucc i),
      T (DirectSum.lof ℂ (Fin n) W i x)
        = DirectSum.lof ℂ (Fin n) W (cyclicSucc i) y)
    (ω : ℂ) (hω : ω ^ n = 1) :
    ∀ lam : ℂ, HasEigenvalue (T : Module.End ℂ (⨁ i, W i)) lam →
      HasEigenvalue (T : Module.End ℂ (⨁ i, W i)) (ω * lam) := by
  intro lam hlam

  set c : ℂ := ω⁻¹ with hc_def
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne n)] at hω
    exact zero_ne_one hω
  have hc : c ^ n = 1 := by
    rw [hc_def, inv_pow, hω, inv_one]
  have hc0 : c ≠ 0 := by
    rw [hc_def]
    exact inv_ne_zero hω0
  have hci0 : ∀ i : Fin n, c ^ (i : ℕ) ≠ 0 := fun i => pow_ne_zero _ hc0

  let S : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i) :=
    DirectSum.toModule ℂ (Fin n) (⨁ i, W i)
      (fun i => (DirectSum.lof ℂ (Fin n) W i).comp ((c ^ (i : ℕ)) • LinearMap.id))

  let Sinv : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i) :=
    DirectSum.toModule ℂ (Fin n) (⨁ i, W i)
      (fun i => (DirectSum.lof ℂ (Fin n) W i).comp (((c ^ (i : ℕ))⁻¹) • LinearMap.id))

  have hSlof : ∀ (j : Fin n) (z : W j),
      S (DirectSum.lof ℂ (Fin n) W j z)
        = DirectSum.lof ℂ (Fin n) W j (c ^ (j : ℕ) • z) := by
    intro j z
    simp [S]

  have hSinvlof : ∀ (j : Fin n) (z : W j),
      Sinv (DirectSum.lof ℂ (Fin n) W j z)
        = DirectSum.lof ℂ (Fin n) W j ((c ^ (j : ℕ))⁻¹ • z) := by
    intro j z
    simp [Sinv]

  have hSinvs : Sinv.comp S = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hSlof i x,
      hSinvlof i (c ^ (i : ℕ) • x), smul_smul, inv_mul_cancel₀ (hci0 i), one_smul]

  have hST : S.comp (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i))
      = c • ((T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)).comp S) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro x
    obtain ⟨y, hy⟩ := hT i x

    have hyM : (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) (DirectSum.lof ℂ (Fin n) W i x)
        = DirectSum.lof ℂ (Fin n) W (cyclicSucc i) y := by simpa using hy

    have hL : S ((T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) (DirectSum.lof ℂ (Fin n) W i x))
        = DirectSum.lof ℂ (Fin n) W (cyclicSucc i) (c ^ (cyclicSucc i : ℕ) • y) := by
      rw [hyM, hSlof (cyclicSucc i) y]

    have hR : c • (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) (S (DirectSum.lof ℂ (Fin n) W i x))
        = DirectSum.lof ℂ (Fin n) W (cyclicSucc i) (c ^ (cyclicSucc i : ℕ) • y) := by
      rw [hSlof i x]
      simp only [map_smul]
      rw [hyM, smul_smul, ← map_smul, ← pow_cyclicSucc hc i, map_smul]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [hL, hR]

  have hSinv_apply : ∀ v, Sinv (S v) = v := by
    intro v
    have := congrArg (fun L : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i) => L v) hSinvs
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this

  obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hlam
  have hxne : x ≠ 0 := (Module.End.hasEigenvector_iff.mp hx).2
  have hTx : (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) x = lam • x :=
    (Module.End.mem_eigenspace_iff).mp (Module.End.hasEigenvector_iff.mp hx).1

  have hSxne : S x ≠ 0 := by
    intro h0
    have hx0 : x = 0 := by rw [← hSinv_apply x, h0, map_zero]
    exact hxne hx0

  have hkey : S ((T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) x)
      = c • (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) (S x) := by
    have := congrArg (fun L : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i) => L x) hST
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using this
  rw [hTx, map_smul] at hkey

  have hTeq : (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) (S x) = (ω * lam) • S x := by
    have step : (c⁻¹ : ℂ) • (lam • S x)
        = (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)) (S x) := by
      rw [hkey, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [← step, smul_smul, show c⁻¹ = ω by rw [hc_def, inv_inv]]

  refine Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.mpr ⟨?_, hSxne⟩)
  exact (Module.End.mem_eigenspace_iff
    (f := (T : (⨁ i, W i) →ₗ[ℂ] (⨁ i, W i)))
    (μ := ω * lam) (x := S x)).mpr hTeq

end Qatlib.Papers.ModularFunct00.MainResults.Density
