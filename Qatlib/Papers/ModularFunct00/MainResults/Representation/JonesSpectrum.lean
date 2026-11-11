/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Spectrum of a Jones generator from an idempotent

`jonesGen q e` is the endomorphism `q • 1 - (1 + q) • e`. For an idempotent `e`, the module
proves its quadratic relation, inverse formula, and eigenvalue restrictions.

When `q ≠ -1`, its two eigenspaces identify with the kernel and fixed subspace of `e`; their
dimensions add to the ambient dimension in finite dimensions. These are the spectral
calculations used for Jones generators in [FreedmanLarsenWang2000].

## Main statements

* `jonesGen_quadratic`: The generator satisfies a quadratic relation with roots `q` and `-1`.
* `eigenspace_jonesGen_q`: Identify the `q` eigenspace with the kernel of the idempotent.
* `finrank_eigenspace_jonesGen`: The two eigenspace dimensions sum to the ambient dimension.

## References

* [Freedman et al., 2000][FreedmanLarsenWang2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ModularFunct00.MainResults.Representation

open Module
open Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The Jones endomorphism `q • 1 - (1 + q) • e` associated with a scalar `q` and an
endomorphism `e`. -/
def jonesGen (q : ℂ) (e : Module.End ℂ V) : Module.End ℂ V :=
  q • (1 : Module.End ℂ V) - (1 + q) • e

/-- Applying `jonesGen q e` to `x` gives `q • x - (1 + q) • e x`. -/
@[simp] lemma jonesGen_apply (q : ℂ) (e : Module.End ℂ V) (x : V) :
    jonesGen q e x = q • x - (1 + q) • e x := by
  simp [jonesGen]

/-- If `e` is idempotent, `jonesGen q e` satisfies `(jonesGen q e - q • 1) * (jonesGen q e + 1)
= 0`; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_quadratic (q : ℂ) (e : Module.End ℂ V) (he : e * e = e) :
    (jonesGen q e - q • (1 : Module.End ℂ V)) * (jonesGen q e + 1) = 0 := by
  have hee : ∀ x : V, e (e x) = e x := fun x => by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f x) he
  ext x
  have hx1 : (1 + q) • x = q • x + x := by module
  have hY : (jonesGen q e + 1) x = (1 + q) • (x - e x) := by
    rw [LinearMap.add_apply, Module.End.one_apply, jonesGen_apply, smul_sub, hx1]
    abel
  rw [Module.End.mul_apply, hY]
  have heY : e ((1 + q) • (x - e x)) = 0 := by
    rw [map_smul, map_sub, hee, sub_self, smul_zero]
  rw [LinearMap.sub_apply, jonesGen_apply, heY, smul_zero, sub_zero,
    LinearMap.smul_apply, Module.End.one_apply, sub_self, LinearMap.zero_apply]

/-- Every eigenvalue of a Jones generator associated with an idempotent is either `q` or `-1`;
see [FreedmanLarsenWang2000]. -/
theorem jonesGen_eigenvalue_mem (q : ℂ) (e : Module.End ℂ V) (he : e * e = e)
    {μ : ℂ} (hμ : HasEigenvalue (jonesGen q e) μ) : μ = q ∨ μ = -1 := by
  obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
  have hx' := Module.End.hasEigenvector_iff.mp hx
  have hxne : x ≠ 0 := hx'.2
  have hMx : jonesGen q e x = μ • x := (Module.End.mem_eigenspace_iff).mp hx'.1
  have hquad : (jonesGen q e - q • (1 : Module.End ℂ V))
      ((jonesGen q e + 1) x) = 0 := by
    have := congrArg (fun f : Module.End ℂ V => f x) (jonesGen_quadratic q e he)
    simpa using this
  have h1 : (jonesGen q e + 1) x = (μ + 1) • x := by
    rw [LinearMap.add_apply, Module.End.one_apply, hMx, add_smul, one_smul]
  have h2 : (jonesGen q e - q • (1 : Module.End ℂ V)) x = (μ - q) • x := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hMx,
      sub_smul]
  rw [h1, map_smul, h2, smul_smul] at hquad
  have hprod : (μ + 1) * (μ - q) = 0 := by
    rcases smul_eq_zero.mp hquad with h | h
    · exact h
    · exact absurd h hxne
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inr (by linear_combination h)
  · exact Or.inl (by linear_combination h)

/-- If `q ≠ -1`, the `q` eigenspace of `jonesGen q e` is the kernel of `e`; see
[FreedmanLarsenWang2000]. -/
theorem eigenspace_jonesGen_q (q : ℂ) (e : Module.End ℂ V) (hq : q ≠ -1) :
    eigenspace (jonesGen q e) q = LinearMap.ker e := by
  ext x
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  constructor
  · intro h
    have h' : q • x - (1 + q) • e x = q • x := h
    have h0 : (1 + q) • e x = 0 := sub_eq_self.mp h'
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (by
        intro hzero
        exact hq (by linear_combination hzero))
    · exact h1
  · intro h
    rw [jonesGen_apply, h, smul_zero, sub_zero]

/-- If `e` is idempotent and `q ≠ -1`, the `-1` eigenspace of `jonesGen q e` is the fixed
subspace `LinearMap.ker (e - 1)`; see [FreedmanLarsenWang2000]. -/
theorem eigenspace_jonesGen_neg_one (q : ℂ) (e : Module.End ℂ V) (he : e * e = e)
    (hq : q ≠ -1) :
    eigenspace (jonesGen q e) (-1) = LinearMap.ker (e - 1) := by
  have hq' : (1 + q) ≠ 0 := by
    intro h0
    exact hq (by linear_combination h0)
  ext x
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker, LinearMap.sub_apply,
    Module.End.one_apply, sub_eq_zero]
  constructor
  · intro h
    have h' : q • x - (1 + q) • e x = (-1 : ℂ) • x := h
    rw [neg_one_smul] at h'
    have h3 : q • x = -x + (1 + q) • e x := sub_eq_iff_eq_add.mp h'
    have h4 : q • x + x = (1 + q) • x := by module
    have h5 : q • x + x = (1 + q) • e x := by
      rw [h3]
      abel
    have key : (1 + q) • e x = (1 + q) • x := by
      rw [← h4, h5]
    have hxe : e x = x := by
      have hinj := congrArg (fun y : V => (1 + q)⁻¹ • y) key
      simpa [smul_smul, inv_mul_cancel₀ hq'] using hinj
    exact hxe
  · intro h
    rw [jonesGen_apply, h, neg_one_smul]
    module

/-- For idempotent `e` and nonzero `q`, multiplying `jonesGen q e` by `jonesGen q⁻¹ e` gives the
identity; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_mul_inv (q : ℂ) (e : Module.End ℂ V) (he : e * e = e) (hq : q ≠ 0) :
    jonesGen q e * jonesGen q⁻¹ e = 1 := by
  have hee : ∀ x : V, e (e x) = e x := fun x => by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f x) he
  have hcoef : q * (1 + q⁻¹) = 1 + q := by
    have := mul_inv_cancel₀ hq
    linear_combination this
  ext x
  rw [Module.End.mul_apply, Module.End.one_apply]
  have hY : e (jonesGen q⁻¹ e x) = - e x := by
    rw [jonesGen_apply, map_sub, map_smul, map_smul, hee, ← sub_smul,
      show q⁻¹ - (1 + q⁻¹) = -1 by ring, neg_one_smul]
  have hinner : jonesGen q⁻¹ e x = q⁻¹ • x - (1 + q⁻¹) • e x := by
    rw [jonesGen_apply]
  rw [jonesGen_apply, hY, hinner, smul_sub, smul_smul, smul_smul, smul_neg,
    mul_inv_cancel₀ hq, one_smul, hcoef]
  module

/-- For idempotent `e` and nonzero `q`, multiplying `jonesGen q⁻¹ e` by `jonesGen q e` gives the
identity; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_inv_mul (q : ℂ) (e : Module.End ℂ V) (he : e * e = e) (hq : q ≠ 0) :
    jonesGen q⁻¹ e * jonesGen q e = 1 := by
  have hq' : q⁻¹ ≠ 0 := inv_ne_zero hq
  have h := jonesGen_mul_inv (q := q⁻¹) e he hq'
  rwa [inv_inv] at h

/-- The range of an idempotent endomorphism is its fixed subspace. -/
lemma range_eq_ker_sub_one (e : Module.End ℂ V) (he : e * e = e) :
    LinearMap.range e = LinearMap.ker (e - 1) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f y) he
  · intro hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    exact ⟨x, hx⟩

/-- In finite dimensions, for idempotent `e` and `q ≠ -1`, the dimensions of the `q` and `-1`
eigenspaces sum to the ambient dimension; see [FreedmanLarsenWang2000]. -/
theorem finrank_eigenspace_jonesGen (q : ℂ) (e : Module.End ℂ V)
    [FiniteDimensional ℂ V] (he : e * e = e) (hq : q ≠ -1) :
    finrank ℂ (eigenspace (jonesGen q e) q) +
        finrank ℂ (eigenspace (jonesGen q e) (-1)) = finrank ℂ V := by
  rw [eigenspace_jonesGen_q q e hq, eigenspace_jonesGen_neg_one q e he hq,
    ← range_eq_ker_sub_one e he, add_comm]
  exact LinearMap.finrank_range_add_finrank_ker e

/-- If an idempotent is neither zero nor the identity, its Jones generator possesses both `q`
and `-1` as eigenvalues; see [FreedmanLarsenWang2000]. -/
theorem jonesGen_hasEigenvalue_both (q : ℂ) (e : Module.End ℂ V) (he : e * e = e)
    (hne0 : e ≠ 0) (hne1 : e ≠ 1) :
    HasEigenvalue (jonesGen q e) q ∧ HasEigenvalue (jonesGen q e) (-1) := by
  have hee : ∀ x : V, e (e x) = e x := fun x => by
    simpa [Module.End.mul_apply] using congrArg (fun f : Module.End ℂ V => f x) he
  constructor
  · obtain ⟨x, hx⟩ : ∃ x : V, e x ≠ x := by
      by_contra h
      push_neg at h
      exact hne1 (by ext x; exact h x)
    have hne : x - e x ≠ 0 := by
      intro hzero
      exact hx (sub_eq_zero.mp hzero).symm
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨?_, hne⟩)
    rw [Module.End.mem_eigenspace_iff, jonesGen_apply]
    have hker : e (x - e x) = 0 := by
      rw [map_sub, hee, sub_self]
    rw [hker, smul_zero, sub_zero]
  · obtain ⟨x, hx⟩ : ∃ x : V, e x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne0 (by ext x; exact h x)
    refine Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨?_, hx⟩)
    rw [Module.End.mem_eigenspace_iff, jonesGen_apply, hee, neg_one_smul]
    module

end Qatlib.Papers.ModularFunct00.MainResults.Representation
