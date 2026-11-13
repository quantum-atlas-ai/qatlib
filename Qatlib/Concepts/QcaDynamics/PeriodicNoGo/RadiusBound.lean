/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.PeriodicNoGo.FiniteKernel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Qatlib.Concepts.QcaDynamics.PeriodicNoGo.KernelTransport

/-!
# Radius bounds for periodic scalar dynamics

Proves injectivity of residue maps on integer difference boxes when every coordinate period is
greater than four times the neighborhood radius. This gives a concrete `KernelNonalias`
criterion and reduces unitary periodic scalar updates to a phase times a translation, following
the scalar obstruction of [Meyer1996].

## Main statements

* `radius_kernel_nonalias`: derives nonaliasing from coordinate period bounds.
* `periodic_radius_noGo`: gives the phase-translation conclusion for quotient weights.
* `periodic_radius_matrix_noGo`: gives the conclusion directly from matrix unitarity.

## References

* [Meyer, 1996][Meyer1996]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section
open Matrix
open Qatlib.Concepts.QcaDynamics.ScalarNoGo
namespace Qatlib.Concepts.QcaDynamics.PeriodicNoGo

/-- Reduction modulo `n` is injective on the integers from `-2r` to `2r` when `4 * r < n`. -/
theorem residue_injective_on_difference_box (n r : ℕ) (hn : 4*r<n)
    (x y : ℤ) (hx : -(2*(r:ℤ)) ≤ x ∧ x ≤ 2*(r:ℤ))
    (hy : -(2*(r:ℤ)) ≤ y ∧ y ≤ 2*(r:ℤ))
    (h : (x:ZMod n) = (y:ZMod n)) : x=y := by
  have hdvd : (n:ℤ) ∣ y-x := (ZMod.intCast_eq_intCast_iff_dvd_sub x y n).mp h
  have hn' : (4:ℤ)*r<n := by exact_mod_cast hn
  by_cases hxy : x≤y
  · have hz : y-x=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdvd
    omega
  · have hdvd' : (n:ℤ) ∣ x-y := by simpa only [neg_sub] using dvd_neg.mpr hdvd
    have hz : x-y=0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) (by omega) hdvd'
    omega

/-- Coordinatewise reduction is injective on the integer box from `-2r` to `2r` when each
coordinate period exceeds `4 * r`. -/
theorem product_residue_injective_on_difference_box (d r : ℕ) (n : Fin d → ℕ)
    (hn : ∀i,4*r<n i) (x y : Fin d → ℤ)
    (hx : ∀i, -(2*(r:ℤ)) ≤ x i ∧ x i ≤ 2*(r:ℤ))
    (hy : ∀i, -(2*(r:ℤ)) ≤ y i ∧ y i ≤ 2*(r:ℤ))
    (h : ∀i,(x i:ZMod (n i)) = (y i:ZMod (n i))) : x=y := by
  funext i
  exact residue_injective_on_difference_box (n i) r (hn i) (x i) (y i) (hx i) (hy i) (h i)

/-- The additive homomorphism reducing each integer coordinate modulo its specified period. -/
def residueHom (d : ℕ) (n : Fin d → ℕ) : (Fin d → ℤ) →+ (∀ i, ZMod (n i)) where
  toFun x i := (x i : ZMod (n i))
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

/-- A neighborhood in the radius `r` integer box satisfies `KernelNonalias` for coordinatewise
residue maps whenever every period exceeds `4 * r`. -/
theorem radius_kernel_nonalias (d r : ℕ) (n : Fin d → ℕ)
    (hn : ∀ i, 4*r<n i) (A : Weights (Fin d → ℤ))
    (hA : ∀ e ∈ A.neighborhood, ∀ i, -(r:ℤ) ≤ e i ∧ e i ≤ r) :
    KernelNonalias (residueHom d n) A.neighborhood := by
  intro x hx y hy hxy
  have hb : ∀ z ∈ neighborhoodDiffs A.neighborhood, ∀ i,
      -(2*(r:ℤ)) ≤ z i ∧ z i ≤ 2*(r:ℤ) := by
    intro z hz i
    obtain ⟨⟨e,f⟩,hef,rfl⟩ := Finset.mem_image.mp hz
    have he := hA e (Finset.mem_product.mp hef).1 i
    have hf := hA f (Finset.mem_product.mp hef).2 i
    change -(2*(r:ℤ)) ≤ e i - f i ∧ e i - f i ≤ 2*(r:ℤ)
    omega
  apply product_residue_injective_on_difference_box d r n hn x y (hb x hx) (hb y hy)
  intro i
  exact congrFun hxy i

/-- Unitary quotient weights from a radius `r` integer neighborhood with periods greater than `4
* r` act as a single translation times a scalar of norm one; see [Meyer1996]. -/
theorem periodic_radius_noGo (d r : ℕ) (n : Fin d → ℕ)
    (hn : ∀ i, 4*r<n i) (A : Weights (Fin d → ℤ))
    (hA : ∀ e ∈ A.neighborhood, ∀ i, -(r:ℤ) ≤ e i ∧ e i ≤ r)
    (hU : Unitary (quotientWeights (residueHom d n) A)) :
    ∃ (e₀ : Fin d → ℤ) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      ∀ (φ : (∀ i, ZMod (n i)) → ℂ) x,
        step (quotientWeights (residueHom d n) A) φ x =
          c * φ (x + residueHom d n e₀) := by
  exact @quotient_noGo (Lex (Fin d → ℤ)) (∀ i, ZMod (n i)) _ _
    (instIsOrderedAddMonoidLexPi d) _ _ _ (residueHom d n) A
    (radius_kernel_nonalias d r n hn A hA) hU

/-- A unitary finite kernel from periodic radius `r` weights, with every period greater than `4
* r`, acts on every field as a phase times a single translation. -/
theorem periodic_radius_matrix_noGo (d r : ℕ) (n : Fin d → ℕ)
    [∀ i, NeZero (n i)] (hn : ∀ i, 4*r<n i) (A : Weights (Fin d → ℤ))
    (hA : ∀ e ∈ A.neighborhood, ∀ i, -(r:ℤ) ≤ e i ∧ e i ≤ r)
    (hU : finiteKernel (quotientWeights (residueHom d n) A).weight ∈
      Matrix.unitaryGroup (∀ i, ZMod (n i)) ℂ) :
    ∃ (e₀ : Fin d → ℤ) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      ∀ (φ : (∀ i, ZMod (n i)) → ℂ) x,
        (finiteKernel (quotientWeights (residueHom d n) A).weight *ᵥ φ) x =
          c * φ (x + residueHom d n e₀) := by
  obtain ⟨e₀,c,hw,hc,hrun⟩ := periodic_radius_noGo d r n hn A hA
    ((finiteKernel_model_iff _).mp hU)
  refine ⟨e₀,c,hw,hc,?_⟩
  intro φ x
  rw [finiteKernel_model_step]
  exact hrun φ x

end Qatlib.Concepts.QcaDynamics.PeriodicNoGo
