/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Electric and magnetic helicity balance

[IrvineBouwmeester2008KnottedLight], equation (1) and pp. 717–719,
[DOI](https://doi.org/10.1038/nphys1056).
For differentiable scalar charges obeying the integrated Maxwell balance laws,
the sum is conserved and a vanishing E·B exchange conserves each charge.
Initial equality is needed to propagate equality; nullness alone does not fix
the integration constants. A finite weighted duality model independently proves
equality under an explicit orthogonal relation between fields and potentials.
Deriving the balance laws from Maxwell PDE, justified integration by parts on
unbounded space and evaluation of the Hopfion spatial integrals remain outside
this module. Cartesian products use
`Qatlib.Papers.KnottedLight08.HopfField.dot3`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.HelicitySpec

open Qatlib.Papers.KnottedLight08.HopfField
open scoped BigOperators

/-- The ordinary derivative of a Cartesian field pairing follows the product rule. -/
theorem dot_derivative (u v : ℝ → Fin 3 → ℝ) (du dv : Fin 3 → ℝ) (t : ℝ)
    (hu : ∀ j, HasDerivAt (fun s => u s j) (du j) t)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (dv j) t) :
    HasDerivAt (fun s => dot3 (u s) (v s))
      (dot3 du (v t) + dot3 (u t) dv) t := by
  have h := HasDerivAt.fun_add
    (HasDerivAt.fun_add (HasDerivAt.fun_mul (hu 0) (hv 0))
      (HasDerivAt.fun_mul (hu 1) (hv 1))) (HasDerivAt.fun_mul (hu 2) (hv 2))
  exact h.congr_deriv (by simp only [dot3]; ring)

/-- Opposite helicity exchange rates conserve the total electromagnetic helicity. -/
theorem total_helicity_conserved (magnetic electric exchange : ℝ → ℝ)
    (hm : ∀ t, HasDerivAt magnetic (-2 * exchange t) t)
    (he : ∀ t, HasDerivAt electric (2 * exchange t) t) (s t : ℝ) :
    magnetic s + electric s = magnetic t + electric t := by
  have h : ∀ x, HasDerivAt (fun y => magnetic y + electric y) 0 x := by
    intro x
    exact (HasDerivAt.fun_add (hm x) (he x)).congr_deriv (by ring)
  exact is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt)
    (fun x => (h x).deriv) s t

/-- A null exchange term conserves magnetic helicity, conditional on its balance law. -/
theorem null_magnetic_conserved (magnetic exchange : ℝ → ℝ)
    (hm : ∀ t, HasDerivAt magnetic (-2 * exchange t) t)
    (hn : ∀ t, exchange t = 0) (s t : ℝ) : magnetic s = magnetic t := by
  have h : ∀ x, HasDerivAt magnetic 0 x := by
    intro x
    simpa [hn x] using hm x
  exact is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt)
    (fun x => (h x).deriv) s t

/-- A null exchange term conserves electric helicity, conditional on its balance law. -/
theorem null_electric_conserved (electric exchange : ℝ → ℝ)
    (he : ∀ t, HasDerivAt electric (2 * exchange t) t)
    (hn : ∀ t, exchange t = 0) (s t : ℝ) : electric s = electric t := by
  have h : ∀ x, HasDerivAt electric 0 x := by
    intro x
    simpa [hn x] using he x
  exact is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt)
    (fun x => (h x).deriv) s t

/-- Initial equality of the two helicities is preserved by null balance. -/
theorem equal_helicities_propagate (magnetic electric exchange : ℝ → ℝ)
    (hm : ∀ t, HasDerivAt magnetic (-2 * exchange t) t)
    (he : ∀ t, HasDerivAt electric (2 * exchange t) t)
    (hn : ∀ t, exchange t = 0) (initial t : ℝ)
    (hi : magnetic initial = electric initial) : magnetic t = electric t := by
  rw [← null_magnetic_conserved magnetic exchange hm hn initial t,
    ← null_electric_conserved electric exchange he hn initial t]
  exact hi

/-- A concrete orthogonal transformation used to model electric–magnetic dual data. -/
def dualRotation (v : Fin 3 → ℝ) : Fin 3 → ℝ := ![-v 1, v 0, v 2]

/-- The dual rotation preserves the bilinear pairing of potentials and fields. -/
theorem dual_pairing (A B : Fin 3 → ℝ) :
    dot3 (dualRotation A) (dualRotation B) = dot3 A B := by
  simp [dot3, dualRotation]
  ring

/-- Finite weighted helicity models a quadrature or a finite collection of modes. -/
noncomputable def helicitySum {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (potential field : ι → Fin 3 → ℝ) : ℝ :=
  ∑ i, weight i * dot3 (potential i) (field i)

/-- Dual-related potentials and fields have equal finite weighted helicities. -/
theorem dual_helicity_equal {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    (A B : ι → Fin 3 → ℝ) :
    helicitySum weight (fun i => dualRotation (A i)) (fun i => dualRotation (B i)) =
      helicitySum weight A B := by
  simp [helicitySum, dual_pairing]

end Qatlib.Papers.KnottedLight08.HelicitySpec
