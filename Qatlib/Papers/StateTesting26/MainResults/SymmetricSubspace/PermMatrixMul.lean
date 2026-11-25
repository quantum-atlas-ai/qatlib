/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.Model.StateModel

@[expose] public section

/-!
# The permutation operators form a representation

Equation (2.3) defines the unitary `V_d(π)` acting on `(ℂ^d)^{⊗k}` by
`V_d(π)|i₁,…,i_k⟩ = |i_{π⁻¹(1)},…,i_{π⁻¹(k)}⟩`, i.e. by permuting the tensor factors. Its matrix
in the model layer is `Qatlib.Papers.StateTesting26.MainResults.Model.permMat`, a permutation
matrix indexed by `Fin k → Fin d`.

This module proves that `π ↦ V_d(π)` is multiplicative, `V_d(π)V_d(σ) = V_d(πσ)`. This is the
step that turns the average `(1/k!) ∑_π V_d(π)` of Eq. (2.5) into a projector: it yields both
`(Π^k_sym)² = Π^k_sym` and self-adjointness of `Π^k_sym`. The proof is a direct entrywise
computation; the sum over intermediate tuples has a single nonzero term.

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Eqs. (2.3)–(2.5).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.StateTesting26.MainResults.SymmetricSubspace

open Qatlib.Papers.StateTesting26.MainResults.Model

/-- Entry form of the product of two permutation operators: for a fixed intermediate tuple `x`
the corresponding summand is nonzero only when `x` is the permuted tuple `i ∘ π`. -/
theorem permMat_mul_permMat_term {d k : ℕ} (π σ : Equiv.Perm (Fin k)) (i j : Fin k → Fin d)
    (x : Fin k → Fin d) :
    permMat (d := d) π i x * permMat (d := d) σ x j =
      if x = (fun a => i (π a)) then (if (fun a => x (σ a)) = j then 1 else 0) else 0 := by
  classical
  by_cases hx : x = (fun a => i (π a))
  · subst hx
    rw [permMat, permMat, ite_eq_left rfl]
    simp
  · have hfx : ¬ (fun a => i (π a)) = x := fun h => hx h.symm
    rw [permMat, permMat]
    simp [hx, hfx]

/-- **Equation (2.3) is a representation**: `V_d(π) V_d(σ) = V_d(πσ)`. -/
theorem permMat_mul_permMat {d k : ℕ} (π σ : Equiv.Perm (Fin k)) :
    permMat (d := d) π * permMat (d := d) σ = permMat (d := d) (π * σ) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_congr rfl fun x _ => permMat_mul_permMat_term π σ i j x]
  rw [Finset.sum_eq_single (fun a => i (π a))]
  · rw [ite_eq_left rfl, permMat]
    have heq : (fun a => i ((π * σ) a)) = (fun a => (fun a => i (π a)) (σ a)) := by
      funext a
      rw [Equiv.Perm.mul_apply]
    by_cases h : (fun a => (fun a => i (π a)) (σ a)) = j
    · have h' : (fun a => i ((π * σ) a)) = j := by rw [heq, h]
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ (fun a => i ((π * σ) a)) = j := by
        intro hh
        exact h (by rw [← heq]; exact hh)
      rw [ite_eq_right h, ite_eq_right h']
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Qatlib.Papers.StateTesting26.MainResults.SymmetricSubspace
