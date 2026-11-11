/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.SchemeAlgebra.BoseMesnerUnitary

/-!
# Composition of scheme phase operators

The phase sums `schemeUnitary` multiply by adding their phase parameters when the underlying
matrices are mutually orthogonal idempotents. Completeness gives the identity and inverse
formulas, complementing the association-scheme operators of [Childs2010].

## Main statements

* `schemeUnitary_mul`: operator multiplication adds phases.
* `schemeUnitary_neg_mul`: negating phases gives a left inverse.

## References

* [Childs, 2010][Childs2010]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.SchemeAlgebra

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The phase of a sum is the product of the two phases, giving the scalar composition identity
used for the operators of [Childs2010]. -/
theorem phase_add (φ ψ : ℝ) : phase (φ + ψ) = phase φ * phase ψ := by
  unfold phase
  push_cast
  rw [mul_add, Complex.exp_add]

/-- If the matrices sum to the identity, their zero-phase sum is the identity. This supplies the
identity operator for the construction in [Childs2010]. -/
theorem schemeUnitary_zero {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hComplete : ∑ i, E i = 1) :
    schemeUnitary E (fun _ => 0) = 1 := by
  unfold schemeUnitary phase
  simp only [mul_zero, Complex.ofReal_zero, Complex.exp_zero, one_smul]
  exact hComplete

/-- For mutually orthogonal idempotents, multiplying two scheme phase sums adds their phase
functions. See [Childs2010]. -/
theorem schemeUnitary_mul {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (φ ψ : Fin m → ℝ) :
    schemeUnitary E φ * schemeUnitary E ψ = schemeUnitary E (φ + ψ) := by
  unfold schemeUnitary
  rw [Finset.sum_mul_sum]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hstep : ∀ i : Fin m,
      (∑ j, (phase (ψ j) * phase (φ i)) • (E i * E j))
        = (phase (ψ i) * phase (φ i)) • E i := by
    intro i
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [hIdem i]
    · intro j _ hji
      simp [hOrth i j hji.symm]
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, phase_add, mul_comm (phase (ψ i)) (phase (φ i))]

/-- For a complete family of mutually orthogonal idempotents, the sum with negated phases is a
left inverse of the original scheme phase sum. See [Childs2010]. -/
theorem schemeUnitary_neg_mul {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1)
    (φ : Fin m → ℝ) :
    schemeUnitary E (fun i => -φ i) * schemeUnitary E φ = 1 := by
  rw [schemeUnitary_mul E hIdem hOrth]
  have hzero : (fun i => -φ i) + φ = (fun _ => 0) := by
    funext i
    simp
  rw [hzero, schemeUnitary_zero E hComplete]

/-- For a complete family of mutually orthogonal Hermitian idempotents, every scheme phase sum
is unitary. -/
theorem schemeUnitary_forall_mem_unitaryGroup {m : ℕ} (E : Fin m → Matrix J J ℂ)
    (hHerm : ∀ i, (E i).IsHermitian)
    (hIdem : ∀ i, E i * E i = E i)
    (hOrth : ∀ i j, i ≠ j → E i * E j = 0)
    (hComplete : ∑ i, E i = 1) (φ : Fin m → ℝ) :
    schemeUnitary E φ ∈ Matrix.unitaryGroup J ℂ :=
  schemeUnitary_mem_unitaryGroup E hHerm hIdem hOrth hComplete φ

/-- Pointwise equal phase functions give equal scheme phase sums. -/
theorem schemeUnitary_congr {m : ℕ} (E : Fin m → Matrix J J ℂ)
    {φ ψ : Fin m → ℝ} (h : ∀ i, φ i = ψ i) :
    schemeUnitary E φ = schemeUnitary E ψ := by
  unfold schemeUnitary
  exact Finset.sum_congr rfl (fun i _ => by rw [h i])

end Qatlib.Papers.ContDiscWalk08.SchemeAlgebra
