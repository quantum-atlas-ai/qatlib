/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Bounded orders of permutation eigenvalues

`permutationEigenvalueBoundedRoot` shows that an eigenvalue associated to a nonzero eigenvector
of a finite permutation matrix is a root of unity. Its order has a positive witness bounded by
the cardinality of the underlying index type, providing the spectral input for rational phase
recovery. The development follows [Kitaev1995].

## Main statements

* `permutationEigenvalueBoundedRoot`: finds a positive exponent at most the dimension for which
  the eigenvalue power is one.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

/-- An eigenvalue of a finite permutation matrix with a nonzero eigenvector has a positive power
equal to one, with exponent at most the index cardinality. This supplies the bounded-root
property used in [Kitaev, 1995, Theorem 1][Kitaev1995]. -/
theorem permutationEigenvalueBoundedRoot {I : Type} [Fintype I] [DecidableEq I]
    (p : Equiv.Perm I) (ψ : QState I) (lam : ℂ)
    (hne : ψ ≠ 0) (heig : (permMatrix p) *ᵥ ψ = lam • ψ) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Fintype.card I ∧ lam ^ q = 1 := by
  classical
  have hp (x : I) : ((permMatrix p) *ᵥ ψ) (p x) = ψ x := by
    simp [Matrix.mulVec, dotProduct, permMatrix, p.injective.eq_iff]
  have hpoint (x : I) : ψ (p.symm x) = lam * ψ x := by
    have hh := congrFun heig (p (p.symm x))
    rw [hp] at hh
    simpa using hh
  have hiter (k : ℕ) (x : I) : ψ ((p.symm^[k]) x) = lam ^ k * ψ x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hpoint, ih, pow_succ]
      ring
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 0 := by
    by_contra h
    apply hne
    funext x
    simpa using not_exists.mp h x
  let q := Function.minimalPeriod p.symm x
  refine ⟨q, Function.minimalPeriod_pos_of_mem_periodicPts (p.symm.injective.mem_periodicPts x),
    Function.minimalPeriod_le_card, ?_⟩
  have hh := hiter q x
  rw [Function.iterate_minimalPeriod] at hh
  exact mul_right_cancel₀ hx (hh.symm.trans (one_mul (ψ x)).symm)

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
