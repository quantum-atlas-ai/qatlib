/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGram
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Real.Sqrt

/-!
# Polynomial and semidefinite ordered search conditions

This module defines the matrix feasibility conditions `tiSDPFeasible`, their root evaluation
form `tiSDPRootForm`, and the normalized polynomial conditions `tiPolyConditions` for
translation-invariant ordered search. It also defines the exact Laurent polynomial conditions
`exactTIProgram`. The semidefinite approach to ordered search is studied in
[ChildsLandahlParrilo2007].

The trace identities identify the generalized-trace transition equations with equality of matrix
Laurent evaluations on the roots of `z ^ n = (-1) ^ t`.

## Main statements

* `ti_initial_trace`: the prescribed initial matrix has trace one.
* `ti_step_trace`: consecutive matrices have equal traces under the normalization assumptions.
* `lemma11_tiSDPFeasible_iff_rootForm`: equates the trace and root formulations of feasibility.

## References

* [Childs, Landahl and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open scoped ComplexOrder

namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge

open scoped BigOperators ComplexOrder
open Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- Evaluates the polynomial with coefficient vector `v` at `z`, using the natural-number values
of the finite indices as exponents. -/
noncomputable def tiPolyEval {n : ℕ} (v : Fin n → ℂ) (z : ℂ) : ℂ := ∑ j, v j * z ^ (j : ℕ)

/-- The constant coefficient vector with every entry equal to the reciprocal square root of `n`. -/
noncomputable def tiDirichletVec (n : ℕ) : Fin n → ℂ := fun _ => (Real.sqrt n)⁻¹

/-- The transition condition equating the generalized traces of `Q` and `Q'` in the combinations
indexed by `j` and `j - n`, with sign `(-1) ^ t`, for `0 < j < n`. -/
def tiTraceStep {n : ℕ} (t : ℕ) (Q Q' : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ j ∈ Finset.Ioo (0 : ℤ) ((n : ℤ)),
    genTrace Q j + (-1 : ℤ) ^ t * genTrace Q (j - (n : ℤ))
      = genTrace Q' j + (-1 : ℤ) ^ t * genTrace Q' (j - (n : ℤ))

/-- Existence of positive semidefinite matrices with the prescribed constant initial matrix,
trace-one iterates, terminal first-entry bound `1 - ε`, and `tiTraceStep` transitions
through step `k`. -/
def tiSDPFeasible (n k : ℕ) (ε : ℝ) [NeZero n] : Prop :=
  ∃ Q : ℕ → Matrix (Fin n) (Fin n) ℂ,
    (∀ t, (Q t).PosSemidef) ∧
    (∀ i j, Q 0 i j = (n : ℂ)⁻¹) ∧
    (∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) ∧
    (1 - ε ≤ (Q k 0 0).re) ∧
    (∀ t ∈ Finset.Icc 1 k, tiTraceStep t (Q t) (Q (t - 1)))

/-- The matrix feasibility conditions with each transition expressed as equality of consecutive
matrix Laurent evaluations at every root of `z ^ n = (-1) ^ t`. -/
def tiSDPRootForm (n k : ℕ) (ε : ℝ) [NeZero n] : Prop :=
  ∃ Q : ℕ → Matrix (Fin n) (Fin n) ℂ,
    (∀ t, (Q t).PosSemidef) ∧
    (∀ i j, Q 0 i j = (n : ℂ)⁻¹) ∧
    (∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) ∧
    (1 - ε ≤ (Q k 0 0).re) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      matrixLaurent (Q t) z = matrixLaurent (Q (t - 1)) z)

/-- Existence of polynomial coefficient vectors starting at `tiDirichletVec n`, normalized
through step `k`, with terminal constant coefficient squared norm at least `1 - ε` and
matching successive magnitudes at the prescribed roots. -/
def tiPolyConditions (n k : ℕ) (ε : ℝ) [NeZero n] : Prop :=
  ∃ p : ℕ → (Fin n → ℂ),
    p 0 = tiDirichletVec n ∧
    (∀ t ∈ Finset.Icc 1 k, ∑ j, Complex.normSq (p t j) = 1) ∧
    (∑ j, Complex.normSq (p 0 j) = 1) ∧
    (1 - ε ≤ Complex.normSq (p k 0)) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      ‖tiPolyEval (p t) z‖ = ‖tiPolyEval (p (t - 1)) z‖)

/-- Existence of real Laurent coefficient vectors starting at `fejerCoeffs n` and ending at the
constant polynomial one, with constant coefficient one, nonnegative real parts of
evaluations on the unit circle, and successive evaluations matching at the prescribed roots. -/
def exactTIProgram (n k : ℕ) [NeZero n] : Prop :=
  ∃ q : ℕ → (Fin n → ℝ),
    q 0 = fejerCoeffs n ∧
    (q k 0 = 1 ∧ ∀ j, (0 : Fin n) < j → q k j = 0) ∧
    (∀ t ∈ Finset.Icc 0 k, q t 0 = 1) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
      laurentEval (q t) z = laurentEval (q (t - 1)) z) ∧
    (∀ t ∈ Finset.Icc 0 k, ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (laurentEval (q t) z).re)

/-- The initial matrix whose entries are all `n⁻¹` has trace one for nonzero `n`. -/
theorem ti_initial_trace (n : ℕ) [NeZero n] (Q : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ i j, Q 0 i j = (n : ℂ)⁻¹) : (Q 0).trace = 1 := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, hQ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast NeZero.ne n : (n : ℂ) ≠ 0)

/-- If the initial matrix has the prescribed constant entries and the subsequent matrices
through step `k` have trace one, then consecutive traces agree at every step from one to
`k`. -/
theorem ti_step_trace (n k : ℕ) [NeZero n] (Q : ℕ → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ∀ i j, Q 0 i j = (n : ℂ)⁻¹)
    (htr : ∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) (t : ℕ) (ht : t ∈ Finset.Icc 1 k) :
    (Q t).trace = (Q (t - 1)).trace := by
  rw [htr t ht]
  by_cases h1 : t = 1
  · subst t
    simpa using (ti_initial_trace n Q hQ).symm
  · symm
    apply htr
    simp only [Finset.mem_Icc] at ht ⊢
    omega

/-- The generalized-trace and root evaluation formulations of translation-invariant SDP
feasibility are equivalent; see [ChildsLandahlParrilo2007] for the ordered search SDP
framework. -/
theorem lemma11_tiSDPFeasible_iff_rootForm (n k : ℕ) (ε : ℝ) [NeZero n] :
    tiSDPFeasible n k ε ↔ tiSDPRootForm n k ε := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  constructor
  · rintro ⟨Q, hps, hQ, htr, hfin, hstep⟩
    refine ⟨Q, hps, hQ, htr, hfin, ?_⟩
    intro t ht
    apply (matrixLaurent_root_matching_iff hn t (Q t) (Q (t - 1))).mpr
    refine ⟨ti_step_trace n k Q hQ htr t ht, ?_⟩
    intro j hj hjn
    have hm : (j : ℤ) ∈ Finset.Ioo (0 : ℤ) (n : ℤ) := by
      simp only [Finset.mem_Ioo]
      constructor <;> exact_mod_cast (by assumption)
    simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using hstep t ht (j : ℤ) hm
  · rintro ⟨Q, hps, hQ, htr, hfin, hroot⟩
    refine ⟨Q, hps, hQ, htr, hfin, ?_⟩
    intro t ht j hj
    have hc := ((matrixLaurent_root_matching_iff hn t (Q t) (Q (t - 1))).mp (hroot t ht)).2
    simp only [Finset.mem_Ioo] at hj
    have hp : 0 < j.toNat := by omega
    have hlt : j.toNat < n := by omega
    have he : ((j.toNat : ℕ) : ℤ) = j := by omega
    simpa only [he, Int.cast_pow, Int.cast_neg, Int.cast_one] using hc j.toNat hp hlt

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
