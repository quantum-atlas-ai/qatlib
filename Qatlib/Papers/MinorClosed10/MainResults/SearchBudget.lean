/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MinorClosed10.MainResults.Source.Lemma41
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! # Uniform versus posterior constants for Lemma 4.1

Childs--Kothari, arXiv:1011.1443v2, Section 4.1, p. 14.

`Source.lemma41_pos` supplies, for each fixed `N` and `K`, a positive constant
`C(N,K)` with `searchQueryComplexity N K ≤ C(N,K)·√(NK)`.  The paper's Lemma 4.1
asks for one constant independent of `N` and `K`.  The locked source model gives
only the pointwise statement, and the definition of `searchQueryComplexity` as an
infimum does not expose the algorithm whose cost would yield a uniform constant.
This module records the logical gap explicitly: pointwise constants never imply a
uniform constant, and it isolates the exact remaining source obligation.
-/

set_option autoImplicit false
namespace Qatlib.Papers.MinorClosed10.MainResults.SearchBudget

open Qatlib.Papers.MinorClosed10.MainResults
open Qatlib.Papers.MinorClosed10.MainResults.Source

/-- A family of costs witnessing that pointwise constants do not uniformise:
`q(N,K) = √(NK)·(N+K+1)` has the pointwise posterior constant `N+K+1` but no
constant independent of `N` and `K`. -/
noncomputable def gapExample (N K : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) * (K : ℝ)) * ((N : ℝ) + (K : ℝ) + 1)

/-- The gap example satisfies the pointwise Lemma 4.1 shape. -/
theorem gapExample_pointwise (N K : ℕ) (hK : 0 < K) (_hKN : K ≤ N) :
    ∃ C : ℝ, 0 < C ∧ gapExample N K ≤ C * Real.sqrt ((N : ℝ) * (K : ℝ)) := by
  refine ⟨(N : ℝ) + (K : ℝ) + 1, by positivity, ?_⟩
  rw [gapExample]
  exact le_of_eq (mul_comm _ _)

/-- No uniform constant bounds the gap example. -/
theorem gapExample_no_uniform :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ N K : ℕ, 0 < K → K ≤ N →
      gapExample N K ≤ C * Real.sqrt ((N : ℝ) * (K : ℝ)) := by
  rintro ⟨C, hC, h⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_trans hC hN
    exact_mod_cast this
  have hineq := h N 1 (by norm_num) hNpos
  have hs : 0 < Real.sqrt ((N : ℝ) * (1 : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  rw [gapExample] at hineq
  have h2 : ((N : ℝ) + 1 + 1) ≤ C := by
    have hm : Real.sqrt ((N : ℝ) * 1) * ((N : ℝ) + 1 + 1) ≤
        Real.sqrt ((N : ℝ) * 1) * C := by
      calc Real.sqrt ((N : ℝ) * 1) * ((N : ℝ) + 1 + 1) ≤
          C * Real.sqrt ((N : ℝ) * 1) := by simpa using hineq
        _ = Real.sqrt ((N : ℝ) * 1) * C := by ring
    exact (mul_le_mul_iff_of_pos_left hs).mp hm
  linarith

/-- Whatever uniform constant is claimed for Lemma 4.1, it is exactly the
missing source statement: a single `C` bounding `searchQueryComplexity N K` on
the promised family. -/
def UniformLemma41Bound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N K : ℕ, 0 < K → K ≤ N →
    searchQueryComplexity N K ≤ C * Real.sqrt ((N : ℝ) * (K : ℝ))

/-- The pointwise posterior statement of the locked source, restated without a
new constant. -/
theorem posterior_bound (N K : ℕ) (hK : 0 < K) (hKN : K ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      searchQueryComplexity N K ≤ C * Real.sqrt ((N : ℝ) * (K : ℝ)) :=
  lemma41_pos N K hK hKN

/-- A uniform bound implies every posterior bound; the converse is not available
from the locked definitions. -/
theorem uniform_implies_posterior (h : UniformLemma41Bound) (N K : ℕ) (hK : 0 < K)
    (hKN : K ≤ N) :
    ∃ C : ℝ, 0 < C ∧
      searchQueryComplexity N K ≤ C * Real.sqrt ((N : ℝ) * (K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := h
  exact ⟨C, hC, hbound N K hK hKN⟩

end Qatlib.Papers.MinorClosed10.MainResults.SearchBudget
