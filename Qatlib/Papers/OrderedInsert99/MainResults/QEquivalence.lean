/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedInsert99.MainResults.InvariantDefs
import Qatlib.Papers.OrderedInsert99.MainResults.PolynomialEquivalence
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.OrderedInsert99.MainResults

open scoped BigOperators

noncomputable def laurentEvalWindow (N : ℕ) (q : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1), q r * z ^ r

def Q0Coeff (N : ℕ) (r : ℤ) : ℂ :=
  (((N - r.natAbs : ℕ) : ℝ) / (N : ℝ) : ℂ)

def QSeqExists (N k : ℕ) : Prop :=
  ∃ Q : ℕ → ℤ → ℂ,
    (∀ ℓ, ℓ ≤ k → ∀ r : ℤ,
      (r < -((N : ℤ)) + 1 ∨ (N : ℤ) - 1 < r) → Q ℓ r = 0) ∧
    (∀ ℓ, ℓ ≤ k → ∀ r : ℤ, Q ℓ (-r) = star (Q ℓ r)) ∧
    (∀ ℓ, ℓ ≤ k → ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (laurentEvalWindow N (Q ℓ) z).re) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ k → ∀ z : ℂ,
      z ^ N = (-1 : ℂ) ^ ℓ →
        laurentEvalWindow N (Q ℓ) z = laurentEvalWindow N (Q (ℓ - 1)) z) ∧
    (∀ r : ℤ, Q 0 r = Q0Coeff N r) ∧
    (∀ r : ℤ, Q k r = if r = 0 then 1 else 0)

theorem qseq_zero_queries (N : ℕ) (hN : 0 < N) :
    QSeqExists N 0 ↔ N = 1 := by
  constructor
  · rintro ⟨Q, hsupp, hrecip, hnonneg, hmatch, hQ0, hQk⟩
    have h0 : Q 0 (1 : ℤ) = Q0Coeff N 1 := hQ0 1
    have hk : Q 0 (1 : ℤ) = (if (1 : ℤ) = 0 then 1 else 0) := hQk 1
    have hval : Q0Coeff N 1 = 0 := by rw [← h0, hk]; simp
    unfold Q0Coeff at hval
    simp only [Int.natAbs_one] at hval
    have hreal : (((N - 1 : ℕ) : ℝ) / (N : ℝ)) = 0 := by
      have h' : ((((N - 1 : ℕ) : ℝ) / (N : ℝ)) : ℂ) = 0 := by simpa using hval
      exact_mod_cast h'
    have hnum : (((N - 1 : ℕ) : ℝ)) = 0 := by
      rcases div_eq_zero_iff.mp hreal with h | h
      · exact h
      · have hNposR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        exact absurd h (ne_of_gt hNposR)
    have hNle : N - 1 = 0 := by exact_mod_cast hnum
    omega
  · intro hN1
    subst hN1
    refine ⟨fun _ r => if r = 0 then 1 else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ℓ hℓ r hr
      have hr0 : r ≠ 0 := by omega
      simp [hr0]
    · intro ℓ hℓ r
      by_cases hr : r = 0
      · subst hr; simp
      · have hr' : -r ≠ 0 := by omega
        simp [hr, hr']
    · intro ℓ hℓ z hz
      simp [laurentEvalWindow]
    · intro ℓ h1 h2; omega
    · intro r
      unfold Q0Coeff
      by_cases hr : r = 0
      · subst hr; simp
      · have hpos : 0 < r.natAbs := by
          rw [Int.natAbs_pos]; exact hr
        have h1 : (1 - r.natAbs : ℕ) = 0 := by omega
        simp [hr, h1]
    · intro r; rfl

end Qatlib.Papers.OrderedInsert99.MainResults
