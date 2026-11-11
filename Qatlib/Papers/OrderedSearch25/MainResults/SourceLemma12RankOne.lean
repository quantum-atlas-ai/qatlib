/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentGramRankOne
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Source Lemma 12: rank-one normalisation of the Theorem 9 program

Carolan–Childs–Kovacs-Deak–Schaeffer, fixed arXiv:2503.21090v2, Section 3.2,
Lemma 12 (page 15) and its proof.

The paper's statement: *"Consider the SDP from Theorem 9 with the constraint in
Equation (32) replaced by Equation (40). The variables `Q^(t)` of this SDP can,
without loss of generality, be taken to have rank 1."*

The proof replaces every `Q^(t)` by a rank-one Gram representation of the same
nonnegative Laurent polynomial `q_t`, which keeps all generalized traces
(Equation (45)) and never decreases the top-left entry (Equation (46)); the last
step is exactly source Theorem 6, available in the frozen library as
`exists_rank_one_gram`.

Formalisation choices, all recorded so the coverage claim stays honest:

* The SDP is taken in its root-of-unity form `tiSDPRootForm`, i.e. the Theorem 9
  program with constraint (32) replaced by Equation (40) — precisely the program
  that Lemma 12 is stated for. The equivalence of that program with the literal
  `tiSDPFeasible` program is frozen as
  `OrderedSearch.TiSdpBridge.lemma11_tiSDPFeasible_iff_rootForm`
  (source Lemma 11).
* The fixed initial matrix `Q^(0) = J_n / n` of Equation (31) is left untouched,
  so the initial constraint (31) survives verbatim; it is already rank one.
* Only `(Q t 0 0).re` is required to increase, because the source success
  probability (33) is a real scalar constraint.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch25.MainResults

open scoped BigOperators ComplexOrder
open Matrix

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

/-- Fixed arXiv:2503.21090v2, Lemma 12. The Theorem 9 program in root form
(Equation (40) substituted for Equation (32)) has a rank-one solution whenever
it has any solution: the matrices `Q^(t)` for `1 ≤ t ≤ k` may be taken to have
rank one, while the fixed initial matrix `Q^(0) = J_n / n` of Equation (31) is
preserved. -/
theorem source_lemma12_rankOne_reduction (n k : ℕ) [NeZero n] (ε : ℝ) :
    tiSDPRootForm n k ε →
      ∃ Q : ℕ → Matrix (Fin n) (Fin n) ℂ,
        (∀ t, (Q t).PosSemidef) ∧
        (∀ i j, Q 0 i j = (n : ℂ)⁻¹) ∧
        (∀ t ∈ Finset.Icc 1 k, (Q t).trace = 1) ∧
        (1 - ε ≤ (Q k 0 0).re) ∧
        (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ n = (-1 : ℂ) ^ t →
          matrixLaurent (Q t) z = matrixLaurent (Q (t - 1)) z) ∧
        (∀ t ∈ Finset.Icc 1 k, (Q t).rank = 1) := by
  rintro ⟨Q, hpsd, hinit, htrace, hfinal, hroot⟩
  have hne : ∀ t ∈ Finset.Icc 1 k, Q t ≠ 0 := by
    intro t ht hzero
    have h1 : (Q t).trace = 0 := by rw [hzero, Matrix.trace_zero]
    rw [htrace t ht] at h1
    norm_num at h1
  -- one trace-preserving rank-one replacement step, reverting to `Q t` outside
  -- the range `1 ≤ t ≤ k` so that Equation (31) is never disturbed
  have hstep : ∀ t : ℕ, ∃ B : Matrix (Fin n) (Fin n) ℂ,
      B.PosSemidef ∧ (∀ j : ℤ, genTrace B j = genTrace (Q t) j) ∧
      (Q t 0 0).re ≤ (B 0 0).re ∧ (t ∈ Finset.Icc 1 k → B.rank = 1) := by
    intro t
    by_cases ht : t ∈ Finset.Icc 1 k
    · obtain ⟨B, hB, hrank, hgram, hfirst⟩ :=
        exists_rank_one_gram (Q t) (hpsd t) (hne t ht)
      exact ⟨B, hB, hgram, (Complex.le_def.mp hfirst).1, fun _ => hrank⟩
    · exact ⟨Q t, hpsd t, fun _ => rfl, le_rfl, fun h => absurd h ht⟩
  let Q' : ℕ → Matrix (Fin n) (Fin n) ℂ :=
    fun t => if t = 0 then Q t else (hstep t).choose
  have hQ'zero : Q' 0 = Q 0 := by simp [Q']
  have hQ'pos : ∀ t, t ≠ 0 → Q' t = (hstep t).choose := by
    intro t ht
    simp [Q', ht]
  refine ⟨Q', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · rw [show Q' t = Q t by rw [ht]; exact hQ'zero]
      exact hpsd t
    · rw [hQ'pos t ht]
      exact (hstep t).choose_spec.1
  · intro i j
    rw [hQ'zero]
    exact hinit i j
  · intro t ht
    have ht0 : t ≠ 0 := by
      simp only [Finset.mem_Icc] at ht
      omega
    rw [hQ'pos t ht0]
    have hg := (hstep t).choose_spec.2.1 0
    rw [genTrace_zero, genTrace_zero] at hg
    rw [hg]
    exact htrace t ht
  · by_cases hk : k = 0
    · subst hk
      rw [hQ'zero]
      exact hfinal
    · have hkmem : k ∈ Finset.Icc 1 k := by
        simp only [Finset.mem_Icc]
        omega
      rw [hQ'pos k hk]
      exact le_trans hfinal ((hstep k).choose_spec.2.2.1)
  · intro t ht z hz
    have ht0 : t ≠ 0 := by
      simp only [Finset.mem_Icc] at ht
      omega
    have hgcur : ∀ j : ℤ, genTrace (Q' t) j = genTrace (Q t) j := by
      intro j
      rw [hQ'pos t ht0]
      exact (hstep t).choose_spec.2.1 j
    have hgprev : ∀ j : ℤ, genTrace (Q' (t - 1)) j = genTrace (Q (t - 1)) j := by
      intro j
      by_cases h1 : t = 1
      · rw [h1, show (1 - 1 : ℕ) = 0 by norm_num, hQ'zero]
      · have hprev : t - 1 ≠ 0 := by omega
        rw [hQ'pos (t - 1) hprev]
        exact (hstep (t - 1)).choose_spec.2.1 j
    have hcur : matrixLaurent (Q' t) z = matrixLaurent (Q t) z := by
      simp only [matrixLaurent]
      exact Finset.sum_congr rfl fun j _ => by rw [hgcur j]
    have hprev : matrixLaurent (Q' (t - 1)) z = matrixLaurent (Q (t - 1)) z := by
      simp only [matrixLaurent]
      exact Finset.sum_congr rfl fun j _ => by rw [hgprev j]
    rw [hcur, hprev]
    exact hroot t ht z hz
  · intro t ht
    have ht0 : t ≠ 0 := by
      simp only [Finset.mem_Icc] at ht
      omega
    rw [hQ'pos t ht0]
    exact (hstep t).choose_spec.2.2.2 ht

end Qatlib.Papers.OrderedSearch25.MainResults
