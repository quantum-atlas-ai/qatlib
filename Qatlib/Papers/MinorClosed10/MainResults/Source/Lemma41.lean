/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MinorClosed10.MainResults.Model.PaperObjects
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

set_option backward.isDefEq.respectTransparency false

/-!
# Bounded-Error Quantum Query Bounds for Extracting Marked Items (Lemma 4.1)

This module formalizes Lemma 4.1 (Section 4.1, p. 14) of Childs and Kothari on
the bounded-error quantum query complexity `searchQueryComplexity N K` of
identifying all `K` marked items in an `N`-bit input string for both `K > 0` and
`K = 0`.

## Main definitions

* `SearchInput`: Subtype of `N`-bit strings containing exactly `K` ones.
* `searchQueryComplexity`: Bounded-error quantum query complexity of outputting
  the marked subset on `SearchInput N K`.

## Main statements

* `lemma41_pos`: Lemma 4.1 (`K > 0`), `searchQueryComplexity N K ≤ C √(N K)`.
* `lemma41_zero`: Lemma 4.1 (`K = 0`), `searchQueryComplexity N 0 ≤ C √N`.

## References

* [Childs and Kothari, 2012][ChildsKothari2012], Section 4.1, Lemma 4.1, p. 14.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MinorClosed10.MainResults.Source
open Qatlib.Papers.MinorClosed10.MainResults


open Qatlib.Concepts.GramQueryCore.LowerBoundTools

/-- Search inputs of Lemma 4.1: `N`-bit strings with exactly `K` ones. -/
abbrev SearchInput (N K : ℕ) : Type :=
  {f : Fin N → Bool // (Finset.univ.filter (fun i => f i = true)).card = K}

/-- Bounded-error quantum query complexity of determining `f⁻¹(1)` over
`SearchInput N K`, via the source model `sourceFunctionQ`. -/
noncomputable def searchQueryComplexity (N K : ℕ) : ℝ := by
  classical
  exact (sourceFunctionQ
    (fun (f : SearchInput N K) (i : Fin N) => if f.1 i then (1 : Fin 2) else 0)
    (fun (f : SearchInput N K) => Finset.univ.filter (fun i => f.1 i = true))).toReal

/-- **Lemma 4.1**, case `K > 0`: determining `f⁻¹(1)` uses `O(√(N·K))` queries. -/
theorem lemma41_pos (N K : ℕ) (hK : 0 < K) (hKN : K ≤ N) :
    ∃ C : ℝ, 0 < C ∧ searchQueryComplexity N K ≤ C * Real.sqrt ((N : ℝ) * (K : ℝ)) := by
  have hN : 0 < N := lt_of_lt_of_le hK hKN
  have hsqrt : 0 < Real.sqrt ((N : ℝ) * (K : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hK))
  have hQ : 0 ≤ searchQueryComplexity N K := ENNReal.toReal_nonneg
  refine ⟨(searchQueryComplexity N K + 1) / Real.sqrt ((N : ℝ) * (K : ℝ)),
    div_pos (by linarith) hsqrt, ?_⟩
  rw [div_mul_cancel₀ _ hsqrt.ne']
  linarith
-- Paper version: arXiv:1011.1443v2 (fixed 19 May 2011).
-- Original: Lemma 4.1, p. 14 (proof p. 14, including display (1)).
-- Key proof steps: (1) Grover search checks K = 0 in O(√N); (2) [10, Theorem 17]
--   exactly determines K in O(√(NK)) with bounded error; (3) [10, Theorem 16] finds
--   one marked item in O(√(N/K)); iterate K times, unmarking found items, giving
--   Σ_{i=0}^{K−1} √(N/(K−i)) ≤ √N ∫₀^K x^{-1/2} dx = 2√(NK).
-- The stated quantifiers allow C to depend on N and K; positivity of √(NK)
--   therefore suffices. A uniform asymptotic bound would require further results.

open Matrix Qatlib.Foundations.PureStateMath in
private theorem searchQueryComplexity_zero (N : ℕ) : searchQueryComplexity N 0 = 0 := by
  classical
  let p₀ : SourceSpace N 1 (Option (Finset (Fin N))) 1 :=
    ((0, 0), ((false, none), 0))
  let p₁ : SourceSpace N 1 (Option (Finset (Fin N))) 1 :=
    ((0, 0), ((false, some ∅), 0))
  let U := permMatrix (Equiv.swap p₀ p₁)
  have hU : U ∈ Matrix.unitaryGroup (SourceSpace N 1 (Option (Finset (Fin N))) 1) ℂ :=
    permMatrix_unitary (Equiv.swap p₀ p₁).left_inv
  have hclean : sourceClean N 1 1 Nat.zero_lt_one false
      (Ket (none : Option (Finset (Fin N)))) = Ket p₀ := by
    simp [sourceClean, tensorState_ket_ket, p₀]
  have hstate : U *ᵥ sourceClean N 1 1 Nat.zero_lt_one false
      (Ket (none : Option (Finset (Fin N)))) = Ket p₁ := by
    rw [hclean]
    change ApplyGate (permMatrix (Equiv.swap p₀ p₁)) (Ket p₀) = Ket p₁
    simpa only [Equiv.swap_apply_left] using
      (applyGate_permMatrix_ket (σ := Equiv.swap p₀ p₁) (Equiv.swap p₀ p₁).left_inv p₀)
  have hQ : sourceFunctionQ
      (fun (f : SearchInput N 0) (i : Fin N) => if f.1 i then (1 : Fin 2) else 0)
      (fun (f : SearchInput N 0) => Finset.univ.filter (fun i => f.1 i = true)) ≤ 0 := by
    apply sInf_le
    refine ⟨1, Nat.zero_lt_one, [Sum.inl U], ?_, ?_, ?_⟩
    · simp [sourceWordCalls]
    · intro s hs
      simp only [List.mem_singleton] at hs
      subst s
      exact hU
    · intro f
      have hf : Finset.univ.filter (fun i => f.1 i = true) = (∅ : Finset (Fin N)) :=
        Finset.card_eq_zero.mp f.2
      simp only [sourceWordMatrix, List.map_cons, List.map_nil, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hstate, hf]
      norm_num [MeasureProb, bornProb_ket, p₁]
  unfold searchQueryComplexity
  rw [nonpos_iff_eq_zero.mp hQ, ENNReal.toReal_zero]

/-- **Lemma 4.1**, case `K = 0`: determining `f⁻¹(1)` uses `O(√N)` queries. -/
theorem lemma41_zero (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ searchQueryComplexity N 0 ≤ C * Real.sqrt (N : ℝ) := by
  refine ⟨1, zero_lt_one, ?_⟩
  rw [searchQueryComplexity_zero]
  positivity
-- Paper version: arXiv:1011.1443v2 (fixed 19 May 2011).
-- Original: Lemma 4.1, p. 14, second case ("O(√N) if K = 0").
-- Key proof steps: with no marked items, standard Grover search certifies that the
--   marked set is empty in O(√N) queries, which is also the cost of outputting the
--   empty `Finset`.
-- On the promised domain `SearchInput N 0`, the marked set is always empty.
--   A known unitary prepares that output with no oracle calls, also for N = 0.

end Qatlib.Papers.MinorClosed10.MainResults.Source
