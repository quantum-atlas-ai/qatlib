/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Sampling the threshold cut with probability `2/3` (Sec. 4, Eq. (12), p. 5--6)

Fixed version: arXiv:2503.12789v2 (2026-01-27), Farhi--Gutmann--Ranard--Villalonga.

This module formalizes the probability argument of Section 4:

* Eq. (12): if `C` is an integer-valued cut size with `0 ≤ C ≤ M` and expectation
  at least `C0`, then a single measurement satisfies `C ≥ C0` with probability at
  least `1/M` (`one_sample_prob_ge`);
* repeating the (fixed-angle) QAOA circuit `N` times independently multiplies the
  failure probability, so the success probability of the best sample is
  `1 − (1 − p₀)^N`; once `(1 − 1/M)^N ≤ 1/3` this is at least `2/3`
  (`repeated_success_ge`, `paper_two_thirds_guarantee`);
* each round uses `O(|E(G)|)` gates, so `N = O(|E(G)|)` rounds cost `O(|E(G)|²)`
  (`repetition_gate_bound`).

The circuit-level constant-depth decomposition (Vizing edge colouring, p. 5) is
hardware bookkeeping which this module does not formalize; it is recorded as the
explicit gate budget hypothesis `K` in `repetition_gate_bound`.  No axiom beyond
the standard three is used.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

variable {Ω : Type*} [Fintype Ω]

/-- **Paper Eq. (12), p. 5--6.** A single sample of an integer cut size `C` with
`0 ≤ C ω ≤ M` and expectation at least `C0` hits the threshold `C0` with
probability at least `1/M`.  The proof is the paper's inequality chain
`E[C] ≤ (1−p₀)(C0−1) + p₀ M ≤ C0 − 1 + p₀ M`, combined with `E[C] ≥ C0`. -/
theorem one_sample_prob_ge
    (P : Ω → ℝ) (C : Ω → ℕ) (M C0 : ℕ)
    (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (hCtop : ∀ ω, C ω ≤ M)
    (hExp : (C0 : ℝ) ≤ ∑ ω, P ω * (C ω : ℝ))
    (hC0le : C0 ≤ M) :
    (1 : ℝ) / M ≤ ∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω := by
  classical
  by_cases hM : M = 0
  · have hC0 : C0 = 0 := by omega
    subst hC0
    subst hM
    have hfilter : (Finset.univ.filter fun ω => (0 : ℕ) ≤ C ω) = Finset.univ := by
      ext ω; simp
    rw [hfilter, hP1]
    norm_num
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    by_cases hC0z : C0 = 0
    · -- Vacuous threshold: the event is everything, so its probability is one.
      subst hC0z
      have hfilter : (Finset.univ.filter fun ω => (0 : ℕ) ≤ C ω) = Finset.univ := by
        ext ω; simp
      rw [hfilter, hP1]
      have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      exact (div_le_one hMposR).mpr (by exact_mod_cast hMpos)
    · have hC0pos : 1 ≤ C0 := Nat.one_le_iff_ne_zero.mpr hC0z
      -- The pointwise inequality of Eq. (12).
      have hpoint : ∀ ω, P ω * (C ω : ℝ) ≤
          P ω * (((C0 : ℝ) - 1) + (M : ℝ) * (if C0 ≤ C ω then 1 else 0)) := by
        intro ω
        refine mul_le_mul_of_nonneg_left ?_ (hP0 ω)
        by_cases hω : C0 ≤ C ω
        · rw [if_pos hω]
          have h1 : (C ω : ℝ) ≤ (M : ℝ) := by exact_mod_cast hCtop ω
          have h2 : (1 : ℝ) ≤ (C0 : ℝ) := by exact_mod_cast hC0pos
          linarith
        · rw [if_neg hω, mul_zero, add_zero]
          have hle : C ω ≤ C0 - 1 := by omega
          have hcast : (C ω : ℝ) ≤ ((C0 - 1 : ℕ) : ℝ) := by exact_mod_cast hle
          rw [Nat.cast_sub hC0pos] at hcast
          push_cast at hcast
          linarith
      have hsum_bound :
          ∑ ω, P ω * (C ω : ℝ) ≤
            ∑ ω, P ω * (((C0 : ℝ) - 1) + (M : ℝ) * (if C0 ≤ C ω then 1 else 0)) :=
        Finset.sum_le_sum fun ω _ => hpoint ω
      have hsplit : ∀ ω, P ω * (((C0 : ℝ) - 1) + (M : ℝ) * (if C0 ≤ C ω then 1 else 0)) =
          P ω * ((C0 : ℝ) - 1) + (M : ℝ) * (if C0 ≤ C ω then P ω else 0) := by
        intro ω
        by_cases hω : C0 ≤ C ω <;> simp [hω] <;> ring
      have hRHS :
          ∑ ω, P ω * (((C0 : ℝ) - 1) + (M : ℝ) * (if C0 ≤ C ω then 1 else 0)) =
            ((C0 : ℝ) - 1) + (M : ℝ) *
              (∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω) := by
        calc
          ∑ ω, P ω * (((C0 : ℝ) - 1) + (M : ℝ) * (if C0 ≤ C ω then 1 else 0))
              = ∑ ω, (P ω * ((C0 : ℝ) - 1) +
                  (M : ℝ) * (if C0 ≤ C ω then P ω else 0)) :=
                  Finset.sum_congr rfl fun ω _ => hsplit ω
          _ = (∑ ω, P ω * ((C0 : ℝ) - 1)) +
                ∑ ω, (M : ℝ) * (if C0 ≤ C ω then P ω else 0) :=
                  Finset.sum_add_distrib
          _ = (∑ ω, P ω) * ((C0 : ℝ) - 1) +
                (M : ℝ) * (∑ ω, if C0 ≤ C ω then P ω else 0) := by
                  rw [Finset.sum_mul, Finset.mul_sum]
          _ = ((C0 : ℝ) - 1) + (M : ℝ) *
                (∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω) := by
                  rw [hP1, ← Finset.sum_filter]
                  ring
      have hCE : (C0 : ℝ) ≤ ((C0 : ℝ) - 1) + (M : ℝ) *
          (∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω) :=
        hExp.trans (hsum_bound.trans_eq hRHS)
      have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
      rw [div_le_iff₀ hMposR]
      nlinarith

/-- **Repetition, Sec. 4 p. 6.** If one independent trial succeeds with
probability `p₀ ≥ 1/M`, then `N` independent trials produce the threshold cut with
probability `1 − (1 − p₀)^N`; whenever `(1 − 1/M)^N ≤ 1/3` this is at least
`2/3`.  The product-measure identity for independent trials is standard and is
recorded here at the level of success probabilities. -/
theorem repeated_success_ge (p₀ : ℝ) (M N : ℕ) (hM : 1 ≤ M)
    (hp0 : (1 : ℝ) / M ≤ p₀) (hp1 : p₀ ≤ 1)
    (hN : (1 - (1 : ℝ) / M) ^ N ≤ 1 / 3) :
    (2 : ℝ) / 3 ≤ 1 - (1 - p₀) ^ N := by
  have hbase0 : 0 ≤ 1 - p₀ := by linarith
  have hfac : 1 - p₀ ≤ 1 - (1 : ℝ) / M := by linarith
  have hmono : (1 - p₀) ^ N ≤ (1 - (1 : ℝ) / M) ^ N :=
    pow_le_pow_left₀ hbase0 hfac N
  linarith

/-- **Paper's `2/3` guarantee, fully composed.** Combine Eq. (12) with the
repetition step: if `N` independent samples are taken and
`(1 − 1/M)^N ≤ 1/3`, then the threshold cut `C ≥ C0 = ⌊|E| c̃_edge(p)⌋` appears
among them with probability at least `2/3`. -/
theorem paper_two_thirds_guarantee
    (P : Ω → ℝ) (C : Ω → ℕ) (M C0 N : ℕ)
    (hP0 : ∀ ω, 0 ≤ P ω) (hP1 : ∑ ω, P ω = 1)
    (hCtop : ∀ ω, C ω ≤ M) (hExp : (C0 : ℝ) ≤ ∑ ω, P ω * (C ω : ℝ))
    (hC0le : C0 ≤ M) (hM : 1 ≤ M)
    (hN : (1 - (1 : ℝ) / M) ^ N ≤ 1 / 3) :
    (2 : ℝ) / 3 ≤ 1 - (1 - ∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω) ^ N := by
  have hp0 := one_sample_prob_ge P C M C0 hP0 hP1 hCtop hExp hC0le
  have hp1 : (∑ ω ∈ (Finset.univ.filter fun ω => C0 ≤ C ω), P ω) ≤ 1 := by
    rw [← hP1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => hP0 x)
  exact repeated_success_ge _ M N hM hp0 hp1 hN

/-- **Runtime `O(|E(G)|²)`, Sec. 4 p. 5.** If one QAOA round costs at most
`K * |E(G)|` gates (the paper's `O(|E(G)|)` gate count at fixed depth) and at most
`N` rounds are run, the total gate count is at most `K * |E| * N`; for
`N ≤ 2 |E|` rounds this is at most `2 K |E|²`. -/
theorem repetition_gate_bound (K M N : ℕ) (hN : N ≤ 2 * M) :
    K * M * N ≤ 2 * K * M ^ 2 := by
  have hMN : M * N ≤ M * (2 * M) := Nat.mul_le_mul_left M hN
  calc
    K * M * N = K * (M * N) := by ring
    _ ≤ K * (M * (2 * M)) := Nat.mul_le_mul_left K hMN
    _ = 2 * K * M ^ 2 := by ring

end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut
