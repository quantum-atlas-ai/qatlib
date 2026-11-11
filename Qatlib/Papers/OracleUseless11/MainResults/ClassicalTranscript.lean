/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Data.Fin.Tuple.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Classical transcripts of adaptive query algorithms

Formal model for the classical query process of Harrow–Rosenbaum,
*Uselessness for an Oracle Model with Internal Randomness*, arXiv:1111.1462v2,
§2.1 (Algorithm 1) and §3.

A classical algorithm adaptively chooses a control `x_i` depending on the answers
to the previous queries; the oracle with internal randomness draws a fresh
internal state for every query (Algorithm 1, p. 2).  Consequently, if two oracle
devices induce the same law on the answer to a query at every control, then they
induce the same law on the full transcript of any adaptive algorithm, and in
particular no decision rule can distinguish them with unbounded error.

This file provides that reduction once and for all:

* `AnswerModel` — the answer law `x ↦ FinDist (Fin N)` of a device;
* `AdaptiveClassicalAlg` — an adaptive query function at every length;
* `prefixMass` / `transcriptLaw` — the law of the transcript, built by the chain
  rule from the per-query answer laws;
* `sum_prefixMass` — the transcript masses sum to one;
* `transcriptLaw_eq` — equality of the answer laws gives equality of the
  transcript laws;
* `successProb` and `not_both_win` — the two complementary success
  probabilities cannot both exceed `1/2` (“no unbounded-error solver”).
-/

namespace Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

set_option autoImplicit false

/-- The answer law of an oracle device: for each control `x`, a distribution
over the target answers `z`. -/
structure AnswerModel (N : ℕ) where
  /-- Law of the answer to a query with control `x`. -/
  law : Fin N → FinDist (Fin N)

/-- An adaptive classical algorithm, specified at every query length `i` by the
control `x_i` it queries after seeing the first `i` answers. -/
abbrev AdaptiveClassicalAlg (N : ℕ) := (i : ℕ) → (Fin i → Fin N) → Fin N

/-- Mass of a transcript prefix of length `i` under the answer model `M`: the
paper's Algorithm 1 draws a fresh permutation at every query, so the mass is the
product of the per-query answer laws along the adaptively chosen controls. -/
noncomputable def prefixMass {N : ℕ} (M : AnswerModel N) (A : AdaptiveClassicalAlg N) :
    (i : ℕ) → (Fin i → Fin N) → ℝ
  | 0, _ => 1
  | i + 1, t =>
      prefixMass M A i (fun j => t j.castSucc) *
        (M.law (A i (fun j => t j.castSucc))).prob (t (Fin.last i))

/-- Prefix masses are nonnegative. -/
theorem prefixMass_nonneg {N : ℕ} (M : AnswerModel N) (A : AdaptiveClassicalAlg N) :
    ∀ (i : ℕ) (t : Fin i → Fin N), 0 ≤ prefixMass M A i t
  | 0, _ => by simp [prefixMass]
  | i + 1, t => by
      simpa [prefixMass] using
        mul_nonneg (prefixMass_nonneg M A i (fun j => t j.castSucc))
          ((M.law (A i (fun j => t j.castSucc))).nonneg (t (Fin.last i)))

/-- **The transcript masses sum to one.**  Inductively the single-query answer
law is a probability distribution. -/
theorem sum_prefixMass {N : ℕ} (M : AnswerModel N) (A : AdaptiveClassicalAlg N) :
    ∀ i : ℕ, ∑ t : Fin i → Fin N, prefixMass M A i t = 1
  | 0 => by
      have hcard : (Finset.univ : Finset (Fin 0 → Fin N)).card = 1 := by simp
      simp [prefixMass]
  | i + 1 => by
      calc ∑ t : Fin (i + 1) → Fin N, prefixMass M A (i + 1) t
          = ∑ p : Fin N × (Fin i → Fin N), prefixMass M A (i + 1) (Fin.snoc p.2 p.1) := by
            rw [← (Fin.snocEquiv (fun _ : Fin (i + 1) => Fin N)).sum_comp
              (fun t => prefixMass M A (i + 1) t)]
            rfl
        _ = ∑ z : Fin N, ∑ t' : Fin i → Fin N,
              prefixMass M A i t' * (M.law (A i t')).prob z := by
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            refine Finset.sum_congr rfl (fun t' _ => ?_)
            simp [prefixMass, Fin.snoc_castSucc, Fin.snoc_last]
        _ = ∑ t' : Fin i → Fin N, ∑ z : Fin N,
              prefixMass M A i t' * (M.law (A i t')).prob z := Finset.sum_comm
        _ = ∑ t' : Fin i → Fin N, prefixMass M A i t' := by
            refine Finset.sum_congr rfl (fun t' _ => ?_)
            rw [← Finset.mul_sum, (M.law (A i t')).sum_one, mul_one]
        _ = 1 := sum_prefixMass M A i

/-- The transcript law of a `k`-query adaptive classical algorithm. -/
noncomputable def transcriptLaw {N : ℕ} (M : AnswerModel N)
    (A : AdaptiveClassicalAlg N) (k : ℕ) : FinDist (Fin k → Fin N) where
  prob t := prefixMass M A k t
  nonneg t := prefixMass_nonneg M A k t
  sum_one := sum_prefixMass M A k

/-- Extensionality of finite distributions by their probability mass function. -/
theorem FinDist.eq_of_prob_eq {X : Type*} [Fintype X] {p q : FinDist X}
    (h : ∀ x, p.prob x = q.prob x) : p = q := by
  cases p with
  | mk f hn hs =>
  cases q with
  | mk g hn' hs' =>
  simp only at h
  have hfg : f = g := funext h
  subst hfg
  rfl

/-- **Same answer law ⇒ same transcript law.**  This is the formal content of
“internal randomness effectively causes a different oracle to be used for each
query” (p. 2): the chain rule only ever uses the single-query answer laws. -/
theorem transcriptLaw_eq {N : ℕ} {M M' : AnswerModel N}
    (h : ∀ x : Fin N, M.law x = M'.law x)
    (A : AdaptiveClassicalAlg N) (k : ℕ) :
    transcriptLaw M A k = transcriptLaw M' A k := by
  have hprefix : ∀ (i : ℕ) (t : Fin i → Fin N), prefixMass M A i t = prefixMass M' A i t := by
    intro i
    induction i with
    | zero => intro t; rfl
    | succ i ih =>
        intro t
        simp only [prefixMass, ih (fun j => t j.castSucc)]
        rw [h (A i (fun j => t j.castSucc))]
  exact FinDist.eq_of_prob_eq (fun t => hprefix k t)

/-- Probability that a `k`-query transcript satisfies `E`. -/
noncomputable def eventProb {N : ℕ} (M : AnswerModel N) (A : AdaptiveClassicalAlg N)
    (k : ℕ) (E : (Fin k → Fin N) → Prop) : ℝ :=
  by classical exact ∑ t : Fin k → Fin N, if E t then (transcriptLaw M A k).prob t else 0

/-- Acceptance probability of a classical decision rule `D` (`true` = “accept”). -/
noncomputable def acceptProb {N : ℕ} (M : AnswerModel N) (A : AdaptiveClassicalAlg N)
    (k : ℕ) (D : (Fin k → Fin N) → Bool) : ℝ :=
  eventProb M A k (fun t => D t = true)

/-- Equal answer laws give equal acceptance probabilities for every decision
rule. -/
theorem acceptProb_eq_of_law_eq {N : ℕ} {M M' : AnswerModel N}
    (h : ∀ x : Fin N, M.law x = M'.law x) (A : AdaptiveClassicalAlg N) (k : ℕ)
    (D : (Fin k → Fin N) → Bool) :
    acceptProb M A k D = acceptProb M' A k D := by
  classical
  unfold acceptProb eventProb
  rw [transcriptLaw_eq h A k]

/-- **No unbounded-error distinguisher.**  If two devices have the same answer
law, then the success probabilities of any decision rule for telling them apart
are complementary, so they cannot both exceed `1/2`.  (The paper's “cannot solve
with unbounded error using any number of queries”, p. 2.) -/
theorem not_both_win {N : ℕ} {M M' : AnswerModel N}
    (h : ∀ x : Fin N, M.law x = M'.law x) (A : AdaptiveClassicalAlg N) (k : ℕ)
    (D : (Fin k → Fin N) → Bool) :
    ¬ (1 / 2 < acceptProb M A k D ∧ 1 / 2 < 1 - acceptProb M' A k D) := by
  rw [acceptProb_eq_of_law_eq h A k D]
  intro hcon
  linarith [hcon.1, hcon.2]

end Qatlib.Papers.OracleUseless11.MainResults
