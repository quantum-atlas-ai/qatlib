/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.2 of TriangleFind14

François Le Gall, *Improved Quantum Algorithm for Triangle Finding via
Combinatorial Arguments*, fixed version arXiv:1407.0085v2 (8 Sep 2014),
Lemma 4.2, printed p. 10.

"Let `A` and `X` be two subsets of `V`, and assume that `Δ_G(X,A)` is known.
Let `m` be a positive integer.  There exists a classical deterministic algorithm
`𝒜` with query complexity `O(m log n)`, which receives as input a binary string
`s` of length `poly(m, log n)` and a vertex `w ∈ V`, and outputs a real number
`𝒜(s,w)` satisfying the following condition: for a fraction at least `1 - 3/n`
of the strings `s`, the inequalities

`1/3 · |Δ_G(X,A,w)| ≤ 𝒜(s,w) ≤ 3/2 · max(|A|(|A|-1)/(2m), |Δ_G(X,A,w)|)`

hold for all vertices `w ∈ V`."

The deterministic algorithm is represented by its input length `strLen`, its
output `run s w`, and its query count `queryCount`; `O(m log n)` is represented
by `c · m · (log₂ n + 1)`.

This layer is a conditional theorem.  The hypothesis `hAlg` isolates the
unformalized components: the estimator itself (query count within the
`O(m log n)` budget) together with the aggregate per-vertex failure bound
`∑_w P[estimate at w fails] ≤ 2/n` — in the paper this bound comes from the
Chernoff estimates of the three regimes (each `1 - 3/n²` per vertex,
pp. 10–12).  What is proved here is the paper's final union bound layer: the
all-`w` failure event is the union of the per-`w` failure events, so its
probability is at most `2/n ≤ 3/n` for `n ≥ 2`, and complementing within the
finite advice-string space gives the `1 - 3/n` success fraction.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.TriangleFind14.MainResults

/-- A deterministic estimator with a binary advice string and a paid query
count: the observable interface of the algorithm `𝒜` of Lemma 4.2. -/
structure ClassicalEstimationAlgorithm (n m : ℕ) where
  /-- Length `poly(m, log n)` of the random/advice string. -/
  strLen : ℕ
  /-- Output `𝒜(s,w)` on advice string `s` and vertex `w`. -/
  run : (Fin strLen → Bool) → Fin n → ℝ
  /-- Worst-case number of oracle queries. -/
  queryCount : ℕ

/-- The event that the estimate `A.run s w` of `|Δ_G(X,A,w)|` falls outside the
two-sided window of Lemma 4.2 at the vertex `w`. -/
def estimateFailsAt (n m : ℕ) (A : ClassicalEstimationAlgorithm n m)
    (G : SimpleGraph (Fin n)) (X Aset : Finset (Fin n)) (w : Fin n)
    (s : Fin A.strLen → Bool) : Prop :=
  ¬ ((1 / 3) * ((deltaSetW G X Aset w).card : ℝ) ≤ A.run s w ∧
      A.run s w ≤ (3 / 2) * max
        (((Aset.card : ℝ) * ((Aset.card : ℝ) - 1)) / (2 * (m : ℝ)))
        ((deltaSetW G X Aset w).card : ℝ))

/-- Lemma 4.2 of arXiv:1407.0085v2 (printed p. 10, proof pp. 10–12,
Algorithm `A′` in Figure 1), conditional union-bound form.  Given an estimator
with `O(m log n)` queries whose summed per-vertex failure probabilities are at
most `2/n`, a `1 - 3/n` fraction of advice strings satisfy the paper's
two-sided estimate simultaneously for all `w`.

The unformalized gap is the estimator construction and its Chernoff estimates:
the algorithm of Figure 1 samples `m` pairs of `E(A)` `⌈240 log n⌉` times,
branches on whether more than half the trials hit `Δ_G(X,A,w)`, and in the
second branch samples `{u,v} ∈ E(A)` `⌈72 m log n⌉` times; Chernoff bounds give
the per-vertex `1 - 3/n²` in the three regimes `|Δ| < |E(A)|/(3m)`,
`|E(A)|/(3m) ≤ |Δ| ≤ 3|E(A)|/m`, `|Δ| > 3|E(A)|/m`.  Candidate dependencies:
`ProbabilityTheory.chernoff`/`Mathlib.Probability.Moments`. -/
theorem source_lemma_4_2 (n m : ℕ) (_hm : 0 < m) (hn : 2 ≤ n)
    (hAlg : ∃ c : ℕ, 0 < c ∧ ∃ A : ClassicalEstimationAlgorithm n m,
      A.queryCount ≤ c * m * (Nat.log 2 n + 1) ∧
        ∀ (G : SimpleGraph (Fin n)) (X Aset : Finset (Fin n)),
          (∑ w : Fin n, uniformProb
              (fun s : Fin A.strLen → Bool => estimateFailsAt n m A G X Aset w s))
            ≤ 2 / (n : ℝ)) :
    ∃ c : ℕ, 0 < c ∧ ∃ A : ClassicalEstimationAlgorithm n m,
      A.queryCount ≤ c * m * (Nat.log 2 n + 1) ∧
        ∀ (G : SimpleGraph (Fin n)) (X Aset : Finset (Fin n)),
          uniformProb (fun s : Fin A.strLen → Bool =>
              ∀ w : Fin n,
                (1 / 3) * ((deltaSetW G X Aset w).card : ℝ) ≤ A.run s w ∧
                  A.run s w ≤ (3 / 2) * max
                    (((Aset.card : ℝ) * ((Aset.card : ℝ) - 1)) / (2 * (m : ℝ)))
                    ((deltaSetW G X Aset w).card : ℝ))
            ≥ 1 - 3 / (n : ℝ) := by
  classical
  obtain ⟨c, hc, A, hq, hper⟩ := hAlg
  refine ⟨c, hc, A, hq, ?_⟩
  intro G X Aset
  have hNE : Nonempty (Fin A.strLen → Bool) := ⟨fun _ => false⟩
  have hfail : uniformProb (fun s : Fin A.strLen → Bool =>
        ¬ ∀ w : Fin n,
          (1 / 3) * ((deltaSetW G X Aset w).card : ℝ) ≤ A.run s w ∧
            A.run s w ≤ (3 / 2) * max
              (((Aset.card : ℝ) * ((Aset.card : ℝ) - 1)) / (2 * (m : ℝ)))
              ((deltaSetW G X Aset w).card : ℝ))
      ≤ ∑ w : Fin n, uniformProb
          (fun s : Fin A.strLen → Bool => estimateFailsAt n m A G X Aset w s) := by
    refine uniformProb_union_bound (t := (Finset.univ : Finset (Fin n))) _ _ ?_
    intro s hs
    have h1 : ∃ w : Fin n, estimateFailsAt n m A G X Aset w s := by
      by_contra hc
      push Not at hc
      exact hs (fun w => not_not.mp (hc w))
    obtain ⟨w, hw⟩ := h1
    exact ⟨w, Finset.mem_univ w, hw⟩
  have h1 : uniformProb (fun s : Fin A.strLen → Bool =>
        ¬ ∀ w : Fin n,
          (1 / 3) * ((deltaSetW G X Aset w).card : ℝ) ≤ A.run s w ∧
            A.run s w ≤ (3 / 2) * max
              (((Aset.card : ℝ) * ((Aset.card : ℝ) - 1)) / (2 * (m : ℝ)))
              ((deltaSetW G X Aset w).card : ℝ)) ≤ 2 / (n : ℝ) :=
    le_trans hfail (hper G X Aset)
  have h2 := uniformProb_compl
    (p := fun s : Fin A.strLen → Bool =>
      ∀ w : Fin n,
        (1 / 3) * ((deltaSetW G X Aset w).card : ℝ) ≤ A.run s w ∧
          A.run s w ≤ (3 / 2) * max
            (((Aset.card : ℝ) * ((Aset.card : ℝ) - 1)) / (2 * (m : ℝ)))
            ((deltaSetW G X Aset w).card : ℝ))
  have h23 : (2 : ℝ) / (n : ℝ) ≤ 3 / (n : ℝ) := by
    have h1 : (3 : ℝ) / (n : ℝ) - (2 : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by ring
    have h2 : (0 : ℝ) < 1 / (n : ℝ) := by positivity
    linarith
  linarith

end Qatlib.Papers.TriangleFind14.MainResults
