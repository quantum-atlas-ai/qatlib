/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.Lemma2Shots
import Qatlib.Papers.RepMultiplic24.MainResults.Lemma6GateCount

set_option backward.isDefEq.respectTransparency false

/-!
# RepMultiplic24.MainResults.Lemma7KroneckerGates

Paper: *Quantum Algorithms for Representation-Theoretic Multiplicities*,
fixed arXiv:2407.17649 (2024), Claim `c010` = Lemma 7 (main text p. 8).

Lemma 7: let `d_λ = d_ν ≥ d_μ` with `d_μ ≤ n^k`. Then Algorithm 1 uses
`O(n^{2k+4})` gates and finds `g_{μλλ}` with constant probability.

Proof route (paper):

* the sampling probability is `g_{μλλ}/d_μ` (Eq. (113)), so Lemma 2 needs
  `O(d_μ²) = O(n^{2k})` shots because `d_μ ≤ n^k`;
* by Lemma 6 (claim `c009`) each shot uses `O(n^4)` gates;
* the product is `O(n^{2k})·O(n^4) = O(n^{2k+4})`.

Formalisation: `N` is again the `⌈32/ε²⌉` shot count of
`shots_constant_probability`, now bounded by `33 n^{2k}`; the per-shot
`KroneckerShot n` budget of Lemma 6 gives the total `99 n^{2k+4}`. The
probability conclusion is proved outright (Lemma 2 is complete); the gate
conclusion is proved from the accounting of Lemma 6. There is no `sorry` in
this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.RepMultiplic24.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped BigOperators unitInterval

/-- **Lemma 7 (c010).** If `d_μ ≤ n^k` and `g = g_{μλλ} ≤ d_μ`, then

* `g` is determined with probability at least `1/2` from `O(n^{2k})` shots, and
* every shot uses `O(n^4)` gates (Lemma 6), so the total is at most
  `99 n^{2k+4}` gates.

Paper: fixed arXiv:2407.17649, Lemma 7, with Eq. (113), Lemma 2 and Lemma 6. -/
theorem lemma7_kronecker_gates (n k dμ g : ℕ)
    (hn : 1 ≤ n) (hdμ : 0 < dμ) (hg : 0 < g) (hgprob : g ≤ dμ)
    (hdμbound : dμ ≤ n ^ k) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ 33 * (n : ℝ) ^ (2 * k) ∧
      probEvent
        (bernoulliLaw
          ⟨(g : ℝ) / (dμ : ℝ),
            by positivity,
            by
              rw [div_le_one (by exact_mod_cast hdμ)]
              exact_mod_cast hgprob⟩)
        (fun ω : Fin N → Bool => frequencyEstimate (1 / (dμ : ℝ)) ω = g) ≥ 1 / 2 ∧
      ∀ s : KroneckerShot n, ((N * s.perShot : ℕ) : ℝ) ≤ 99 * (n : ℝ) ^ (2 * k + 4) := by
  classical
  have hdμ0 : (0 : ℝ) < (dμ : ℝ) := by exact_mod_cast hdμ
  have hg0 : (0 : ℝ) ≤ (g : ℝ) := by positivity
  have hgle : (g : ℝ) ≤ (dμ : ℝ) := by exact_mod_cast hgprob
  set p : I :=
    ⟨(g : ℝ) / (dμ : ℝ),
      by positivity,
      by rw [div_le_one hdμ0]; exact hgle⟩ with hpdef
  have hpm : (p : ℝ) = (g : ℝ) * (1 / (dμ : ℝ)) := by
    simp only [hpdef]
    field_simp
  have hε : (0 : ℝ) < 1 / (dμ : ℝ) := by positivity
  obtain ⟨N, hN, hbound, hprob⟩ := shots_constant_probability p hε hpm
  refine ⟨N, hN, ?_, hprob, ?_⟩
  · -- `32/(1/d_μ)² + 1 = 32 d_μ² + 1 ≤ 33 d_μ² ≤ 33 n^{2k}`
    have hsimple : (32 : ℝ) / (1 / (dμ : ℝ)) ^ 2 + 1 = 32 * (dμ : ℝ) ^ 2 + 1 := by
      field_simp
    have hdμ1 : (1 : ℝ) ≤ (dμ : ℝ) := by exact_mod_cast hdμ
    have hsq1 : (1 : ℝ) ≤ (dμ : ℝ) ^ 2 := by nlinarith [hdμ1]
    have hle : (dμ : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast hdμbound
    have hpow : (n : ℝ) ^ (2 * k) = ((n : ℝ) ^ k) ^ 2 := by
      rw [mul_comm 2 k, pow_mul]
    have hsq : (dμ : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) := by
      have h := mul_self_le_mul_self (le_of_lt hdμ0) hle
      rw [hpow]
      simpa [pow_two] using h
    nlinarith [hbound, hsimple, hsq1, hsq]
  · intro s
    have hper : ((s.perShot : ℕ) : ℝ) ≤ 3 * (n : ℝ) ^ 4 := by
      exact_mod_cast lemma6_per_shot_gates n hn s
    have hNspan : (N : ℝ) ≤ 33 * (n : ℝ) ^ (2 * k) := by
      -- the same bound as the second component
      have hsimple : (32 : ℝ) / (1 / (dμ : ℝ)) ^ 2 + 1 = 32 * (dμ : ℝ) ^ 2 + 1 := by
        field_simp
      have hdμ1 : (1 : ℝ) ≤ (dμ : ℝ) := by exact_mod_cast hdμ
      have hsq1 : (1 : ℝ) ≤ (dμ : ℝ) ^ 2 := by nlinarith [hdμ1]
      have hle : (dμ : ℝ) ≤ (n : ℝ) ^ k := by exact_mod_cast hdμbound
      have hpow : (n : ℝ) ^ (2 * k) = ((n : ℝ) ^ k) ^ 2 := by
        rw [mul_comm 2 k, pow_mul]
      have hsq : (dμ : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * k) := by
        have h := mul_self_le_mul_self (le_of_lt hdμ0) hle
        rw [hpow]
        simpa [pow_two] using h
      linarith [hbound, hsimple, hsq1, hsq]
    have hN' : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have hper0 : (0 : ℝ) ≤ ((s.perShot : ℕ) : ℝ) := by positivity
    have hright : (0 : ℝ) ≤ 33 * (n : ℝ) ^ (2 * k) := by positivity
    have hmul : ((N * s.perShot : ℕ) : ℝ) ≤
        (33 * (n : ℝ) ^ (2 * k)) * (3 * (n : ℝ) ^ 4) := by
      push_cast
      exact mul_le_mul hNspan hper hper0 hright
    calc ((N * s.perShot : ℕ) : ℝ) ≤ (33 * (n : ℝ) ^ (2 * k)) * (3 * (n : ℝ) ^ 4) := hmul
      _ = 99 * ((n : ℝ) ^ (2 * k) * (n : ℝ) ^ 4) := by ring
      _ = 99 * (n : ℝ) ^ (2 * k + 4) := by rw [← pow_add]

end Qatlib.Papers.RepMultiplic24.MainResults
