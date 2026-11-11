/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneShotLDPC23.MainResults.Stochastic.RepeatedRounds
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

set_option backward.isDefEq.respectTransparency false

/-!
# OneShotLDPC23.MainResults.Stochastic.NoiseTail — Corollary 3.8

Fixed paper: **arXiv:2306.12470v2**, §3.3, pp. 11–12.

**Corollary 3.8.**  Let `{(eᵢ, Dᵢ)}_{i=1}^M` be data and syndrome errors whose
marginal distributions are `p`- and `q`-bounded (Definition 3.7: for every
`B`, `Σ_{B' ⊇ B} E(B') ≤ p^{|B|}`).  Running the decoder with fresh syndrome
measurements in each round, the final residual error satisfies

  `Pr(|e'_M|_R > (αR+βS)/(1−α) · n) ≤ M (e^{−n ln(2^{−H(R)} p^{−R})} + e^{−n ln(2^{−ϱH(S/ϱ)} q^{−S})})`,

with `H(τ) = −τ log₂ τ − (1−τ) log₂(1−τ)` the binary entropy and `ϱ = r_Z/n`.

Source proof: `Pr(|eᵢ| > Rn) ≤ C(n, Rn) p^{Rn} ≤ 2^{nH(R)} p^{Rn}`
(binomial-entropy bound), then Corollary 3.6.

`tailExp n H p R` is the paper's exponential `e^{−n ln(2^{−H} p^{−R})}`;
`Real.binEntropy R / Real.log 2` is `H(R)` since `H` is base-2 entropy.
The reduction to Corollary 3.6 is proved here; the per-round tail bound
`Pr(|eᵢ| > Rn) ≤ tailExp n H(R) p R` is the input hypothesis
`hdata_tail` (its proof is the binomial-entropy step, which Mathlib does not
provide — see the note below).
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults.Stochastic

open Model
open scoped BigOperators

/-- The exponential rate `e^{−n ln(2^{−H} p^{−R})}` of Corollary 3.8, with
`H = H(R)` the binary entropy in nats divided by `ln 2`. -/
noncomputable def tailExp (n H p R : ℝ) : ℝ :=
  Real.exp (-(n * Real.log ((2 : ℝ) ^ (-H) * p ^ (-R))))

/-- **Source Corollary 3.8** (arXiv:2306.12470v2, §3.3 p. 11).

Given the per-round `p`-bounded / `q`-bounded tail bounds
`Pr(|eᵢ| > Rn) ≤ e^{−n ln(2^{−H(R)} p^{−R})}` and
`Pr(|Dᵢ| > Sn) ≤ e^{−n ln(2^{−ϱH(S/ϱ)} q^{−S})}`, the final residual error obeys
the same union bound as Corollary 3.6 with these two rates. -/
theorem corollary_3_8 {Ω : Type*} [Fintype Ω]
    (α β R S A B C n p q ϱ : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ : 0 ≤ β)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) (hn : 0 ≤ n)
    (hbudget : A * (roundBound α β R S + R) + B * S ≤ C)
    (mass : Ω → ℝ) (hmass : ∀ ω, 0 ≤ mass ω)
    (M : ℕ)
    (residual data syndrome : ℕ → Ω → ℝ)
    (hzero : ∀ ω, residual 0 ω = 0)
    (hstep : ∀ ω i, A * (residual i ω + data i ω) + B * syndrome i ω ≤ C * n →
      residual (i + 1) ω ≤ α * (residual i ω + data i ω) + β * syndrome i ω)
    (hdata_tail : ∀ i : ℕ,
      (Finset.univ.filter fun ω => R * n < data i ω).sum mass ≤
        tailExp n (Real.binEntropy R / Real.log 2) p R)
    (hsyndrome_tail : ∀ i : ℕ,
      (Finset.univ.filter fun ω => S * n < syndrome i ω).sum mass ≤
        tailExp n (ϱ * Real.binEntropy (S / ϱ) / Real.log 2) q S) :
    (Finset.univ.filter fun ω => roundBound α β R S * n < residual M ω).sum mass ≤
      M * (tailExp n (Real.binEntropy R / Real.log 2) p R +
        tailExp n (ϱ * Real.binEntropy (S / ϱ) / Real.log 2) q S) := by
  classical
  have hdata' : ∀ i : ℕ,
      (Finset.univ.filter fun ω => R * n < data i ω).sum mass ≤
        Real.exp (-(Real.log ((2 : ℝ) ^ (-(Real.binEntropy R / Real.log 2)) *
          p ^ (-R)) * n)) := by
    intro i
    have h := hdata_tail i
    have he : tailExp n (Real.binEntropy R / Real.log 2) p R =
        Real.exp (-(Real.log ((2 : ℝ) ^ (-(Real.binEntropy R / Real.log 2)) *
          p ^ (-R)) * n)) := by
      unfold tailExp
      congr 1
      ring
    rwa [he] at h
  have hsyn' : ∀ i : ℕ,
      (Finset.univ.filter fun ω => S * n < syndrome i ω).sum mass ≤
        Real.exp (-(Real.log ((2 : ℝ) ^ (-(ϱ * Real.binEntropy (S / ϱ) / Real.log 2)) *
          q ^ (-S)) * n)) := by
    intro i
    have h := hsyndrome_tail i
    have he : tailExp n (ϱ * Real.binEntropy (S / ϱ) / Real.log 2) q S =
        Real.exp (-(Real.log ((2 : ℝ) ^ (-(ϱ * Real.binEntropy (S / ϱ) / Real.log 2)) *
          q ^ (-S)) * n)) := by
      unfold tailExp
      congr 1
      ring
    rwa [he] at h
  have hmain := corollary_3_6 α β R S A B C n
    (Real.log ((2 : ℝ) ^ (-(Real.binEntropy R / Real.log 2)) * p ^ (-R)))
    (Real.log ((2 : ℝ) ^ (-(ϱ * Real.binEntropy (S / ϱ) / Real.log 2)) * q ^ (-S)))
    hα0 hα1 hβ hA hB hR0 hS0 hn hbudget
    mass hmass M residual data syndrome hzero hstep hdata' hsyn'
  have h1 : Real.exp (-(Real.log ((2 : ℝ) ^ (-(Real.binEntropy R / Real.log 2)) *
        p ^ (-R)) * n)) = tailExp n (Real.binEntropy R / Real.log 2) p R := by
    unfold tailExp
    congr 1
    ring
  have h2 : Real.exp (-(Real.log ((2 : ℝ) ^ (-(ϱ * Real.binEntropy (S / ϱ) / Real.log 2)) *
        q ^ (-S)) * n)) = tailExp n (ϱ * Real.binEntropy (S / ϱ) / Real.log 2) q S := by
    unfold tailExp
    congr 1
    ring
  rwa [h1, h2] at hmain

end Qatlib.Papers.OneShotLDPC23.MainResults.Stochastic
