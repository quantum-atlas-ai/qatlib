/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-! # NearestLearn14 — source query bounds

Wiebe–Kapoor–Svore, *Quantum Algorithms for Nearest–Neighbor Methods for
Supervised and Unsupervised Learning*, fixed arXiv:1401.2142v1 (2014).

This file carries the paper-layer statements of the quantitative query bounds:
Theorem 1 (Sec. III, p. 5), Theorem 2 (Sec. V, p. 7), Corollary 3 (p. 11),
Lemma 8 (Appendix B.2, p. 19), Corollary 9 (p. 20), Lemma 12 (Appendix B.3,
p. 24) and Lemma 14 (p. 30).

The formalization records the arithmetic composition that the paper performs in
Appendix B: the search bound of Corollary 9 is instantiated with the state
preparation budgets of Lemma 11 (`|a₀| = 8/π²`) and Lemma 12
(`|a₀| = 64/π⁴`), and with the un-normalized k-means distance budget of
(B41) (`|a₀| = 8/π²`, one amplitude instead of two).  The paper's quantum
algorithmic side (the samplers and circuits realizing those amplitudes) is
consumed as the input budget `Q`; it is exactly the interface at which the
shared Frozen blocks `Qatlib.Concepts.AmplitudeCore.AmplifyCore`
(deterministic amplification from a known amplitude) and
`Qatlib.Concepts.QueryComplexity.Amplification`
(query accounting for repeated subroutines) are reused.

Boundary: these theorems state the source's closed-form query counts and the
composition identities between them; they do not re-derive the amplitude
estimation sampler itself (that is the Frozen
`Qatlib.Concepts.AEMeanReadout.*` layer).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NearestLearn14.MainResults.QueryBounds

/-- Euler–Mascheroni constant as fixed by the paper (`γ ≈ 0.5772`); the
statements below only use that it is a nonnegative real constant. -/
def eulerGamma : ℝ := 0.5772

/-- Lemma 11 (p. 22, eq. (B32)): the swap-test amplitude encoder of a pair of
`d`-sparse vectors uses `Q ≤ 12⌈4π(π+1)d²r₀max²r_jmax²/ε⌉` oracle queries. -/
def lemma11Queries (d : ℕ) (r0max rjmax ε : ℝ) : ℕ :=
  12 * Nat.ceil (4 * Real.pi * (Real.pi + 1) * (d : ℝ) ^ 2 * r0max ^ 2 * rjmax ^ 2 / ε)

/-- Lemma 12 (p. 24, eq. (B42)): the nested (distance and variance) encoder
uses `Q ≤ 10⌈8π(π+1)d r_max²/ε⌉` oracle queries. -/
def lemma12Queries (d : ℕ) (rmax ε : ℝ) : ℕ :=
  10 * Nat.ceil (8 * Real.pi * (Real.pi + 1) * (d : ℝ) * rmax ^ 2 / ε)

/-- Corollary 3 (p. 11, proof; (B41)): one un-normalized one-amplitude distance
estimate costs `4⌈8π(π+1)d r_max²/ε⌉` queries. -/
def kMeansDistanceQueries (d : ℕ) (rmax ε : ℝ) : ℕ :=
  4 * Nat.ceil (8 * Real.pi * (Real.pi + 1) * (d : ℝ) * rmax ^ 2 / ε)

/-- Corollary 9 (p. 20, eq. (B18)): `90√M·Q·⌈ln(81M(ln M+γ)/δ₀)/(2(|a₀|−1/2)²)⌉`
expected queries for finding the minimum with failure probability `δ₀`. -/
def searchQueries (M Q : ℕ) (a0 δ0 : ℝ) : ℝ :=
  90 * Real.sqrt (M : ℝ) * (Q : ℝ) *
    (Nat.ceil (Real.log (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma) / δ0) /
      (2 * (a0 - 1 / 2) ^ 2)) : ℝ)

/-- Theorem 1 (p. 5): `1080√M⌈4π(π+1)d²r_max⁴/ε⌉⌈ln(81M(ln M+γ)/δ₀)/(2(8/π²−1/2)²)⌉`. -/
def theorem1Queries (M d : ℕ) (rmax ε δ0 : ℝ) : ℝ :=
  1080 * Real.sqrt (M : ℝ) *
    (Nat.ceil (4 * Real.pi * (Real.pi + 1) * (d : ℝ) ^ 2 * rmax ^ 4 / ε) : ℝ) *
    (Nat.ceil (Real.log (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma) / δ0) /
      (2 * (8 / Real.pi ^ 2 - 1 / 2) ^ 2)) : ℝ)

/-- Theorem 2 (p. 7): `900√M′⌈8π(π+1)d r_max²/ε⌉⌈log(81M′(log M′+γ)/δ₀)/(2((8/π²)²−1/2)²)⌉`. -/
def theorem2Queries (M' d : ℕ) (rmax ε δ0 : ℝ) : ℝ :=
  900 * Real.sqrt (M' : ℝ) *
    (Nat.ceil (8 * Real.pi * (Real.pi + 1) * (d : ℝ) * rmax ^ 2 / ε) : ℝ) *
    (Nat.ceil (Real.log (81 * (M' : ℝ) * (Real.log (M' : ℝ) + eulerGamma) / δ0) /
      (2 * ((8 / Real.pi ^ 2) ^ 2 - 1 / 2) ^ 2)) : ℝ)

/-- Corollary 3 (p. 11): `360M√k⌈8π(π+1)d r_max²/ε⌉⌈log(81k(log k+γ)/δ₀)/(2(8/π²−1/2)²)⌉`
average queries per training vector and k-means iteration. -/
def corollary3Queries (M k d : ℕ) (rmax ε δ0 : ℝ) : ℝ :=
  360 * (M : ℝ) * Real.sqrt (k : ℝ) *
    (Nat.ceil (8 * Real.pi * (Real.pi + 1) * (d : ℝ) * rmax ^ 2 / ε) : ℝ) *
    (Nat.ceil (Real.log (81 * (k : ℝ) * (Real.log (k : ℝ) + eulerGamma) / δ0) /
      (2 * (8 / Real.pi ^ 2 - 1 / 2) ^ 2)) : ℝ)

/-- Lemma 8 (p. 19, eq. (B12)): the number of coherent copies whose median
succeeds outside the bad subspace with probability at least `1 − Δ`,
`k = ⌈ln(1/Δ)/(2(|a₀|−1/2)²)⌉`. -/
def lemma8Copies (Δ a0 : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / Δ) / (2 * (a0 - 1 / 2) ^ 2))

/-- Theorem 1 as the paper derives it (Appendix B.1, last paragraph): the
`1080√M⌈·⌉⌈·⌉` count is Corollary 9 instantiated with the Lemma 11 budget
`Q = 12⌈4π(π+1)d²r_max²r_max²/ε⌉` and the swap-test success amplitude
`|a₀| = 8/π²`, with `r₀max = r_jmax = r_max`.  This is the arithmetic
identity `90·12 = 1080` together with `r_max²·r_max² = r_max⁴`. -/
theorem theorem1_queryBudget (M d : ℕ) (rmax ε δ0 : ℝ) :
    searchQueries M (lemma11Queries d rmax rmax ε) (8 / Real.pi ^ 2) δ0
      = theorem1Queries M d rmax ε δ0 := by
  unfold searchQueries lemma11Queries theorem1Queries
  have harg :
      4 * Real.pi * (Real.pi + 1) * (d : ℝ) ^ 2 * rmax ^ 2 * rmax ^ 2 / ε
        = 4 * Real.pi * (Real.pi + 1) * (d : ℝ) ^ 2 * rmax ^ 4 / ε := by
    ring
  rw [harg]
  push_cast
  ring

/-- Theorem 1 upper bound, in the form used by the paper: if the encoding
algorithm uses at most the Lemma 11 budget then the search uses at most the
announced `1080√M⌈·⌉⌈·⌉` queries. -/
theorem theorem1_query_upperBound (M d : ℕ) (rmax ε δ0 : ℝ) (Q : ℕ)
    (hQ : Q ≤ lemma11Queries d rmax rmax ε) :
    searchQueries M Q (8 / Real.pi ^ 2) δ0 ≤ theorem1Queries M d rmax ε δ0 := by
  rw [← theorem1_queryBudget]
  unfold searchQueries
  have h1 : (Q : ℝ) ≤ (lemma11Queries d rmax rmax ε : ℝ) := by exact_mod_cast hQ
  have hC : (0 : ℝ) ≤ (Nat.ceil
      (Real.log (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma) / δ0) /
        (2 * (8 / Real.pi ^ 2 - 1 / 2) ^ 2)) : ℝ) := by positivity
  have hcoef : (0 : ℝ) ≤ 90 * Real.sqrt (M : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hC) hcoef]

/-- Theorem 2 (p. 7) as the composition stated in its proof ("follows as a
trivial consequence of taking `M = M′` in Corollary 9, applying Lemma 12"):
`90·10 = 900` and `|a₀| = (8/π²)² = 64/π⁴`. -/
theorem theorem2_queryBudget (M' d : ℕ) (rmax ε δ0 : ℝ) :
    searchQueries M' (lemma12Queries d rmax ε) ((8 / Real.pi ^ 2) ^ 2) δ0
      = theorem2Queries M' d rmax ε δ0 := by
  unfold searchQueries lemma12Queries theorem2Queries
  push_cast
  ring

/-- Lemma 12 (p. 24, (B40)–(B41)): the nested amplification amplitude is the
square of the single-query Born mass, `(8/π²)² = 64/π⁴`, which the paper uses
as `|a₀|` in the outer Corollary 9 search. -/
theorem lemma12_nestedAmplitude :
    (8 / Real.pi ^ 2) ^ 2 = 64 / Real.pi ^ 4 := by
  rw [div_pow]
  ring

/-- Lemma 12 (p. 24, (B41)–(B42)): the query budget is the sum of a six-call
distance-emission stage and a four-call variance-emission stage, so
`6⌈·⌉ + 4⌈·⌉ = 10⌈·⌉`, the announced Lemma 12 bound. -/
theorem lemma12_queryComposition (C : ℕ) : 6 * C + 4 * C = 10 * C := by
  ring

/-- Theorem 2 upper bound: the Lemma 12 budget yields the announced
`900√M′⌈·⌉⌈·⌉` bound. -/
theorem theorem2_query_upperBound (M' d : ℕ) (rmax ε δ0 : ℝ) (Q : ℕ)
    (hQ : Q ≤ lemma12Queries d rmax ε) :
    searchQueries M' Q ((8 / Real.pi ^ 2) ^ 2) δ0 ≤ theorem2Queries M' d rmax ε δ0 := by
  rw [← theorem2_queryBudget]
  unfold searchQueries
  have h1 : (Q : ℝ) ≤ (lemma12Queries d rmax ε : ℝ) := by exact_mod_cast hQ
  have hC : (0 : ℝ) ≤ (Nat.ceil
      (Real.log (81 * (M' : ℝ) * (Real.log (M' : ℝ) + eulerGamma) / δ0) /
        (2 * ((8 / Real.pi ^ 2) ^ 2 - 1 / 2) ^ 2)) : ℝ) := by positivity
  have hcoef : (0 : ℝ) ≤ 90 * Real.sqrt (M' : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hC) hcoef]

/-- Corollary 3 (p. 11): per training vector the k-means iteration needs the
un-normalized distance estimate (B41), hence `Q = 4⌈8π(π+1)d r_max²/ε⌉` and
`|a₀| = 8/π²` inside Corollary 9; averaging over the `M` training vectors gives
`90·4 = 360`. -/
theorem corollary3_queryBudget (M k d : ℕ) (rmax ε δ0 : ℝ) :
    (M : ℝ) * searchQueries k (kMeansDistanceQueries d rmax ε) (8 / Real.pi ^ 2) δ0
      = corollary3Queries M k d rmax ε δ0 := by
  unfold searchQueries kMeansDistanceQueries corollary3Queries
  push_cast
  ring

/-- Corollary 3 upper bound. -/
theorem corollary3_query_upperBound (M k d : ℕ) (rmax ε δ0 : ℝ) (Q : ℕ)
    (hQ : Q ≤ kMeansDistanceQueries d rmax ε) :
    (M : ℝ) * searchQueries k Q (8 / Real.pi ^ 2) δ0 ≤ corollary3Queries M k d rmax ε δ0 := by
  rw [← corollary3_queryBudget]
  unfold searchQueries
  have h1 : (Q : ℝ) ≤ (kMeansDistanceQueries d rmax ε : ℝ) := by exact_mod_cast hQ
  have hC : (0 : ℝ) ≤ (Nat.ceil
      (Real.log (81 * (k : ℝ) * (Real.log (k : ℝ) + eulerGamma) / δ0) /
        (2 * (8 / Real.pi ^ 2 - 1 / 2) ^ 2)) : ℝ) := by positivity
  have hstep : (Q : ℝ) * (Nat.ceil
      (Real.log (81 * (k : ℝ) * (Real.log (k : ℝ) + eulerGamma) / δ0) /
        (2 * (8 / Real.pi ^ 2 - 1 / 2) ^ 2)) : ℝ)
      ≤ (kMeansDistanceQueries d rmax ε : ℝ) * (Nat.ceil
      (Real.log (81 * (k : ℝ) * (Real.log (k : ℝ) + eulerGamma) / δ0) /
        (2 * (8 / Real.pi ^ 2 - 1 / 2) ^ 2)) : ℝ) :=
    mul_le_mul_of_nonneg_right h1 hC
  have hcoef : (0 : ℝ) ≤ (M : ℝ) * (90 * Real.sqrt (k : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hstep hcoef]

/-- Lemma 8 (p. 19, (B11)–(B12)): with `|a| ≥ |a₀| > 1/2`, `k` coherent copies
put the probability of a wrong median below `Δ`, because the Hoeffding bound
`exp(−2k(|a₀|−1/2)²)` is at most `Δ` for the paper's `k`. -/
theorem lemma8_copyCount_error (Δ a0 : ℝ) (hΔ : 0 < Δ) (ha0 : 1 / 2 < a0) :
    Real.exp (-(2 * (lemma8Copies Δ a0 : ℝ) * (a0 - 1 / 2) ^ 2)) ≤ Δ := by
  have hc : (0 : ℝ) < 2 * (a0 - 1 / 2) ^ 2 := by nlinarith
  have hk : Real.log (1 / Δ) / (2 * (a0 - 1 / 2) ^ 2) ≤ (lemma8Copies Δ a0 : ℝ) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hc] at hk
  have hlog : Real.log (1 / Δ) = -Real.log Δ := by
    rw [one_div, Real.log_inv]
  have hineq : -(2 * (lemma8Copies Δ a0 : ℝ) * (a0 - 1 / 2) ^ 2) ≤ Real.log Δ := by
    rw [hlog] at hk
    linarith
  calc Real.exp (-(2 * (lemma8Copies Δ a0 : ℝ) * (a0 - 1 / 2) ^ 2))
      ≤ Real.exp (Real.log Δ) := Real.exp_le_exp.mpr hineq
    _ = Δ := Real.exp_log hΔ

/-- Lemma 8 (p. 19, eq. (B14)): if the good mass satisfies `1 − |A|² ≤ Δ`, then
the uncomputed state is within `√(2Δ)` of the target state, the distance
written `‖|Ψ⟩ − |0^⊗nk⟩|y⟩‖₂ ≤ √(2Δ)` in the paper. -/
theorem lemma8_stateDistance (A Δ : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hΔ : 1 - A ^ 2 ≤ Δ) :
    Real.sqrt (2 * (1 - A ^ 2)) ≤ Real.sqrt (2 * Δ) := by
  apply Real.sqrt_le_sqrt
  nlinarith

/-- Corollary 9 (p. 20): the announced `90√M Q⌈ln(81M(ln M+γ)/δ₀)/(2(|a₀|−1/2)²)⌉`
is the Dürr–Høyer search cost `2·(45√M)` (Lemma 7, two oracle calls per
iteration) times the Lemma 8 deterministic amplification cost `Q·k`, with
`k = ⌈ln(1/Δ)/(2(|a₀|−1/2)²)⌉` at `Δ = δ₀/(81M(ln M+γ))` (B15)–(B17). -/
theorem corollary9_queryBudget (M Q : ℕ) (a0 δ0 : ℝ) (hM : 0 < M) (hδ0 : 0 < δ0) :
    searchQueries M Q a0 δ0
      = 2 * (45 * Real.sqrt (M : ℝ)) *
          ((Q : ℝ) * (lemma8Copies
            (δ0 / (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma))) a0 : ℝ)) := by
  have hMle : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : (0 : ℝ) ≤ Real.log (M : ℝ) := Real.log_nonneg hMle
  have hγ : (0 : ℝ) < eulerGamma := by unfold eulerGamma; norm_num
  have hX : (0 : ℝ) < 81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma) := by nlinarith
  have hXne : (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma)) ≠ 0 := ne_of_gt hX
  have hδne : δ0 ≠ 0 := ne_of_gt hδ0
  have harg : Real.log (1 / (δ0 / (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma))))
      = Real.log (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma) / δ0) := by
    rw [show 1 / (δ0 / (81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma)))
        = 81 * (M : ℝ) * (Real.log (M : ℝ) + eulerGamma) / δ0 by
      field_simp]
  unfold searchQueries lemma8Copies
  rw [harg]
  push_cast
  ring

/-- Lemma 14 (p. 30): if each of the `k` nearest-neighbour rounds costs at most
`Q` queries (the paper's induction step removes the already-found vectors from
the Grover oracle at no query cost), then the `k`-nearest-neighbour algorithm
costs at most `kQ` queries in total. -/
theorem lemma14_kNearest_cost (k Q : ℕ) (cost : Fin k → ℕ) (h : ∀ i, cost i ≤ Q) :
    ∑ i, cost i ≤ k * Q := by
  calc ∑ i, cost i ≤ ∑ _i : Fin k, Q := Finset.sum_le_sum (fun i _ => h i)
    _ = k * Q := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Qatlib.Papers.NearestLearn14.MainResults.QueryBounds
