/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPictureDefs
import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# MainAlgorithm — Theorem 3, Theorem 15, Corollary 16 of InteractPic18

Low--Wiebe, *Hamiltonian Simulation in the Interaction Picture*,
fixed arXiv:1805.00675v2.

* Theorem 3 (p. 5, Appendix B p. 22--26): error `ε` segment simulation with
  the closed-form cutoff/grid schedule, `O(log(1/ε)/log log(1/ε))` HAM-T
  queries and `O(ε)` failure.
* Theorem 15 (Appendix C p. 26--28): the same statement with duplicated
  registers.
* Corollary 16 (Appendix D p. 30): compressed truncated Taylor simulation.

What is formalized here is the quantitative model level: the actual cutoff
`effectiveSegmentK p = computedDysonCutoff (p.precision+8)`, its integer
`log/log log` rate `K·log₂(K+2) ≤ C(K+2)`, the dyadic segment error
`(1/2)^{p.precision+6}` of the truncated ordered grid sum, the Bernoulli
failure ledger `1-(1-δ)^L ≤ Lδ`, and the duplicated-register layout
witness. The paper's asymptotic qubit/gate expressions (and the compressed
Taylor qubit saving of Corollary 16) are not formalized as big-O statements
in this library; the exact resource functions they bound are the frozen
`ipSegment*`/`ipTotal*` definitions.

Boundary: no claim of a near-linear classical algorithm; these are matrix
and integer-ledger statements.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.InteractionEvo
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.CoherentSim.FactorialTaylor
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.InteractPic18.MainResults.MainAlgorithm

/-- **Theorem 3, segment error** (fixed arXiv:1805.00675v2, Appendix B): the
actual computed truncated ordered grid sum of one segment approximates the
time-ordered exponential within the dyadic accuracy `(1/2)^{precision+6}`. -/
theorem theorem3_segment_error (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (hp : effectiveSegmentDomain p) (hF : EffectiveField p H Hd) :
    ‖dysonGridTruncatedSum H p.time (effectiveSegmentM p) (effectiveSegmentK p) -
      orderedEvolution (fun u => Complex.I • H u) 0 p.time‖ ≤ (1/2 : ℝ)^(p.precision+6) :=
  effectiveDysonParameters_error p H Hd hp hF

/-- **Theorem 3, query rate** (fixed arXiv:1805.00675v2, Theorem 3 item 1):
the per-segment HAM-T query count `ipSegmentQueries p = effectiveSegmentK p`
obeys the integer `log/log log` rate `K·log₂(K+2) ≤ C(K+2)`, i.e. grows as
`O(log(1/ε)/log log(1/ε))` in the precision `k ≈ log₂(1/ε)`. -/
theorem theorem3_segment_query_rate :
    ∃ C m0 : ℕ, 0 < C ∧ 2 ≤ m0 ∧
      ∀ (p : EffectiveSegmentParameters), m0 ≤ p.precision + 8 + 2 →
        ipSegmentQueries p * Nat.log 2 (p.precision + 8 + 2) ≤ C * (p.precision + 8 + 2) := by
  obtain ⟨C, m0, hC, hm0, h⟩ := computedDysonCutoff_tail_and_rate.2
  refine ⟨C, m0, hC, hm0, fun p hp => ?_⟩
  simpa [ipSegmentQueries, effectiveSegmentK] using h (p.precision + 8) hp

/-- **Theorem 3, failure probability** (fixed arXiv:1805.00675v2, Eq. (14)):
the accumulated failure of `L` segments each failing with probability `δ ≤ 1`
is at most `Lδ`. -/
theorem theorem3_total_failure (L : ℕ) (δ : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ipTotalFailure L δ ≤ (L : ℝ) * δ := by
  unfold ipTotalFailure
  have h := one_add_mul_le_pow (a := -δ) (n := L) (by linarith)
  push_cast at h
  ring_nf at h ⊢
  linarith

/-- **Theorem 3, segment width** (fixed arXiv:1805.00675v2, Theorem 3 item 2):
the actual segment program width is `ns + K(na + nd)`. -/
theorem theorem3_segment_width (p : EffectiveSegmentParameters) :
    ipSegmentWidth p = p.ns + effectiveSegmentK p * (p.na + p.nd) := rfl

/-- **Theorem 15** (fixed arXiv:1805.00675v2, Appendix C): a program in the
duplicated-register layout has width at least `ns + K(na + nd)` and contains
the `K` oracle queries, one per copy. -/
theorem theorem15_duplicated_layout (p : EffectiveSegmentParameters) (c : EffectiveProgram)
    (hc : EffectiveDuplicatedLayout p c) :
    p.ns + effectiveSegmentK p * (p.na + p.nd) ≤ c.width ∧
      ∀ j < effectiveSegmentK p, ∃ cs adj,
        EffectiveStep.query 0 (effectiveDuplicatedWires p j) cs adj ∈ c.steps :=
  ⟨hc.1, hc.2.2⟩

/-- **Theorem 15, segment error** (fixed arXiv:1805.00675v2, Appendix C): the
duplicated-register segment attains the same dyadic error as Theorem 3. -/
theorem theorem15_segment_error (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (hp : effectiveSegmentDomain p) (hF : EffectiveField p H Hd) :
    ‖dysonGridTruncatedSum H p.time (effectiveSegmentM p) (effectiveSegmentK p) -
      orderedEvolution (fun u => Complex.I • H u) 0 p.time‖ ≤ (1/2 : ℝ)^(p.precision+6) :=
  effectiveDysonParameters_error p H Hd hp hF

/-- **Corollary 16, truncation order existence** (fixed arXiv:1805.00675v2,
Corollary 16 / Appendix D): for any `ε > 0` and `|αt| ≤ ln 2` there is a
truncation order `K` whose factorial tail is at most `ε`. The order is the
native bounded factorial search output `computedDysonCutoff m` for a dyadic
precision `m` with `2^{-m} < ε`. -/
theorem corollary16_cutoff_exists (α t ε : ℝ) (hα : 0 ≤ α)
    (ht : |α * t| ≤ Real.log 2) (hε : 0 < ε) :
    ∃ K : ℕ, (2 : ℝ) * (α * |t|) ^ (K + 1) / (Nat.factorial (K + 1) : ℝ) ≤ ε := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨computedDysonCutoff m, ?_⟩
  have hx : 0 ≤ α * |t| := mul_nonneg hα (abs_nonneg _)
  have ht' : α * |t| ≤ Real.log 2 := by
    rw [abs_mul, abs_of_nonneg hα] at ht; exact ht
  have h1 := computedDysonCutoff_tail_and_rate.1 m (α * |t|) hx ht'
  have hpos : (0 : ℝ) < (1/2 : ℝ) ^ m := by positivity
  have h2 : (1/2 : ℝ) ^ m / 2 ≤ ε := by
    have : (1/2 : ℝ) ^ m / 2 < (1/2 : ℝ) ^ m := by
      rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 2)]; linarith
    linarith
  exact h1.trans h2

/-- **Corollary 16, `log/log log` order** (fixed arXiv:1805.00675v2,
Corollary 16 item 1): the same factorial search cutoff also satisfies the
integer `log/log log` rate `K·log₂(K+2) ≤ C(K+2)`. -/
theorem corollary16_cutoff_rate :
    ∃ C m0 : ℕ, 0 < C ∧ 2 ≤ m0 ∧ ∀ m : ℕ, m0 ≤ m + 2 →
      computedDysonCutoff m * Nat.log 2 (m + 2) ≤ C * (m + 2) := by
  obtain ⟨C, m0, hC, hm0, h⟩ := computedDysonCutoff_tail_and_rate.2
  exact ⟨C, m0, hC, hm0, h⟩

end Qatlib.Papers.InteractPic18.MainResults.MainAlgorithm
