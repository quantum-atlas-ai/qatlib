/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Theorem43DistAAEquivalenceDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Corollary48BiasedProductAAEquivDist
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Proposition412ProductSliceTransferDist

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Distributional Aaronson--Ambainis equivalences (arXiv:2609.35327v1, §4)

Paper-layer statements of Theorem 4.3 (= Theorem 1.2), Corollary 4.8 and
Proposition 4.12 of Girish--Mittal--Nehoran--Raz, fixed at arXiv:2609.35327v1.

`AAHolds (muFamily p)` is `AA(μ_p)` and `AAHolds (nuFamily p)` is `AA(ν_p)` in
the sense of Definition 4.1, with variance and influence measured under the
corresponding distribution. The open Aaronson--Ambainis conjecture
`AAHolds (muFamily (1/2))` is neither asserted nor refuted.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Theorem 4.3 / Theorem 1.2: for `p, q ∈ (0,1)`, `AA(μ_p)` holds if and only
if `AA(ν_q)` holds. -/
theorem theorem43_aa_mu_iff_aa_nu (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    AAHolds (muFamily p) ↔ AAHolds (nuFamily q) :=
  theorem43DistributionalAAEquivalence p q hp0 hp1 hq0 hq1

/-- Corollary 4.8: for `p, q ∈ (0,1)`, `AA(μ_p)` holds if and only if `AA(μ_q)`
holds. -/
theorem corollary48_aa_mu_iff_aa_mu (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    AAHolds (muFamily p) ↔ AAHolds (muFamily q) :=
  corollary48BiasedProductAAEquivalence p q hp0 hp1 hq0 hq1

/-- Proposition 4.12: for `p ∈ (0,1)` and an `S` taking values in `[0,1]` on
the paper's domain, `AA(μ_p, S)` transfers to `AA(ν_p, S')` and conversely,
where `S' = sliceTransferS S = 10⁻⁹ d⁻⁸ · min{v⁵, v·S(v/2,d)⁴}`. -/
theorem proposition412_slice_transfer (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (S : ℝ → ℕ → ℝ)
    (hS : ∀ v : ℝ, 0 < v → v ≤ 1 / 4 → ∀ d : ℕ, S v d ∈ Set.Icc 0 1) :
    (AAWith (muFamily p) S → AAWith (nuFamily p) (sliceTransferS S)) ∧
      (AAWith (nuFamily p) S → AAWith (muFamily p) (sliceTransferS S)) :=
  proposition412ProductSliceTransfer p hp0 hp1 S hS

end Qatlib.Papers.AADistrib26.MainResults
