/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Proposition47ProductBiasTransferDist

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Transfer of AA across product biases (arXiv:2609.35327v1, Proposition 4.7)

Paper-layer statement of Proposition 4.7 of Girish--Mittal--Nehoran--Raz,
fixed at arXiv:2609.35327v1: if `AA(μ_p, S)` holds then, for every `D ≥ 1`,
`AA(μ_q, S_D)` holds with `S_D(v,d) = S(v/2, d·m_D(v,d)) - (v/d)^D`.

The frozen gadget size `biasGadgetSize` uses `⌈(4D/a)·log₂(d/v)⌉`, whereas the
paper prints `⌈(3D/a)·log₂(d/v)⌉`; the larger factor is the library's recorded
constant adaptation and leaves the qualitative transfer unchanged.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Proposition 4.7 at the frozen gadget size: `AA(μ_p, S)` transfers to
`AA(μ_q, biasTransferS S a D)` for every `D ≥ 1`, where
`a = min(p, 1-p, q, 1-q)`. -/
theorem proposition47_bias_transfer (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (S : ℝ → ℕ → ℝ)
    (hS : AAWith (muFamily p) S) (D : ℕ) (hD : 0 < D) :
    AAWith (muFamily q)
      (biasTransferS S (min (min p (1 - p)) (min q (1 - q))) D) :=
  proposition47ProductBiasTransfer p q hp0 hp1 hq0 hq1 S hS D hD

end Qatlib.Papers.AADistrib26.MainResults
