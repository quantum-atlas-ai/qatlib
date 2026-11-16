/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Lemma37BiasGadgetDist

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Bias gadget (arXiv:2609.35327v1, Lemma 3.7)

Paper-layer statement of Lemma 3.7 of Girish--Mittal--Nehoran--Raz, fixed at
arXiv:2609.35327v1: for `p ∈ (0,1)` and every target `q ∈ [0,1]` there is a
Boolean function on `{0,1}^m` whose `μ_{m,p}`-probability of output `1` lies in
`[q, q + 2^{-a m}]`, with `a = min(p, 1-p)`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.AADistrib26.MainResults

open Qatlib.Concepts.ProbabilityCore.DistributionAA
open Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Lemma 3.7: a Boolean gadget whose `μ_{m,p}`-mass overshoots `q` by at most
`2^{-min(p,1-p)·m}`. -/
theorem lemma37_bias_gadget (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    ∃ g : (Fin m → Bool) → Bool,
      q ≤ cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0) ∧
        cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0) ≤
          q + (2 : ℝ) ^ (-(min p (1 - p) * (m : ℝ))) :=
  lemma37BiasGadget p q hp0 hp1 hq0 hq1 m

end Qatlib.Papers.AADistrib26.MainResults
