/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.PairwiseLoss.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# PairwiseLoss/CommonLosses — Corollary 2: concentration points of the common explicit losses

Paper: Rudolph–Lerch–Thanasilp–Kiss–Shaya–Vallecorsa–Grossi–Holmes, *Trainability barriers and
opportunities in quantum generative modeling*, fixed arXiv:2305.02881v2, Corollary 2, pp.~10–11.

Under the hypotheses of Theorem 1, each common explicit loss concentrates at the value of its
fixed point of Eq. (23).  This module records those four fixed-point values:

* `classicalFidelity` — the classical-fidelity instance `(a, b) ↦ a - √(a b)` of Eq. (8), whose
  pairwise sum is `1 - Σ √(p x · q x)` (`classicalFidelity_pairwise_eq`);
* `classicalFidelity_lossFixedPoint_eq_one` — Eq. (26): the classical-fidelity concentration
  point is the constant `1`;
* `corollary2_concentration_points` — the four concentration points of Eqs. (25)–(28):
  `Σ p̃ log(p̃/ε)`, `1`, `Σ q̃_θ log(q̃_θ/ε)` and `2`.

The KL, reverse-KL and total-variation values are cited from the Frozen development
(`kl_lossFixedPoint_eq`, `revKl_lossFixedPoint_eq`, `tv_lossFixedPoint_eq_two`); the
classical-fidelity instance was missing there and is proved here.

The connection to Theorem 1 is the deterministic equality of
`Concentration.theorem1_loss_eq_fixedPoint_of_noOverlap`: on the no-overlap event the estimated
loss equals the fixed point, and Theorem 1 bounds the complement's probability by
`δ ∈ O(poly(n)/c^n)`.  Hence the values below are exactly the concentration points.
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.PairwiseLoss

namespace Qatlib.Papers.Trainability23.PairwiseLoss.CommonLosses

open scoped BigOperators

/-- The classical-fidelity pairwise loss of Eq. (8): `L_CF = Σ x, (p x - √(p x · q x))`. -/
noncomputable def classicalFidelity (a b : ℝ) : ℝ := a - Real.sqrt (a * b)

/-- The classical-fidelity loss is `1` minus the Bhattacharyya coefficient, paper Eq. (8). -/
theorem classicalFidelity_pairwise_eq {X : Type*} [Fintype X] (p q : FinDist X) :
    pairwiseLoss classicalFidelity p.prob q.prob
      = 1 - ∑ x, Real.sqrt (p.prob x * q.prob x) := by
  unfold pairwiseLoss classicalFidelity
  rw [Finset.sum_sub_distrib, p.sum_one]

/-- Eq. (26): the classical-fidelity concentration point is the constant `1`. -/
theorem classicalFidelity_lossFixedPoint_eq_one {X : Type*} [Fintype X] (p q : FinDist X) :
    lossFixedPoint classicalFidelity p.prob (support p) q.prob (support q) = 1 := by
  have hleft : ∀ a : ℝ, classicalFidelity a 0 = a := by
    intro a
    simp [classicalFidelity]
  have hright : ∀ b : ℝ, classicalFidelity 0 b = 0 := by
    intro b
    simp [classicalFidelity]
  unfold lossFixedPoint
  rw [Finset.sum_congr rfl (fun x _ => hleft (p.prob x)),
    Finset.sum_congr rfl (fun x _ => hright (q.prob x)), Finset.sum_const_zero, add_zero,
    sum_support p]

/-- **Corollary 2, Eqs. (25)–(28).**  The four concentration points of the common explicit
losses: the KL fixed point `Σ p̃ log(p̃/ε)`, the classical-fidelity value `1`, the reverse-KL
fixed point `Σ q̃_θ log(q̃_θ/ε)` and the total-variation value `2`.  The first, third and fourth
conjuncts cite the Frozen development; the second is proved above. -/
theorem corollary2_concentration_points {X : Type*} [Fintype X] (ε : ℝ) (hε : 0 < ε)
    (p q : FinDist X) :
    lossFixedPoint (clippedKL ε) p.prob (support p) q.prob (support q)
        = ∑ x ∈ support p, p.prob x * Real.log (p.prob x / ε)
      ∧ lossFixedPoint classicalFidelity p.prob (support p) q.prob (support q) = 1
      ∧ lossFixedPoint (clippedKLRev ε) p.prob (support p) q.prob (support q)
        = ∑ x ∈ support q, q.prob x * Real.log (q.prob x / ε)
      ∧ lossFixedPoint tvPairwise p.prob (support p) q.prob (support q) = 2 :=
  ⟨kl_lossFixedPoint_eq ε hε p q, classicalFidelity_lossFixedPoint_eq_one p q,
    revKl_lossFixedPoint_eq ε hε p q, tv_lossFixedPoint_eq_two p q⟩

/-- The concentration points of the KL and total-variation losses do not depend on the model
parameter, while the classical-fidelity value is the constant `1`; only the reverse-KL point
retains a `θ`-dependence (through `Σ q̃_θ log(q̃_θ/ε)`).  This is the paper's remark after
Eq. (28) that the KL, classical-fidelity and total-variation costs cannot be used to train the
circuit model. -/
theorem corollary2_kl_tv_param_independent {X Θ : Type*} [Fintype X] (ε : ℝ) (hε : 0 < ε)
    (p : FinDist X) (f : Θ → FinDist X) (t t' : Θ) :
    lossFixedPoint (clippedKL ε) p.prob (support p) (f t).prob (support (f t))
        = lossFixedPoint (clippedKL ε) p.prob (support p) (f t').prob (support (f t'))
      ∧ lossFixedPoint tvPairwise p.prob (support p) (f t).prob (support (f t))
        = lossFixedPoint tvPairwise p.prob (support p) (f t').prob (support (f t')) := by
  constructor
  · rw [kl_lossFixedPoint_eq ε hε p (f t), kl_lossFixedPoint_eq ε hε p (f t')]
  · exact tv_lossFixedPoint_const p f t t'

end Qatlib.Papers.Trainability23.PairwiseLoss.CommonLosses
