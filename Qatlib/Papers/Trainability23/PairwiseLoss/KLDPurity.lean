/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section


/-!
# KLDPurity source results

These finite probability identities and conditional estimates preserve closed
results from arXiv:2305.02881v2. They do not assert the missing full Haar-product
MMD variance identity or an unconditional trainability theorem.
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators Matrix
namespace Qatlib.Papers.Trainability23.PairwiseLoss.KLDPurity

/-- **Corollary 1, Eq. (22), arithmetic core.**  If some target probability is at least
`1/(n+1)^d`, the deep-Haar KLD variance `(π²/6) Σ_x p(x)²` is at least
`(π²/6)·(1/(n+1)^d)²`, a polynomially large lower bound, so it does not vanish exponentially. -/
theorem purity_lower {X : Type*} [Fintype X] (p : FinDist X) (x0 : X)
    (n d : ℕ) (hx : 1 / ((n : ℝ) + 1) ^ d ≤ p.prob x0) :
    Real.pi ^ 2 / 6 * (1 / ((n : ℝ) + 1) ^ d) ^ 2
      ≤ Real.pi ^ 2 / 6 * ∑ x, (p.prob x) ^ 2 := by
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc (1 / ((n : ℝ) + 1) ^ d) ^ 2 ≤ (p.prob x0) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hx 2
    _ ≤ ∑ x, (p.prob x) ^ 2 :=
        Finset.single_le_sum (f := fun x => (p.prob x) ^ 2)
          (fun x _ => sq_nonneg _) (Finset.mem_univ x0)
end Qatlib.Papers.Trainability23.PairwiseLoss.KLDPurity
