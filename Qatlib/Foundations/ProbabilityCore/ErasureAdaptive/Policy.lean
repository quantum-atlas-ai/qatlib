/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.ErasureAdaptive.ErasureMasks

/-!
# Budgeted adaptive erasure policies

The inductive type `ErasurePolicy` describes random choices and mask-dependent noise steps
indexed by remaining step count and width budget. Its semantics `execute` stops with failure on
complete erasure, while `bestProduct` maximizes the deterministic survival product by recursion,
setting up the bounds used in [BhartiHaugTanggara2026].

## Main statements

* `ErasurePolicy`: Adaptive programs track noise steps and total available width.
* `execute`: The PMF semantics returns the survival Boolean.
* `step_le_best`: Each permitted first-width choice is bounded by the dynamic-programming
  optimum.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false
open scoped NNReal ENNReal BigOperators

namespace Qatlib.Foundations.ProbabilityCore.ErasureAdaptive

/-- Adaptive erasure policies indexed by the number of remaining noise steps and the remaining
width budget, with termination, random-choice, and mask-dependent noise constructors. -/
inductive ErasurePolicy (R : Type*) : ℕ → ℕ → Type _

  | done {budget : ℕ} : ErasurePolicy R 0 budget

  | random {steps budget : ℕ} (draw : PMF R) (next : R → ErasurePolicy R steps budget) :
      ErasurePolicy R steps budget

  | noise {steps budget : ℕ} (width : Fin (budget+1))
      (observe : (Fin width.val → Bool) → PMF R)
      (next : (Fin width.val → Bool) → R → ErasurePolicy R steps (budget-width.val)) :
      ErasurePolicy R (steps+1) budget

/-- The Boolean survival distribution of a policy, returning failure at the first all-true
erasure mask and success on termination. -/
noncomputable def execute {R : Type*} (p : ℝ≥0) (hp : p ≤ 1)
    {S C : ℕ} : ErasurePolicy R S C → PMF Bool
  | .done => PMF.pure true
  | .random draw next => draw.bind (fun r => execute p hp (next r))
  | .noise width observe next =>
      (erasureMask width.val p hp).bind (fun mask =>
        if mask = (fun _ => true) then PMF.pure false
        else (observe mask).bind (fun r => execute p hp (next mask r)))

/-- The recursively maximal product of `S` factors `1 - p ^ width` under total width budget `C`,
computed in the nonnegative reals. -/
noncomputable def bestProduct (p : ℝ≥0) : ℕ → ℕ → ℝ≥0
  | 0, _ => 1
  | S+1, C => Finset.univ.sup' Finset.univ_nonempty
      (fun n : Fin (C+1) => (1-p^n.val) * bestProduct p S (C-n.val))

/-- The product obtained from any permitted first width and an optimal continuation is at most
`bestProduct p (S + 1) C`. -/
theorem step_le_best (p : ℝ≥0) (S C : ℕ) (n : Fin (C+1)) :
    (1-p^n.val) * bestProduct p S (C-n.val) ≤ bestProduct p (S+1) C :=
  by
    change _ ≤ Finset.univ.sup' Finset.univ_nonempty
      (fun k : Fin (C+1) => (1-p^k.val) * bestProduct p S (C-k.val))
    exact Finset.le_sup' (fun k : Fin (C+1) =>
      (1-p^k.val) * bestProduct p S (C-k.val)) (Finset.mem_univ n)

end Qatlib.Foundations.ProbabilityCore.ErasureAdaptive
