/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Phase-oracle lower-bound statement

`theorem4Statement` expresses the absence of a uniform polynomial bound for phase-oracle
simulation in terms of spectral-norm time and logarithmic dimension. The module defines this
proposition and proves elementary identities for `phaseEntry`. This development accompanies
[ChildsKothari2010].

## Main statements

* `theorem4Statement`: the phase-oracle polynomial-query impossibility proposition.
* `phaseEntry_of_zero`: zero matrix entries receive phase one.
* `phaseEntry_norm_eq_one`: a nonzero matrix entry gives a unit-modulus phase.

## References

* [Childs and Kothari, 2010][ChildsKothari2010]
-/

set_option autoImplicit false
noncomputable section

open Matrix Finset
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Statement only — not proved in Qatlib.** The proposition encoding Theorem 4 of [ChildsKothari2010]: no polynomially bounded query
function uniformly supplies phase-oracle simulations of all Hermitian evolutions at
nonnegative times with error `1 / 4`, using spectral-norm time and logarithmic dimension as
inputs. -/
def theorem4Statement : Prop :=
  ¬ ∃ (p : ℝ → ℝ → ℕ) (C : ℝ) (k : ℕ),
      0 < C ∧
      (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → (p x y : ℝ) ≤ C * (1 + x + y) ^ k) ∧
      (∀ (N : ℕ) [NeZero N] (H : Matrix (Fin N) (Fin N) ℂ) (ψ : Fin N → ℂ) (t : ℝ),
        H.IsHermitian → 0 ≤ t →
        ∃ q : ℕ, q ≤ p (specNorm H * t) (Real.log N) ∧
          SimulatesPhaseWithQueries H ψ t (1 / 4) q)

omit [Fintype ι] [DecidableEq ι] in

/-- The phase assigned to a zero matrix entry is one. See [ChildsKothari2010]. -/
lemma phaseEntry_of_zero (H : Matrix ι ι ℂ) (i j : ι) (h : H i j = 0) :
    phaseEntry H i j = 1 := by
  unfold phaseEntry
  rw [ite_eq_left h]

omit [Fintype ι] [DecidableEq ι] in

/-- The phase assigned to a nonzero matrix entry has norm one. See [ChildsKothari2010]. -/
lemma phaseEntry_norm_eq_one (H : Matrix ι ι ℂ) (i j : ι) (h : H i j ≠ 0) :
    ‖phaseEntry H i j‖ = 1 := by
  unfold phaseEntry
  rw [ite_eq_right h, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  exact div_self (ne_of_gt (norm_pos_iff.mpr h))

end Qatlib.Papers.NonSparseHam09.MainResults
