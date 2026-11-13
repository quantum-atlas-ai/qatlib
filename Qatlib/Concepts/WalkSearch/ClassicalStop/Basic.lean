/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalStopComparisonQuan
import Qatlib.Concepts.WalkSearch.ClassicalStop.SzegedyClassicalAbsorbingMassDecayQuan
import Qatlib.Concepts.WalkSearch.ProjectorCS

/-!
# Classical stopping bounds for marked chains

The module exposes the classical detection and absorbing-mass estimates for a symmetric chain
with gap parameter `δ` and marked fraction at least `ε`. It also translates a bound on the
number of steps into a weighted setup, update, and checking cost. See [Szegedy2004] for the
mathematical background.

## Main statements

* `source_expression_ten_classical_stop`: constant success after the prescribed number of steps.
* `source_classical_absorbing_mass_decay`: geometric decay of unmarked mass.
* `source_expression_ten_cost`: the weighted cost estimate.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.ClassicalStop

namespace Qatlib.Concepts.WalkSearch.ClassicalStop.Basic

/-- Under the stated gap and marked-fraction assumptions, packages zero success for an empty
marked set and success at least `1 / 32` for every `K ≥ 1000 / (δ * ε)`. See [Szegedy2004]. -/
theorem source_expression_ten_classical_stop
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S) :
    (S = ∅ → ∀ K : ℕ, classicalDetectSuccess P S K = 0) ∧
    ∀ K : ℕ, 1000 / (δ * ε) ≤ (K : ℝ) → (1 / 32 : ℝ) ≤ classicalDetectSuccess P S K :=
  szegedyClassicalStopComparison I P S δ ε hδ hδ1 hgap hε hεp

/-- For a law starting uniformly and evolving by the marked absorbing kernel, the unmarked mass
after `K` steps is at most `(1 - δ * ε / 2) ^ K` under the stated gap assumptions. -/
theorem source_classical_absorbing_mass_decay
    (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (K : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hgap : SymmetricChainGap P δ)
    (hε : 0 < ε) (hεp : ε ≤ markedFraction S)
    (law : ℕ → I → ℝ) (h0 : law 0 = fun _ => (1 : ℝ) / (Fintype.card I : ℝ))
    (hstep : ∀ t j, law (t + 1) j =
      ∑ i, law t i * (if i ∈ S then (if j = i then 1 else 0) else P i j)) :
    (∑ i : {x : I // x ∉ S}, law K i) ≤ (1 - δ * ε / 2) ^ K :=
  szegedyClassicalAbsorbingMassDecay I P S δ ε K hδ hδ1 hgap hε hεp law h0 hstep

/-- A step bound `K ≤ 1000 / (δ * ε) + 1` yields the displayed setup, update, and checking cost
bound when the update and checking weights are nonnegative. -/
theorem source_expression_ten_cost
    (K : ℕ) (δ ε : ℝ) (_hδ : 0 < δ) (_hε : 0 < ε)
    (hK : (K : ℝ) ≤ 1000 / (δ * ε) + 1)
    (w0 w1 w2 : ℝ) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) :
    w0 + (K : ℝ) * w1 + ((K : ℝ) + 1) * w2 ≤
      w0 + (1000 / (δ * ε) + 1) * w1 + (1000 / (δ * ε) + 2) * w2 := by
  have hK1 : (K : ℝ) + 1 ≤ 1000 / (δ * ε) + 1 + 1 := by linarith
  have hw1 := mul_le_mul_of_nonneg_right hK h1
  have hw2 := mul_le_mul_of_nonneg_right hK1 h2
  linarith

end Qatlib.Concepts.WalkSearch.ClassicalStop.Basic
