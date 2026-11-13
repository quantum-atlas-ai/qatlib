/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutingLLL13.MainResults.Defs
import Qatlib.Papers.CommutingLLL13.MainResults.EntropyChain
import Qatlib.Papers.CommutingLLL13.MainResults.FailureBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
# Conditional failure bounds and commuting sweeps

This module assembles scalar natural-logarithm failure bounds and algebraic zero-postselection
sweeps for commuting projector families in [SattathArad2015]. The parameters `naturalSlack`,
`naturalEta`, and `naturalThreshold` determine the explicit failure-bound expression.

Under the stated local-lemma inequality and positive target `δ`, `conditional_natural_and_sweep`
bounds any failure value satisfying the scalar estimate and proves that a sweep covering all
constraints produces a matrix annihilated by every constraint projector.

## Main statements

* `zeroSweep_covers_satisfies`: A covering sweep satisfies every projector constraint.
* `kappa_pos_of_qlll`: The stated local-lemma inequality gives positive natural-logarithm slack.
* `conditional_natural_and_sweep`: Combines the conditional scalar bound with the covering-sweep
  property.

## References

* [Sattath and Arad, 2015][SattathArad2015]
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Papers.CommutingLLL13.MainResults.MainTheorem

open Qatlib.Papers.CommutingLLL13.MainResults

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The natural-logarithm slack `P.k - log(P.g * P.r * exp 1)` associated with the
satisfiability parameters. -/
noncomputable def naturalSlack (P : Defs.QSatParams) : ℝ :=
  (P.k : ℝ) - Real.log ((P.g : ℝ) * (P.r : ℝ) * Real.exp 1)

/-- The reciprocal target-times-slack parameter obtained from `Defs.etaNatural` and the fields
of `P`. -/
noncomputable def naturalEta (P : Defs.QSatParams) (δ : ℝ) : ℝ :=
  Defs.etaNatural δ (P.k : ℝ) (P.r : ℝ) (P.g : ℝ)

/-- The integer threshold obtained from `Defs.thresholdNatural P.m` and `naturalEta P δ`. -/
noncomputable def naturalThreshold (P : Defs.QSatParams) (δ : ℝ) : ℕ :=
  Defs.thresholdNatural P.m (naturalEta P δ)

/-- For a commuting projector family, a finite zero-postselection sweep makes every projector
whose index occurs in the sweep annihilate the output matrix. -/
theorem zeroSweep_satisfies_mem {m : ℕ} (F : Defs.QSatFamily D m)
    (hcomm : Defs.CommutingFamily F) (l : List (Fin m)) (M : Matrix D D ℂ) :
    ∀ i ∈ l, F.P i * (l.foldr (Defs.zeroPostselect F) M) = 0 := by
  induction l with
  | nil => intro i hi; simp at hi
  | cons i0 rest ih =>
    intro j hj
    rw [List.foldr_cons] at ⊢
    rw [List.mem_cons] at hj
    rcases hj with rfl | hmem
    · exact Defs.zeroPostselect_satisfies_own F _
        (rest.foldr (Defs.zeroPostselect F) M)
    · exact Defs.zeroPostselect_preserves F hcomm _ j
        (rest.foldr (Defs.zeroPostselect F) M) (ih j hmem)

/-- For a commuting projector family, a zero-postselection sweep whose list contains every index
produces a matrix satisfying all constraints. -/
theorem zeroSweep_covers_satisfies {m : ℕ} (F : Defs.QSatFamily D m)
    (hcomm : Defs.CommutingFamily F) (l : List (Fin m))
    (M : Matrix D D ℂ) (hcov : ∀ i, i ∈ l) :
    Defs.SatisfiesMat (l.foldr (Defs.zeroPostselect F) M) F := by
  intro i
  exact zeroSweep_satisfies_mem F hcomm l M i (hcov i)

/-- For `P.k ≥ 1` and `P.g ≥ 1`, the stated inequality `P.g < 2 ^ P.k / (P.r * exp 1)` implies
`naturalSlack P > 0`. -/
theorem kappa_pos_of_qlll (P : Defs.QSatParams) (hk : 1 ≤ P.k) (hg : 1 ≤ P.g)
    (hcond : (P.g : ℝ) < 2 ^ (P.k : ℝ) / ((P.r : ℝ) * Real.exp 1)) :
    0 < naturalSlack P := by
  have hgR : (0 : ℝ) < (P.g : ℝ) := by exact_mod_cast (by omega : 0 < P.g)
  have hrR : (0 : ℝ) < (P.r : ℝ) := by exact_mod_cast P.hr
  have hexp : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hkR : (1 : ℝ) ≤ (P.k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < (P.r : ℝ) * Real.exp 1 := by positivity
  have hlogrhs : Real.log (2 ^ (P.k : ℝ) / ((P.r : ℝ) * Real.exp 1))
      = (P.k : ℝ) * Real.log 2 - (Real.log (P.r : ℝ) + 1) := by
    rw [Real.log_div (by positivity : (2 : ℝ) ^ (P.k : ℝ) ≠ 0) hden.ne',
        Real.log_rpow (by norm_num)]
    have : Real.log ((P.r : ℝ) * Real.exp 1) = Real.log (P.r : ℝ) + 1 := by
      rw [Real.log_mul hrR.ne' hexp, Real.log_exp]
    rw [this]
  have hlg : Real.log (P.g : ℝ) < (P.k : ℝ) * Real.log 2 - (Real.log (P.r : ℝ) + 1) := by
    rw [← hlogrhs]
    exact Real.log_lt_log hgR hcond
  have hlogger : Real.log ((P.g : ℝ) * (P.r : ℝ) * Real.exp 1)
      = Real.log (P.g : ℝ) + Real.log (P.r : ℝ) + 1 := by
    rw [show (P.g : ℝ) * (P.r : ℝ) * Real.exp 1
          = ((P.g : ℝ) * (P.r : ℝ)) * Real.exp 1 by ring,
        Real.log_mul (by positivity) hexp, Real.log_mul hgR.ne' hrR.ne', Real.log_exp]
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_two_lt_d9; linarith
  rw [naturalSlack, hlogger]
  nlinarith [hlg, hlog2lt, hkR]

/-- For `P.m ≥ 2`, positive target `δ`, and positive `naturalSlack P`, the scalar failure
expression at `naturalThreshold P δ` is at most `δ`. -/
theorem conditional_natural_bound (P : Defs.QSatParams) (hm : 2 ≤ P.m)
    (δ : ℝ) (hδ : 0 < δ)
    (hκ : 0 < naturalSlack P) :
    (Real.log ((naturalThreshold P δ : ℝ)) + (P.m : ℝ))
        / ((naturalThreshold P δ : ℝ) * naturalSlack P) ≤ δ := by
  have hηpos : 0 < naturalEta P δ := by
    rw [naturalEta]
    unfold Defs.etaNatural
    exact div_pos one_pos (mul_pos hδ hκ)
  have hηδ : naturalEta P δ * δ * naturalSlack P = 1 := by
    rw [naturalEta, naturalSlack]
    unfold Defs.etaNatural
    have h1 : δ ≠ 0 := hδ.ne'
    have h2 : (P.k : ℝ) - Real.log ((P.g : ℝ) * (P.r : ℝ) * Real.exp 1) ≠ 0 := hκ.ne'
    field_simp
  exact FailureBound.eq5_le_delta P.m hm (naturalEta P δ) (naturalSlack P) δ hηpos hκ hηδ

/-- Under the stated local-lemma inequality and positivity conditions, every failure value
bounded by the natural-threshold expression is at most `δ`, and every covering
zero-postselection sweep satisfies all constraints of the commuting family. These are
conditional scalar and algebraic conclusions for [SattathArad2015]. -/
theorem conditional_natural_and_sweep (P : Defs.QSatParams) (hm : 2 ≤ P.m) (hk : 1 ≤ P.k)
    (hg : 1 ≤ P.g)
    (hcond : (P.g : ℝ) < 2 ^ (P.k : ℝ) / ((P.r : ℝ) * Real.exp 1))
    (δ : ℝ) (hδ : 0 < δ) (F : Defs.QSatFamily D P.m)
    (hcomm : Defs.CommutingFamily F) :
    (∀ pFail : ℝ,
        pFail ≤ (Real.log ((naturalThreshold P δ : ℝ)) + (P.m : ℝ))
                   / ((naturalThreshold P δ : ℝ) * naturalSlack P) → pFail ≤ δ)
      ∧ (∀ (M : Matrix D D ℂ) (l : List (Fin P.m)),
          (∀ i, i ∈ l) → Defs.SatisfiesMat (l.foldr (Defs.zeroPostselect F) M) F) := by
  have hκ : 0 < naturalSlack P := kappa_pos_of_qlll P hk hg hcond
  refine ⟨?_, ?_⟩
  · intro pFail hp
    exact le_trans hp (conditional_natural_bound P hm δ hδ hκ)
  · intro M l hl
    exact zeroSweep_covers_satisfies F hcomm l M hl

end Qatlib.Papers.CommutingLLL13.MainResults.MainTheorem
