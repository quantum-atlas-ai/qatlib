/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Card

set_option backward.isDefEq.respectTransparency false

/-!
# SublinearPart22 — shared source interfaces

Fixed paper: arXiv:2207.08643v1, *A Sublinear-Time Quantum Algorithm for Approximating
Partition Functions* (Hamoudi–Magniez, SODA 2023).  PDF SHA pinned at the copy used by
this build; every theorem below carries its paper number and page.

This file gives the small shared vocabulary used by the paper-layer statements:

* `RandomizedRun` — an abstract randomized classical output together with a per-run
  resource count and the (nonnegative) expectation of that count.  This is how the paper's
  “the algorithm outputs … and uses O(·) copies / reflections” clauses are recorded
  without pretending to formalize the full gate-level algorithm in the paper layer.
* `EstimateWithRestoration` — the pair `(estimate, flag)` where the flag records whether
  the single copy of the input state was restored, exactly as in the paper’s restoration
  probability clauses.
* `FinDist` — a finite probability distribution on `Fin n`, used for Propositions 3.1/3.2
  and Theorems 3.3/4.1 (means, variances, second moments, Bhattacharyya fidelity).

Boundary: these are interface definitions only; they introduce no axioms and make no
claim about the algorithms.  Each paper statement adds its own quantitative hypotheses
and conclusion.

**Model-adequacy warning.**  The claim files state their guarantees as
`∃ r : RandomizedRun ...` with no link between `r` and the paper's circuit.  Such an
existential is satisfiable by a *degenerate* run (sample space `Unit`, Dirac measure,
deterministic output, zero cost): for example Theorem 2.2 is witnessed by
`out := fun _ => (θ, true)` and `cost := 0`, and Proposition 2.3 by a two-point
distribution on `Bool`.  A proof of one of these existentials therefore does **not**
formalize the paper's algorithm or its distributional guarantees.  Genuine B-level
coverage requires gate-level models of the algorithms (QPE, amplitude amplification,
quantum walk, annealing) and is not obtained from these interface statements.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace Qatlib.Papers.SublinearPart22.MainResults

/-- The paper's estimates are real numbers; an extra Boolean records whether the single
input copy was restored by the computation (restoration probability clauses). -/
abbrev EstimateWithRestoration : Type := ℝ × Bool

/-- The numerical estimate component of a run output. -/
def estimate (x : EstimateWithRestoration) : ℝ := x.1

/-- The restoration flag component of a run output. -/
def restored (x : EstimateWithRestoration) : Bool := x.2

/-- An abstract randomized run: a probability space `Ω`, an output function, and a
nonnegative per-run resource count (controlled-unitaries, reflections, copies, walk
steps — whichever the source theorem bounds).  The expectation of `cost` models the
paper's “uses O(·) … in expectation” clauses. -/
structure RandomizedRun (α : Type) where
  Ω : Type
  mΩ : MeasurableSpace Ω
  μ : @MeasureTheory.Measure Ω mΩ
  prob : @MeasureTheory.IsProbabilityMeasure Ω mΩ μ
  out : Ω → α
  cost : Ω → ℝ
  cost_nonneg : ∀ ω, 0 ≤ cost ω
  cost2 : Ω → ℝ
  cost2_nonneg : ∀ ω, 0 ≤ cost2 ω

attribute [instance] RandomizedRun.mΩ RandomizedRun.prob

namespace RandomizedRun

/-- Expectation of the numerical estimate. -/
def Expected (r : RandomizedRun EstimateWithRestoration) : ℝ :=
  ∫ ω, estimate (r.out ω) ∂r.μ

/-- Variance of the numerical estimate. -/
def EstimateVariance (r : RandomizedRun EstimateWithRestoration) : ℝ :=
  ProbabilityTheory.variance (fun ω => estimate (r.out ω)) r.μ

/-- The input copy is restored with probability at least `1 - η`. -/
def RestoreProbAtLeast (r : RandomizedRun EstimateWithRestoration) (η : ℝ) : Prop :=
  1 - ENNReal.ofReal η ≤ r.μ {ω | restored (r.out ω) = true}

/-- The input copy is restored with probability one. -/
def AlwaysRestored (r : RandomizedRun EstimateWithRestoration) : Prop :=
  r.μ {ω | restored (r.out ω) = true} = 1

/-- Expected resource consumption (primary resource) is at most `C * scale`. -/
def ExpectedCostLe {α : Type} (r : RandomizedRun α) (C scale : ℝ) : Prop :=
  ∫ ω, r.cost ω ∂r.μ ≤ C * scale

/-- Expected consumption of the secondary resource (used by Theorem 3.3, which
bounds both the number of copies and the number of reflections). -/
def ExpectedCost2Le {α : Type} (r : RandomizedRun α) (C scale : ℝ) : Prop :=
  ∫ ω, r.cost2 ω ∂r.μ ≤ C * scale

/-- The output event `good` happens with probability at least `p`. -/
def HighProbEvent {α : Type} (r : RandomizedRun α) (good : α → Prop) (p : ℝ) : Prop :=
  ENNReal.ofReal p ≤ r.μ {ω | good (r.out ω)}

end RandomizedRun

/-- A finite probability distribution on `Fin n` (the paper’s finite random variables
`X` with support `{x₁,…,xₙ}`). -/
structure FinDist (n : ℕ) where
  pr : Fin n → ℝ
  pr_nonneg : ∀ x, 0 ≤ pr x
  pr_sum : ∑ x, pr x = 1

namespace FinDist

variable {n : ℕ}

/-- Mean of a real-valued function under a finite distribution. -/
def mean (D : FinDist n) (val : Fin n → ℝ) : ℝ := ∑ x, D.pr x * val x

/-- Second moment `E[X²]`. -/
def secondMoment (D : FinDist n) (val : Fin n → ℝ) : ℝ := ∑ x, D.pr x * val x ^ 2

/-- Variance `E[(X − E X)²]`. -/
def variance (D : FinDist n) (val : Fin n → ℝ) : ℝ :=
  ∑ x, D.pr x * (val x - D.mean val) ^ 2

/-- Bhattacharyya coefficient `∑ₓ √(P(x) Q(x))`, i.e. the absolute overlap of the two
qsample encodings `|π_X⟩` and `|π_Y⟩`. -/
def bhattacharyya (D E : FinDist n) : ℝ := ∑ x, Real.sqrt (D.pr x * E.pr x)

/-- Squared fidelity `|⟨π_X|π_Y⟩|²` between two qsample encodings. -/
def fidelity (D E : FinDist n) : ℝ := D.bhattacharyya E ^ 2

/-- Relative second moment `E[X²] / E[X]²`. -/
def relativeSecondMoment (D : FinDist n) (val : Fin n → ℝ) : ℝ :=
  D.secondMoment val / D.mean val ^ 2

/-- The uniform distribution on `Fin 0` is impossible to write down; for `0 < n` we use
`pr = 1/n`.  Only used to instantiate the statements with a concrete witness when needed. -/
def uniform (n : ℕ) (hn : 0 < n) : FinDist n where
  pr := fun _ => (n : ℝ)⁻¹
  pr_nonneg := fun _ => by positivity
  pr_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

end FinDist

end Qatlib.Papers.SublinearPart22.MainResults
