/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — shared objects for arXiv:2110.13086 (QRegression21)

Chen--de Wolf, *Quantum Algorithms and Lower Bounds for Linear Regression with Norm
Constraints*, fixed arXiv:2110.13086v2 (19 Jul 2022).

This file fixes the paper's notation in Lean: the ℓ1/ℓ2 balls, the ε-minimizer notion
(Definitions 2.5/2.6), the finite distributions `D_{p,W}` (Lasso, Section 4.1) and
`D'_{p,W}` (Ridge, Section 5), the expected squared losses `L_D` (Section 2.3), the
closed forms of Theorem 4.1 / Section 5, the explicit gradient/Hessian of the Lasso
loss, the vectors `θ* = v·e_W` (Lasso) and `θ*_j = (-1)^{[j∈W]}/√d` (Ridge), and the
KP-tree data structure of Definition 2.9.

Boundary: this is the paper-layer model. It does not modify any shared Foundations or
Concepts declaration. The finite probability laws are built on the shared
`FinDist`/`independentSampleLaw` machinery; the losses are the paper's own analytic
expressions, whose agreement with the distributional expectation is recorded separately
as `lassoLoss_eq_expectation` / `ridgeLoss_eq_expectation` in the Lasso and Ridge
loss files.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Classical
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults

variable {d : ℕ}

/-! ## Norms, balls, minimizers -/

/-- The ℓ1 norm `‖θ‖₁ = ∑ j, |θ_j|`. -/
def l1Norm (θ : Fin d → ℝ) : ℝ := ∑ j, |θ j|

/-- The squared ℓ2 norm `‖θ‖₂² = ∑ j, θ_j²`. -/
def l2NormSq (θ : Fin d → ℝ) : ℝ := ∑ j, θ j ^ 2

/-- The unit ℓ1 ball `B₁^d`. -/
def l1Ball (θ : Fin d → ℝ) : Prop := l1Norm θ ≤ 1

/-- The unit ℓ2 ball `B₂^d`. -/
def l2Ball (θ : Fin d → ℝ) : Prop := l2NormSq θ ≤ 1

/-- Euclidean inner product on `Fin d → ℝ`. -/
def dot (θ φ : Fin d → ℝ) : ℝ := ∑ j, θ j * φ j

/-- `ε`-minimizer over a feasible set (Definitions 2.5 and 2.6): the loss exceeds the
infimum by at most `ε`, written in the equivalent form `L θ ≤ L θ' + ε` for all
feasible `θ'`. -/
def IsEpsilonMinimizer (L : (Fin d → ℝ) → ℝ) (S : Set (Fin d → ℝ)) (ε : ℝ)
    (θ : Fin d → ℝ) : Prop :=
  θ ∈ S ∧ ∀ θ' ∈ S, L θ ≤ L θ' + ε

/-! ## The finite laws `D_{p,W}` and `D'_{p,W}` -/

/-- The Bernoulli law with `Pr[true] = q`. -/
def bernoulli (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDist Bool where
  prob b := if b then q else 1 - q
  nonneg b := by
    cases b
    · simp only [Bool.false_eq_true, if_false]; linarith
    · simp only [if_true]; exact h0
  sum_one := by
    rw [Fintype.sum_bool]
    simp

/-- Coordinate law of `D_{p,W}` (Section 4.1): `Pr[x_j = 1] = 1/2 + p` for `j ∈ W` and
`Pr[x_j = 1] = 1/2` for `j ∉ W`.  The value `true` encodes the sign `+1`. -/
def lassoCoord (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (W : Finset (Fin d))
    (j : Fin d) : FinDist Bool :=
  if j ∈ W then bernoulli (1 / 2 + p) (by linarith) (by linarith)
  else bernoulli (1 / 2) (by norm_num) (by norm_num)

/-- Coordinate law of `D'_{p,W}` (Section 5): `Pr[x_j = +1/√d] = 1/2 + p` for `j ∈ W`
and `Pr[x_j = -1/√d] = 1/2 + p`, i.e. `Pr[x_j = +1/√d] = 1/2 - p`, for `j ∉ W`. -/
def ridgeCoord (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (W : Finset (Fin d))
    (j : Fin d) : FinDist Bool :=
  if j ∈ W then bernoulli (1 / 2 + p) (by linarith) (by linarith)
  else bernoulli (1 / 2 - p) (by linarith) (by linarith)

/-- `D_{p,W}`, the product law over sign configurations of Section 4.1. -/
def lassoDist (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (W : Finset (Fin d)) :
    FinDist (Fin d → Bool) :=
  independentSampleLaw (lassoCoord p hp0 hp1 W)

/-- `D'_{p,W}`, the product law over sign configurations of Section 5. -/
def ridgeDist (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) (W : Finset (Fin d)) :
    FinDist (Fin d → Bool) :=
  independentSampleLaw (ridgeCoord p hp0 hp1 W)

/-- The sign value `+1` for `true`, `-1` for `false`. -/
def sgnBool (b : Bool) : ℝ := if b then 1 else -1

/-- Lasso column value: `x_j = ±1`. -/
def lassoX (b : Bool) : ℝ := sgnBool b

/-- The Ridge scale `1/√d`. -/
def ridgeScale (d : ℕ) : ℝ := 1 / Real.sqrt d

/-- Ridge column value: `x_j = ±1/√d`. -/
def ridgeX (d : ℕ) (b : Bool) : ℝ := ridgeScale d * sgnBool b

/-- Expected squared loss against a fixed target `y = 1`, for the product law over
sign configurations `x_j = xval (b_j)` (Section 2.3 with `ℓ(ŷ,y) = (ŷ-y)²`). -/
def expectedLoss (μ : FinDist (Fin d → Bool)) (xval : Bool → ℝ) (θ : Fin d → ℝ) : ℝ :=
  μ.expect (fun b => ((∑ j, θ j * xval (b j)) - 1) ^ 2)

/-! ## Closed-form losses and minimizers -/

/-- The Lasso loss `L_{D_{p,W}}(θ)` in the compact analytic form of the proof of
Theorem 4.1 (p. 19): after completing the square,
`L = ∑ θ² + 4p²((∑_{W}θ)² - ∑_{W}θ²) - 4p∑_{W}θ + 1`.  The expanded display of
Theorem 4.1 is recorded as `lassoLossExpanded` in the Lasso loss file. -/
def lassoLoss (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) : ℝ :=
  (∑ j, θ j ^ 2)
    + 4 * p ^ 2 * ((∑ j ∈ W, θ j) ^ 2 - ∑ j ∈ W, θ j ^ 2)
    - 4 * p * (∑ j ∈ W, θ j) + 1

/-- The Lasso loss exactly as displayed in Theorem 4.1 (p. 19), with `w = |W|`. -/
def lassoLossExpanded (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) : ℝ :=
  (∑ j, if j ∈ W then 0 else θ j ^ 2)
    + (∑ j ∈ W, (θ j - 2 * p) ^ 2)
    + 4 * p ^ 2 * (∑ j ∈ W, ∑ k ∈ W.erase j, θ j * θ k)
    - 4 * p ^ 2 * (W.card : ℝ) + 1

/-- The Ridge minimizer `θ*_j = (-1)^{[j∈W]}/√d` (Section 5, p. 25). -/
def thetaStarRidge (d : ℕ) (W : Finset (Fin d)) : Fin d → ℝ :=
  fun j => (1 / Real.sqrt d) * (if j ∈ W then 1 else -1)

/-- The Ridge loss `L_{D'_{p,W}}` in the closed form derived at the start of Section 5
(p. 25): `‖θ‖²(1-4p²)/d + (2p⟨θ,θ*⟩ - 1)²`. -/
def ridgeLoss (d : ℕ) (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) : ℝ :=
  l2NormSq θ * (1 - 4 * p ^ 2) / (d : ℝ)
    + (2 * p * dot θ (thetaStarRidge d W) - 1) ^ 2

/-- `w = |W|` as a real number. -/
def cardR (W : Finset (Fin d)) : ℝ := (W.card : ℝ)

/-- The indicator vector `e_W = ∑_{j∈W} e_j`. -/
def eW (W : Finset (Fin d)) : Fin d → ℝ := fun j => if j ∈ W then 1 else 0

/-- The Lasso optimum value `v = 2p/(1 + 4p²(w-1))` (Section 4.1, p. 19). -/
def lassoV (p : ℝ) (W : Finset (Fin d)) : ℝ := 2 * p / (1 + 4 * p ^ 2 * (cardR W - 1))

/-- The Lasso minimizer `θ* = v·e_W` (Section 4.1, p. 19). -/
def thetaStarLasso (p : ℝ) (W : Finset (Fin d)) : Fin d → ℝ := fun j => lassoV p W * eW W j

/-- The Lasso optimum is the unique global minimizer of the closed-form loss
(Theorem 4.1, last sentence). -/
def IsUniqueGlobalMinimizer (L : (Fin d → ℝ) → ℝ) (θ : Fin d → ℝ) : Prop :=
  (∀ θ', L θ ≤ L θ') ∧ (∀ θ', L θ' = L θ → θ' = θ)

/-! ## Explicit gradient and Hessian of the Lasso loss (Theorem 4.1, p. 19) -/

/-- The partial derivative `∇_j L_{D_{p,W}}` displayed in Theorem 4.1. -/
def lassoGrad (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) (j : Fin d) : ℝ :=
  if j ∈ W then 2 * θ j - 4 * p + 8 * p ^ 2 * (∑ l ∈ W.erase j, θ l)
  else 2 * θ j

/-- The Hessian `[∇² L_{D_{p,W}}]_{jk}` displayed in Theorem 4.1, with the block form
`(8p²J_w + (2-8p²)I_w) ⊕ 2I_{w̄}`. -/
def lassoHessian (p : ℝ) (W : Finset (Fin d)) (j k : Fin d) : ℝ :=
  if j ∈ W ∧ k ∈ W then (2 - 8 * p ^ 2) * (if j = k then 1 else 0) + 8 * p ^ 2
  else if j ∉ W ∧ k ∉ W then 2 * (if j = k then 1 else 0)
  else 0

/-- Quadratic form of the Lasso Hessian. -/
def lassoHessianForm (p : ℝ) (W : Finset (Fin d)) (v : Fin d → ℝ) : ℝ :=
  ∑ j, ∑ k, v j * lassoHessian p W j k * v k

/-! ## KP-tree (Definition 2.9) — explicit finite model

The tree stores a root scalar `A`, a per-coordinate leaf value, and a depth.  Reading
coordinate `j` follows the binary path of `j` (so it reads at most `depth` nodes), and
updating to `a·θ + b·e_j` rewrites the root scalar and one leaf, touching at most
`depth+1` nodes.  The internal "sum of absolute children" fields of Definition 2.9 are
only used by the state-preparation construction of Theorem 2.12 and are not needed for
the cost statements of Theorems 2.10 and 2.11. -/
structure KPTree (d : ℕ) where
  /-- The scalar `A` stored at the root. -/
  rootScalar : ℝ
  /-- The scalar stored at the leaf of coordinate `j` (zero when there is no leaf). -/
  leafValue : Fin d → ℝ
  /-- Depth of the tree; the paper uses `⌈log d⌉`. -/
  depth : ℕ
  /-- Support size `t` stored at the root. -/
  support : ℕ

/-- The vector represented by a KP-tree: `θ_j = A · leafValue_j`. -/
def KPTree.theta (K : KPTree d) : Fin d → ℝ := fun j => K.rootScalar * K.leafValue j

/-- Number of nodes read on the root-to-leaf path of `j`. -/
def KPTree.readCost (K : KPTree d) (_j : Fin d) : ℕ := K.depth

/-- Update to `a·θ + b·e_j`: the root scalar becomes `a·A`, the leaf of `j` becomes
`(θ_j + b)/(a·A)` (in units of the old tree, `leafValue_j + b/(a·A)`), and all other
leaves are unchanged. -/
def KPTree.update (K : KPTree d) (a b : ℝ) (j : Fin d) : KPTree d where
  rootScalar := a * K.rootScalar
  leafValue := fun k => if k = j then K.leafValue k + b / (a * K.rootScalar)
    else K.leafValue k
  depth := K.depth
  support := if K.leafValue j = 0 ∧ b ≠ 0 then K.support + 1 else K.support

/-- Number of node values rewritten by `update`: the root, the new leaf, and the path. -/
def KPTree.updateCost (K : KPTree d) (_j : Fin d) : ℕ := K.depth + 1

/-! ## Abstract resource profiles for quantum algorithms

The source theorems assert the existence (or the cost of any) bounded-error quantum
algorithm.  At this paper layer we record the paper's numeric resource guarantees in
these profiles; no amplitude-amplification or query-model semantics is re-derived here.
-/
structure RunProfile where
  /-- Worst-case number of oracle queries (as a real number). -/
  queryCost : ℝ
  /-- Worst-case number of elementary gates (as a real number). -/
  gateCost : ℝ
  /-- Worst-case space (QRAM plus classical bits, as a real number). -/
  spaceCost : ℝ
  /-- Worst-case success probability. -/
  successProb : ℝ

/-- Total variation distance between two finite distributions. -/
def tvDist {X : Type} [Fintype X] [DecidableEq X] (p q : FinDist X) : ℝ :=
  (∑ x, |p.prob x - q.prob x|) / 2

/-- Squared Hellinger distance, in the normalisation used by the shared finite-laws
module: `∑ x, (√(p x) - √(q x))² = 2 d_H²`. -/
def hellingerSqDist {X : Type} [Fintype X] [DecidableEq X] (p q : FinDist X) : ℝ :=
  ∑ x, (Real.sqrt (p.prob x) - Real.sqrt (q.prob x)) ^ 2

end Qatlib.Papers.QRegression21.MainResults
