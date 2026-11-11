/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 model: Euclidean space, convex analysis predicates and oracle interfaces

Fixed source: Chakrabarti--Childs--Li--Wu, *Quantum algorithms and lower bounds for
convex optimization*, arXiv:1809.01731v3 (18 Dec 2019), accepted in Quantum 2019-12-03.

This module is the shared vocabulary for the paper layer.  It records the paper's
definitions from Section 2.1 and Section 3 verbatim in spirit:

* `Pt n` is the ambient Euclidean coordinate space `ℝ^n`; the paper's `B_p(x,r)` balls are
  `ballInf`/`ball2` (Definitions 2.1);
* `IsLipschitzOn` is Definition 2.9, stated through its consequence (2.2):
  `|f y - f x| ≤ L * ‖y - x‖∞`;
* `IsSubgradient` is Definition 2.8, equation (2.1);
* `EvaluationOracle`/`MembershipOracle`/`SeparationOracle`/`OptimizationOracle` are
  Definitions 2.4--2.7 as semantic interfaces (soundness clauses match the definitions);
* `Delta` is the deviation-from-linearity functional (2.23).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- Ambient Euclidean coordinate space `ℝⁿ`. -/
abbrev Pt (n : ℕ) := Fin n → ℝ

/-- Euclidean inner product written as a finite sum (the paper's `⟨u, v⟩`). -/
def dot {n : ℕ} (u v : Pt n) : ℝ := ∑ i, u i * v i

/-- Coordinate-wise maximum norm `‖x‖∞`. -/
def normInf {n : ℕ} (x : Pt n) : ℝ := ⨆ i, |x i|

/-- `ℓ¹` norm `‖x‖₁`. -/
def norm1 {n : ℕ} (x : Pt n) : ℝ := ∑ i, |x i|

/-- Squared Euclidean norm. -/
def norm2Sq {n : ℕ} (x : Pt n) : ℝ := ∑ i, (x i) ^ 2

/-- Euclidean norm `‖x‖₂`. -/
def norm2 {n : ℕ} (x : Pt n) : ℝ := Real.sqrt (norm2Sq x)

/-- Definition 2.1: the Euclidean ball `B₂(x, r)`. -/
def ball2 {n : ℕ} (x : Pt n) (r : ℝ) : Set (Pt n) := {y | norm2 (y - x) ≤ r}

/-- Definition 2.1: the `ℓ∞` ball `B∞(x, r)` (a hypercube). -/
def ballInf {n : ℕ} (x : Pt n) (r : ℝ) : Set (Pt n) := {y | ∀ i, |y i - x i| ≤ r}

/-- Definition 2.3: the `δ`-neighborhood `B₂(K, δ)` of a set `K`. -/
def neighborhood {n : ℕ} (K : Set (Pt n)) (δ : ℝ) : Set (Pt n) :=
  {x | ∃ y ∈ K, norm2 (x - y) ≤ δ}

/-- Definition 2.2: the `δ`-interior `B₂(K, -δ)` of a set `K`. -/
def deltaInterior {n : ℕ} (K : Set (Pt n)) (δ : ℝ) : Set (Pt n) :=
  {x | ball2 x δ ⊆ K}

/-- Definition 2.9: `L`-Lipschitz continuity through consequence (2.2). -/
def IsLipschitzOn {n : ℕ} (f : Pt n → ℝ) (S : Set (Pt n)) (L : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, |f y - f x| ≤ L * normInf (y - x)

/-- Definition 2.8, equation (2.1): `g` is a subgradient of `f` at `x`. -/
def IsSubgradient {n : ℕ} (f : Pt n → ℝ) (x g : Pt n) : Prop :=
  ∀ y, f y ≥ f x + dot g (y - x)

/-- The continuous linear functional `v ↦ ⟨g, v⟩`. -/
def dotCLM {n : ℕ} (g : Pt n) : Pt n →L[ℝ] ℝ :=
  ∑ i, g i • ContinuousLinearMap.proj i

/-- `g` is the gradient (Fréchet derivative) of `f` at `x`; for a differentiable convex
function this is Definition 2.8's unique subgradient. -/
def HasGradientAt {n : ℕ} (f : Pt n → ℝ) (x g : Pt n) : Prop :=
  HasFDerivAt f (dotCLM g) x

/-- Equation (2.23): the deviation from linearity of `f` between `y` and `z`, using the
gradient field `gradf`. -/
def Delta {n : ℕ} (f : Pt n → ℝ) (gradf : Pt n → Pt n) (y z : Pt n) : ℝ :=
  f z - f y - dot (gradf y) (z - y)

/-- Definition 2.4: an evaluation oracle for `f` with precision `δ` returns `α` with
`|α - f x| ≤ δ` when queried at `(x, δ)`. -/
structure EvaluationOracle {n : ℕ} (f : Pt n → ℝ) where
  eval : Pt n → ℝ → ℝ
  sound : ∀ x δ, 0 < δ → |eval x δ - f x| ≤ δ

/-- Definition 2.5: a membership oracle for `K` asserts `x ∈ B₂(K, δ)` (returns `true`) or
`x ∉ B₂(K, -δ)` (returns `false`). -/
structure MembershipOracle {n : ℕ} (K : Set (Pt n)) where
  mem : Pt n → ℝ → Bool
  sound_in : ∀ x δ, 0 < δ → mem x δ = true → x ∈ neighborhood K δ
  sound_out : ∀ x δ, 0 < δ → mem x δ = false → x ∉ deltaInterior K δ

/-- Definition 2.6: a separation oracle.  The output `none` certifies `x ∈ B₂(K, δ)`; the
output `some ĉ` is a unit vector with `⟨ĉ, x⟩ ≤ ⟨ĉ, y⟩ + δ` for all `y ∈ B₂(K, -δ)`.
Success probability is handled at the level of the algorithm, so the interface records the
deterministic soundness clause only. -/
structure SeparationOracle {n : ℕ} (K : Set (Pt n)) where
  query : Pt n → Option (Pt n)
  sound_in : ∀ x, query x = none → x ∈ neighborhood K 0
  sound_sep : ∀ x ĉ, query x = some ĉ → norm2 ĉ = 1 ∧
    ∀ y ∈ deltaInterior K 0, dot ĉ x ≤ dot ĉ y

/-- Definition 2.7: an optimization oracle for `K`: on a unit vector `c` it returns
`y` with `⟨c, x⟩ ≤ ⟨c, y⟩ + δ` for all `x ∈ B₂(K, -δ)`. -/
structure OptimizationOracle {n : ℕ} (K : Set (Pt n)) where
  query : Pt n → ℝ → Pt n
  sound : ∀ c δ, norm2 c = 1 → 0 < δ → ∀ x ∈ deltaInterior K δ, dot c x ≤ dot c (query c δ) + δ

/-- Error parameter bookkeeping for the membership-to-optimization reduction: the paper's
Algorithm 4 uses `δ ∈ (0, min{r/(7κ), 1/(7κ)})` (Theorem 2.3). -/
def admissibleMembershipError (r κ δ : ℝ) : Prop :=
  0 < δ ∧ δ < r / (7 * κ) ∧ δ < 1 / (7 * κ)

/-- The paper's rounding function `sgn_{-3/2}` of equation (3.13). -/
def sgnNegThreeHalves (z : ℝ) : Bool := decide (z < (-3 / 2 : ℝ))

/-- The paper's rounding function `sgn_{1/2}` of equation (3.33). -/
def sgnHalf (z : ℝ) : Bool := decide (z < (1 / 2 : ℝ))

/-- The projection `π` of (3.15) onto `[0,1]`. -/
def piProj (x : ℝ) : ℝ := max 0 (min x 1)

/-- The penalty part `g_i(x) = |π(x_i) - x_i|` of (C.3). -/
def projectionPenalty {n : ℕ} (x : Pt n) (i : Fin n) : ℝ := |piProj (x i) - x i|

/-- The max-norm objective `f_c` of (3.14). -/
def maxNormObjective {n : ℕ} (c : Pt n) (x : Pt n) : ℝ :=
  (⨆ i, |piProj (x i) - c i|) + ∑ i, projectionPenalty x i

/-- Dimension side length of the discretization grid `D_n` of (3.34): `2n+1`. -/
def gridDenom (n : ℕ) : ℕ := 2 * n + 1

/-- Entry `χ(a, π)_i` of (3.35). -/
def gridPoint {n : ℕ} (a : Pt n) (π : Equiv.Perm (Fin n)) : Pt n :=
  fun i => (1 - a i) * ((π i : ℝ) / (gridDenom n : ℝ)) +
    a i * (1 - (π i : ℝ) / (gridDenom n : ℝ))

/-- The restricted function `f|_{D_n}` for the max-norm objective of (3.37). -/
def maxNormObjectiveOnGrid {n : ℕ} (c : Pt n) (a : Pt n) (π : Equiv.Perm (Fin n)) : ℝ :=
  maxNormObjective c (gridPoint a π)

/-- The inverse QFT over `[0,N-1]` of equation (B.3), as a matrix. -/
def qftInv (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun x y => (Real.sqrt N : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * x.val * y.val / N))

/-- The signed index map `γ(x) = x - N/2` of Lemma B.1.  For the paper's even `N = 2^b`
this is `x - ⌊N/2⌋`; we use natural division so that the definition is total. -/
def gamma (N : ℕ) (x : Fin N) : ℤ := (x.val : ℤ) - ((N / 2 : ℕ) : ℤ)

/-- The inverse QFT over `G = {-N/2, ..., N/2-1}` of equation (B.4), as a matrix. -/
def qftGInv (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun x y =>
    (Real.sqrt N : ℂ)⁻¹ *
      Complex.exp (-(2 * Real.pi * Complex.I * (gamma N x : ℂ) * (gamma N y : ℂ) / N))

end Qatlib.Papers.ConvexOpt18.MainResults
