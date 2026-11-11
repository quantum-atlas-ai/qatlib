/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGames19 — shared model of finite zero-sum games and cost contracts

This module fixes the object-level definitions used by every claim of
van Apeldoorn–Gilyén, *Quantum algorithms for zero-sum games*, fixed
arXiv:1904.03180v1 (2019-04-08).

The paper never formalises its algorithmic primitives; the paper layer therefore
introduces

* `PayoffMatrix` for `A ∈ [-1,1]^{n×m}` (paper §1, p.1);
* `rowPayoff`/`colPayoff` for `(Ay)_i` and `(Aᵀx)_j` (paper §2, p.3);
* `EpsOptimal` exactly as the sufficient condition displayed in equation (3),
  p.5: `(Ay/y₁)_i − (Aᵀx/x₁)_j ≤ ε` for all `i,j`;
* `gibbsDist` for Definition 5, p.7: `G(v) := e^v / ‖e^v‖₁`;
* `tvDist` for total-variation distance used in Lemma 8/10;
* `fixedAccuracyRounds` for `T = ⌈16 ln(nm/δ)/ε²⌉` (Lemma 1, p.3);
* `stepSize` and `epsPrime` for Algorithm 1 and Lemma 1's `ε′(t)`;
* `potential` for `Φ(t) = (∑_j P_j)(∑_i Q_i)` (proof of Lemma 1, p.4);
* `SoftOIn` for the paper's `Õ(·)` complexity notation;
* cost contracts `ClassicalImplementation`, `QuantumImplementation`, `GibbsSampler`.

These are definitions only; the per-claim modules state and (where possible)
prove the paper's results over them.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

open Finset
open scoped BigOperators

/-! ## Finite matrix games (paper §1) -/

/-- A finite two-player zero-sum game with payoff matrix `A ∈ [-1,1]^{n×m}`.
    Paper §1, p.1: Alice picks `i ∈ [n]`, Bob picks `j ∈ [m]`, Alice receives `A_ij`. -/
structure PayoffMatrix (n m : ℕ) where
  A : Fin n → Fin m → ℝ
  hA : ∀ i j, -1 ≤ A i j ∧ A i j ≤ 1

/-- Row payoff `(Ay)_i` (paper §2, Algorithm 1, p.3). -/
def rowPayoff {n m : ℕ} (A : PayoffMatrix n m) (y : Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ j, A.A i j * y j

/-- Column payoff `(Aᵀx)_j` (paper §2, Algorithm 1, p.3). -/
def colPayoff {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i, x i * A.A i j

/-- Alice's expected payoff `xᵀAy` (paper §1, p.1). -/
def expectedPayoff {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  ∑ i, x i * rowPayoff A y i

/-- `x` is a probability distribution on `Fin n` (i.e. `x ∈ Δ_n`). -/
def IsDistribution {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- The paper's sufficient condition for an `ε`-optimal strategy pair, display (3)
    on p.5 of arXiv:1904.03180v1: `(Ay/y₁)_i − (Aᵀx/x₁)_j ≤ ε` for all `i, j`.
    Under strong duality this is equivalent to `ε`-optimality (paper's proof of
    Lemma 1); the paper itself uses this display as the operative definition. -/
def EpsOptimal {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (ε : ℝ) : Prop :=
  ∀ i j, rowPayoff A y i - colPayoff A x j ≤ ε

/-! ## Normalisation bridges -/

/-- Dividing the strategy `y` by `S ≠ 0` divides the row payoff by `S`. -/
theorem rowPayoff_div {n m : ℕ} (A : PayoffMatrix n m) (y : Fin m → ℝ) {S : ℝ}
    (hS : S ≠ 0) (i : Fin n) :
    rowPayoff A (fun j => y j / S) i = rowPayoff A y i / S := by
  unfold rowPayoff
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Dividing the strategy `x` by `S ≠ 0` divides the column payoff by `S`. -/
theorem colPayoff_div {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) {S : ℝ}
    (hS : S ≠ 0) (j : Fin m) :
    colPayoff A (fun i => x i / S) j = colPayoff A x j / S := by
  unfold colPayoff
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- If the unnormalised payoff difference is at most `ε′ · S`, then the pair
    `(x/S, y/S)` satisfies the paper's display (3) with error `ε′`.
    This is exactly the last normalisation step of the proof of Lemma 1 (p.5). -/
theorem epsOptimal_of_normalized {n m : ℕ} (A : PayoffMatrix n m)
    (x : Fin n → ℝ) (y : Fin m → ℝ) {S ε' : ℝ} (hS : 0 < S)
    (h : ∀ i j, rowPayoff A y i - colPayoff A x j ≤ ε' * S) :
    EpsOptimal A (fun i => x i / S) (fun j => y j / S) ε' := by
  intro i j
  rw [rowPayoff_div A y (ne_of_gt hS) i, colPayoff_div A x (ne_of_gt hS) j,
    div_sub_div_same, div_le_iff₀ hS]
  exact h i j

/-! ## Gibbs distribution (Definition 5, p.7) -/

/-- `G(v)_i = e^{v_i} / ∑_j e^{v_j}`. Paper Definition 5, p.7. -/
def gibbsDist {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.exp (v i) / ∑ j, Real.exp (v j)

/-- The Gibbs normaliser `∑ j, e^{v_j}` is positive for a nonempty index set. -/
theorem expSum_pos {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    0 < ∑ j, Real.exp (v j) := by
  apply Finset.sum_pos (fun j _ => Real.exp_pos _)
  exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- Gibbs weights are nonnegative. -/
theorem gibbsDist_nonneg {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (i : Fin n) :
    0 ≤ gibbsDist v i :=
  le_of_lt (div_pos (Real.exp_pos _) (expSum_pos hn v))

/-- Gibbs weights sum to one. -/
theorem gibbsDist_sum {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    ∑ i, gibbsDist v i = 1 := by
  unfold gibbsDist
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (expSum_pos hn v))

/-- The Gibbs weights form a probability distribution. -/
theorem gibbsDist_isDistribution {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    IsDistribution (gibbsDist v) :=
  ⟨gibbsDist_nonneg hn v, gibbsDist_sum hn v⟩

/-- Total-variation distance `(1/2) ∑_a |p a − q a|` (as used in Lemma 8/10). -/
def tvDist {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ a, |p a - q a|

/-- Total-variation distance is nonnegative. -/
theorem tvDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) : 0 ≤ tvDist p q := by
  unfold tvDist
  positivity

/-- The total-variation distance of a distribution from itself is zero. -/
theorem tvDist_self {α : Type*} [Fintype α] (p : α → ℝ) : tvDist p p = 0 := by
  simp [tvDist]

/-- Total-variation distance is symmetric. -/
theorem tvDist_comm {α : Type*} [Fintype α] (p q : α → ℝ) : tvDist p q = tvDist q p := by
  unfold tvDist
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [abs_sub_comm]

/-! ## Algorithm 1 quantities (p.3-5) -/

/-- Algorithm 1's running step size `η^(t) = 1/(2√t)` (p.3). -/
def stepSize (t : ℕ) : ℝ := 1 / (2 * Real.sqrt t)

/-- The fixed-accuracy step size `η^(t) := ε/4` used in the second half of Lemma 1. -/
def fixedStepSize (ε : ℝ) : ℝ := ε / 4

/-- The stopping rule `T = ⌈16 ln(nm/δ)/ε²⌉` of Lemma 1 (p.3). -/
def fixedAccuracyRounds (n m : ℕ) (ε δ : ℝ) : ℕ :=
  Nat.ceil (16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2)

/-- Lemma 1's intermediate accuracy
    `ε′(t) = (2/√t)(3 ln t + ln(nm) + ln(1/δ) + 2)` (p.3). -/
def epsPrime (n m : ℕ) (δ : ℝ) (t : ℕ) : ℝ :=
  2 / Real.sqrt t * (3 * Real.log t + Real.log ((n : ℝ) * m) + Real.log (1 / δ) + 2)

/-- The potential `Φ(t) = (∑_j P_j)(∑_i Q_i)` of the proof of Lemma 1 (p.4),
    with `P = e^{−Aᵀx}` and `Q = e^{Ay}`. -/
def potential {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) (y : Fin m → ℝ) : ℝ :=
  (∑ j, Real.exp (-(colPayoff A x j))) * (∑ i, Real.exp (rowPayoff A y i))

/-! ## Complexity notation and implementation contracts -/

/-- The paper's `Õ(·)` notation (p.2): `cost` is at most `g` times a
    polylogarithmic factor in `scale`. -/
def SoftOIn (scale g cost : ℝ) : Prop :=
  ∃ k : ℕ, ∃ C : ℝ, 0 < C ∧ cost ≤ C * g * (Real.log (2 + scale)) ^ k

/-- Cost contract for a classical randomised implementation of Algorithm 1. -/
structure ClassicalImplementation (n m : ℕ) where
  rounds : ℕ
  timePerRound : ℝ
  queriesPerRound : ℝ
  successProb : ℝ

/-- Cost contract for a quantum implementation of Algorithm 1. -/
structure QuantumImplementation (n m : ℕ) where
  rounds : ℕ
  successProb : ℝ
  perRoundTime : ℕ → ℝ
  perRoundQueries : ℕ → ℝ
  totalTime : ℝ
  totalQueries : ℝ

/-- Output distribution and cost of a Gibbs sampler `G(xᵀA)` (Lemma 8/10). -/
structure GibbsSampler (m : ℕ) where
  output : Fin m → ℝ
  queryCost : ℝ
  timeCost : ℝ

/-- Data of the LP-to-game reduction of §4: LP (4) and its game (6),
    with the optimal values `OPT` of the LP and `lambdaStar` of the game. -/
structure LPGameReduction (n m : ℕ) where
  A : Fin n → Fin m → ℝ
  b : Fin m → ℝ
  c : Fin n → ℝ
  α : ℝ
  R : ℝ
  r : ℝ
  OPT : ℝ
  lambdaStar : ℝ

end Qatlib.Papers.ZeroSumGames19.MainResults.GameModel
