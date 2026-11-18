/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux

@[expose] public section


/-!
# Reviewed closed fragment of Wilde, arXiv:1106.1445v8

Only closed definitions and proofs are present. Capacity records have unconstrained
fields; conditional limits and averaging steps do not establish operational coding
or source algorithm costs. See the per-declaration source review receipt.
-/

namespace Qatlib.Papers.QShannonWilde11.MainResults.ClassicalInfo

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open scoped BigOperators

noncomputable section

/-! ## Local classical definitions -/

/-- The `ℓ₁` distance `‖p−q‖₁ = Σ_x |p(x)−q(x)|`. -/
def l1Dist {X : Type} [Fintype X] (p q : X → ℝ) : ℝ := ∑ x, |p x - q x|

/-- Classical conditional entropy `H(X|Y) = H(XY) − H(Y)`. -/
def condEnt {X Y : Type} [Fintype X] [Fintype Y] (p : X × Y → ℝ) : ℝ :=
  classicalEntropy p - classicalEntropy (fun y => ∑ x, p (x, y))

/-- Classical conditional mutual information `I(X;Y|Z)`. -/
def classicalCondMutualInfo {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (p : X × Y × Z → ℝ) : ℝ :=
  classicalEntropy (fun (x, y) => ∑ z, p (x, y, z)) +
    classicalEntropy (fun (y, z) => ∑ x, p (x, y, z)) -
    classicalEntropy p -
    classicalEntropy (fun y => ∑ x, ∑ z, p (x, y, z))

/-- Action of a classical channel `W : X → Y → ℝ` on an input distribution. -/
def chanAct {X Y : Type} [Fintype X] (W : X → Y → ℝ) (p : X → ℝ) : Y → ℝ :=
  fun y => ∑ x, W x y * p x

/-- The Bayesian recovery map `R_{p,W}` of Thm 10.7.2 / Thm 10.8.4. -/
def bayesRecover {X Y : Type} [Fintype X] [Fintype Y] (W : X → Y → ℝ)
    (p : X → ℝ) (q' : Y → ℝ) : X → ℝ :=
  fun x => ∑ y, (p x * W x y / (∑ x', p x' * W x' y)) * q' y

/-- **Lemma 10.7.1** — arXiv:1106.1445v8, fixed PDF p. 307. For probability
distributions `p, q` on `X` and `A = {x : p(x) ≥ q(x)}`,
`½‖p−q‖₁ = p(A) − q(A) = Σ_x max(p(x)−q(x), 0)`.
Proved with the pointwise identity `|p−q| = 2·max(p−q,0) + (q−p)`: summing and
using `Σ p = Σ q = 1` cancels the linear term. The equal-total-mass hypotheses
are exactly the paper's assumption that `p` and `q` are distributions. -/
theorem half_l1Dist_eq_sum_nonneg_difference {X : Type} [Fintype X] (p q : X → ℝ)
    (hp : IsProb p) (hq : IsProb q) :
    (1 / 2) * l1Dist p q =
      ∑ x, if p x ≥ q x then p x - q x else 0 := by
  have hterm : ∀ x, |p x - q x| =
      2 * (if p x ≥ q x then p x - q x else 0) + (q x - p x) := by
    intro x
    by_cases h : p x ≥ q x
    · rw [ite_eq_left h, abs_of_nonneg (by linarith)]
      ring
    · rw [ite_eq_right h, abs_of_neg (by have := not_le.mp h; linarith)]
      ring
  have hsum : (∑ x, |p x - q x|) =
      2 * (∑ x, if p x ≥ q x then p x - q x else 0) +
        ((∑ x, q x) - ∑ x, p x) := by
    calc (∑ x, |p x - q x|)
        = ∑ x, (2 * (if p x ≥ q x then p x - q x else 0) + (q x - p x)) :=
          Finset.sum_congr rfl (fun x _ => hterm x)
      _ = 2 * (∑ x, if p x ≥ q x then p x - q x else 0) +
            ((∑ x, q x) - ∑ x, p x) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_sub_distrib]
  unfold l1Dist
  have hzero : (∑ x, q x) - ∑ x, p x = 0 := by rw [hq.2, hp.2]; ring
  rw [hsum, hzero]
  ring

end

end Qatlib.Papers.QShannonWilde11.MainResults.ClassicalInfo
