/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic

/-!
# X-program circuits and sums over paths

This module defines binary X-programs through their row vectors and action angles, the commuting
gate action `xGate`, and the output probability `prob`. The path representation `pathSum` is
shown to equal the recursively defined circuit amplitude, establishing the sum-over-paths
identity of Lemma 1 in [ShepherdBremner2009].

## Main statements

* `xGate_comm`: proves commutativity of the X-gate actions.
* `circuit_eq_pathSum`: identifies circuit amplitudes with constrained path sums.
* `prob_eq_pathSum`: expresses output probabilities as squared norms of path sums.

## References

* [Shepherd and Bremner, 2009][ShepherdBremner2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.Instantaneous08.MainResults.XProgram

/-- The type of length-`n` vectors over `ZMod 2`. -/
abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

/-- Every binary vector added to itself is zero. -/
theorem add_self_eq_zero_vec {n : ℕ} (x : F2Vec n) : x + x = 0 := by
  funext j
  exact CharTwo.add_self_eq_zero (x j)

/-- The complex coefficient of one Boolean path choice, equal to `cos θ` for false and `I * sin
θ` for true. -/
def pathCoeff (θ : ℝ) (b : Bool) : ℂ :=
  if b then Complex.I * (Real.sin θ : ℂ) else (Real.cos θ : ℂ)

/-- The false path choice has coefficient `cos θ`. -/
@[simp]
theorem pathCoeff_false (θ : ℝ) : pathCoeff θ false = (Real.cos θ : ℂ) := by
  simp [pathCoeff]

/-- The true path choice has coefficient `I * sin θ`. -/
@[simp]
theorem pathCoeff_true (θ : ℝ) : pathCoeff θ true = Complex.I * (Real.sin θ : ℂ) := by
  simp [pathCoeff]

/-- The product of the individual path coefficients for the angle family `θ`. -/
def pathWeight {k : ℕ} (θ : Fin k → ℝ) (a : Fin k → Bool) : ℂ :=
  ∏ i, pathCoeff (θ i) (a i)

/-- The binary sum of program rows selected by the true entries of the path. -/
def pathSample {n k : ℕ} (p : Fin k → F2Vec n) (a : Fin k → Bool) : F2Vec n :=
  ∑ i, if a i then p i else 0

/-- The sum of path weights over all Boolean paths whose selected rows sum to `x`. -/
def pathSum {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) (x : F2Vec n) : ℂ :=
  ∑ a : Fin k → Bool, pathWeight θ a * (if pathSample p a = x then 1 else 0)

/-- The X-gate action `cos θ * ψ x + I * sin θ * ψ (x + p)` on amplitudes. -/
def xGate {n : ℕ} (θ : ℝ) (p : F2Vec n) (ψ : F2Vec n → ℂ) : F2Vec n → ℂ :=
  fun x => (Real.cos θ : ℂ) * ψ x + Complex.I * (Real.sin θ : ℂ) * ψ (x + p)

/-- X-gate actions commute for arbitrary angles and binary row vectors. See
[ShepherdBremner2009]. -/
theorem xGate_comm {n : ℕ} (θ φ : ℝ) (p q : F2Vec n) (ψ : F2Vec n → ℂ) :
    xGate θ p (xGate φ q ψ) = xGate φ q (xGate θ p ψ) := by
  funext x
  simp only [xGate]
  rw [show (x + p) + q = (x + q) + p by abel]
  ring

/-- The recursive X-program amplitude obtained by applying the row gates to the zero basis
state. -/
def circuit {n : ℕ} : (k : ℕ) → (Fin k → F2Vec n) → (Fin k → ℝ) → F2Vec n → ℂ
  | 0, _, _, x => if x = 0 then 1 else 0
  | k + 1, p, θ, x =>
      xGate (θ 0) (p 0) (circuit k (fun i => p i.succ) (fun i => θ i.succ)) x

/-- The output probability, defined as the squared norm of the circuit amplitude. -/
def prob {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ) (x : F2Vec n) : ℝ :=
  Complex.normSq (circuit k p θ x)

/-- The equivalence splitting a Boolean vector of length `k + 1` into its first entry and its
length-`k` tail. -/
def succEquiv (k : ℕ) : (Fin (k + 1) → Bool) ≃ Bool × (Fin k → Bool) where
  toFun a := (a 0, fun i => a i.succ)
  invFun b := Fin.cons b.1 b.2
  left_inv a := by
    funext i
    exact congrFun (Fin.cons_self_tail a) i
  right_inv b := by
    rcases b with ⟨b0, br⟩
    simp only [Prod.mk.injEq]
    exact ⟨rfl, rfl⟩

/-- Splits the path sum according to the first path choice into a cosine-weighted tail and an
imaginary-sine-weighted shifted tail. -/
theorem pathSum_succ {n k : ℕ} (p : Fin (k + 1) → F2Vec n) (θ : Fin (k + 1) → ℝ)
    (x : F2Vec n) :
    pathSum p θ x =
      (Real.cos (θ 0) : ℂ) * pathSum (fun i => p i.succ) (fun i => θ i.succ) x +
        Complex.I * (Real.sin (θ 0) : ℂ) *
          pathSum (fun i => p i.succ) (fun i => θ i.succ) (x + p 0) := by
  have hsplit :
      pathSum p θ x =
        ∑ b : Bool × (Fin k → Bool),
          pathWeight θ (Fin.cons b.1 b.2) *
            (if pathSample p (Fin.cons b.1 b.2) = x then 1 else 0) := by
    rw [pathSum]
    exact Fintype.sum_equiv (succEquiv k) _ _
      (fun a => by
        show pathWeight θ a * (if pathSample p a = x then 1 else 0) =
          pathWeight θ (Fin.cons (a 0) (Fin.tail a)) *
            (if pathSample p (Fin.cons (a 0) (Fin.tail a)) = x then 1 else 0)
        rw [Fin.cons_self_tail])
  rw [hsplit, Fintype.sum_prod_type, Fintype.sum_bool]
  have hfalse :
      (∑ rest : Fin k → Bool,
          pathWeight θ (Fin.cons false rest) *
            (if pathSample p (Fin.cons false rest) = x then 1 else 0)) =
        (Real.cos (θ 0) : ℂ) *
          ∑ rest : Fin k → Bool,
            pathWeight (fun i => θ i.succ) rest *
              (if pathSample (fun i => p i.succ) rest = x then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun rest _ => ?_
    simp [pathWeight, Fin.prod_univ_succ, pathSample, Fin.sum_univ_succ]
  have htrue :
      (∑ rest : Fin k → Bool,
          pathWeight θ (Fin.cons true rest) *
            (if pathSample p (Fin.cons true rest) = x then 1 else 0)) =
        (Complex.I * (Real.sin (θ 0) : ℂ)) *
          ∑ rest : Fin k → Bool,
            pathWeight (fun i => θ i.succ) rest *
              (if pathSample (fun i => p i.succ) rest = x + p 0 then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun rest _ => ?_
    have htag : ∀ y : F2Vec n, pathSample p (Fin.cons true rest) = y ↔
        pathSample (fun i => p i.succ) rest = y + p 0 := by
      intro y
      simp only [pathSample, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, if_true]
      constructor
      · intro h
        have h2 : (p 0 + ∑ i, if rest i then p i.succ else 0) + p 0 = y + p 0 :=
          congrArg (fun z => z + p 0) h
        have hcancel : (p 0 + ∑ i, if rest i then p i.succ else 0) + p 0 =
            ∑ i, if rest i then p i.succ else 0 := by
          rw [add_assoc, add_comm (∑ i, if rest i then p i.succ else 0), ← add_assoc,
            add_self_eq_zero_vec, zero_add]
        rwa [hcancel] at h2
      · intro h
        rw [h, add_comm y (p 0), ← add_assoc, add_self_eq_zero_vec, zero_add]
    simp [pathWeight, Fin.prod_univ_succ, htag x]
  rw [hfalse, htrue, add_comm]
  rfl

/-- The recursive circuit amplitude equals its constrained sum over Boolean paths, as in
[Shepherd and Bremner, Lemma 1][ShepherdBremner2009]. -/
theorem circuit_eq_pathSum {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) : circuit k p θ x = pathSum p θ x := by
  induction k generalizing x with
  | zero =>
      have h : pathSum p θ x = (if x = 0 then 1 else 0) := by
        by_cases hx : x = 0
        · simp [pathSum, pathWeight, pathSample, hx]
        · simp [pathSum, pathWeight, pathSample]
          rw [if_neg hx, if_neg (Ne.symm hx)]
      rw [h]
      by_cases hx : x = 0
      · simp [circuit, hx]
      · simp [circuit, hx]
  | succ k ih =>
      rw [show circuit (k + 1) p θ x =
          xGate (θ 0) (p 0) (circuit k (fun i => p i.succ) (fun i => θ i.succ)) x from rfl,
        pathSum_succ]
      simp only [xGate, ih]

/-- The X-program output probability equals the squared norm of the constrained path sum, as in
[Shepherd and Bremner, Lemma 1][ShepherdBremner2009]. -/
theorem prob_eq_pathSum {n k : ℕ} (p : Fin k → F2Vec n) (θ : Fin k → ℝ)
    (x : F2Vec n) : prob p θ x = Complex.normSq (pathSum p θ x) := by
  simp [prob, circuit_eq_pathSum]

end Qatlib.Papers.Instantaneous08.MainResults.XProgram
