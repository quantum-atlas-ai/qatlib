/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinDynamics23.DiscreteObs.Proposition20HybridObservableBiasStat
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary

/-!
# Bias bounds for hybrid observable reconstruction

`hybridObservable_double_sum` identifies the coefficient-weighted pairwise observable expression
with the quadratic form of the reconstructed vector. Vector reconstruction and quadratic-form
perturbation estimates then establish `proposition20HybridObservableBias`, separating quadrature
error from errors in the individual simulated evolutions. See [AnChildsLin2026] for the paper
context.

## Main statements

* `hybridObservable_quadratic_error`: For vectors within Euclidean distance `d`, the difference
  of their observable quadratic forms has norm at most `‖O‖ * d * (2 * ‖y‖ + d)`, with the
  vector norm interpreted through `toEuclidean_fromVec`.
* `hybridObservable_reconstruction_error`: On a unit input, replacing each evolution by a matrix
  within operator-norm error `εhs` changes the reconstructed vector by at most `(∑ j, ‖c j‖) *
  εhs` in Euclidean norm.
* `proposition20HybridObservableBias`: The hybrid observable bias contract holds, giving the
  double-sum identity and the stated quadratic bias bound from quadrature and
  individual-evolution errors.

## References

* [An et al., 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

namespace Qatlib.Papers.LinDynamics23.DiscreteObs

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The coefficient-weighted double sum of pairwise observable matrix elements equals the
observable quadratic form of the linearly reconstructed vector. -/
theorem hybridObservable_double_sum {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ} (c : Fin N → ℂ) (W : Fin N → Matrix I I ℂ)
    (O : Matrix I I ℂ) (x : QState I) :
    (∑ l : Fin N, ∑ j : Fin N, star (c l) * c j *
      Inner (W l *ᵥ x) (O *ᵥ (W j *ᵥ x))) =
      Inner ((∑ j, c j • W j) *ᵥ x) (O *ᵥ ((∑ j, c j • W j) *ᵥ x)) := by
  symm
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum,
    Matrix.mulVec_smul]
  simp only [← inner_euclidean_fromVec, toEuclidean_fromVec,
    WithLp.toLp_sum, WithLp.toLp_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  simp only [starRingEnd_apply]
  ring

/-- If the Euclidean distance from `x` to `y` is at most `d`, then the Euclidean norm of `x` is
at most that of `y` plus `d`. -/
theorem hybridObservable_norm_of_close {I : Type} [Fintype I]
    (x y : QState I) (d : ℝ)
    (h : ‖toEuclidean_fromVec x - toEuclidean_fromVec y‖ ≤ d) :
    ‖toEuclidean_fromVec x‖ ≤ ‖toEuclidean_fromVec y‖ + d := by
  have ht := norm_add_le (toEuclidean_fromVec x - toEuclidean_fromVec y)
    (toEuclidean_fromVec y)
  rw [sub_add_cancel] at ht
  linarith

/-- For vectors within Euclidean distance `d`, the difference of their observable quadratic
forms has norm at most `‖O‖ * d * (2 * ‖y‖ + d)`, with the vector norm interpreted through
`toEuclidean_fromVec`. -/
theorem hybridObservable_quadratic_error {I : Type} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (x y : QState I) (d : ℝ)
    (h : ‖toEuclidean_fromVec x - toEuclidean_fromVec y‖ ≤ d) :
    ‖Inner x (O *ᵥ x) - Inner y (O *ᵥ y)‖ ≤
      ‖O‖ * (d * (2 * ‖toEuclidean_fromVec y‖ + d)) := by
  have hd : 0 ≤ d := (norm_nonneg _).trans h
  have hx := hybridObservable_norm_of_close x y d h
  have he : Inner x (O *ᵥ x) - Inner y (O *ᵥ y) =
      Inner (x - y) (O *ᵥ x) + Inner y (O *ᵥ (x - y)) := by
    simp only [Matrix.mulVec_sub, ← inner_euclidean_fromVec, toEuclidean_fromVec,
      WithLp.toLp_sub, inner_sub_left, inner_sub_right]
    ring
  have hn : ‖toEuclidean_fromVec (x - y)‖ =
      ‖toEuclidean_fromVec x - toEuclidean_fromVec y‖ := by
    simp only [toEuclidean_fromVec, WithLp.toLp_sub]
  rw [he]
  calc
    _ ≤ ‖Inner (x - y) (O *ᵥ x)‖ + ‖Inner y (O *ᵥ (x - y))‖ := norm_add_le _ _
    _ ≤ ‖O‖ * ‖toEuclidean_fromVec (x - y)‖ * ‖toEuclidean_fromVec x‖ +
        ‖O‖ * ‖toEuclidean_fromVec y‖ * ‖toEuclidean_fromVec (x - y)‖ :=
      add_le_add (adv_inner_matrix_bound _ _ _) (adv_inner_matrix_bound _ _ _)
    _ = ‖O‖ * (‖toEuclidean_fromVec x - toEuclidean_fromVec y‖ *
        (‖toEuclidean_fromVec x‖ + ‖toEuclidean_fromVec y‖)) := by rw [hn]; ring
    _ ≤ ‖O‖ * (d * (2 * ‖toEuclidean_fromVec y‖ + d)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul h (by linarith) (by positivity) hd) (norm_nonneg _)

/-- On a unit input, replacing each evolution by a matrix within operator-norm error `εhs`
changes the reconstructed vector by at most `(∑ j, ‖c j‖) * εhs` in Euclidean norm. -/
theorem hybridObservable_reconstruction_error {I : Type} [Fintype I] [DecidableEq I]
    {N : ℕ} (c : Fin N → ℂ) (W U : Fin N → Matrix I I ℂ)
    (x : QState I) (hx : ‖toEuclidean_fromVec x‖ = 1) (εhs : ℝ)
    (herror : ∀ j, ‖W j - U j‖ ≤ εhs) :
    ‖toEuclidean_fromVec ((∑ j, c j • W j) *ᵥ x) -
      toEuclidean_fromVec ((∑ j, c j • U j) *ᵥ x)‖ ≤ (∑ j, ‖c j‖) * εhs := by
  have hm : ‖∑ j, c j • (W j - U j)‖ ≤ (∑ j, ‖c j‖) * εhs := by
    calc
      _ ≤ ∑ j, ‖c j • (W j - U j)‖ := norm_sum_le _ _
      _ = ∑ j, ‖c j‖ * ‖W j - U j‖ := by simp only [norm_smul]
      _ ≤ ∑ j, ‖c j‖ * εhs := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (herror j) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul]
  have he : toEuclidean_fromVec ((∑ j, c j • W j) *ᵥ x) -
      toEuclidean_fromVec ((∑ j, c j • U j) *ᵥ x) =
      toEuclidean_fromVec ((∑ j, c j • (W j - U j)) *ᵥ x) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Matrix.sub_mulVec,
      toEuclidean_fromVec, WithLp.toLp_sub]
  rw [he]
  exact (l2_norm_mulVec_fromVec_le _ x).trans (by simpa only [hx, mul_one] using! hm)

/-- The hybrid observable bias contract holds, giving the double-sum identity and the stated
quadratic bias bound from quadrature and individual-evolution errors [An et al., Proposition
20][AnChildsLin2026]. -/
theorem proposition20HybridObservableBias : Proposition20HybridObservableBias := by
  intro I _ _ N c kk W L H B i₀ O T η εhs _hL _hH _hLp _hHh _hT _hW hB _hO
  (try dsimp only)
  intro hsim hdisc
  let U : Fin N → Matrix I I ℂ := fun j =>
    orderedEvolution (fun u => Complex.I • (H u + kk j • L u)) 0 T
  let x : QState I := B *ᵥ Ket i₀
  let u : QState I := (orderedEvolution (fun t => L t + Complex.I • H t) 0 T) *ᵥ x
  let vU : QState I := (∑ j, c j • U j) *ᵥ x
  let v : QState I := (∑ j, c j • W j) *ᵥ x
  let γ : ℝ := ∑ j, ‖c j‖
  have hx : ‖toEuclidean_fromVec x‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec x).mp (normalized_applyGate hB (normalized_ket i₀))
  have hsimv : ‖toEuclidean_fromVec v - toEuclidean_fromVec vU‖ ≤ γ * εhs :=
    hybridObservable_reconstruction_error c W U x hx εhs hsim
  have hdisc' : ‖toEuclidean_fromVec vU - toEuclidean_fromVec u‖ ≤ η := hdisc
  have hd : 0 ≤ γ * εhs := (norm_nonneg _).trans hsimv
  have hvU := hybridObservable_norm_of_close vU u η hdisc'
  have hs := hybridObservable_quadratic_error O v vU (γ * εhs) hsimv
  have ht := hybridObservable_quadratic_error O vU u η hdisc'
  refine ⟨hybridObservable_double_sum c W O x, ?_⟩
  change ‖Inner v (O *ᵥ v) - Inner u (O *ᵥ u)‖ ≤ _
  calc
    _ ≤ ‖Inner v (O *ᵥ v) - Inner vU (O *ᵥ vU)‖ +
        ‖Inner vU (O *ᵥ vU) - Inner u (O *ᵥ u)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖O‖ * (γ * εhs * (2 * ‖toEuclidean_fromVec vU‖ + γ * εhs)) +
        ‖O‖ * (η * (2 * ‖toEuclidean_fromVec u‖ + η)) := add_le_add hs ht
    _ ≤ ‖O‖ * (γ * εhs * (2 * (‖toEuclidean_fromVec u‖ + η) + γ * εhs)) +
        ‖O‖ * (η * (2 * ‖toEuclidean_fromVec u‖ + η)) :=
      by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg O)
          apply mul_le_mul_of_nonneg_left _ hd
          linarith only [hvU]
        · exact le_rfl
    _ = _ := by ring

end Qatlib.Papers.LinDynamics23.DiscreteObs
