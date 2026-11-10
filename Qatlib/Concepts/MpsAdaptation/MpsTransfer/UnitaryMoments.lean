/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.MixedFidelity.FidelityMetric.SimultaneousDiagonalization
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Ring
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MixedFidelity.FidelityMetric

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Qatlib.Concepts.MpsAdaptation.MpsTransfer

open scoped Classical BigOperators Matrix

theorem exists_unitary_phase_diagonalization {d : ℕ} (U : Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    ∃ (W : Operator d) (z : Fin d → ℂ),
      W * W.conjTranspose = 1 ∧ W.conjTranspose * W = 1 ∧
      (∀ j, ‖z j‖ = 1) ∧
      U = W * Matrix.diagonal z * W.conjTranspose := by
  have hUleft : U * U.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp hU)
  have hUright : U.conjTranspose * U = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hU)
  let R : Operator d := (1 / 2 : ℂ) • (U + U.conjTranspose)
  let S : Operator d := (-Complex.I / 2 : ℂ) • (U - U.conjTranspose)
  have hR : R.IsHermitian := by
    change ((1 / 2 : ℂ) • (U + U.conjTranspose)).conjTranspose =
      (1 / 2 : ℂ) • (U + U.conjTranspose)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose]
    have hc : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by simp
    rw [hc, add_comm U.conjTranspose U]
  have hS : S.IsHermitian := by
    change ((-Complex.I / 2 : ℂ) • (U - U.conjTranspose)).conjTranspose =
      (-Complex.I / 2 : ℂ) • (U - U.conjTranspose)
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    have hc : star (-Complex.I / 2 : ℂ) = (Complex.I / 2 : ℂ) := by
      simp [Complex.star_def]
    rw [hc]
    ext i j
    change (Complex.I / 2) * (U.conjTranspose i j - U i j) =
      (-Complex.I / 2) * (U i j - U.conjTranspose i j)
    ring
  have hcomm : Commute U U.conjTranspose := hUleft.trans hUright.symm
  have hsumU : Commute (U + U.conjTranspose) U :=
    (Commute.refl U).add_left hcomm.symm
  have hsumAdj : Commute (U + U.conjTranspose) U.conjTranspose :=
    hcomm.add_left (Commute.refl U.conjTranspose)
  have hRS : Commute R S :=
    ((hsumU.sub_right hsumAdj).smul_left (1 / 2 : ℂ)).smul_right
      (-Complex.I / 2 : ℂ)
  let H : Bool → Operator d := fun b => if b then S else R
  have hHerm : ∀ b, (H b).IsHermitian := by
    intro b
    cases b
    · exact hR
    · exact hS
  have hComm : ∀ b c, H b * H c = H c * H b := by
    intro b c
    cases b <;> cases c
    · rfl
    · exact hRS.eq
    · exact hRS.symm.eq
    · rfl
  obtain ⟨W, diag, hleft, hright, hdiag⟩ :=
    exists_simultaneous_unitary_diagonalization H hHerm hComm
  let z : Fin d → ℂ := fun j =>
    (diag false j : ℂ) + Complex.I * (diag true j : ℂ)
  have hRspec : R = W * Matrix.diagonal (fun j => (diag false j : ℂ)) *
      W.conjTranspose := hdiag false
  have hSspec : S = W * Matrix.diagonal (fun j => (diag true j : ℂ)) *
      W.conjTranspose := hdiag true
  have hcoef : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I, neg_neg]
  have hsplit : U = R + Complex.I • S := by
    ext i j
    change U i j = (1 / 2 : ℂ) * (U i j + U.conjTranspose i j) +
      Complex.I * ((-Complex.I / 2) * (U i j - U.conjTranspose i j))
    rw [← mul_assoc, hcoef]
    ring
  have hdiagadd :
      Matrix.diagonal (fun j => (diag false j : ℂ)) +
        Complex.I • Matrix.diagonal (fun j => (diag true j : ℂ)) =
      Matrix.diagonal z := by
    rw [← Matrix.diagonal_smul, Matrix.diagonal_add]
    rfl
  have hspec : U = W * Matrix.diagonal z * W.conjTranspose := by
    calc
      U = R + Complex.I • S := hsplit
      _ = W * Matrix.diagonal (fun j => (diag false j : ℂ)) * W.conjTranspose +
          Complex.I •
            (W * Matrix.diagonal (fun j => (diag true j : ℂ)) * W.conjTranspose) := by
        rw [hRspec, hSspec]
      _ = W * (Matrix.diagonal (fun j => (diag false j : ℂ)) +
          Complex.I • Matrix.diagonal (fun j => (diag true j : ℂ))) *
          W.conjTranspose := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = W * Matrix.diagonal z * W.conjTranspose := by rw [hdiagadd]
  have hconj : W.conjTranspose * U * W = Matrix.diagonal z := by
    calc
      W.conjTranspose * U * W =
          (W.conjTranspose * W) * Matrix.diagonal z * (W.conjTranspose * W) := by
        rw [hspec]
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal z := by rw [hright, Matrix.one_mul, Matrix.mul_one]
  have hD : (Matrix.diagonal z).conjTranspose * Matrix.diagonal z = 1 := by
    calc
      (Matrix.diagonal z).conjTranspose * Matrix.diagonal z =
          (W.conjTranspose * U * W).conjTranspose * (W.conjTranspose * U * W) := by
        simp only [hconj]
      _ = W.conjTranspose * U.conjTranspose * (W * W.conjTranspose) * U * W := by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = W.conjTranspose * (U.conjTranspose * U) * W := by
        rw [hleft]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hUright, Matrix.mul_one, hright]
  have hz : ∀ j, ‖z j‖ = 1 := by
    intro j
    have hj : star (z j) * z j = (1 : ℂ) := by
      simpa only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply_eq, Pi.star_apply, Matrix.one_apply_eq] using
        congrArg (fun A : Operator d => A j j) hD
    have hnormSq : Complex.normSq (z j) = 1 := by
      apply Complex.ofReal_injective
      rw [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one]
      simpa only [Complex.star_def] using hj
    rw [Complex.norm_def, hnormSq, Real.sqrt_one]
  exact ⟨W, z, hleft, hright, hz, hspec⟩

theorem unitary_diagonalization_pow {d : ℕ} (U W : Operator d) (z : Fin d → ℂ)
    (hleft : W * W.conjTranspose = 1) (hright : W.conjTranspose * W = 1)
    (hspec : U = W * Matrix.diagonal z * W.conjTranspose) (t : ℕ) :
    U ^ t = W * Matrix.diagonal (fun j => z j ^ t) * W.conjTranspose := by
  induction t with
  | zero =>
    simpa only [pow_zero, Matrix.diagonal_one, Matrix.mul_one] using hleft.symm
  | succ t ih =>
    calc
      U ^ (t + 1) = U ^ t * U := pow_succ U t
      _ = (W * Matrix.diagonal (fun j => z j ^ t) * W.conjTranspose) *
          (W * Matrix.diagonal z * W.conjTranspose) := by rw [ih, hspec]
      _ = W * Matrix.diagonal (fun j => z j ^ t) * (W.conjTranspose * W) *
          Matrix.diagonal z * W.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = W * (Matrix.diagonal (fun j => z j ^ t) * Matrix.diagonal z) *
          W.conjTranspose := by
        rw [hright]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = W * Matrix.diagonal (fun j => z j ^ (t + 1)) * W.conjTranspose := by
        simp only [Matrix.diagonal_mul_diagonal, pow_succ]

theorem unitary_coordinate_moments {d : ℕ} (U : Operator d)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (a : Fin d) :
    ∃ (p : FinDist (Fin d)) (z : Fin d → ℂ),
      (∀ j, ‖z j‖ = 1) ∧
      ∀ t : ℕ, ∑ j, (p.prob j : ℂ) * z j ^ t = (U ^ t) a a := by
  obtain ⟨W, z, hleft, hright, hz, hspec⟩ :=
    exists_unitary_phase_diagonalization U hU
  have hrow : ∑ j, Complex.normSq (W a j) = 1 := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.ofReal_one]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq,
      Complex.star_def, mul_comm] using
      congrArg (fun A : Operator d => A a a) hleft
  let p : FinDist (Fin d) :=
    ⟨fun j => Complex.normSq (W a j), fun j => Complex.normSq_nonneg (W a j), hrow⟩
  refine ⟨p, z, hz, ?_⟩
  intro t
  rw [unitary_diagonalization_pow U W z hleft hright hspec t, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.star_def]
  change (∑ j, (Complex.normSq (W a j) : ℂ) * z j ^ t) =
    ∑ j, (W a j * z j ^ t) * (starRingEnd ℂ) (W a j)
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_eq_conj_mul_self]
  ring

end Qatlib.Concepts.MpsAdaptation.MpsTransfer
