/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualPolynomial
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
set_option warningAsError false

theorem unitary_normSq {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (hM : Mᴴ*M=1) (v : I → ℂ) :
    ∑ i, ‖(M *ᵥ v) i‖^2 = ∑ i, ‖v i‖^2 := by
  have hs : star (M *ᵥ v) ⬝ᵥ (M *ᵥ v) = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      hM, Matrix.vecMul_one]
  have hcast (z : ℂ) : star z*z=((‖z‖^2:ℝ):ℂ) := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  apply Complex.ofReal_injective
  simpa only [dotProduct, Pi.star_apply, hcast, ← Complex.ofReal_sum] using! hs

theorem actual_run_normSq {d a : ℕ} {S : Type} (phi : S → ℂ)
    (hphi : ∀s,‖phi s‖=1) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (U : Fin d → S) : ∑x, ‖run phi Alg n U x‖^2=1 := by
  induction n with
  | zero => exact (unitary_normSq _ (Alg.hstep 0) Alg.init).trans Alg.hinit
  | succ n ih =>
    have hQ : (queryMat (a := a) phi U)ᴴ * queryMat phi U = 1 := by
      ext i j
      simp only [queryMat, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
      have hp (z : S) : (starRingEnd ℂ) (phi z)*phi z = 1 := by
        change star (phi z)*phi z=1
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
          Complex.normSq_eq_norm_sq, hphi z]; norm_num
      simp only [Pi.star_apply]
      by_cases hij : i=j
      · subst j
        simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
        exact hp (U i.1)
      · simp [hij]
    change ∑ x, ‖(Alg.step (n+1) *ᵥ (queryMat phi U *ᵥ run phi Alg n U)) x‖^2=1
    rw [unitary_normSq _ (Alg.hstep (n+1)), unitary_normSq _ hQ]
    exact ih

theorem actual_outProb_total {d a : ℕ} {S : Type} (phi : S → ℂ)
    (hphi : ∀s,‖phi s‖=1) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (U : Fin d → S) : outProb phi Alg n U false + outProb phi Alg n U true = 1 := by
  rw [outProb, outProb, ← Finset.sum_add_distrib, ← actual_run_normSq phi hphi Alg n U]
  apply Finset.sum_congr rfl
  intro x _
  cases Alg.good x <;> simp

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
