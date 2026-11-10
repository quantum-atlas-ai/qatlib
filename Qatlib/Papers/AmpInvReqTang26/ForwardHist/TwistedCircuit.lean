/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualNorm
import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualDensity
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel

theorem unitPhase_query_unitary {d a : ℕ} (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1) :
    (queryMat (a := a) id D)ᴴ*queryMat id D=1 := by
  ext i j
  simp only [queryMat,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,Pi.star_apply]
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    change star (D i.1)*D i.1=1
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hD]
    norm_num
  · simp [hij]

def twistedAlgorithm {d a : ℕ} (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1)
    (Alg : ForwardQueryAlgorithm d a) : ForwardQueryAlgorithm d a where
  init := Alg.init
  hinit := Alg.hinit
  good := Alg.good
  step := fun t => if t=0 then Alg.step 0 else Alg.step t*queryMat id D
  hstep := by
    intro t
    split_ifs
    · exact Alg.hstep 0
    · calc
        _ = (queryMat id D)ᴴ*((Alg.step t)ᴴ*Alg.step t)*queryMat id D := by
          simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
        _ = 1 := by rw [Alg.hstep t,Matrix.mul_one,unitPhase_query_unitary D hD]

theorem twistedAlgorithm_run {d a : ℕ} {S : Type} (phi : S → ℂ)
    (D : Fin d → ℂ) (hD : ∀i,‖D i‖=1) (Alg : ForwardQueryAlgorithm d a)
    (n : ℕ) (U : Fin d → S) :
    run phi (twistedAlgorithm D hD Alg) n U=run id Alg n (fun i => D i*phi (U i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hQ : queryMat (a := a) id D * queryMat phi U = queryMat id (fun i => D i*phi (U i)) := by
      simp only [queryMat,Matrix.diagonal_mul_diagonal]
      rfl
    change (Alg.step (n+1)*queryMat id D) *ᵥ
        (queryMat phi U *ᵥ run phi (twistedAlgorithm D hD Alg) n U) =
      Alg.step (n+1) *ᵥ (queryMat id (fun i => D i*phi (U i)) *ᵥ
        run id Alg n (fun i => D i*phi (U i)))
    rw [← Matrix.mulVec_mulVec,ih]
    rw [Matrix.mulVec_mulVec (run id Alg n (fun i => D i*phi (U i))) (queryMat id D) (queryMat phi U),hQ]

theorem run_assignment {d a : ℕ} {S : Type} (phi : S → ℂ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (U : Fin d → S) :
    run phi Alg n U=run id Alg n (fun i => phi (U i)) := by
  funext x
  have h := queryPolynomial_eval phi Alg n U x
  have hi := queryPolynomial_eval id Alg n (fun i => phi (U i)) x
  change (MvPolynomial.eval (fun i => phi (U i))) (queryPolynomial Alg n x)=_ at hi
  exact h.symm.trans hi

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
