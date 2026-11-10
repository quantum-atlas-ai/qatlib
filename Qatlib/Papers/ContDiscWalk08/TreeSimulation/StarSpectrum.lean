/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum.WalkDefs
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.ContDiscWalk08.TreeSimulation

open Qatlib.Papers.ContDiscWalk08.MainResults.WalkSpectrum

theorem sum_option_eq (k : ℕ) (f : Option (Fin k) → ℂ) :
    (∑ o, f o) = f none + ∑ i : Fin k, f (some i) := by
  rw [univ_option, Finset.sum_insertNone]

def starMatrix (k : ℕ) (w : Fin k → ℂ) : Matrix (Option (Fin k)) (Option (Fin k)) ℂ :=
  fun p q =>
    match p, q with
    | none, none => 0
    | none, some i => (starRingEnd ℂ) (w i)
    | some i, none => w i
    | some i, some j => 0

theorem starMatrix_isHermitian (k : ℕ) (w : Fin k → ℂ) :
    (starMatrix k w).IsHermitian := by
  ext p q
  cases p <;> cases q <;> simp [starMatrix, Matrix.conjTranspose_apply]

def starCenter (k : ℕ) : QState (Option (Fin k)) := Ket none

def starLeafVec (k : ℕ) (w : Fin k → ℂ) : QState (Option (Fin k)) :=
  fun p => match p with
    | none => 0
    | some i => w i

theorem starMatrix_mulVec_none (k : ℕ) (w : Fin k → ℂ)
    (φ : QState (Option (Fin k))) :
    (starMatrix k w *ᵥ φ) none = ∑ i : Fin k, (starRingEnd ℂ) (w i) * φ (some i) := by
  rw [Matrix.mulVec, dotProduct, sum_option_eq]
  simp [starMatrix]

theorem starMatrix_mulVec_some (k : ℕ) (w : Fin k → ℂ)
    (φ : QState (Option (Fin k))) (j : Fin k) :
    (starMatrix k w *ᵥ φ) (some j) = w j * φ none := by
  rw [Matrix.mulVec, dotProduct, sum_option_eq]
  simp [starMatrix]

theorem starMatrix_mulVec_center (k : ℕ) (w : Fin k → ℂ) :
    starMatrix k w *ᵥ starCenter k
      = fun p => match p with
        | none => 0
        | some i => w i := by
  funext p
  cases p with
  | none =>
    rw [starMatrix_mulVec_none]
    simp [starCenter, Ket]
  | some j =>
    rw [starMatrix_mulVec_some]
    simp [starCenter, Ket]

theorem starMatrix_mulVec_leaf (k : ℕ) (w : Fin k → ℂ) :
    starMatrix k w *ᵥ starLeafVec k w
      = fun p => match p with
        | none => ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ)
        | some _ => 0 := by
  funext p
  cases p with
  | none =>
    rw [starMatrix_mulVec_none]
    have hterm : ∀ i : Fin k, (starRingEnd ℂ) (w i) * starLeafVec k w (some i)
        = ((‖w i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      simp only [starLeafVec]
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Complex.ofReal_sum]
  | some j =>
    rw [starMatrix_mulVec_some]
    simp [starLeafVec]

def starWeight (k : ℕ) (w : Fin k → ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin k, ‖w i‖ ^ 2)

theorem starWeight_sq (k : ℕ) (w : Fin k → ℂ) :
    starWeight k w ^ 2 = ∑ i : Fin k, ‖w i‖ ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

theorem starWeight_sq_complex (k : ℕ) (w : Fin k → ℂ) :
    ((starWeight k w : ℝ) : ℂ) * ((starWeight k w : ℝ) : ℂ)
      = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  have h := starWeight_sq k w
  have : ((starWeight k w : ℝ) : ℂ) * ((starWeight k w : ℝ) : ℂ)
      = (((starWeight k w) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, h]

theorem starWeight_pos (k : ℕ) (w : Fin k → ℂ) (i : Fin k) (hi : w i ≠ 0) :
    0 < starWeight k w := by
  unfold starWeight
  apply Real.sqrt_pos.mpr
  have hterm : 0 < ‖w i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  have hle : ‖w i‖ ^ 2 ≤ ∑ j : Fin k, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin k => ‖w j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

def invSqrtTwoC : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

def starEigenvector (k : ℕ) (w : Fin k → ℂ) (lam c : ℂ) :
    QState (Option (Fin k)) :=
  fun p => match p with
    | none => c
    | some i => c * lam⁻¹ * w i

theorem starMatrix_mulVec_eigenvector (k : ℕ) (w : Fin k → ℂ) (lam c : ℂ)
    (hlam_sq : lam * lam = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ)) (hlam0 : lam ≠ 0) :
    starMatrix k w *ᵥ starEigenvector k w lam c
      = lam • starEigenvector k w lam c := by
  funext p
  cases p with
  | none =>
    rw [starMatrix_mulVec_none]
    have hterm : ∀ i : Fin k,
        (starRingEnd ℂ) (w i) * starEigenvector k w lam c (some i)
          = (c * lam⁻¹) * ((starRingEnd ℂ) (w i) * w i) := by
      intro i
      simp only [starEigenvector]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
    have hsum : (∑ i : Fin k, (starRingEnd ℂ) (w i) * w i)
        = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [hsum, ← hlam_sq]
    simp only [starEigenvector, Pi.smul_apply, smul_eq_mul]
    rw [show (c * lam⁻¹) * (lam * lam) = lam * c from by
      rw [show (c * lam⁻¹) * (lam * lam) = c * (lam⁻¹ * (lam * lam)) from by ring]
      rw [show lam⁻¹ * (lam * lam) = (lam⁻¹ * lam) * lam from by ring,
        inv_mul_cancel₀ hlam0, one_mul]
      ring]
  | some j =>
    rw [starMatrix_mulVec_some]
    simp only [starEigenvector, Pi.smul_apply, smul_eq_mul]
    rw [show w j * c = lam * (c * lam⁻¹ * w j) from by
      rw [show lam * (c * lam⁻¹ * w j) = c * (lam * lam⁻¹) * w j from by ring,
        mul_inv_cancel₀ hlam0, mul_one]
      ring]

def eigPlus (k : ℕ) (w : Fin k → ℂ) : QState (Option (Fin k)) :=
  starEigenvector k w ((starWeight k w : ℝ) : ℂ) invSqrtTwoC

def eigMinus (k : ℕ) (w : Fin k → ℂ) : QState (Option (Fin k)) :=
  starEigenvector k w (-((starWeight k w : ℝ) : ℂ)) invSqrtTwoC

theorem starMatrix_mulVec_eigPlus (k : ℕ) (w : Fin k → ℂ)
    (hS : starWeight k w ≠ 0) :
    starMatrix k w *ᵥ eigPlus k w = ((starWeight k w : ℝ) : ℂ) • eigPlus k w :=
  starMatrix_mulVec_eigenvector k w ((starWeight k w : ℝ) : ℂ) invSqrtTwoC
    (starWeight_sq_complex k w) (by exact_mod_cast hS)

theorem starMatrix_mulVec_eigMinus (k : ℕ) (w : Fin k → ℂ)
    (hS : starWeight k w ≠ 0) :
    starMatrix k w *ᵥ eigMinus k w = (-((starWeight k w : ℝ) : ℂ)) • eigMinus k w := by
  have hcast : -((starWeight k w : ℝ) : ℂ) = ((-(starWeight k w) : ℝ) : ℂ) := by push_cast; ring
  have hsq : (-((starWeight k w : ℝ) : ℂ)) * (-((starWeight k w : ℝ) : ℂ))
      = ((∑ i : Fin k, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hcast, ← starWeight_sq_complex k w]
    push_cast
    ring
  have hne : -((starWeight k w : ℝ) : ℂ) ≠ 0 := by
    exact neg_ne_zero.mpr (by exact_mod_cast hS)
  exact starMatrix_mulVec_eigenvector k w (-((starWeight k w : ℝ) : ℂ)) invSqrtTwoC hsq hne

theorem eigPlus_eigenvalue (k : ℕ) (w : Fin k → ℂ) :
    ((starWeight k w : ℝ) : ℂ) = (starWeight k w : ℂ) := rfl

end Qatlib.Papers.ContDiscWalk08.TreeSimulation
