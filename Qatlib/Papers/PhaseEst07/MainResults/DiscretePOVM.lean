/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.DiscretePOVM

open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

theorem phaseState_eq_fourier (q : ℕ) (s k : Fin q) :
    PhaseState q s k
      = (Real.sqrt (q : ℝ) : ℂ)⁻¹ * primRoot q ^ ((s.val : ℤ) * (k.val : ℤ)) := rfl

theorem phaseState_eq_qft (q : ℕ) (s k : Fin q) :
    PhaseState q s k = QFTMatrix q s k := rfl

theorem source_discrete_fourier_orthogonality (q : ℕ) (hq : 0 < q) (n : ℤ) :
    (1 / (q : ℂ)) * (∑ s : Fin q, primRoot q ^ (n * (s : ℤ)))
      = if (q : ℤ) ∣ n then 1 else 0 := by
  by_cases h : (q : ℤ) ∣ n
  · rw [sum_primRoot_zpow_of_dvd hq h, if_pos h]
    rw [one_div, inv_mul_cancel₀]
    exact_mod_cast hq.ne'
  · rw [sum_primRoot_zpow hq h, if_neg h, mul_zero]

theorem qftMatrix_symm (q : ℕ) (a b : Fin q) : QFTMatrix q a b = QFTMatrix q b a := by
  rw [qftMatrix_apply, qftMatrix_apply]
  congr 2
  ring

theorem source_phase_state_orthonormal (q : ℕ) (hq : 0 < q) (s t : Fin q) :
    Inner (PhaseState q s) (PhaseState q t) = if s = t then 1 else 0 := by
  have hU : (QFTMatrix q)ᴴ * QFTMatrix q = 1 := by
    have := qftMatrix_unitary hq
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at this
    exact this
  have hentry : Inner (PhaseState q s) (PhaseState q t)
      = ((QFTMatrix q)ᴴ * QFTMatrix q) s t := by
    rw [inner_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, phaseState_eq_qft]
    rw [qftMatrix_symm q k s, qftMatrix_symm q t k]
  rw [hentry, hU, Matrix.one_apply]

theorem source_discrete_povm_complete (q : ℕ) (hq : 0 < q) :
    (∑ s : Fin q,
        Matrix.of (fun k l : Fin q => PhaseState q s k * starRingEnd ℂ (PhaseState q s l)))
      = 1 := by
  have hU : QFTMatrix q * (QFTMatrix q)ᴴ = 1 := by
    have := qftMatrix_unitary hq
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at this
    exact this
  have hentry : ∀ k l : Fin q,
      (∑ s : Fin q, Matrix.of (fun k l : Fin q =>
          PhaseState q s k * starRingEnd ℂ (PhaseState q s l)) k l)
        = (QFTMatrix q * (QFTMatrix q)ᴴ) k l := by
    intro k l
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro s _
    simp only [Matrix.of_apply, phaseState_eq_qft, Matrix.conjTranspose_apply]
    rw [qftMatrix_symm q s k, qftMatrix_symm q s l]
    rfl
  ext k l
  rw [Matrix.sum_apply, hentry k l, hU, Matrix.one_apply]

theorem source_qft_prepares_phase_state (q : ℕ) (s : Fin q) :
    ApplyGate (QFTMatrix q) (Ket s) = PhaseState q s := by
  funext k
  rw [ApplyGate, Matrix.mulVec, dotProduct]
  simp only [phaseState_eq_qft, Ket]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl, mul_one]
    exact qftMatrix_symm q k s
  · intro b _ hb
    simp [hb]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

end Qatlib.Papers.PhaseEst07.MainResults.DiscretePOVM
