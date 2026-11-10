/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormStat
import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeLowc
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix

theorem lcPlusExtract_unitary (phis : List ℝ) (θ : ℝ) :
    lcHad * lcWord phis θ * lcHad ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hHad : lcHad.conjTranspose = lcHad := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [lcHad, Matrix.conjTranspose_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, RCLike.star_def, Complex.conj_ofReal]
  have hH : lcHad ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hHad, lcHad_mul_self]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hH (equation1WordBridge phis θ).2.2.2) hH

theorem unitary_entry_normSq_le_one {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.conjTranspose * M = 1) (i j : n) :
    (M i j).re * (M i j).re + (M i j).im * (M i j).im ≤ 1 := by
  have hdiag := congrFun (congrFun hM j) j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def] at hdiag
  rw [Matrix.one_apply, if_pos rfl] at hdiag
  have hsumR : (∑ k, Complex.normSq (M k j)) = 1 := by
    have h1 : ((∑ k, Complex.normSq (M k j) : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← hdiag]
      exact Finset.sum_congr rfl fun k _ => Complex.normSq_eq_conj_mul_self
    exact_mod_cast h1
  have hsingle : Complex.normSq (M i j) ≤ ∑ k, Complex.normSq (M k j) :=
    Finset.single_le_sum
      (f := fun k => Complex.normSq (M k j))
      (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  calc (M i j).re * (M i j).re + (M i j).im * (M i j).im
      = Complex.normSq (M i j) := (Complex.normSq_apply _).symm
    _ ≤ 1 := hsingle.trans_eq hsumR

theorem achievableNecessitySourceForm : AchievableNecessitySourceForm := by
  intro phis θ
  refine ⟨?_, lcPlusAmp_zero_angle phis, ?_⟩
  · have hU := lcPlusExtract_unitary phis θ
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact unitary_entry_normSq_le_one _ hU 0 0
  · intro hne hθ1 hθ2
    obtain ⟨psis, γ₀, γ₁, hlen, _hγ, hpsis, hword⟩ :=
      (equation1WordBridge phis θ).1 hne hθ1 hθ2
    refine ⟨psis, γ₀, γ₁, hlen, hpsis, ?_⟩
    unfold lcPlusAmp lcRepoAmp
    rw [hword, (equation1WordBridge phis θ).2.1 hθ1 hθ2]
    simp only [Matrix.mul_assoc]

end Qatlib.Concepts.QspSimulation.Achievability
