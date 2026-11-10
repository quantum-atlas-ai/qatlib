/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormLowc
import Qatlib.Foundations.PureStateMath.Qubit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Qatlib  Polynomial Matrix

noncomputable def sourceSuccessProb (phis : List ℝ) (theta : ℝ) : ℝ :=
  BornProb (ApplyGate (lcHad * lcWord phis theta * lcHad) (Ket (0 : Fin 2))) 0

theorem sourceSuccessProb_eq (phis : List ℝ) (theta : ℝ) :
    sourceSuccessProb phis theta = ‖lcPlusAmp phis theta‖ ^ 2 := by
  unfold sourceSuccessProb BornProb
  rw [applyGate_eq_mulVec_ket]
  rfl

theorem sourceSuccessProb_le_one (phis : List ℝ) (theta : ℝ) :
    sourceSuccessProb phis theta ≤ 1 := by
  rw [sourceSuccessProb_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  exact (achievableNecessitySourceForm phis theta).1

theorem sourceSuccessProb_zero (phis : List ℝ) : sourceSuccessProb phis 0 = 1 := by
  rw [sourceSuccessProb_eq, lcPlusAmp_zero_angle]
  norm_num

theorem frontier1 (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (eps : ℝ)
    (hN : Even N) (hp : 0 < N) (hodd : ∀ theta, h (-theta) = -h theta)
    (hAeven : A.comp (-X) = A) (hQtodd : Qt.comp (-X) = -Qt)
    (hAdeg : A.degree ≤ (N : WithBot ℕ)) (hQtdeg : Qt.degree < (N : WithBot ℕ))
    (heps : 0 < eps) (heps16 : eps ≤ 1 / 16)
    (happrox : ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
      ‖realEval A (Real.cos (theta / 2) : ℂ) + Complex.I * (Real.sin (theta / 2) : ℂ) *
        realEval Qt (Real.cos (theta / 2) : ℂ) - Complex.exp (Complex.I * (h theta : ℂ))‖ ≤ eps) :
    ∃ phis : List ℝ, phis.length = N ∧
      (∀ theta, lcHad * lcWord phis theta * lcHad ∈ Matrix.unitaryGroup (Fin 2) ℂ) ∧
      sourceSuccessProb phis 0 = 1 ∧
      ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
        ‖lcPlusAmp phis theta - Complex.exp (Complex.I * (h theta : ℂ))‖ ≤ 8 * eps ∧
        (1 - 8 * eps)^2 ≤ sourceSuccessProb phis theta ∧ sourceSuccessProb phis theta ≤ 1 := by
  obtain ⟨phis, hlen, hamp⟩ := lcSourceCompilation N h A Qt eps hN hp hodd hAeven hQtodd
    hAdeg hQtdeg heps heps16 happrox
  refine ⟨phis, hlen, lcPlusExtract_unitary phis, sourceSuccessProb_zero phis, ?_⟩
  intro theta htheta
  refine ⟨hamp theta htheta, ?_, sourceSuccessProb_le_one phis theta⟩
  have hn : ‖Complex.exp (Complex.I * (h theta : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have ht := norm_sub_norm_le (Complex.exp (Complex.I * (h theta : ℂ))) (lcPlusAmp phis theta)
  rw [hn, norm_sub_rev] at ht
  have hl : 1 - 8 * eps ≤ ‖lcPlusAmp phis theta‖ := by linarith [hamp theta htheta]
  rw [sourceSuccessProb_eq]
  have hnon : 0 ≤ 1 - 8 * eps := by linarith
  nlinarith [norm_nonneg (lcPlusAmp phis theta)]

end Qatlib.Concepts.QspSimulation.Achievability
