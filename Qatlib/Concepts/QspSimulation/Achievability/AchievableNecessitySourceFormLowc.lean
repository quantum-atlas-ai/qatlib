/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormStat
import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeLowc

/-!
# Necessity for source-form QSP amplitudes

This module proves the source-form necessity statement for the Low--Chuang QSP word. Conjugating
the word by `lcHad` gives a unitary matrix, so its extracted amplitude has squared modulus at
most one; the zero-angle amplitude is exactly one. The nonempty-word case also transfers the
amplitude to the repository phase convention through reversed half-differences, following the
QSP framework of [LowChuang2017].

## Main statements

- `lcPlusExtract_unitary` proves unitarity of the Hadamard-conjugated source word.
- `unitary_entry_normSq_le_one` bounds the squared modulus of every entry of a unitary matrix.
* `achievableNecessitySourceForm` establishes the amplitude bound, zero-angle normalization, and
  source-to-repository representation.

## References

* [Low and Chuang, 2017][LowChuang2017], *Optimal Hamiltonian Simulation by Quantum Signal
  Processing*.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix

/-- The source word `lcWord phis θ`, conjugated on both sides by `lcHad`, is unitary for every
phase list and real signal angle. -/
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

/-- If `M.conjTranspose * M = 1`, then the sum of the squares of the real and imaginary parts of
each entry `M i j` is at most one. -/
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

/-- Establishes `AchievableNecessitySourceForm`: the source amplitude has squared modulus at
most one and equals one at zero angle, and every nonempty phase list has the specified
repository-amplitude representation on the signal-angle interval. -/
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
