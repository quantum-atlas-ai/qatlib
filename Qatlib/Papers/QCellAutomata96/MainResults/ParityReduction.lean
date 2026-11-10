/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.PairWeights
import Qatlib.Concepts.QcaDynamics.ParityWeights
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section

open Complex

open Qatlib.Concepts.QcaDynamics.PairWeights
open Qatlib.Concepts.QcaDynamics.ParityWeights

namespace Qatlib.Papers.QCellAutomata96.MainResults

theorem unitary_sym_two (a b : ℂ)
    (h1 : a * star a + b * star b = 1)
    (h2 : a * star b + b * star a = 0) :
    (!![a, b; b, a] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h1' : b * star b + a * star a = 1 := by rw [add_comm]; exact h1
  have h2' : b * star a + a * star b = 0 := by rw [add_comm]; exact h2
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
  all_goals assumption

lemma P2_eq_of : P2 = Matrix.of (fun i j : Fin 2 => if i = j then 0 else 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P2]

theorem parity_iff_equal_entries (S : Matrix (Fin 2) (Fin 2) ℂ) :
    P2 * S * P2 = S ↔ S 0 0 = S 1 1 ∧ S 0 1 = S 1 0 := by
  constructor
  · intro h
    have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    rw [P2_eq_of] at h00 h01
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
    exact ⟨h00.symm, h01.symm⟩
  · rintro ⟨h00, h01⟩
    rw [P2_eq_of]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h00, h01]

theorem P2_mem_unitary : P2 ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h1 : (0 : ℂ) * star 0 + (1 : ℂ) * star 1 = 1 := by simp
  have h2 : (0 : ℂ) * star 1 + (1 : ℂ) * star 0 = 0 := by simp
  simpa [P2] using unitary_sym_two (0 : ℂ) 1 h1 h2

def cellPairMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I * (Real.sin θ : ℂ), (Real.cos θ : ℂ);
     (Real.cos θ : ℂ), I * (Real.sin θ : ℂ)]

theorem cellPairMatrix_mem_unitary (θ : ℝ) :
    cellPairMatrix θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  apply unitary_sym_two
  · set s : ℂ := (Real.sin θ : ℂ)
    set c : ℂ := (Real.cos θ : ℂ)
    have hs : star s = s := by
      simp only [s]
      rw [Complex.star_def]; exact Complex.conj_ofReal _
    have hc : star c = c := by
      simp only [c]
      rw [Complex.star_def]; exact Complex.conj_ofReal _
    have hII : (I : ℂ) * I = -1 := Complex.I_mul_I
    have hsa : star (I * s) = -(I * s) := by
      rw [star_mul]
      have hI : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
      rw [hI, hs]
      ring
    rw [hsa, hc]
    have hsc : s ^ 2 + c ^ 2 = 1 := by
      simp only [s, c, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq, Complex.ofReal_one]
    calc (I * s) * (-(I * s)) + c * c
        = -((I * I) * (s * s)) + c * c := by ring
      _ = -((-1) * (s * s)) + c * c := by rw [hII]
      _ = 1 := by
        have : -((-1 : ℂ) * (s * s)) + c * c = s ^ 2 + c ^ 2 := by ring
        rw [this, hsc]
  · set s : ℂ := (Real.sin θ : ℂ)
    set c : ℂ := (Real.cos θ : ℂ)
    have hs : star s = s := by
      simp only [s]
      rw [Complex.star_def]; exact Complex.conj_ofReal _
    have hc : star c = c := by
      simp only [c]
      rw [Complex.star_def]; exact Complex.conj_ofReal _
    have hsa : star (I * s) = -(I * s) := by
      rw [star_mul]
      have hI : star (I : ℂ) = -I := by rw [Complex.star_def, Complex.conj_I]
      rw [hI, hs]
      ring
    rw [hsa, hc]
    ring

theorem cellPairMatrix_parity (θ : ℝ) :
    P2 * cellPairMatrix θ * P2 = cellPairMatrix θ := by
  rw [parity_iff_equal_entries]
  constructor <;> simp [cellPairMatrix]

theorem cellPairMatrix_zero_theta : cellPairMatrix 0 = P2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cellPairMatrix, P2]

def staggeredPair (U T : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  U * (T * U * star T)

theorem staggeredPair_mem_unitary (U T : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hT : T ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    staggeredPair U T ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h : staggeredPair U T =
      ((⟨U, hU⟩ * ⟨T, hT⟩ * ⟨U, hU⟩ * (⟨T, hT⟩)⁻¹ : Matrix.unitaryGroup (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) := by
    simp [staggeredPair, mul_assoc]
  rw [h]
  exact Subtype.mem _

theorem cellPair_staggered_mem_unitary (θ : ℝ) :
    staggeredPair (cellPairMatrix θ) P2 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  staggeredPair_mem_unitary _ _ (cellPairMatrix_mem_unitary θ) P2_mem_unitary

end Qatlib.Papers.QCellAutomata96.MainResults
