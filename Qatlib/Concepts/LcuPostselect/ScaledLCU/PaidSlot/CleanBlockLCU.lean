/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidSlot.NativeWeightedLCUSlot
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
open Matrix
open scoped BigOperators Kronecker

variable {J H I : Type} [Fintype J] [DecidableEq J]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

omit [Fintype H] [DecidableEq H] in

private theorem label_frame_fiber (F : Matrix H I ℂ) (j₀ : J) :
    Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ F =
      ((1 : Matrix J J ℂ) ⊗ₖ F) * Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := I) j₀ := by
  classical
  ext ⟨j,h⟩ i
  rw [Matrix.mul_apply, Finset.sum_eq_single (j₀,i)]
  · simp [Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame,
      Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  · intro x _ hx
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber_apply, hx]
  · simp

private theorem label_prepare_intertwine (F : Matrix H I ℂ) (P : Matrix J J ℂ) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) P * ((1 : Matrix J J ℂ) ⊗ₖ F) =
      ((1 : Matrix J J ℂ) ⊗ₖ F) * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) P := by
  simp only [Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

omit [Fintype J] [Fintype I] in

private theorem diagonal_phase_select (d : J → ℂ) :
    Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) (Matrix.diagonal (fun j => Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase (d j))) =
      Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d (fun _ => (1 : Matrix I I ℂ))) := by
  ext ⟨j,i⟩ ⟨k,l⟩
  by_cases hj : j = k <;> by_cases hi : i = l <;>
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister, Matrix.kroneckerMap_apply,
      Qatlib.Concepts.BlockEncoding.LCU.select, Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed, Matrix.one_apply, hj, hi]

theorem clean_block_lcu_compress
    (F : Matrix H I ℂ) (W : Matrix (J × H) (J × H) ℂ)
    (Y : J → Matrix I I ℂ) (d : J → ℂ) (j₀ : J)
    (hmass : 0 < Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d)
    (hblock : Qatlib.Concepts.Execution.WorkspaceCP.compress ((1 : Matrix J J ℂ) ⊗ₖ F) W
      ((1 : Matrix J J ℂ) ⊗ₖ F) = Qatlib.Concepts.BlockEncoding.LCU.select Y) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ F)
      ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare d j₀))ᴴ *
        Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Matrix.diagonal (fun j => Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase (d j))) *
        W * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare d j₀))
      (Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame j₀ F) =
      ∑ j, (d j / (Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientMass d : ℂ)) • Y j := by
  let E : Matrix (J × H) (J × I) ℂ := (1 : Matrix J J ℂ) ⊗ₖ F
  let Q : Matrix J J ℂ := Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPrepare d j₀
  let D : Matrix J J ℂ :=
      Matrix.diagonal
      (fun j => Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientPhase (d j))
  have hQ : Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q * E = E * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q :=
    label_prepare_intertwine F Q
  have hQa : Eᴴ * (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q)ᴴ =
      (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q)ᴴ * Eᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hQ
  have hD' : Eᴴ * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) D =
      Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) D * Eᴴ := by
    have h := congrArg Matrix.conjTranspose (label_prepare_intertwine F Dᴴ)
    simpa only [E, Matrix.conjTranspose_mul, Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_one] using h
  have hsandwich :
      Eᴴ * ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q)ᴴ * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) D *
        W * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q) * E =
      (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q)ᴴ * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) D *
        (Eᴴ * W * E) * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q := by
    calc
      _ = (Eᴴ * (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q)ᴴ) *
          Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) D * W * (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q * E) := by
            simp only [Matrix.mul_assoc]
      _ = ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q)ᴴ * Eᴴ) *
          Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) D * W * (E * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q) := by rw [hQa, hQ]
      _ = (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q)ᴴ *
          (Eᴴ * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) D) * W * E * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q := by
            simp only [Matrix.mul_assoc]
      _ = (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q)ᴴ *
          (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) D * Eᴴ) * W * E * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q := by rw [hD']
      _ = _ := by simp only [Matrix.mul_assoc]
  have hselect : Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) D * Qatlib.Concepts.BlockEncoding.LCU.select Y =
      Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d Y) := by
    rw [diagonal_phase_select, Qatlib.Concepts.CopyEvolution.Discriminate.parallel_select_mul]
    apply congrArg Qatlib.Concepts.BlockEncoding.LCU.select
    funext j
    simp [Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed]
  change Eᴴ * W * E = Qatlib.Concepts.BlockEncoding.LCU.select Y at hblock
  calc
    _ = Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := I) j₀)
          (Eᴴ * ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q)ᴴ * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) D *
            W * Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := H) Q) * E)
          (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := I) j₀) := by
      rw [label_frame_fiber]
      simp only [Qatlib.Concepts.Execution.WorkspaceCP.compress, Matrix.conjTranspose_mul]
      simp only [E, Q, D, Matrix.mul_assoc]
    _ = Qatlib.Concepts.Execution.WorkspaceCP.compress (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := I) j₀)
          ((Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q)ᴴ * Qatlib.Concepts.BlockEncoding.LCU.select (Qatlib.Concepts.BlockEncoding.EncodingCore.phaseAbsorbed d Y) *
            Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) Q) (Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := I) j₀) := by
      rw [hsandwich, hblock]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (Qatlib.Concepts.BlockEncoding.EncodingCore.prepareRegister (I := I) D) (Qatlib.Concepts.BlockEncoding.LCU.select Y), hselect]
    _ = _ := by
      have hf : Qatlib.Concepts.BlockEncoding.LCU.prepareLift (I := I) (Qatlib.Foundations.PureStateMath.Ket j₀) =
          Qatlib.Concepts.BlockEncoding.EncodingCore.encodingFiber (I := I) j₀ := by
        have h := Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame_eq j₀ (1 : Matrix I I ℂ)
        simpa only [Qatlib.Concepts.LcuPostselect.ScaledLCU.tagFrame_one, Matrix.mul_one] using
            h.symm
      simpa only [Q, Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary, hf] using
          Qatlib.Concepts.BlockEncoding.EncodingCore.coefficientLCUUnitary_compress d Y j₀ hmass

end Qatlib.Concepts.LcuPostselect.ScaledLCU.PaidWeightedLCUSlot
