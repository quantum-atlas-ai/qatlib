/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.ProposalUnitary
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.MbqcFlow.FlowDecision.StageAQUANTUMGIBBS

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup
namespace StageAQUANTUMGIBBS

open Matrix Qatlib
open scoped Classical BigOperators ComplexOrder

theorem registerProjector_hermitian (G : PhaseGrid) (j : Fin G.levels) :
    (registerProjector G j)ᴴ = registerProjector G j := by
  ext i k
  simp only [registerProjector, Matrix.diagonal_apply, Matrix.conjTranspose_apply]
  by_cases h : i = k
  · subst h
    rw [if_pos rfl]
    split_ifs <;> simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem registerProjector_sq (G : PhaseGrid) (j : Fin G.levels) :
    registerProjector G j * registerProjector G j = registerProjector G j := by
  ext i k
  simp only [registerProjector, Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases h : i = k
  · subst h
    by_cases h1 : i = j <;> simp [h1]
  · simp only [if_neg h, zero_mul]

private theorem sum_ite_eq_one (M : ℕ) (i : Fin M) :
    (∑ j : Fin M, if i = j then (1 : ℂ) else 0) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg (fun h : i = b => hb h.symm)]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

theorem registerProjector_sum (G : PhaseGrid) :
    (∑ j : Fin G.levels, registerProjector G j) = 1 := by
  ext i k
  simp only [registerProjector, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.one_apply]
  by_cases h : i = k
  · subst h
    simp only [if_true]
    rw [sum_ite_eq_one]
  · simp only [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    simp

theorem registerProjector_tensor_sum (G : PhaseGrid) (D : ℕ) :
    (∑ j : Fin G.levels, TensorGate (registerProjector G j) (1 : Operator D))
      = 1 := by
  ext p q
  obtain ⟨i, a⟩ := p
  obtain ⟨k, b⟩ := q
  simp only [Matrix.sum_apply, Matrix.one_apply, tensorGate_apply, registerProjector,
    Matrix.diagonal_apply]
  by_cases hp : (i, a) = (k, b)
  · have hik : i = k := (Prod.mk.inj hp).1
    have hab : a = b := (Prod.mk.inj hp).2
    simp only [if_pos hik, if_pos hab, if_pos hp, mul_one]
    rw [sum_ite_eq_one]
  · have hzero : (1 : Matrix (QpeSpace G D) (QpeSpace G D) ℂ) (i, a) (k, b) = 0 := by
      simp only [Matrix.one_apply, if_neg hp, Matrix.zero_apply]
    simp only [if_neg hp]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hik : i = k
    · have hab : a ≠ b := by
        intro h
        exact hp (Prod.ext hik h)
      simp only [if_pos hik, if_neg hab, mul_zero]
    · simp only [if_neg hik, zero_mul]

theorem qftTensorGate_unitary (G : PhaseGrid) (D : ℕ) :
    TensorGate (QFTMatrix G.levels)ᴴ (1 : Operator D)
      ∈ Matrix.unitaryGroup (QpeSpace G D) ℂ := by
  have hU : (QFTMatrix G.levels)ᴴ ∈ Matrix.unitaryGroup (Fin G.levels) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have h := (Matrix.mem_unitaryGroup_iff).1 (qftMatrix_unitary G.levelsPos)
    rw [Matrix.star_eq_conjTranspose] at h
    rw [Matrix.conjTranspose_conjTranspose]
    exact h
  have h1 : (1 : Operator D) ∈ Matrix.unitaryGroup (Fin D) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    simp [Matrix.conjTranspose_one, Matrix.one_mul]
  exact tensorGate_unitary hU h1

theorem qpeCircuit_unitary {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    qpeCircuit O G ∈ Matrix.unitaryGroup (QpeSpace G D) ℂ := by
  rw [qpeCircuit]
  exact Submonoid.mul_mem (Matrix.unitaryGroup (QpeSpace G D) ℂ)
    (qftTensorGate_unitary G D)
    (controlledPowers_unitary (M := G.levels) O.evolution O.evolutionUnitary)

theorem qpeKraus_complete {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    (∑ j : Fin G.levels, (qpeKraus O G j)ᴴ * (qpeKraus O G j)) = 1 := by
  have hV : (qpeCircuit O G)ᴴ * (qpeCircuit O G) = 1 := by
    have h := (Matrix.mem_unitaryGroup_iff').1 (qpeCircuit_unitary O G)
    rw [Matrix.star_eq_conjTranspose] at h
    exact h
  have hP : ∀ j : Fin G.levels,
      (TensorGate (registerProjector G j) (1 : Operator D))ᴴ
        * (TensorGate (registerProjector G j) (1 : Operator D))
      = TensorGate (registerProjector G j) (1 : Operator D) := by
    intro j
    rw [tensorGate_conjTranspose, tensorGate_mul]
    simp only [registerProjector_hermitian, registerProjector_sq, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hdist : (∑ j : Fin G.levels, (qpeCircuit O G)ᴴ
        * (TensorGate (registerProjector G j) (1 : Operator D)) * (qpeCircuit O G))
      = (qpeCircuit O G)ᴴ
        * ((∑ j : Fin G.levels, TensorGate (registerProjector G j) (1 : Operator D))
            * (qpeCircuit O G)) := by
    calc (∑ j : Fin G.levels, (qpeCircuit O G)ᴴ
        * (TensorGate (registerProjector G j) (1 : Operator D)) * (qpeCircuit O G))
        = ∑ j : Fin G.levels, (qpeCircuit O G)ᴴ
            * ((TensorGate (registerProjector G j) (1 : Operator D)) * (qpeCircuit O G)) := by
          rw [Finset.sum_congr rfl (fun j _ => by rw [Matrix.mul_assoc])]
    _ = (qpeCircuit O G)ᴴ
            * (∑ j : Fin G.levels, (TensorGate (registerProjector G j) (1 : Operator D))
                * (qpeCircuit O G)) := by rw [Finset.mul_sum]
    _ = (qpeCircuit O G)ᴴ
            * ((∑ j : Fin G.levels, TensorGate (registerProjector G j) (1 : Operator D))
                * (qpeCircuit O G)) := by
          rw [← Finset.sum_mul]
  have hstep : ∀ j : Fin G.levels,
      (qpeKraus O G j)ᴴ * (qpeKraus O G j)
      = (qpeCircuit O G)ᴴ * (TensorGate (registerProjector G j) (1 : Operator D))
          * (qpeCircuit O G) := by
    intro j
    rw [qpeKraus, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    have h1 : (TensorGate (registerProjector G j) (1 : Operator D))ᴴ
          * ((TensorGate (registerProjector G j) (1 : Operator D)) * (qpeCircuit O G))
        = (TensorGate (registerProjector G j) (1 : Operator D)) * (qpeCircuit O G) := by
      rw [← Matrix.mul_assoc, hP]
    rw [h1]
  calc (∑ j : Fin G.levels, (qpeKraus O G j)ᴴ * (qpeKraus O G j))
      = ∑ j : Fin G.levels, (qpeCircuit O G)ᴴ
          * (TensorGate (registerProjector G j) (1 : Operator D)) * (qpeCircuit O G) := by
        rw [Finset.sum_congr rfl (fun j _ => hstep j)]
    _ = (qpeCircuit O G)ᴴ
        * ((∑ j : Fin G.levels, TensorGate (registerProjector G j) (1 : Operator D))
            * (qpeCircuit O G)) := hdist
    _ = (qpeCircuit O G)ᴴ * (qpeCircuit O G) := by
        rw [registerProjector_tensor_sum, Matrix.one_mul]
    _ = 1 := hV

noncomputable def energyEigenbasis {D : ℕ} (O : EnergyOracle D) : Operator D :=
  O.hamHermitian.eigenvectorUnitary.1

theorem energyEigenbasis_unitary {D : ℕ} (O : EnergyOracle D) :
    energyEigenbasis O ∈ Matrix.unitaryGroup (Fin D) ℂ :=
  O.hamHermitian.eigenvectorUnitary.2

noncomputable def energyBinProjector {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (j : Fin G.levels) : Operator D :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.energyProjector (energyLabelMap O G) (energyEigenbasis O) j

noncomputable def energyInstrument {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    Instrument (Fin G.levels) D D :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.energyInstrument (energyLabelMap O G) (energyEigenbasis O)
    (energyEigenbasis_unitary O)

theorem energyInstrument_branch {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (j : Fin G.levels) (X : Operator D) :
    (energyInstrument O G).branch j X
      = energyBinProjector O G j * X * energyBinProjector O G j := by
  have h := Qatlib.Concepts.MbqcFlow.FlowDecision.energy_actual_instrument_projector_map D G.levels
    (energyLabelMap O G) (energyEigenbasis O) (energyEigenbasis_unitary O) j X
  rw [energyInstrument, energyBinProjector]
  exact h.1

theorem energyInstrument_labelMass {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (X : Operator D) :
    (∑ j : Fin G.levels, instrumentProb (energyInstrument O G) X j)
      = (Matrix.trace X).re :=
  sum_instrumentProb (energyInstrument O G) X

theorem energyInstrument_referenceMarginal {D R : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    partialTraceFirst (∑ j : Fin G.levels,
        tensorLeft ((energyInstrument O G).branch j) ρ)
      = partialTraceFirst ρ :=
  Instrument.referenceMarginal (energyInstrument O G) ρ

theorem energyInstrument_tensorLeft_tni {D R : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : ρ.PosSemidef) (j : Fin G.levels) :
    (Matrix.trace (tensorLeft ((energyInstrument O G).branch j) ρ)).re
      ≤ (Matrix.trace ρ).re :=
  Instrument.tensorLeft_tni (energyInstrument O G) hρ j

theorem energyBinProjector_resolution {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    (∀ j : Fin G.levels, (energyBinProjector O G j)ᴴ = energyBinProjector O G j ∧
        energyBinProjector O G j * energyBinProjector O G j = energyBinProjector O G j) ∧
      (∀ j k : Fin G.levels, j ≠ k →
        energyBinProjector O G j * energyBinProjector O G k = 0) ∧
      (∑ j : Fin G.levels, energyBinProjector O G j) = 1 := by
  have h := Qatlib.Concepts.MbqcFlow.FlowDecision.energy_projector_actual_orthogonal_resolution D G.levels
    (energyLabelMap O G) (energyEigenbasis O) (energyEigenbasis_unitary O)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact ⟨by simp only [energyBinProjector]; exact (h.2.1 j).1, by
      simp only [energyBinProjector]; exact (h.2.1 j).2⟩
  · intro j k hjk
    simp only [energyBinProjector]
    exact h.2.2.1 j k hjk
  · simp only [energyBinProjector]
    exact h.2.2.2

theorem controlledPowers_kickback_general {D M : ℕ} {U : Matrix (Fin D) (Fin D) ℂ}
    {ψ : QState (Fin D)} {lam : ℂ} (hψ : U *ᵥ ψ = lam • ψ) :
    ControlledPowers U M *ᵥ TensorState (fun _ : Fin M => (Real.sqrt (M : ℝ) : ℂ)⁻¹) ψ
      = TensorState (fun x => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * lam ^ (x.val : ℕ)) ψ := by
  funext p
  obtain ⟨x, i⟩ := p
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, ControlledPowers,
    Matrix.of_apply, TensorState]
  rw [Finset.sum_eq_single x]
  · have hsum : (∑ j : Fin D, (U ^ (x.val : ℕ)) i j * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * ψ j))
        = ((Real.sqrt (M : ℝ) : ℂ)⁻¹) * ((U ^ (x.val : ℕ)) *ᵥ ψ) i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [if_true]
    rw [hsum, mulVec_pow_of_eigen hψ, Pi.smul_apply]
    ring
  · intro m _ hm
    simp [show x ≠ m from fun e => hm e.symm]
  · intro hcon
    exact absurd (Finset.mem_univ x) hcon

noncomputable def qpeReadoutAmplitude (G : PhaseGrid) (lam : ℂ) (j : Fin G.levels) : ℂ :=
  (G.levels : ℂ)⁻¹ * ∑ x : Fin G.levels,
    (lam * (primRoot G.levels) ^ (-((j.val : ℤ)))) ^ (x.val : ℕ)

theorem qft_readout_amplitude (M : ℕ) (hM : 0 < M) (lam : ℂ) (j : Fin M) :
    ((QFTMatrix M)ᴴ *ᵥ (fun x => (Real.sqrt (M : ℝ) : ℂ)⁻¹ * lam ^ (x.val : ℕ))) j
      = qpeReadoutAmplitude { levels := M, levelsPos := hM } lam j := by
  have hconj : ∀ x : Fin M,
      (QFTMatrix M)ᴴ j x
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((x.val : ℤ) * (j.val : ℤ))) := by
    intro x
    rw [Matrix.conjTranspose_apply, qftMatrix_apply, RCLike.star_def, map_mul, map_inv₀,
      Complex.conj_ofReal, primRoot_conj_zpow]
  have hsq : ((Real.sqrt (M : ℝ) : ℂ)⁻¹) * ((Real.sqrt (M : ℝ) : ℂ)⁻¹) = (M : ℂ)⁻¹ :=
    inv_sqrt_mul_inv_sqrt hM
  have hcomm : ∀ x : Fin M,
      (primRoot M ^ (-((j.val : ℤ))) * lam) ^ (x.val : ℕ)
        = (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) := by
    intro x
    rw [mul_pow, mul_pow, mul_comm]
  have hterm : ∀ x : Fin M,
      ((QFTMatrix M)ᴴ j x
        * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * lam ^ (x.val : ℕ)))
        = ((M : ℂ)⁻¹) * (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) := by
    intro x
    rw [hconj]
    have harg : -((x.val : ℤ) * (j.val : ℤ)) = (-((j.val : ℤ))) * ((x.val : ℕ) : ℤ) := by
      push_cast
      ring
    have hzp : primRoot M ^ (-((x.val : ℤ) * (j.val : ℤ)))
        = (primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) := by
      rw [harg, _root_.zpow_mul, zpow_natCast]
    calc (Real.sqrt (M : ℝ) : ℂ)⁻¹ * primRoot M ^ (-((x.val : ℤ) * (j.val : ℤ)))
          * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * lam ^ (x.val : ℕ))
        = (Real.sqrt (M : ℝ) : ℂ)⁻¹ * (primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ)
            * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * lam ^ (x.val : ℕ)) := by rw [hzp]
      _ = ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹)
            * ((primRoot M ^ (-((j.val : ℤ))) * lam) ^ (x.val : ℕ)) := by
            calc (Real.sqrt (M : ℝ) : ℂ)⁻¹ * (primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ)
                  * ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * lam ^ (x.val : ℕ))
                = ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹)
                    * ((primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) * lam ^ (x.val : ℕ)) := by
                    ring
              _ = ((Real.sqrt (M : ℝ) : ℂ)⁻¹ * (Real.sqrt (M : ℝ) : ℂ)⁻¹)
                    * ((primRoot M ^ (-((j.val : ℤ))) * lam) ^ (x.val : ℕ)) := by
                    rw [mul_pow]
      _ = ((M : ℂ)⁻¹) * (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) := by
            rw [hsq, hcomm]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  simp only [qpeReadoutAmplitude]
  rw [Finset.mul_sum]

theorem qpe_phase_error_bound (M : ℕ) (hM : 0 < M) (lam : ℂ) (j : Fin M) (hlam : ‖lam‖ = 1) :
    ‖qpeReadoutAmplitude { levels := M, levelsPos := hM } lam j‖
      ≥ 1 - (M : ℝ)⁻¹ * ((M * (M - 1) : ℝ) / 2)
        * ‖lam - primRoot M ^ ((j.val : ℤ))‖ := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hw_norm : ‖lam * primRoot M ^ (-((j.val : ℤ)))‖ = 1 := by
    rw [norm_mul, hlam, norm_primRoot_zpow]
    simp
  have hbound : ∀ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖
      ≤ (x.val : ℝ) * ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ := by
    intro x
    by_cases hw1 : lam * primRoot M ^ (-((j.val : ℤ))) = 1
    · have hx : (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) = 1 := by
        rw [hw1]
        simp
      rw [hx]
      simp only [norm_zero, sub_self, zero_mul]
      positivity
    · have hgeom : ∑ i ∈ Finset.range x.val, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ i
          = ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)
            / (lam * primRoot M ^ (-((j.val : ℤ))) - 1) := geom_sum_eq hw1 x.val
      have htri : ‖∑ i ∈ Finset.range x.val, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ i‖
          ≤ (x.val : ℝ) := by
        calc ‖∑ i ∈ Finset.range x.val, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ i‖
            ≤ ∑ i ∈ Finset.range x.val, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ i‖ :=
              norm_sum_le _ _
          _ = ∑ i ∈ Finset.range x.val, (1 : ℝ) := by
              rw [Finset.sum_congr rfl (fun i _ => by rw [norm_pow, hw_norm])]
              simp
          _ = (x.val : ℝ) := by simp
      have heq : (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1
          = (lam * primRoot M ^ (-((j.val : ℤ))) - 1)
            * ∑ i ∈ Finset.range x.val, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ i := by
        rw [hgeom, div_eq_mul_inv]
        field_simp
      rw [heq, norm_mul]
      calc ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖
            * ‖∑ i ∈ Finset.range x.val, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ i‖
          ≤ ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ * (x.val : ℝ) :=
            mul_le_mul_of_nonneg_left htri (norm_nonneg _)
        _ = (x.val : ℝ) * ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ := by ring
  have hsumfin : (∑ x : Fin M, (x.val : ℝ)) = (M * (M - 1) : ℝ) / 2 := by
    have hA : (∑ x : Fin M, (x.val : ℝ)) = ∑ i ∈ Finset.range M, (i : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range]
    have h2 := Finset.sum_range_id_mul_two M
    have hB : (∑ i ∈ Finset.range M, (i : ℝ))
        = ((∑ i ∈ Finset.range M, i : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]
    have h3 : ((∑ i ∈ Finset.range M, i : ℕ) : ℝ) * 2
        = (M : ℝ) * ((M - 1 : ℕ) : ℝ) := by
      have hthis : ((∑ i ∈ Finset.range M, i : ℕ) : ℝ) * 2
          = ((∑ i ∈ Finset.range M, i) * 2 : ℕ) := by
        norm_cast
      rw [hthis, h2]
      norm_cast
    have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      have h1 : M = (M - 1 : ℕ) + 1 := by omega
      have h2 : (M : ℝ) = ((M - 1 : ℕ) : ℝ) + 1 := by
        rw [h1]
        norm_cast
      linarith
    have h3' : ((∑ i ∈ Finset.range M, i : ℕ) : ℝ) * 2
        = (M : ℝ) * ((M : ℝ) - 1) := by
      rw [h3, hcast]
    rw [hA, hB]
    linarith
  have htotal : (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖)
      ≤ (M * (M - 1) : ℝ) / 2 * ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ := by
    calc (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖)
        ≤ ∑ x : Fin M, (x.val : ℝ) * ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ :=
          Finset.sum_le_sum fun x _ => hbound x
    _ = ((∑ x : Fin M, (x.val : ℝ))) * ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ := by
          rw [Finset.sum_mul]
    _ = (M * (M - 1) : ℝ) / 2 * ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖ := by
          rw [hsumfin]
  have hdecomp : ∑ x : Fin M, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ)
        = (M : ℂ) + ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1) := by
    calc ∑ x : Fin M, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ)
        = ∑ x : Fin M, (1 + ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (∑ x : Fin M, (1 : ℂ)) + ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1) := by
          rw [Finset.sum_add_distrib]
      _ = (M : ℂ) + ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          norm_num
  have hamp : ‖(M : ℂ)⁻¹ * ∑ x : Fin M, (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ)‖
      ≥ 1 - (M : ℝ)⁻¹ * (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖) := by
    rw [hdecomp]
    have h1 : (M : ℂ)⁻¹ * (M : ℂ) = 1 :=
      inv_mul_cancel₀ hM0
    have hn1 : ‖(M : ℂ)⁻¹‖ = (M : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    have hn2 : ‖(M : ℂ)‖ = (M : ℝ) := by
      rw [Complex.norm_natCast]
    have h2 : ‖(M : ℂ)⁻¹ * ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖
        = (M : ℝ)⁻¹ * ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ := by
      calc ‖(M : ℂ)⁻¹ * ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖
          = ‖(M : ℂ)⁻¹‖ * ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ :=
          Complex.norm_mul _ _
        _ = (M : ℝ)⁻¹ * ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ := by
          rw [hn1]
    have h3 : ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖
        ≤ ∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖ := by
      have h := norm_sum_le (Finset.univ : Finset (Fin M))
        (fun x => (lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)
      simpa using h
    have htri : ‖(M : ℂ)⁻¹ * ((M : ℂ) + ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1))‖
        ≥ ‖(M : ℂ)⁻¹ * (M : ℂ)‖
            - ‖(M : ℂ)⁻¹ * ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ := by
      have h := norm_sub_le ((M : ℂ)⁻¹ * ((M : ℂ) + ∑ x : Fin M,
          ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)))
        ((M : ℂ)⁻¹ * ∑ x : Fin M,
          ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1))
      have h2 : (M : ℂ)⁻¹ * ((M : ℂ) + ∑ x : Fin M,
            ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1))
            - (M : ℂ)⁻¹ * ∑ x : Fin M,
              ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)
          = (M : ℂ)⁻¹ * (M : ℂ) := by ring
      rw [h2] at h
      linarith
    calc ‖(M : ℂ)⁻¹ * ((M : ℂ) + ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1))‖
        ≥ ‖(M : ℂ)⁻¹ * (M : ℂ)‖
            - ‖(M : ℂ)⁻¹ * ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ := htri
      _ ≥ 1 - (M : ℝ)⁻¹ * (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖) := by
        have hM0r : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
        have hpos : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
        have hmul : (M : ℝ)⁻¹ * ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖
            ≤ (M : ℝ)⁻¹ * (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖) :=
          mul_le_mul_of_nonneg_left h3 hpos
        calc ‖(M : ℂ)⁻¹ * (M : ℂ)‖
              - ‖(M : ℂ)⁻¹ * ∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖
            = (‖(M : ℂ)⁻¹‖ * ‖(M : ℂ)‖)
              - (M : ℝ)⁻¹ * ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ := by
              rw [Complex.norm_mul, h2]
            _ = (M : ℝ)⁻¹ * (M : ℝ)
              - (M : ℝ)⁻¹ * ‖∑ x : Fin M, ((lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1)‖ := by
              rw [hn1, hn2]
            _ ≥ (M : ℝ)⁻¹ * (M : ℝ)
              - (M : ℝ)⁻¹ * (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖) := by
              linarith
            _ = 1 - (M : ℝ)⁻¹ * (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖) := by
              rw [inv_mul_cancel₀ hM0r]
  have hdist : ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖
      = ‖lam - primRoot M ^ ((j.val : ℤ))‖ := by
    have hζ : ‖primRoot M ^ (-((j.val : ℤ)))‖ = 1 := norm_primRoot_zpow M _
    have hz : primRoot M ^ (-((j.val : ℤ))) * primRoot M ^ ((j.val : ℤ)) = 1 := by
      rw [← zpow_add₀ (primRoot_ne_zero M) (-((j.val : ℤ))) ((j.val : ℤ))]
      simp
    have heq : lam * primRoot M ^ (-((j.val : ℤ))) - 1
        = primRoot M ^ (-((j.val : ℤ))) * (lam - primRoot M ^ ((j.val : ℤ))) := by
      rw [mul_sub, hz]
      ring
    calc ‖lam * primRoot M ^ (-((j.val : ℤ))) - 1‖
        = ‖primRoot M ^ (-((j.val : ℤ))) * (lam - primRoot M ^ ((j.val : ℤ)))‖ := by
          rw [heq]
      _ = ‖primRoot M ^ (-((j.val : ℤ)))‖ * ‖lam - primRoot M ^ ((j.val : ℤ))‖ := Complex.norm_mul _ _
      _ = ‖lam - primRoot M ^ ((j.val : ℤ))‖ := by rw [hζ, one_mul]
  simp only [qpeReadoutAmplitude]
  rw [hdist] at htotal
  have hcomb : (M : ℝ)⁻¹
        * (∑ x : Fin M, ‖(lam * primRoot M ^ (-((j.val : ℤ)))) ^ (x.val : ℕ) - 1‖)
      ≤ (M : ℝ)⁻¹ * ((M * (M - 1) : ℝ) / 2
        * ‖lam - primRoot M ^ ((j.val : ℤ))‖) := by
    have hpos : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left htotal hpos
  linarith

theorem energyLabelMap_const_on_level {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (i j : Fin D) (h : energyLevel O i = energyLevel O j) :
    energyLabelMap O G i = energyLabelMap O G j := by
  exact congrArg (fun E => energyLabel G O.time E) h

theorem energyEigenvector_energy_spec {D : ℕ} (O : EnergyOracle D) (i : Fin D) :
    O.ham *ᵥ energyEigenvector O i = (energyLevel O i : ℂ) • energyEigenvector O i :=
  energyEigenvector_spec O i

noncomputable def acceptMass (M : ℕ) (accept : Fin M → ℝ) (propose : Fin M → Fin M → ℝ)
    (j : Fin M) : ℝ :=
  ∑ k, labelChain M accept propose j k

theorem acceptMass_nonneg {M : ℕ} (accept : Fin M → ℝ) (propose : Fin M → Fin M → ℝ)
    (ha : ∀ k, 0 ≤ accept k) (hp : ∀ k j, 0 ≤ propose k j) (j : Fin M) :
    0 ≤ acceptMass M accept propose j := by
  unfold acceptMass
  exact Finset.sum_nonneg fun k _ => mul_nonneg (ha k) (hp k j)

theorem acceptMass_le_one {M : ℕ} (accept : Fin M → ℝ) (propose : Fin M → Fin M → ℝ)
    (ha : ∀ k, accept k ≤ 1) (hp : ∀ k j, 0 ≤ propose k j)
    (hrow : ∀ j, (∑ k, propose k j) = 1) (j : Fin M) :
    acceptMass M accept propose j ≤ 1 := by
  unfold acceptMass
  calc ∑ k, labelChain M accept propose j k
      = ∑ k, accept k * propose k j := by
        apply Finset.sum_congr rfl
        intro k _
        rfl
    _ ≤ ∑ k, 1 * propose k j := by
        exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (ha k) (hp k j)
    _ = 1 := by
      calc ∑ k, 1 * propose k j = ∑ k, propose k j := by
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ = 1 := hrow j

theorem acceptReject_partition {M : ℕ} (accept : Fin M → ℝ) (propose : Fin M → Fin M → ℝ)
    (ha : ∀ k, accept k ≤ 1) (hp : ∀ k j, 0 ≤ propose k j)
    (hrow : ∀ j, (∑ k, propose k j) = 1) (j : Fin M) :
    acceptMass M accept propose j + (1 - acceptMass M accept propose j) = 1 := by ring

theorem chainMinorization_pos {M : ℕ} {T : Fin M → Fin M → ℝ} (d : ChainMinorization M T) :
    0 < d.epsilon ∧ d.epsilon < 1 :=
  ⟨d.epsilonPos, d.epsilonLtOne⟩

theorem gibbsState_eq {D : ℕ} (O : EnergyOracle D) (β : ℝ) :
    gibbsState O β = Qatlib.Concepts.LindbladFlow.GkslSemigroup.gibbsDensity O.ham β := rfl

theorem gibbsState_stationary {D : ℕ} (G : Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D)
    (O : EnergyOracle D) (β : ℝ)
    (h : Qatlib.Concepts.LindbladFlow.GkslSemigroup.KMSNormalForm G (gibbsState O β)) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.IsStationary G (gibbsState O β) :=
  Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore.stationary_of_kmsNormalForm G (gibbsState O β) h

theorem mixing_budget {D : ℕ} (G : Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D)
    (ρ : Operator D) (γ : ℝ)
    (hKMS : Qatlib.Concepts.LindbladFlow.GkslSemigroup.KMSNormalForm G ρ)
    (hGap : Qatlib.Concepts.LindbladFlow.GkslSemigroup.SpectralGapPositive G ρ γ)
    (hMix : Qatlib.Concepts.LindbladFlow.GkslSemigroup.TraceMixingFromGap)
    (σ : Operator D) (hσ : Qatlib.Foundations.PureStateMath.IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.traceDistance
        (Qatlib.Concepts.LindbladFlow.GkslSemigroup.lindbladSemigroup G t σ) ρ
      ≤ Real.exp (-γ * t) * Real.sqrt (2 * Qatlib.Concepts.LindbladFlow.GkslSemigroup.relativeEntropy σ ρ) :=
  (hMix D G ρ γ hKMS hGap σ hσ t ht).1

theorem mixing_entropy_monotone {D : ℕ} (G : Qatlib.Concepts.LindbladFlow.GkslSemigroup.GKSL D)
    (ρ : Operator D) (γ : ℝ)
    (hKMS : Qatlib.Concepts.LindbladFlow.GkslSemigroup.KMSNormalForm G ρ)
    (hGap : Qatlib.Concepts.LindbladFlow.GkslSemigroup.SpectralGapPositive G ρ γ)
    (hMix : Qatlib.Concepts.LindbladFlow.GkslSemigroup.TraceMixingFromGap)
    (σ : Operator D) (hσ : Qatlib.Foundations.PureStateMath.IsDensityOperator σ)
    (t : ℝ) (ht : 0 ≤ t) :
    Qatlib.Concepts.LindbladFlow.GkslSemigroup.relativeEntropy
        (Qatlib.Concepts.LindbladFlow.GkslSemigroup.lindbladSemigroup G t σ) ρ
      ≤ Qatlib.Concepts.LindbladFlow.GkslSemigroup.relativeEntropy σ ρ :=
  (hMix D G ρ γ hKMS hGap σ hσ t ht).2

theorem qpeCostLedger_counts {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    (qpeCostLedger O G).levels = G.levels ∧
      (qpeCostLedger O G).controlledPowers = G.levels ∧
      (qpeCostLedger O G).inverseQftGates = G.levels ∧
      (qpeCostLedger O G).controlledSystemQubits = D := ⟨rfl, rfl, rfl, rfl⟩

theorem exp_mul_I_eq_primRoot (M : ℕ) (n : ℕ) (x : ℝ)
    (hx : x = (n : ℝ) * (2 * Real.pi) / (M : ℝ)) :
    Complex.exp (x * Complex.I) = primRoot M ^ n := by
  have harg : (x : ℂ) * Complex.I = (n : ℕ) * (2 * Real.pi * Complex.I / (M : ℝ)) := by
    rw [hx]
    push_cast
    ring
  rw [harg, Complex.exp_nat_mul (2 * Real.pi * Complex.I / (M : ℝ)) n, primRoot]

theorem qpe_readout_exact_label {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid)
    (ψ : QState (Fin D)) (E : ℝ) (j : Fin G.levels)
    (hψn : Normalized ψ)
    (hψ : O.ham *ᵥ ψ = (E : ℂ) • ψ)
    (hgrid : phaseIndexReal G O.time E = (j.val : ℝ)) :
    ApplyGate (TensorGate (QFTMatrix G.levels)ᴴ (1 : Operator D))
        (ControlledPowers O.evolution G.levels *ᵥ
          TensorState (fun _ : Fin G.levels => (Real.sqrt (G.levels : ℝ) : ℂ)⁻¹) ψ)
      = TensorState (Ket j) ψ ∧
    MeasureProb (ApplyGate (TensorGate (QFTMatrix G.levels)ᴴ (1 : Operator D))
        (ControlledPowers O.evolution G.levels *ᵥ
          TensorState (fun _ : Fin G.levels => (Real.sqrt (G.levels : ℝ) : ℂ)⁻¹) ψ))
        ({j} ×ˢ (Finset.univ : Finset (Fin D))) = 1 := by
  have hstep : O.evolution *ᵥ ψ = (primRoot G.levels ^ ((j.val : ℤ))) • ψ := by
    have hph := O.evolutionPhase E ψ hψ
    rw [hph]
    have hx : -(O.time * E) = (j.val : ℝ) * (2 * Real.pi) / (G.levels : ℝ) := by
      have h1 := hgrid
      simp only [phaseIndexReal] at h1
      have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have hlev : (G.levels : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt G.levelsPos)
      rw [div_eq_iff h2pi] at h1
      have hstep' : -(O.time * E) * (G.levels : ℝ) = (j.val : ℝ) * (2 * Real.pi) := by
        linarith
      exact (eq_div_iff hlev).2 hstep'
    have hexp := exp_mul_I_eq_primRoot G.levels (j.val) (-(O.time * E)) hx
    simp only [Complex.ofReal_neg, Complex.ofReal_mul] at hexp ⊢
    have hzp : primRoot G.levels ^ (j.val : ℕ) = primRoot G.levels ^ ((j.val : ℤ)) :=
      (zpow_natCast (primRoot G.levels) (j.val)).symm
    rw [hexp, hzp]
  exact qpe_exact_readout G.levelsPos hψn j hstep

theorem energyLabel_alias_width {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) (E E' : ℝ)
    (h : phaseIndex G O.time E = phaseIndex G O.time E') :
    |E - E'| ≤ 2 * Real.pi / (O.time * (G.levels : ℝ)) := by
  have herr1 := phaseIndex_round_error G O.time E
  have herr2 := phaseIndex_round_error G O.time E'
  have h1a := abs_le.mp herr1
  have h2a := abs_le.mp herr2
  have hidx : (phaseIndex G O.time E : ℝ) = (phaseIndex G O.time E' : ℝ) := by
    exact_mod_cast h
  have hreal : |phaseIndexReal G O.time E - phaseIndexReal G O.time E'| ≤ 1 := by
    rw [abs_le]
    constructor
    · have h1 : phaseIndexReal G O.time E ≤ phaseIndexReal G O.time E' + 1 := by
        linarith [h1a.1, h1a.2, h2a.1, h2a.2, hidx]
      linarith
    · have h2 : phaseIndexReal G O.time E' ≤ phaseIndexReal G O.time E + 1 := by
        linarith [h1a.1, h1a.2, h2a.1, h2a.2, hidx]
      linarith
  have hkey : phaseIndexReal G O.time E - phaseIndexReal G O.time E'
      = -(O.time * (G.levels : ℝ) / (2 * Real.pi)) * (E - E') := by
    simp only [phaseIndexReal]
    ring
  have hc : 0 < O.time * (G.levels : ℝ) / (2 * Real.pi) := by
    have h1 : 0 < O.time := O.timePos
    have h2 : 0 < (G.levels : ℝ) := by exact_mod_cast G.levelsPos
    positivity
  have hneg : -(O.time * (G.levels : ℝ) / (2 * Real.pi)) ≤ 0 := by
    linarith
  have habs : |-(O.time * (G.levels : ℝ) / (2 * Real.pi))|
      = O.time * (G.levels : ℝ) / (2 * Real.pi) := by
    rw [abs_neg, abs_of_pos hc]
  rw [hkey, abs_mul, habs] at hreal
  rw [mul_comm] at hreal
  have hone : |E - E'| ≤ 1 / (O.time * (G.levels : ℝ) / (2 * Real.pi)) := by
    rw [le_div_iff₀ hc]
    exact hreal
  have hrewrite : 1 / (O.time * (G.levels : ℝ) / (2 * Real.pi))
      = 2 * Real.pi / (O.time * (G.levels : ℝ)) := by
    have h1 : 0 < O.time := O.timePos
    have h2 : 0 < (G.levels : ℝ) := by exact_mod_cast G.levelsPos
    have hn1 : O.time * (G.levels : ℝ) ≠ 0 := by positivity
    have hn2 : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hrewrite] at hone
  exact hone

noncomputable def energyLabelProjectors {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    LabelProjectors D G.levels where
  proj := energyBinProjector O G
  hermitian := fun j => (energyBinProjector_resolution O G).1 j |>.1
  idempotent := fun j => (energyBinProjector_resolution O G).1 j |>.2
  orthogonality := fun j k hjk => (energyBinProjector_resolution O G).2.1 j k hjk
  total := (energyBinProjector_resolution O G).2.2

theorem metropolisAcceptKraus_KK {D M : ℕ} (P : LabelProjectors D M) (Q : ProposalOracle D)
    (α : AcceptWeights M) (j : Fin M) :
    (metropolisAcceptKraus P Q α j)ᴴ * (metropolisAcceptKraus P Q α j)
      = (α.weight j : ℂ) • (Q.unitaryᴴ * (P.proj j * Q.unitary)) := by
  rw [metropolisAcceptKraus]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, acceptScale_star]
  rw [smul_mul_smul, acceptScale_sq (α.nonneg j)]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [P.hermitian j]
  rw [← Matrix.mul_assoc (P.proj j) (P.proj j) Q.unitary]
  rw [P.idempotent j]

theorem metropolisRejectKraus_KK {D M : ℕ} (P : LabelProjectors D M) (Q : ProposalOracle D)
    (α : AcceptWeights M) (j : Fin M) :
    (metropolisRejectKraus P Q α j)ᴴ * (metropolisRejectKraus P Q α j)
      = (1 - (α.weight j : ℂ)) • (Q.unitaryᴴ * (P.proj j * Q.unitary)) := by
  rw [metropolisRejectKraus]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, acceptScale_star]
  rw [smul_mul_smul, acceptScale_sq_sub (α.le_one j)]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Q.inverseᴴ Q.inverse (P.proj j * Q.unitary)]
  rw [Q.inverse_KK, one_mul, P.hermitian j]
  rw [← Matrix.mul_assoc (P.proj j) (P.proj j) Q.unitary]
  rw [P.idempotent j]

theorem metropolisJointKraus_complete {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) :
    (∑ jb : Fin M × Fin 2,
        (metropolisJointKraus P Q α jb)ᴴ * (metropolisJointKraus P Q α jb)) = 1 := by
  classical
  have hacc : ∀ j : Fin M,
      (metropolisJointKraus P Q α (j, 0))ᴴ * (metropolisJointKraus P Q α (j, 0))
        = (α.weight j : ℂ) • (Q.unitaryᴴ * (P.proj j * Q.unitary)) := by
    intro j
    have h : metropolisJointKraus P Q α (j, 0) = metropolisAcceptKraus P Q α j := by
      simp [metropolisJointKraus]
    rw [h]
    exact metropolisAcceptKraus_KK P Q α j
  have hrej : ∀ j : Fin M,
      (metropolisJointKraus P Q α (j, 1))ᴴ * (metropolisJointKraus P Q α (j, 1))
        = (1 - (α.weight j : ℂ)) • (Q.unitaryᴴ * (P.proj j * Q.unitary)) := by
    intro j
    have h : metropolisJointKraus P Q α (j, 1) = metropolisRejectKraus P Q α j := by
      simp [metropolisJointKraus]
    rw [h]
    exact metropolisRejectKraus_KK P Q α j
  have hsplit : (∑ jb : Fin M × Fin 2,
        (metropolisJointKraus P Q α jb)ᴴ * (metropolisJointKraus P Q α jb))
      = ∑ j : Fin M, ((metropolisJointKraus P Q α (j, 0))ᴴ
            * (metropolisJointKraus P Q α (j, 0))
          + (metropolisJointKraus P Q α (j, 1))ᴴ * (metropolisJointKraus P Q α (j, 1))) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    rw [Fin.sum_univ_two]
  rw [hsplit]
  calc (∑ j : Fin M, ((metropolisJointKraus P Q α (j, 0))ᴴ
          * (metropolisJointKraus P Q α (j, 0))
        + (metropolisJointKraus P Q α (j, 1))ᴴ * (metropolisJointKraus P Q α (j, 1))))
      = ∑ j : Fin M, ((α.weight j : ℂ) • (Q.unitaryᴴ * (P.proj j * Q.unitary))
        + (1 - (α.weight j : ℂ)) • (Q.unitaryᴴ * (P.proj j * Q.unitary))) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hacc j, hrej j]
    _ = ∑ j : Fin M, (1 : ℂ) • (Q.unitaryᴴ * (P.proj j * Q.unitary)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← add_smul]
          congr 1
          ring
    _ = ∑ j : Fin M, Q.unitaryᴴ * (P.proj j * Q.unitary) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [one_smul]
    _ = Q.unitaryᴴ * ((∑ j : Fin M, P.proj j) * Q.unitary) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ = Q.unitaryᴴ * (1 * Q.unitary) := by rw [P.total]
    _ = Q.unitaryᴴ * Q.unitary := by rw [Matrix.one_mul]
    _ = 1 := Q.unitary_KK

noncomputable def metropolisJointInstrument {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) : Instrument (Fin M × Fin 2) D D :=
  Instrument.ofKraus (metropolisJointKraus P Q α) (metropolisJointKraus_complete P Q α)

theorem metropolisJoint_total {D M : ℕ} (P : LabelProjectors D M) (Q : ProposalOracle D)
    (α : AcceptWeights M) (ρ : Operator D) :
    (∑ jb : Fin M × Fin 2, instrumentProb (metropolisJointInstrument P Q α) ρ jb)
      = (Matrix.trace ρ).re :=
  sum_instrumentProb (metropolisJointInstrument P Q α) ρ

theorem metropolisJoint_isProbability {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (ρ : Operator D)
    (hρ : Qatlib.Foundations.PureStateMath.IsDensityOperator ρ) :
    (∑ jb : Fin M × Fin 2, instrumentProb (metropolisJointInstrument P Q α) ρ jb) = 1 :=
  sum_instrumentProb_isDensityOperator (metropolisJointInstrument P Q α) hρ

theorem metropolisJoint_referenceMarginal {D M R : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    partialTraceFirst (∑ jb : Fin M × Fin 2,
        tensorLeft ((metropolisJointInstrument P Q α).branch jb) ρ)
      = partialTraceFirst ρ :=
  Instrument.referenceMarginal (metropolisJointInstrument P Q α) ρ

theorem metropolisJoint_tni {D M R : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : ρ.PosSemidef) (jb : Fin M × Fin 2) :
    (Matrix.trace (tensorLeft ((metropolisJointInstrument P Q α).branch jb) ρ)).re
      ≤ (Matrix.trace ρ).re :=
  Instrument.tensorLeft_tni (metropolisJointInstrument P Q α) hρ jb

theorem metropolisReject_branch_general {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (ρ : Operator D) (j : Fin M) :
    (metropolisRejectKraus P Q α j) * ρ * (metropolisRejectKraus P Q α j)ᴴ
      = (1 - (α.weight j : ℂ))
          • ((Q.inverse * P.proj j * Q.unitary) * ρ
            * (Q.inverse * P.proj j * Q.unitary)ᴴ) := by
  rw [metropolisRejectKraus]
  simp only [Matrix.conjTranspose_smul, acceptScale_star]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      acceptScale_sq_sub (α.le_one j)]

theorem metropolisReject_branch_commuting {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (ρ : Operator D) (j : Fin M)
    (hcomm : Q.unitary * P.proj j = P.proj j * Q.unitary) :
    (metropolisRejectKraus P Q α j) * ρ * (metropolisRejectKraus P Q α j)ᴴ
      = (1 - (α.weight j : ℂ)) • (P.proj j * ρ * P.proj j) := by
  have hinv : Q.inverse * P.proj j * Q.unitary = P.proj j := by
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc Q.inverse Q.unitary (P.proj j),
      Q.inverse_mul, Matrix.one_mul]
  rw [metropolisRejectKraus]
  simp only [Matrix.conjTranspose_smul, acceptScale_star]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      acceptScale_sq_sub (α.le_one j)]
  rw [hinv, P.hermitian j]

theorem metropolisReject_branch_restores {D M : ℕ} (P : LabelProjectors D M)
    (Q : ProposalOracle D) (α : AcceptWeights M) (ρ : Operator D) (j : Fin M)
    (hcomm : Q.unitary * P.proj j = P.proj j * Q.unitary)
    (hsupp : P.proj j * ρ = ρ) (hherm : ρᴴ = ρ) :
    (metropolisRejectKraus P Q α j) * ρ * (metropolisRejectKraus P Q α j)ᴴ
      = (1 - (α.weight j : ℂ)) • ρ := by
  have hsupp' : ρ * P.proj j = ρ := by
    have h := congrArg Matrix.conjTranspose hsupp
    rw [Matrix.conjTranspose_mul, hherm, P.hermitian j] at h
    exact h
  rw [metropolisReject_branch_commuting P Q α ρ j hcomm]
  rw [hsupp, hsupp']

noncomputable def metropolisStepLedger {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    MetropolisStepLedger where
  energyControlledPowers := G.levels
  energyInverseQftGates := G.levels
  proposalApplications := 1
  rewindApplications := 1
  controlledSystemQubits := D
  classicalReadoutBits := Nat.log2 G.levels + 1

theorem metropolisStepLedger_counts {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    (metropolisStepLedger O G).energyControlledPowers = G.levels ∧
      (metropolisStepLedger O G).energyInverseQftGates = G.levels ∧
      (metropolisStepLedger O G).proposalApplications = 1 ∧
      (metropolisStepLedger O G).rewindApplications = 1 ∧
      (metropolisStepLedger O G).controlledSystemQubits = D ∧
      (metropolisStepLedger O G).classicalReadoutBits = Nat.log2 G.levels + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem metropolisStepLedger_readout_le {D : ℕ} (O : EnergyOracle D) (G : PhaseGrid) :
    (metropolisStepLedger O G).classicalReadoutBits ≤ G.levels + 1 := by
  simp only [metropolisStepLedger]
  exact Nat.succ_le_succ (Nat.log2_le_self G.levels)

end StageAQUANTUMGIBBS
end Qatlib.Concepts.LindbladFlow.GkslSemigroup
