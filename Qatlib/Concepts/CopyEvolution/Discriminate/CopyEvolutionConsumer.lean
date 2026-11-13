/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.FreshCopyComposition

/-!
# Explicit copy-evolution examples

This module computes partial-swap evolution for qubit inputs with copies of the zero-state
projector. `copy_zero_projector_repeated_coherence` gives closed formulas for repeated
populations and coherences, together with the resource tuple. These examples instantiate the
density-matrix exponentiation step of [LloydMohseniRebentrost2014].

The plus-state example produces a density operator that is not pure, while the Bell-state
example tracks a full swap with an entangled reference. The zero-angle, full-swap, and empty-run
cases provide exact limiting identities.

## Main statements

* `copy_zero_projector_one_step`: the explicit single-step qubit matrix.
* `copy_zero_projector_repeated_coherence`: the repeated-step matrix and resource counts.
* `copy_noncommuting_mixed_consumer`: the non-pure output of the plus-state example.
* `copy_entangled_reference_swap_consumer`: full-swap behavior with a Bell reference.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.CopyEvolution.Discriminate

open Matrix
open scoped ComplexOrder

/-- The projector onto the zero computational basis state is a density operator. -/
private theorem hrho0 : IsDensityOperator (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) :=
  isDensityOperator_outerProduct (normalized_ket 0)

/-- The zero-state projector has entry one at `(0, 0)` and zero elsewhere. -/
private theorem rho0_apply (i j : Fin 2) :
    outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) i j = if i = 0 ∧ j = 0 then (1 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;> simp [outerProduct_apply, Qatlib.Foundations.PureStateMath.Ket]

/-- A partial-swap step with a zero-state copy has the displayed two-by-two matrix formula,
including its complex coherence factors. -/
theorem copy_zero_projector_one_step (θ : ℝ) (σ : Operator 2) :
    partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ =
    !![σ 0 0 + ((Real.sin θ)^2 : ℂ)*σ 1 1,
        (((Real.cos θ)^2 : ℂ)-Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))*σ 0 1;
       (((Real.cos θ)^2 : ℂ)+Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))*σ 1 0,
        ((Real.cos θ)^2 : ℂ)*σ 1 1] := by
  have hc2s : ((Real.cos θ)^2 : ℂ) = 1 - ((Real.sin θ)^2 : ℂ) := by
    exact_mod_cast (by linear_combination Real.cos_sq_add_sin_sq θ :
      ((Real.cos θ)^2 : ℝ) = 1 - (Real.sin θ)^2)
  rw [partial_swap_actual_output_formula, hrho0.2, one_smul, hc2s]
  have htrace : Matrix.trace σ = σ 0 0 + σ 1 1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  rw [htrace]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, rho0_apply] <;>
    ring

/-- Repeated equal-angle steps with zero-state copies have the displayed closed form for
populations and coherences. The resource tuple for `n` steps is `(n, n, n, 0)`. -/
theorem copy_zero_projector_repeated_coherence (θ : ℝ) (n : ℕ) (σ : Operator 2) :
    freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (List.replicate n θ) σ =
    !![Matrix.trace σ - (((Real.cos θ)^2)^n : ℂ)*σ 1 1,
       ((((Real.cos θ)^2 : ℂ)-Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^n)*σ 0 1;
       ((((Real.cos θ)^2 : ℂ)+Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^n)*σ 1 0,
       (((Real.cos θ)^2)^n : ℂ)*σ 1 1] ∧
    freshCopyResourceCounts 2 (List.replicate n θ) = (n,n,n,0) := by
  induction n generalizing σ with
  | zero =>
      have hrun : freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (List.replicate 0 θ) σ
          = σ := by
        simp [freshCopyRun]
      refine ⟨?_, by rw [freshCopyResourceCounts_eq, List.length_replicate]⟩
      rw [hrun]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [pow_zero, Matrix.trace, Matrix.diag_apply]
  | succ n ih =>
      refine ⟨?_, by rw [freshCopyResourceCounts_eq, List.length_replicate]⟩
      rw [List.replicate_succ,
        show freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (θ :: List.replicate n θ) σ
            = freshCopyRun (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (List.replicate n θ)
              (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ) from rfl]
      obtain ⟨ih1, _⟩ :=
          ih (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ)
      have htr : Matrix.trace (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) θ σ)
          = Matrix.trace σ :=
        (partial_swap_cptp_bridge (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) hrho0 θ σ).2.1
      rw [ih1, htr, copy_zero_projector_one_step θ σ,
        show (((Real.cos θ)^2 : ℂ))^(n+1)
            = ((Real.cos θ)^2 : ℂ)^n * ((Real.cos θ)^2 : ℂ) from (pow_succ _ _).symm,
        show (((Real.cos θ)^2 : ℂ) - Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^(n+1)
            = (((Real.cos θ)^2 : ℂ) - Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^n
              * (((Real.cos θ)^2 : ℂ) - Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))
            from (pow_succ _ _).symm,
        show (((Real.cos θ)^2 : ℂ) + Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^(n+1)
            = (((Real.cos θ)^2 : ℂ) + Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))^n
              * (((Real.cos θ)^2 : ℂ) + Complex.I*(Real.sin θ : ℂ)*(Real.cos θ : ℂ))
            from (pow_succ _ _).symm]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.trace, Matrix.diag_apply] <;>
        ring

/-- The qubit density matrix of the equal superposition of the two computational basis states. -/
noncomputable def copyEvolutionPlusInput : Operator 2 := (1/2 : ℂ) • !![1,1;1,1]

/-- Every matrix entry of `copyEvolutionPlusInput` equals `1 / 2`. -/
private theorem plusInput_apply (i j : Fin 2) :
    copyEvolutionPlusInput i j = 1 / 2 := by
  fin_cases i <;> fin_cases j <;> simp [copyEvolutionPlusInput]

/-- The plus-state input is a density operator. -/
theorem isDensityOperator_copyEvolutionPlusInput :
    IsDensityOperator copyEvolutionPlusInput := by
  have hin : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = 1 / 2 := by
    rw [inv_sqrt2_mul_self]
    norm_num
  have hEq : copyEvolutionPlusInput = outerProduct (fun _ => (Real.sqrt 2 : ℂ)⁻¹) := by
    ext i j
    rw [plusInput_apply, outerProduct_apply]
    have hstar : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
      rw [show ((Real.sqrt 2 : ℂ))⁻¹
            = Complex.ofReal ((Real.sqrt 2 : ℝ)⁻¹) from
            (Complex.ofReal_inv (Real.sqrt 2 : ℝ)).symm,
        Complex.conj_ofReal]
    rw [hstar, hin]
  refine ⟨?_, ?_⟩
  · rw [hEq]
    exact outerProduct_posSemidef _
  · rw [copyEvolutionPlusInput]
    have htr : Matrix.trace (!![1,1;1,1] : Matrix (Fin 2) (Fin 2) ℂ) = 2 := by
      simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
      norm_num
    rw [Matrix.trace_smul, htr]
    norm_num

/-- A partial swap of angle `π / 4` between the plus-state input and a zero-state copy yields
the displayed density matrix, which is not pure. -/
theorem copy_noncommuting_mixed_consumer :
    copyEvolutionPlusInput = (1/2 : ℂ) • !![1,1;1,1] ∧
    IsDensityOperator copyEvolutionPlusInput ∧
    partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4) copyEvolutionPlusInput =
    !![3/4,(1-Complex.I)/4;(1+Complex.I)/4,1/4] ∧
    IsDensityOperator (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4)
      copyEvolutionPlusInput) ∧
    ¬ IsPureDensityOperator (partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4)
      copyEvolutionPlusInput) := by
  have hcsq : ((Real.sqrt 2 : ℂ) / 2)^2 = 1 / 2 := by
    rw [show ((Real.sqrt 2 : ℂ) / 2)^2 = ((Real.sqrt 2 : ℂ))^2 / 4 from by ring,
      sqrt2_sq]
    norm_num
  have hprod : ((Real.sqrt 2 : ℂ) / 2) * ((Real.sqrt 2 : ℂ) / 2) = 1 / 2 := by
    rw [show ((Real.sqrt 2 : ℂ) / 2) * ((Real.sqrt 2 : ℂ) / 2)
          = ((Real.sqrt 2 : ℂ))^2 / 4 from by ring, sqrt2_sq]
    norm_num
  have hc2 : ((Real.cos (Real.pi/4))^2 : ℂ) = 1/2 := by
    rw [Real.cos_pi_div_four]
    push_cast
    exact hcsq
  have hs2 : ((Real.sin (Real.pi/4))^2 : ℂ) = 1/2 := by
    rw [Real.sin_pi_div_four]
    push_cast
    exact hcsq
  have hsc : ((Real.sin (Real.pi/4) : ℂ) * (Real.cos (Real.pi/4) : ℂ)) = 1/2 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    push_cast
    exact hprod
  have htrace : Matrix.trace copyEvolutionPlusInput = 1 := by
    rw [isDensityOperator_copyEvolutionPlusInput.2]
  have hscI : Complex.I * ((Real.sin (Real.pi/4) : ℂ)) * ((Real.cos (Real.pi/4) : ℂ))
      = Complex.I / 2 := by
    rw [show Complex.I * ((Real.sin (Real.pi/4) : ℂ)) * ((Real.cos (Real.pi/4) : ℂ))
          = Complex.I * (((Real.sin (Real.pi/4) : ℂ)) * ((Real.cos (Real.pi/4) : ℂ))) from by
        ring, hsc]
    ring
  have hout : partialSwapOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/4) copyEvolutionPlusInput
      = !![3/4,(1-Complex.I)/4;(1+Complex.I)/4,1/4] := by
    rw [copy_zero_projector_one_step, hc2, hs2, hscI]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [plusInput_apply] <;>
      ring
  refine ⟨rfl, isDensityOperator_copyEvolutionPlusInput, hout, ?_, ?_⟩
  · exact (partial_swap_cptp_bridge (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) hrho0 (Real.pi/4)
      copyEvolutionPlusInput).2.2 isDensityOperator_copyEvolutionPlusInput
  · rintro ⟨_, hmul⟩
    have h00 := congrFun (congrFun hmul 0) 0
    rw [hout] at h00
    simp at h00
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have h01 : (0 : ℂ) = 1 := by
      linear_combination 16 * h00 + hI
    exact zero_ne_one h01

/-- The two-qubit Bell state used to test copy evolution with an entangled reference. -/
noncomputable def copyEvolutionBellInput : QState (Fin 2 × Fin 2) :=
  fun p => if p.1 = p.2 then (Real.sqrt 2 : ℂ)⁻¹ else 0

/-- The left partial trace of the Bell-state density matrix is the maximally mixed qubit state. -/
theorem traceLeft_outerProduct_copyEvolutionBellInput :
    Matrix.traceLeft (outerProduct copyEvolutionBellInput) = (1/2 : ℂ) • (1 : Operator 2) := by
  ext b b'
  fin_cases b <;> fin_cases b' <;>
    simp [Matrix.traceLeft, outerProduct_apply, copyEvolutionBellInput] <;>
    norm_num [inv_sqrt2_mul_self]

/-- For the Bell-state input, a full swap with a zero-state copy resets the system to zero and
leaves the reference maximally mixed. -/
theorem copy_entangled_reference_swap_consumer :
    Matrix.traceLeft (outerProduct copyEvolutionBellInput) = (1/2 : ℂ) • (1 : Operator 2) ∧
    partialSwapReferenceOutput (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) (Real.pi/2) 2
      (outerProduct copyEvolutionBellInput)
      = TensorGate (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) ((1/2 : ℂ) • (1 : Operator 2)) := by
  refine ⟨traceLeft_outerProduct_copyEvolutionBellInput, ?_⟩
  rw [(partial_swap_reference_output_formula (outerProduct (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) hrho0
      (Real.pi/2) 2 (outerProduct copyEvolutionBellInput)).1]
  have hc0 : (((Real.cos (Real.pi / 2))^2 : ℂ)) = 0 := by
    push_cast
    norm_num
  have hs1 : (((Real.sin (Real.pi / 2))^2 : ℂ)) = 1 := by
    push_cast
    norm_num
  have hsc0 : Complex.I * ((Real.sin (Real.pi / 2) : ℂ)) * ((Real.cos (Real.pi / 2) : ℂ)) = 0 := by
    rw [Real.sin_pi_div_two, Real.cos_pi_div_two]
    norm_num
  rw [hc0, hs1, hsc0, traceLeft_outerProduct_copyEvolutionBellInput]
  simp only [zero_smul, zero_add, one_smul, sub_zero]

/-- At angle zero the partial-swap output is unchanged, while at `π / 2` it is `Matrix.trace σ •
ρ`. An empty copy run is the identity and has zero resource counts. -/
theorem copy_zero_and_full_swap_limits {D : ℕ} (ρ : Operator D) (hρ : IsDensityOperator ρ)
    (σ : Operator D) :
    partialSwapOutput ρ 0 σ = σ ∧ partialSwapOutput ρ (Real.pi/2) σ = Matrix.trace σ • ρ ∧
    freshCopyRun ρ [] σ = σ ∧ freshCopyResourceCounts D [] = (0,0,0,0) := by
  refine ⟨?_, ?_, rfl, by rw [freshCopyResourceCounts_eq]; rfl⟩
  · rw [partial_swap_actual_output_formula]
    have h1 : (((Real.cos 0)^2 : ℂ)) = 1 := by
      rw [Real.cos_zero]
      norm_num
    have h0 : (((Real.sin 0)^2 : ℂ)) = 0 := by
      rw [Real.sin_zero]
      norm_num
    have hc0' : Complex.I * ((Real.sin 0 : ℂ)) * ((Real.cos 0 : ℂ)) = 0 := by
      rw [Real.sin_zero]
      norm_num
    rw [h1, one_smul, hρ.2, one_smul, h0, zero_smul, hc0', zero_smul, add_zero, sub_zero]

  · rw [partial_swap_actual_output_formula]
    have h0 : (((Real.cos (Real.pi / 2))^2 : ℂ)) = 0 := by
      rw [Real.cos_pi_div_two]
      norm_num
    have h1 : (((Real.sin (Real.pi / 2))^2 : ℂ)) = 1 := by
      rw [Real.sin_pi_div_two]
      norm_num
    have hsc0 : Complex.I * ((Real.sin (Real.pi / 2) : ℂ)) * ((Real.cos (Real.pi / 2) : ℂ))
        = 0 := by
      rw [Real.cos_pi_div_two]
      norm_num
    rw [h0, h1, zero_smul, zero_add, one_smul, hsc0, zero_smul, sub_zero]

end Qatlib.Concepts.CopyEvolution.Discriminate
