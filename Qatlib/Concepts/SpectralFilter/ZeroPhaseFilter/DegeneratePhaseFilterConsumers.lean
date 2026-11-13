/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter.DegeneratePhaseFilter
import Qatlib.Concepts.WalkFind.UniformThree.PhaseReflectionSearch

/-!
# Coherent reflection with degenerate targets

This module bounds the counted coherent reflection error for an orthonormal eigenfamily whose
target may contain several zero-phase vectors. It extends the phase-detection reflection
construction of [MagniezNayakRolandSantha2011] to an explicitly selected target subspace.

The three-dimensional example `degenerateThreeWalk` has a two-dimensional +1 eigenspace and one
−1 eigenvector. One binary phase-detection round extracts the target components exactly and
implements their coherent reflection.

## Main statements

* `degenerate_phase_actual_coherent_reflection_error`: reflection error controlled by phase gap
  and nontarget mass.
* `degenerateThreeWalk_branch`: exact removal of the third component.
* `degenerate_phase_two_dimensional_target_actual_consumer`: explicit probability, reflection,
  and detection costs.

## References

* [Magniez et al., 2011, Theorem 6][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

/-- For a normalized orthonormal eigenstate combination with zero-phase target and gap `η`
outside it, the counted reflection differs from the embedded target reflection by at most
`2*(1/(2*M*η))^k` times the square root of the nontarget mass. See
[MagniezNayakRolandSantha2011]. -/
theorem degenerate_phase_actual_coherent_reflection_error
    (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
    (φ : J → ℝ) (T : Finset J) (η : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hη : 0 < η) (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (ht : ∀ j ∈ T, phaseDistance (φ j) 0 = 0)
    (hg : ∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) :
    let ψ := ∑ j, c j • v j;
    ‖toEuclidean_fromVec (phaseReflectionState W M k ψ -
      phaseReflectionEmbed M k ((2 : ℂ) • spectralTargetState v c T - ψ))‖ ≤
      2 * (1 / (2 * (M : ℝ) * η)) ^ k * Real.sqrt (1 - (∑ j ∈ T, ‖c j‖ ^ 2)) := by
  intro ψ
  let D := evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord (I := I) M k)
  let E := degenerateEmbedLinear (I := I) M k
  let R := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
    (phaseReflectionWord M k))).comp E
  let L := (degenerateApplyLinear Dᴴ).comp ((2 : ℂ) • E)
  let α : J → ℂ := fun j => (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k
  let z := degenerateZeroBranch W M k (by omega) ψ
  let t := spectralTargetState v c T
  have hD : D ∈ Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (phaseDetectionWord_resources M k (by omega)).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have hres (j : J) : R (v j) + E (v j) = L (α j • v j) := by
    change phaseReflectionState W M k (v j) + phaseReflectionEmbed M k (v j) =
      ApplyGate Dᴴ ((2 : ℂ) • E (α j • v j))
    rw [E.map_smul]
    exact phase_reflection_eigenstate_residual M k hM W (v j) (φ j) hW (he j)
  have hsum : R ψ + E ψ = L z := by
    change R (∑ j, c j • v j) + E (∑ j, c j • v j) = L z
    have hz : z = ∑ j, (c j * α j) • v j :=
      (degenerate_phase_actual_spectral_packet I J W M k (by omega) v c φ he).2
    rw [hz, map_sum, map_sum, map_sum]
    simp only [map_smul, ← Finset.sum_add_distrib, ← smul_add, mul_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hres j, map_smul]
  have htarget : L t = (2 : ℂ) • E t := by
    change L (∑ j ∈ T, c j • v j) = (2 : ℂ) • E (∑ j ∈ T, c j • v j)
    rw [map_sum, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hα : α j = 1 := by
      simp [α, qpeKernel_zero_distance M (by omega) (φ j) (ht j hj), Ket]
    have hfix : R (v j) = E (v j) :=
      (phase_reflection_actual_eigenstate_error M k hM W (v j) (φ j) hW (he j)).1 (ht j hj)
    have hr := hres j
    rw [hα, one_smul, hfix] at hr
    rw [map_smul, map_smul, ← hr]
    module
  have herr : phaseReflectionState W M k ψ -
      phaseReflectionEmbed M k ((2 : ℂ) • t - ψ) = L (z - t) := by
    change R ψ - E ((2 : ℂ) • t - ψ) = _
    rw [E.map_sub, E.map_smul, L.map_sub, htarget]
    rw [← hsum]
    abel
  have hn := (degenerate_phase_zero_event_and_full_branch_error I J W M k hM v c φ T η
    hW hη hv hc he ht hg).2.2
  rw [herr]
  change ‖toEuclidean_fromVec (ApplyGate Dᴴ ((2 : ℂ) • E (z - t)))‖ ≤ _
  rw [norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
  change ‖(2 : ℂ) • toEuclidean_fromVec (phaseReflectionEmbed M k (z - t))‖ ≤ _
  rw [norm_smul, phaseReflectionEmbed_norm M k (by omega)]
  norm_num only [Complex.norm_ofNat]
  nlinarith [hn]

/-- The diagonal matrix with eigenvalues +1 on the first two coordinates and −1 on the third. -/
noncomputable def degenerateThreeWalk : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => if i = 2 then -1 else 1)

/-- The phase assignment zero on the first two coordinates and one half on the third. -/
noncomputable def degenerateThreePhase (i : Fin 3) : ℝ := if i = 2 then 1 / 2 else 0

/-- Each basis ket is an eigenvector of `degenerateThreeWalk` with the exponential eigenvalue
specified by `degenerateThreePhase`. -/
theorem degenerateThreeWalk_eigen (j : Fin 3) :
    degenerateThreeWalk *ᵥ Ket j =
      Complex.exp (2 * Real.pi * Complex.I * (degenerateThreePhase j : ℂ)) • Ket j := by
  have hex : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℝ)) = -1 := by
    rw [show (2 * Real.pi * Complex.I * (1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]
  have hphase : Complex.exp (2 * Real.pi * Complex.I * (degenerateThreePhase j : ℂ)) =
      if j = 2 then -1 else 1 := by
    by_cases hj : j = 2
    · simpa only [degenerateThreePhase, if_pos hj] using hex
    · simp only [degenerateThreePhase, if_neg hj, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [hphase]
  funext i
  rw [degenerateThreeWalk, Matrix.mulVec_diagonal]
  by_cases hi : i = j
  · subst i; simp [Ket, Pi.smul_apply, smul_eq_mul]
  · simp [Ket, hi, Pi.smul_apply, smul_eq_mul]

/-- The binary QPE zero-label kernel is one on the two zero-phase coordinates and zero on the
half-phase coordinate. -/
theorem degenerateThreePhase_kernel (j : Fin 3) :
    qpeKernel 2 (degenerateThreePhase j) (0 : Fin 2) = if j = 2 then 0 else 1 := by
  have hh : qpeKernel 2 (1 / 2) (0 : Fin 2) = 0 := by
    have h := (offgrid_phase_geometric_and_periodic 2 0 (0 : Fin 2) (by decide)).2.2 (1 : Fin 2)
    simpa [Ket] using h
  have hz : qpeKernel 2 0 (0 : Fin 2) = 1 := by
    have h := (offgrid_phase_geometric_and_periodic 2 0 (0 : Fin 2) (by decide)).2.2 (0 : Fin 2)
    simpa [Ket] using h
  by_cases hj : j = 2
  · simpa only [degenerateThreePhase, if_pos hj] using hh
  · simpa only [degenerateThreePhase, if_neg hj] using hz

/-- One binary detection round for `degenerateThreeWalk` preserves the first two amplitudes and
sets the third to zero. -/
theorem degenerateThreeWalk_branch (c : Fin 3 → ℂ) :
    degenerateZeroBranch degenerateThreeWalk 2 1 (by decide) c =
      (fun i => if i = 2 then 0 else c i) := by
  have hsum : c = ∑ j : Fin 3, c j • Ket j := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Ket, smul_eq_mul]
  rw [hsum, (degenerate_phase_actual_spectral_packet (Fin 3) (Fin 3)
    degenerateThreeWalk 2 1 (by decide) Ket c degenerateThreePhase degenerateThreeWalk_eigen).2]
  change (∑ j : Fin 3, (c j * qpeKernel 2 (degenerateThreePhase j) (0 : Fin 2) ^ 1) • Ket j) = _
  funext i
  simp only [degenerateThreePhase_kernel, pow_one, mul_ite, mul_zero, mul_one,
    ite_smul, zero_smul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ket]
  rw [Finset.sum_eq_single i]
  · by_cases hi : i = 2 <;> simp [hi]
  · intro j _ hji
    by_cases hj : j = 2 <;> simp [hj, Ket, Ne.symm hji]
  · simp

/-- For the uniform three-coordinate input, one binary detection round has zero-event
probability `2/3` and retains exactly the first two components, while coherent reflection
negates the third. The detection word uses one query and four gates. -/
theorem degenerate_phase_two_dimensional_target_actual_consumer :
    let W : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal (fun i => if i = 2 then -1 else 1);
    let ψ : QState (Fin 3) := fun _ => (Real.sqrt 3 : ℂ)⁻¹;
    MeasureProb (degenerateDetectionState W 2 1 ψ) (phaseZeroEvent 2 1) = 2 / 3 ∧
      degenerateZeroBranch W 2 1 (by decide) ψ =
        (fun i => if i = 2 then 0 else (Real.sqrt 3 : ℂ)⁻¹) ∧
      phaseReflectionState W 2 1 ψ = phaseReflectionEmbed 2 1
        (fun i => if i = 2 then -(Real.sqrt 3 : ℂ)⁻¹ else (Real.sqrt 3 : ℂ)⁻¹) ∧
      adjointQueryCount (phaseDetectionWord (I := Fin 3) 2 1) = 1 ∧
      adjointGateCount (phaseDetectionWord (I := Fin 3) 2 1) = 4 := by
  (try dsimp only)
  let ψ : QState (Fin 3) := fun _ => (Real.sqrt 3 : ℂ)⁻¹
  have hbranch := degenerateThreeWalk_branch ψ
  have hsum : ψ = ∑ j : Fin 3, ψ j • Ket j := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Ket, smul_eq_mul]
  have hmass : MeasureProb (degenerateDetectionState degenerateThreeWalk 2 1 ψ)
      (phaseZeroEvent 2 1) = 2 / 3 := by
    rw [hsum, degenerate_detection_mass degenerateThreeWalk 2 1 (by decide)
      Ket ψ degenerateThreePhase degenerateThreeWalk_eigen, ← hsum, hbranch,
      norm_toEuclidean_fromVec_sq]
    rw [Fin.sum_univ_three]
    simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
      if_false, if_true, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    norm_num [ψ, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3), inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hWW : degenerateThreeWalk * degenerateThreeWalk = 1 := by
    rw [degenerateThreeWalk, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hi : i = 2 <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hi]
  have hW : degenerateThreeWalk ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    have ha : degenerateThreeWalkᴴ = degenerateThreeWalk := by
      rw [degenerateThreeWalk, Matrix.diagonal_conjTranspose]
      congr 1
      funext i
      by_cases hi : i = 2 <;> simp [hi]
    rw [ha, hWW]
  have href : phaseReflectionState degenerateThreeWalk 2 1 ψ =
      phaseReflectionEmbed 2 1 (fun i => if i = 2 then -ψ i else ψ i) := by
    rw [phase_reflection_involutive_walk_exact _ _ hW hWW]
    congr 1
    funext i
    rw [ApplyGate, degenerateThreeWalk, Matrix.mulVec_diagonal]
    by_cases hi : i = 2 <;> simp [hi]
  have hr := phaseDetectionWord_resources (I := Fin 3) 2 1 (by decide)
  exact ⟨hmass, hbranch, href, by simpa using hr.2.1, by simpa using hr.2.2⟩

end Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
