/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleMeasurement
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.PauliClifford.ExactRank.PauliShadowStatistics
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.ShadowChannel

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {X : Type} [Fintype X] {D : ℕ}

theorem trace_mul_comm_assoc4 (A B C R : Operator D) :
    Matrix.trace (A * B * C * R) = Matrix.trace (C * R * A * B) := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]

theorem psd_spectral {E : Operator D} (hE : E.IsHermitian) (hEps : E.PosSemidef)
    (hD : 0 < D) :
    (∀ {ρ : Operator D}, IsDensityOperator ρ → (Matrix.trace (E * ρ)).re ≤ ‖E‖) ∧
      ∃ (ρ : Operator D) (hρ : IsDensityOperator ρ),
        (Matrix.trace (E * ρ)).re = ‖E‖ := by
  classical
  set U : Operator D := (hE.eigenvectorUnitary : Matrix (Fin D) (Fin D) ℂ) with hUdef
  set ev : Fin D → ℝ := hE.eigenvalues with hevdef
  set d : Fin D → ℂ := fun i => RCLike.ofReal (ev i) with hddef
  have hUmem : U ∈ Matrix.unitaryGroup (Fin D) ℂ := hE.eigenvectorUnitary.2
  have hne : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hU1 : U * Uᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hUmem
    rwa [Matrix.star_eq_conjTranspose] at h
  have hU1' : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hUmem
    rwa [Matrix.star_eq_conjTranspose] at h
  have hevnn : ∀ i, 0 ≤ ev i := fun i => hEps.eigenvalues_nonneg i

  have hdiag : Uᴴ * E * U = Matrix.diagonal d := by
    have h := hE.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] at h
    exact h
  have hE2 : E = U * Matrix.diagonal d * Uᴴ := by
    calc E = (U * Uᴴ) * E * (U * Uᴴ) := by
          rw [hU1, Matrix.one_mul, Matrix.mul_one]
      _ = U * (Uᴴ * E * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal d * Uᴴ := by rw [hdiag]
  obtain ⟨i₀, _, hmax⟩ := Finset.exists_max_image (Finset.univ) ev
    Finset.univ_nonempty
  have hle : ‖Matrix.diagonal d‖ ≤ ev i₀ := by
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (hevnn i₀)).mpr fun i => ?_
    show ‖RCLike.ofReal (ev i)‖ ≤ ev i₀
    rw [RCLike.norm_ofReal, abs_of_nonneg (hevnn i)]
    exact hmax i (Finset.mem_univ i)
  have hge : ev i₀ ≤ ‖Matrix.diagonal d‖ := by
    have h : ‖d i₀‖ ≤ ‖d‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mp (le_refl _) i₀
    rw [show d i₀ = RCLike.ofReal (ev i₀) from rfl, RCLike.norm_ofReal,
      abs_of_nonneg (hevnn i₀)] at h
    exact h.trans_eq (Matrix.l2_opNorm_diagonal d).symm
  have hun1 : ‖U‖ = 1 := l2_norm_unitary_eq_one hUmem
  have hun1' : ‖Uᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hun1
  have hnormE : ‖E‖ = ‖Matrix.diagonal d‖ := by
    refine le_antisymm ?_ ?_
    · calc ‖E‖ = ‖U * Matrix.diagonal d * Uᴴ‖ := by rw [hE2]
        _ = ‖U * (Matrix.diagonal d * Uᴴ)‖ := by rw [Matrix.mul_assoc]
        _ ≤ ‖U‖ * ‖Matrix.diagonal d * Uᴴ‖ :=
            Matrix.l2_opNorm_mul U (Matrix.diagonal d * Uᴴ)
        _ ≤ ‖U‖ * (‖Matrix.diagonal d‖ * ‖Uᴴ‖) :=
            mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul (Matrix.diagonal d) Uᴴ)
              (norm_nonneg _)
        _ = ‖Matrix.diagonal d‖ := by rw [hun1, hun1', one_mul, mul_one]
    · calc ‖Matrix.diagonal d‖ = ‖Uᴴ * E * U‖ := by rw [← hdiag]
        _ = ‖Uᴴ * (E * U)‖ := by rw [Matrix.mul_assoc]
        _ ≤ ‖Uᴴ‖ * ‖E * U‖ := Matrix.l2_opNorm_mul Uᴴ (E * U)
        _ ≤ ‖Uᴴ‖ * (‖E‖ * ‖U‖) :=
            mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul E U) (norm_nonneg _)
        _ = ‖E‖ := by rw [hun1', hun1, one_mul, mul_one]
  have hEq : ‖E‖ = ev i₀ := hnormE.trans (le_antisymm hle hge)

  constructor
  · intro ρ1 hρ1
    have htrE : Matrix.trace (E * ρ1)
        = Matrix.trace (Matrix.diagonal d * (Uᴴ * ρ1 * U)) := by
      calc Matrix.trace (E * ρ1)
          = Matrix.trace (U * Matrix.diagonal d * Uᴴ * ρ1) := by rw [hE2]
        _ = Matrix.trace (Uᴴ * ρ1 * U * Matrix.diagonal d) := trace_mul_comm_assoc4 _ _ _ _
        _ = Matrix.trace (Matrix.diagonal d * (Uᴴ * ρ1 * U)) := Matrix.trace_mul_comm _ _
    have hexp : Matrix.trace (Matrix.diagonal d * (Uᴴ * ρ1 * U))
        = ∑ i, d i * (Uᴴ * ρ1 * U) i i := by
      simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
    have hpsd' : (Uᴴ * ρ1 * U).PosSemidef := hρ1.1.conjTranspose_mul_mul_same U
    have hnn' : ∀ i, 0 ≤ ((Uᴴ * ρ1 * U) i i).re := fun i =>
      (RCLike.nonneg_iff.mp hpsd'.diag_nonneg).1
    have htrρ' : Matrix.trace (Uᴴ * ρ1 * U) = 1 := by
      calc Matrix.trace (Uᴴ * ρ1 * U) = Matrix.trace (U * Uᴴ * ρ1) :=
            Matrix.trace_mul_cycle _ _ _
        _ = Matrix.trace ρ1 := by rw [hU1, Matrix.one_mul]
        _ = 1 := hρ1.2
    have hterm : ∀ i, (d i * (Uᴴ * ρ1 * U) i i).re = ev i * ((Uᴴ * ρ1 * U) i i).re := by
      intro i
      show (RCLike.ofReal (ev i) * (Uᴴ * ρ1 * U) i i).re = _
      simp [Complex.mul_re]
    calc (Matrix.trace (E * ρ1)).re = ∑ i, ev i * ((Uᴴ * ρ1 * U) i i).re := by
          rw [htrE, hexp, Complex.re_sum]
          exact Finset.sum_congr rfl fun i _ => hterm i
      _ ≤ ∑ k : Fin D, ev i₀ * ((Uᴴ * ρ1 * U) k k).re :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ i)) (hnn' i)
      _ = ev i₀ * ∑ i : Fin D, ((Uᴴ * ρ1 * U) i i).re := by rw [Finset.mul_sum]
      _ = ev i₀ * (Matrix.trace (Uᴴ * ρ1 * U)).re := by
          rw [show ∑ i : Fin D, ((Uᴴ * ρ1 * U) i i).re
                = (Matrix.trace (Uᴴ * ρ1 * U)).re from by
              simp only [Matrix.trace, Complex.re_sum, Matrix.diag_apply]]
      _ = ev i₀ * (1 : ℂ).re := by rw [htrρ']
      _ = ev i₀ := by simp
      _ = ‖Matrix.diagonal d‖ := le_antisymm hge hle
      _ = ‖E‖ := hnormE.symm

  · set ψ : QState (Fin D) := ⇑(hE.eigenvectorBasis i₀) with hψdef
    have hvec : E *ᵥ ψ = (ev i₀) • ψ := hE.mulVec_eigenvectorBasis i₀
    have hnormψ : Normalized ψ := by
      show ∑ i, ‖ψ i‖ ^ 2 = 1
      have h2 : ‖(hE.eigenvectorBasis i₀ : EuclideanSpace ℂ (Fin D))‖ ^ 2
          = ∑ i, ‖ψ i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
      rw [← h2, OrthonormalBasis.norm_eq_one _ i₀, one_pow]
    have key : ∀ i : Fin D, ∑ j, E i j * (ψ j * starRingEnd ℂ (ψ i))
        = starRingEnd ℂ (ψ i) * (E *ᵥ ψ) i := by
      intro i
      have hEi : (E *ᵥ ψ) i = ∑ j, E i j * ψ j := rfl
      rw [hEi, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hnormeq : ∀ i : Fin D,
        starRingEnd ℂ (ψ i) * ψ i = ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have htrEψ : Matrix.trace (E * outerProduct ψ)
        = ((ev i₀ : ℝ) : ℂ) * ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, outerProduct_apply]
      have h1 : ∀ i : Fin D, ∑ j : Fin D, E i j * (ψ j * starRingEnd ℂ (ψ i))
          = ((ev i₀ : ℝ) : ℂ) * (starRingEnd ℂ (ψ i) * ψ i) := by
        intro i
        rw [key i, hvec, Pi.smul_apply, Complex.real_smul]
        ring
      simp only [h1, ← Finset.mul_sum, hnormeq]
    refine ⟨outerProduct ψ, isDensityOperator_outerProduct hnormψ, ?_⟩
    have hsum : ∑ i, ‖ψ i‖ ^ 2 = 1 := hnormψ
    rw [htrEψ, ← Complex.ofReal_sum, hsum, Complex.ofReal_one, mul_one,
      Complex.ofReal_re, hEq]

theorem re_trace_psd_density_le {E : Operator D} (hE : E.IsHermitian) (hEps : E.PosSemidef)
    {ρ : Operator D} (hρ : IsDensityOperator ρ) (hD : 0 < D) :
    (Matrix.trace (E * ρ)).re ≤ ‖E‖ :=
  (psd_spectral hE hEps hD).1 hρ

theorem exists_density_re_trace_eq {E : Operator D} (hE : E.IsHermitian)
    (hEps : E.PosSemidef) (hD : 0 < D) :
    ∃ (ρ : Operator D) (hρ : IsDensityOperator ρ),
      (Matrix.trace (E * ρ)).re = ‖E‖ :=
  (psd_spectral hE hEps hD).2

noncomputable def ensembleMeasurementEquiv (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) : Operator D ≃ₗ[ℂ] Operator D :=
  LinearEquiv.ofBijective (ensembleMeasurementMap p U) hM

noncomputable def ensembleSnapshot (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (o : X × Fin D) : Operator D :=
  (ensembleMeasurementEquiv p U hM).symm (ensembleProjector U o)

noncomputable def ensembleStatistic (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (A : Operator D)
    (o : X × Fin D) : ℝ :=
  (Matrix.trace (A * ensembleSnapshot p U hM o)).re

noncomputable def ensembleMomentEffect (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (A : Operator D) : Operator D :=
  ∑ o : X × Fin D, ((p.prob o.1 * (ensembleStatistic p U hM A o) ^ 2 : ℝ) : ℂ)
    • ensembleProjector U o

theorem ensembleMeasurementMap_snapshot (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (o : X × Fin D) :
    ensembleMeasurementMap p U (ensembleSnapshot p U hM o) = ensembleProjector U o :=
  (ensembleMeasurementEquiv p U hM).apply_symm_apply _

theorem ensembleMeasurementMap_conjTranspose (p : FinDist X) (U : X → Operator D)
    (A : Operator D) :
    ensembleMeasurementMap p U (Aᴴ) = (ensembleMeasurementMap p U A)ᴴ := by
  rw [ensembleMeasurementMap_apply, ensembleMeasurementMap_apply,
    Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hstar : Matrix.trace (ensembleProjector U o * Aᴴ)
      = star (Matrix.trace (ensembleProjector U o * A)) := by
    have h := Matrix.trace_conjTranspose (ensembleProjector U o * Aᴴ)
    rw [Matrix.conjTranspose_mul, ensembleProjector_conjTranspose,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm] at h
    rw [h, star_star]
  rw [Matrix.conjTranspose_smul, ensembleProjector_conjTranspose, hstar, star_mul,
    Complex.star_def, Complex.conj_ofReal]
  congr 1
  ring

theorem ensembleMeasurementMap_trace (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) (A : Operator D) :
    Matrix.trace (ensembleMeasurementMap p U A) = Matrix.trace A := by
  have h := ensembleMeasurementMap_trace_adjoint p U A 1
  rw [ensembleMeasurementMap_one p U hU, Matrix.mul_one, Matrix.mul_one] at h
  exact h.symm

theorem ensembleSnapshot_isHermitian (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (o : X × Fin D) :
    (ensembleSnapshot p U hM o).IsHermitian := by
  apply hM.1
  rw [ensembleMeasurementMap_conjTranspose, ensembleMeasurementMap_snapshot,
    ensembleProjector_conjTranspose]

theorem ensembleSnapshot_trace (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (o : X × Fin D) :
    Matrix.trace (ensembleSnapshot p U hM o) = 1 := by
  rw [← ensembleMeasurementMap_trace p U hU, ensembleMeasurementMap_snapshot,
    ensembleProjector_trace U hU o]

theorem ensembleMeasurementMap_rho (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ) {ρ : Operator D}
    (hρ : IsDensityOperator ρ) :
    ensembleMeasurementMap p U ρ
      = ∑ o : X × Fin D, ((ensembleRecordLaw p U hU ρ hρ).prob o : ℂ)
          • ensembleProjector U o := by
  have hPPD : ∀ o : X × Fin D,
      (ensembleProjector U o * ρ * ensembleProjector U o).PosSemidef := by
    intro o
    have h := hρ.1.conjTranspose_mul_mul_same (ensembleProjector U o)
    rwa [ensembleProjector_conjTranspose] at h
  have hreal : ∀ o : X × Fin D, Matrix.trace (ensembleProjector U o * ρ)
      = (((Matrix.trace (ensembleProjector U o * ρ)).re : ℝ) : ℂ) := by
    intro o
    have htr : Matrix.trace (ensembleProjector U o * ρ)
        = Matrix.trace (ensembleProjector U o * ρ * ensembleProjector U o) := by
      rw [Matrix.trace_mul_cycle, ensembleProjector_idem U hU o]
    refine Complex.ext ?_ ?_
    · rfl
    · rw [htr, Complex.ofReal_im]
      exact (RCLike.nonneg_iff.mp (hPPD o).trace_nonneg).2
  rw [ensembleMeasurementMap_apply]
  refine Finset.sum_congr rfl fun o _ => ?_
  have hc : ((p.prob o.1 : ℂ) * Matrix.trace (ensembleProjector U o * ρ))
      = (((ensembleRecordLaw p U hU ρ hρ).prob o : ℝ) : ℂ) := by
    rw [hreal o, (finite_ensemble_actual_kraus_born X D p U hU).2 ρ hρ o,
      Complex.ofReal_mul]
  rw [hc]

theorem ensembleSnapshot_reconstruction (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) :
    ∑ o : X × Fin D, ((ensembleRecordLaw p U hU ρ hρ).prob o : ℂ)
        • ensembleSnapshot p U hM o = ρ := by
  apply hM.1
  simp only [map_sum, map_smul, ensembleMeasurementMap_snapshot]
  exact (ensembleMeasurementMap_rho p U hU hρ).symm

theorem finite_ensemble_inverse_snapshot_reconstruction (X : Type) [Fintype X] (D : ℕ)
    (p : FinDist X) (U : X → Operator D) (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) :
    (∀ o : X × Fin D, (ensembleSnapshot p U hM o).IsHermitian ∧
        Matrix.trace (ensembleSnapshot p U hM o) = 1) ∧
      ∀ (ρ : Operator D) (hρ : IsDensityOperator ρ),
        (∑ o : X × Fin D, ((ensembleRecordLaw p U hU ρ hρ).prob o : ℂ)
          • ensembleSnapshot p U hM o) = ρ :=
  ⟨fun o => ⟨ensembleSnapshot_isHermitian p U hM o,
    ensembleSnapshot_trace p U hU hM o⟩,
    fun ρ hρ => ensembleSnapshot_reconstruction p U hU hM ρ hρ⟩

theorem ensemble_expect_statistic (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (ensembleRecordLaw p U hU ρ hρ).expect (ensembleStatistic p U hM A)
      = (Matrix.trace (A * ρ)).re := by
  show ∑ o : X × Fin D, (ensembleRecordLaw p U hU ρ hρ).prob o
      * (Matrix.trace (A * ensembleSnapshot p U hM o)).re = _
  rw [show (Matrix.trace (A * ρ)).re = (Matrix.trace (A * (∑ o : X × Fin D,
        ((ensembleRecordLaw p U hU ρ hρ).prob o : ℂ)
          • ensembleSnapshot p U hM o))).re from by
      rw [ensembleSnapshot_reconstruction p U hU hM ρ hρ],
    Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem ensemble_expect_statistic_sq (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (ensembleRecordLaw p U hU ρ hρ).expect (fun o => (ensembleStatistic p U hM A o) ^ 2)
      = (Matrix.trace (ensembleMomentEffect p U hM A * ρ)).re := by
  show ∑ o : X × Fin D, (ensembleRecordLaw p U hU ρ hρ).prob o
      * (ensembleStatistic p U hM A o) ^ 2 = _
  rw [ensembleMomentEffect, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    (finite_ensemble_actual_kraus_born X D p U hU).2 ρ hρ o]
  ring

theorem ensembleMomentEffect_posSemidef (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (A : Operator D) :
    (ensembleMomentEffect p U hM A).PosSemidef := by
  rw [ensembleMomentEffect]
  refine Matrix.posSemidef_sum Finset.univ fun o _ => ?_
  exact (ensembleProjector_posSemidef U o).smul
    (RCLike.nonneg_iff.mpr ⟨mul_nonneg (p.nonneg o.1) (sq_nonneg _),
      RCLike.ofReal_im _⟩)

theorem ensembleStatistic_center (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (A : Operator D)
    (o : X × Fin D) :
    ensembleStatistic p U hM (A - (Matrix.trace A / (D : ℂ)) • (1 : Operator D)) o
      = ensembleStatistic p U hM A o - (Matrix.trace A / (D : ℂ)).re := by
  rw [ensembleStatistic, ensembleStatistic, Matrix.sub_mul, Matrix.trace_sub,
    Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul,
    ensembleSnapshot_trace p U hU hM o, mul_one, Complex.sub_re]

theorem ensemble_variance_le (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Operator D) :
    (ensembleRecordLaw p U hU ρ hρ).variance (ensembleStatistic p U hM A)
      ≤ ‖ensembleMomentEffect p U hM
          (A - (Matrix.trace A / (D : ℂ)) • (1 : Operator D))‖ := by
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h1
    · subst h0
      exact absurd (hρ.2.symm.trans (Matrix.trace_eq_zero_of_isEmpty ρ)) (by simp)
    · exact h1
  set q := ensembleRecordLaw p U hU ρ hρ with hq
  set A0 := A - (Matrix.trace A / (D : ℂ)) • (1 : Operator D) with hA0
  set k := (Matrix.trace A / (D : ℂ)).re with hk
  have hshift : ∀ o : X × Fin D, ensembleStatistic p U hM A o
      = ensembleStatistic p U hM A0 o + k := by
    intro o
    rw [ensembleStatistic_center p U hU hM A o, hk]
    ring
  have hmu : q.expect (ensembleStatistic p U hM A)
      = q.expect (ensembleStatistic p U hM A0) + k := by
    show ∑ o : X × Fin D, q.prob o * ensembleStatistic p U hM A o = _
    simp only [hshift, mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, q.sum_one, one_mul]
    rfl
  have hkey : q.expect (fun o => (ensembleStatistic p U hM A o) ^ 2)
      = q.expect (fun o => (ensembleStatistic p U hM A0 o) ^ 2)
        + 2 * k * q.expect (ensembleStatistic p U hM A0) + k ^ 2 := by
    show ∑ o : X × Fin D, q.prob o * (ensembleStatistic p U hM A o) ^ 2 = _
    have hterm : ∀ o : X × Fin D, q.prob o * (ensembleStatistic p U hM A o) ^ 2
        = q.prob o * (ensembleStatistic p U hM A0 o) ^ 2
          + 2 * k * (q.prob o * ensembleStatistic p U hM A0 o)
          + q.prob o * k ^ 2 := by
      intro o
      rw [hshift o, add_sq]
      ring
    simp only [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul, q.sum_one, one_mul]
    rfl
  have hMEps := ensembleMomentEffect_posSemidef p U hM A0
  calc q.variance (ensembleStatistic p U hM A)
      = q.expect (fun o => (ensembleStatistic p U hM A0 o) ^ 2)
        - (q.expect (ensembleStatistic p U hM A0)) ^ 2 := by
        rw [q.variance_eq_expect_sq_sub (ensembleStatistic p U hM A), hkey, hmu]
        ring
    _ ≤ q.expect (fun o => (ensembleStatistic p U hM A0 o) ^ 2) :=
        sub_le_self _ (sq_nonneg _)
    _ = (Matrix.trace (ensembleMomentEffect p U hM A0 * ρ)).re :=
        ensemble_expect_statistic_sq p U hU hM ρ hρ A0
    _ ≤ ‖ensembleMomentEffect p U hM A0‖ :=
        re_trace_psd_density_le hMEps.1 hMEps hρ hD

theorem finite_ensemble_computed_variance_bound (X : Type) [Fintype X] (D : ℕ)
    (p : FinDist X) (U : X → Operator D) (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (ρ A : Operator D)
    (hρ : IsDensityOperator ρ) :
    A.IsHermitian →
    let A0 := A - (Matrix.trace A / (D : ℂ)) • (1 : Operator D);
    (ensembleRecordLaw p U hU ρ hρ).expect (ensembleStatistic p U hM A)
      = (Matrix.trace (A * ρ)).re ∧
      (ensembleRecordLaw p U hU ρ hρ).variance (ensembleStatistic p U hM A)
        ≤ ‖ensembleMomentEffect p U hM A0‖ := by
  intro _hA
  exact ⟨ensemble_expect_statistic p U hU hM ρ hρ A,
    ensemble_variance_le p U hU hM ρ hρ A⟩

theorem finite_ensemble_second_moment_spectral_maximum (X : Type) [Fintype X] (D : ℕ)
    (p : FinDist X) (U : X → Operator D) (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (A : Operator D) :
    0 < D → A.IsHermitian →
    (ensembleMomentEffect p U hM A).PosSemidef ∧
      IsGreatest {v : ℝ | ∃ (ρ : Operator D) (hρ : IsDensityOperator ρ),
        v = (ensembleRecordLaw p U hU ρ hρ).expect
          (fun o => (ensembleStatistic p U hM A o) ^ 2)}
        ‖ensembleMomentEffect p U hM A‖ := by
  intro hD _hA
  have hME := ensembleMomentEffect_posSemidef p U hM A
  obtain ⟨rhostar, hrhostar, hstar⟩ := exists_density_re_trace_eq hME.1 hME hD
  refine ⟨hME, ⟨rhostar, hrhostar, ?_⟩, ?_⟩
  · rw [ensemble_expect_statistic_sq p U hU hM rhostar hrhostar A]
    exact hstar.symm
  · intro v hv
    obtain ⟨ρ, hρ, rfl⟩ := hv
    rw [ensemble_expect_statistic_sq p U hU hM ρ hρ A]
    exact re_trace_psd_density_le hME.1 hME hρ hD

theorem finite_ensemble_same_records_many_observables (X Z : Type) [Fintype X] [Fintype Z]
    (D L K : ℕ) (p : FinDist X) (U : X → Operator D)
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hM : Function.Bijective (ensembleMeasurementMap p U)) (ρ : Operator D)
    (hρ : IsDensityOperator ρ) (A : Z → Operator D) (ε : ℝ) :
    0 < L → 0 < K → 0 < ε →
    (∀ z : Z, (A z).IsHermitian ∧
      4 * ‖ensembleMomentEffect p U hM
        (A z - (Matrix.trace (A z) / (D : ℂ)) • (1 : Operator D))‖
        ≤ (L : ℝ) * ε ^ 2) →
    (∑ ω ∈ Finset.univ.filter
        (fun ω : Fin K → Fin L → X × Fin D => ∃ z : Z,
          ε < |(ensembleRecordLaw p U hU ρ hρ).medianOfMeans
              (ensembleStatistic p U hM (A z)) ω
            - (Matrix.trace (A z * ρ)).re|),
      ∏ k, (ensembleRecordLaw p U hU ρ hρ).probOf (ω k))
      ≤ (Fintype.card Z : ℝ) * 3 ^ (K / 2) / 2 ^ K := by
  intro hL hK hε hA
  set q := ensembleRecordLaw p U hU ρ hρ with hq
  set r : FinDist (Fin L → X × Fin D) :=
    ⟨q.probOf, fun ω => Finset.prod_nonneg fun i _ => q.nonneg _, q.sum_probOf L⟩ with hrdef
  have hconc : ∀ z : Z,
      FinDist.probEvent r (fun ω : Fin K → Fin L → X × Fin D =>
        ε < |q.medianOfMeans (ensembleStatistic p U hM (A z)) ω
          - (Matrix.trace (A z * ρ)).re|) ≤ 3 ^ (K / 2) / 2 ^ K := by
    intro z
    have h4 : 4 * q.variance (ensembleStatistic p U hM (A z)) ≤ (L : ℝ) * ε ^ 2 :=
      le_trans
        (mul_le_mul_of_nonneg_left (ensemble_variance_le p U hU hM ρ hρ (A z))
          (by norm_num)) ((hA z).2)
    have h1 := q.median_of_means_concentration (ensembleStatistic p U hM (A z)) hL hK ε hε h4
    rw [ensemble_expect_statistic p U hU hM ρ hρ (A z)] at h1
    exact h1
  have hub := FinDist.union_bound (X := Fin L → X × Fin D) (L := K)
    (M := Fintype.card Z) r
    (fun (i : Fin (Fintype.card Z)) (ω : Fin K → Fin L → X × Fin D) =>
      ε < |q.medianOfMeans (ensembleStatistic p U hM (A ((Fintype.equivFin Z).symm i))) ω
        - (Matrix.trace (A ((Fintype.equivFin Z).symm i) * ρ)).re|)
  show FinDist.probEvent r (fun ω : Fin K → Fin L → X × Fin D =>
      ∃ z : Z, ε < |q.medianOfMeans (ensembleStatistic p U hM (A z)) ω
        - (Matrix.trace (A z * ρ)).re|) ≤ _
  rw [show (FinDist.probEvent r (fun ω : Fin K → Fin L → X × Fin D =>
      ∃ z : Z, ε < |q.medianOfMeans (ensembleStatistic p U hM (A z)) ω
        - (Matrix.trace (A z * ρ)).re|))
    = FinDist.probEvent r (fun ω : Fin K → Fin L → X × Fin D =>
      ∃ i : Fin (Fintype.card Z),
        ε < |q.medianOfMeans (ensembleStatistic p U hM (A ((Fintype.equivFin Z).symm i))) ω
          - (Matrix.trace (A ((Fintype.equivFin Z).symm i) * ρ)).re|) from by
    unfold FinDist.probEvent
    exact Finset.sum_congr (Finset.filter_congr fun ω _ =>
      ((Fintype.equivFin Z).symm.surjective.exists)) fun _ _ => rfl]
  refine hub.trans ?_
  calc (∑ i : Fin (Fintype.card Z), FinDist.probEvent r
        (fun ω : Fin K → Fin L → X × Fin D =>
          ε < |q.medianOfMeans (ensembleStatistic p U hM (A ((Fintype.equivFin Z).symm i))) ω
            - (Matrix.trace (A ((Fintype.equivFin Z).symm i) * ρ)).re|))
      ≤ ∑ i : Fin (Fintype.card Z), 3 ^ (K / 2) / 2 ^ K :=
        Finset.sum_le_sum fun i _ => hconc ((Fintype.equivFin Z).symm i)
    _ = (Fintype.card Z : ℝ) * 3 ^ (K / 2) / 2 ^ K := by
        simp
        ring

noncomputable def ensembleStatisticSumCounted {X : Type} (f : X → ℝ) : List X → ℝ × ℕ
  | [] => (0,0)
  | x::xs => let s := ensembleStatisticSumCounted f xs; (f x+s.1,s.2+1)

theorem ensembleStatisticSumCounted_spec {X : Type} (f : X → ℝ) (xs : List X) :
    (ensembleStatisticSumCounted f xs).1 = (xs.map f).sum ∧ (ensembleStatisticSumCounted f xs).2 = xs.length := by
  induction xs with
  | nil => simp [ensembleStatisticSumCounted]
  | cons x xs ih => simp [ensembleStatisticSumCounted, ih]

noncomputable def ensembleMedianOfMeansCounted {X : Type} (f : X → ℝ) {L K : ℕ}
    (ω : Fin K → Fin L → X) : ℝ × ℕ × ℕ :=
  let groups := List.ofFn fun k =>
    let s := ensembleStatisticSumCounted f (List.ofFn (ω k)); (s.1/(L:ℝ),s.2)
  let sort := insertionSortCounted (groups.map Prod.fst)
  (sort.1.getD (K/2) 0,(groups.map Prod.snd).sum,sort.2)

theorem ensembleMedianOfMeansCounted_spec {X : Type} [Fintype X] [DecidableEq X]
    (q : FinDist X) (f : X → ℝ) {L K : ℕ} (ω : Fin K → Fin L → X) :
    (ensembleMedianOfMeansCounted f ω).1 = q.medianOfMeans f ω ∧
    (ensembleMedianOfMeansCounted f ω).2.1 = K*L ∧ (ensembleMedianOfMeansCounted f ω).2.2 ≤ K*K := by
  let values := List.ofFn fun k => FinDist.avg f (ω k)
  have hvalues : (List.ofFn (fun k =>
      let s :=
          ensembleStatisticSumCounted f (List.ofFn (ω k));
          (s.1/(L:ℝ),s.2))).map Prod.fst = values := by
    simp [values, List.map_ofFn, (ensembleStatisticSumCounted_spec _ _).1, List.sum_ofFn,
        FinDist.avg, Function.comp_def]
  have hsort : (insertionSortCounted values).1 = values.mergeSort (· ≤ ·) :=
    ((insertionSortCounted_perm values).trans (List.mergeSort_perm values (· ≤ ·)).symm).eq_of_sortedLE
      (insertionSortCounted_sorted values) (List.sortedLE_mergeSort (l := values))
  refine ⟨?_,?_,?_⟩
  · change (insertionSortCounted _).1.getD (K/2) 0 = _
    rw [hvalues, hsort]
    rfl
  · simp [ensembleMedianOfMeansCounted, (ensembleStatisticSumCounted_spec _ _).2, List.map_ofFn,
      List.sum_ofFn]
  · change (insertionSortCounted _).2 ≤ _
    rw [hvalues]
    simpa [values] using insertionSortCounted_cost_le values

theorem ensemble_shared_records_statistic_work {Z : Type} [Fintype Z]
    (p : FinDist X) (U : X → Operator D)
    (hM : Function.Bijective (ensembleMeasurementMap p U))
    (hU : ∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (A : Z → Operator D)
    {L K : ℕ} (ω : Fin K → Fin L → X × Fin D) :
    (∀ z, (ensembleMedianOfMeansCounted (ensembleStatistic p U hM (A z)) ω).1 =
      (ensembleRecordLaw p U hU ρ hρ).medianOfMeans (ensembleStatistic p U hM (A z)) ω) ∧
    (∑ z, (ensembleMedianOfMeansCounted (ensembleStatistic p U hM (A z)) ω).2.1) =
      Fintype.card Z*(K*L) ∧
    (∑ z, (ensembleMedianOfMeansCounted (ensembleStatistic p U hM (A z)) ω).2.2) ≤
      Fintype.card Z*(K*K) := by
  have h z := ensembleMedianOfMeansCounted_spec (ensembleRecordLaw p U hU ρ hρ)
    (ensembleStatistic p U hM (A z)) ω
  refine ⟨fun z => (h z).1, ?_, ?_⟩
  · simp [(h _).2.1]
  · calc
      _ ≤ ∑ _z : Z, K*K := Finset.sum_le_sum fun z _ => (h z).2.2
      _ = _ := by simp

end Qatlib.Concepts.ShadowModels.ShadowChannel
