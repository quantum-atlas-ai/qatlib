/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSingleCU
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.PhysicalMidpoint
import Qatlib.Concepts.OperatorAccess.EncodedAccess
import Qatlib.Concepts.InstrumentCore.PovmBridge.MeasurementNetwork
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open MeasureTheory
open scoped Interval ComplexOrder

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorHistoryBorn

variable {A E I C : Type} [Fintype A] [DecidableEq A]
  [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [Fintype C] [DecidableEq C]

theorem singleton_effect (U : Matrix (A × I) (A × I) ℂ) (a : A) :
    outcomeEffect U a {a} =
      (compress (encodingFiber a) U (encodingFiber a))ᴴ *
        compress (encodingFiber a) U (encodingFiber a) := by
  have hc : outcomeKraus U a a = compress (encodingFiber a) U (encodingFiber a) := by
    ext i j
    rw [compress_encodingFiber_eq]
    rfl
  simp only [outcomeEffect, Finset.sum_singleton, hc]

theorem projector_block_born (Pi : Matrix I I ℂ)
    (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (henc : ProjectedUnitaryEncoding Pi U (encodingFiber a) (encodingFiber a))
    (hstar : Piᴴ = Pi) (hsq : Pi * Pi = Pi) (v : QState I) :
    MeasureProb (U *ᵥ (encodingFiber a *ᵥ v)) {x | x.1 = a} =
      (Inner v (Pi *ᵥ v)).re := by
  have h := outcomeEffect_born U a {a} v
  simpa only [Finset.mem_singleton, singleton_effect, henc.encoded, hstar, hsq] using! h

noncomputable def idealOutput (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (V : C → Matrix I I ℂ) (psi : QState (E × I)) : QState (C × (E × (A × I))) :=
  fun x => Uniform C x.1 *
    (U *ᵥ (encodingFiber a *ᵥ (V x.1 *ᵥ (fun i => psi (x.2.1,i))))) x.2.2

theorem purified_expectation (psi : QState (E × I)) (K : Matrix I I ℂ) :
    Matrix.trace (purifiedDensity psi * K) =
      ∑ r : E, Inner (fun i => psi (r,i)) (K *ᵥ (fun i => psi (r,i))) := by
  rw [Matrix.trace_mul_comm, purifiedDensity_sum, Matrix.mul_sum, Matrix.trace_sum]
  simp only [Qatlib.Concepts.InstrumentCore.PovmBridge.trace_mul_outerProduct]

omit [DecidableEq I] in

theorem evolution_quadratic (V K : Matrix I I ℂ) (v : QState I) :
    Inner (V *ᵥ v) (K *ᵥ (V *ᵥ v)) = Inner v ((Vᴴ * K * V) *ᵥ v) := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

omit [DecidableEq C] in

theorem idealOutput_born (Pi : Matrix I I ℂ)
    (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (henc : ProjectedUnitaryEncoding Pi U (encodingFiber a) (encodingFiber a))
    (hstar : Piᴴ = Pi) (hsq : Pi * Pi = Pi)
    (V : C → Matrix I I ℂ) (psi : QState (E × I)) :
    MeasureProb (idealOutput U a V psi) {x | x.2.2.1 = a} =
      (Fintype.card C : ℝ)⁻¹ * ∑ c : C,
        (Matrix.trace (purifiedDensity psi * ((V c)ᴴ * Pi * V c))).re := by
  have hw (c : C) : ‖Uniform C c‖ ^ 2 = (Fintype.card C : ℝ)⁻¹ :=
    by
      simp only [Uniform, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hmass (c : C) (r : E) :
      (∑ b : A, ∑ i : I, if b = a then
        ‖Uniform C c * (U *ᵥ (encodingFiber a *ᵥ
          (V c *ᵥ (fun j => psi (r,j))))) (b,i)‖ ^ 2 else 0) =
        (Fintype.card C : ℝ)⁻¹ *
          (Inner (fun i => psi (r,i))
            (((V c)ᴴ * Pi * V c) *ᵥ (fun i => psi (r,i)))).re := by
    simp only [norm_mul, mul_pow, hw]
    have hb := projector_block_born Pi U a henc hstar hsq
      (V c *ᵥ (fun i => psi (r,i)))
    rw [evolution_quadratic] at hb
    simpa only [MeasureProb, BornProb, Finset.sum_filter, Fintype.sum_prod_type,
      Finset.mul_sum, mul_ite, mul_zero] using!
      congrArg (fun z : ℝ => (Fintype.card C : ℝ)⁻¹ * z) hb
  simp only [MeasureProb, BornProb, Finset.sum_filter, Fintype.sum_prod_type,
    idealOutput]
  simp_rw [hmass]
  simp only [← Finset.mul_sum, purified_expectation, Complex.re_sum]

omit [DecidableEq E] in

theorem idealOutput_normalized [Nonempty C]
    (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (hU : U ∈ Matrix.unitaryGroup (A × I) ℂ)
    (V : C → Matrix I I ℂ) (hV : ∀ c, V c ∈ Matrix.unitaryGroup I ℂ)
    (psi : QState (E × I)) (hpsi : Normalized psi) :
    Normalized (idealOutput U a V psi) := by
  have hu : IsIsometry U := by simpa only [IsIsometry, Matrix.star_eq_conjTranspose] using! hU.1
  have hv (c : C) : IsIsometry (V c) := by
    simpa only [IsIsometry, Matrix.star_eq_conjTranspose] using! (hV c).1
  have hs (c : C) (r : E) :
      (∑ b : A, ∑ i : I, ‖(U *ᵥ (encodingFiber a *ᵥ
        (V c *ᵥ (fun j => psi (r,j))))) (b,i)‖^2) =
        ∑ i : I, ‖psi (r,i)‖^2 := by
    have he := congrArg (fun z : ℝ => z^2)
      ((isometry_mulVec_norm hu (encodingFiber a *ᵥ (V c *ᵥ (fun j => psi (r,j))))).trans
        ((isometry_mulVec_norm (encodingFiber_isIsometry a) (V c *ᵥ (fun j => psi (r,j)))).trans
          (isometry_mulVec_norm (hv c) (fun j => psi (r,j)))))
    simpa only [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type] using! he
  change (∑ x : C × (E × (A × I)), ‖idealOutput U a V psi x‖^2) = 1
  simp only [idealOutput, norm_mul, mul_pow, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hs]
  have hp : (∑ r : E, ∑ i : I, ‖psi (r,i)‖^2) = 1 := by
    simpa only [Normalized, Fintype.sum_prod_type] using! hpsi
  rw [hp]
  simpa only [mul_one] using! (normalized_uniform (I := C) Fintype.card_pos)

theorem whole_event_error [Nonempty C]
    (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (hU : U ∈ Matrix.unitaryGroup (A × I) ℂ)
    (V : C → Matrix I I ℂ) (hV : ∀ c, V c ∈ Matrix.unitaryGroup I ℂ)
    (psi : QState (E × I)) (hpsi : Normalized psi)
    (actual : QState (C × (E × (A × I)))) (hactual : Normalized actual)
    (delta : ℝ)
    (herr : ‖toEuclidean_fromVec (actual - idealOutput U a V psi)‖ ≤ delta) :
    |MeasureProb actual {x | x.2.2.1 = a} -
      MeasureProb (idealOutput U a V psi) {x | x.2.2.1 = a}| ≤ 2*delta :=
  (measureProb_sub_le_two_mul_l2 actual (idealOutput U a V psi) _ hactual
    (idealOutput_normalized U a hU V hV psi hpsi)).trans
      (mul_le_mul_of_nonneg_left herr (by norm_num))

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorHistoryBorn

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorHistoryBorn

variable {I E A : Type} [Fintype I] [DecidableEq I]
  [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]

theorem midpoint_born_quadrature (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (Pi : Matrix I I ℂ) (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (henc : ProjectedUnitaryEncoding Pi U (encodingFiber a) (encodingFiber a))
    (hstar : Piᴴ = Pi) (hsq : Pi * Pi = Pi)
    (psi : QState (E × I)) (hpsi : Normalized psi)
    (alpha T : ℝ) (halpha : ‖H‖ ≤ alpha) (hT : 0 ≤ T)
    (N : ℕ) (hN : 0 < N) :
    |(∫ t in (0:ℝ)..T, physicalReadout H Pi (purifiedDensity psi) t) -
      T * MeasureProb (idealOutput U a
        (fun j : Fin N => HamiltonianEvolution H
          (T * Clock.midpoint N j)) psi) {x | x.2.2.1 = a}| ≤
      alpha * ‖Pi‖ * T^2 / (2*N) := by
  have htr : Matrix.trace (purifiedDensity psi) = 1 := by
    rw [purifiedDensity_trace]
    change (∑ x : E × I, ‖psi x‖^2) = 1 at hpsi
    exact_mod_cast hpsi
  have hb : MeasureProb (idealOutput U a
        (fun j : Fin N => HamiltonianEvolution H
          (T * Clock.midpoint N j)) psi) {x | x.2.2.1 = a} =
      Clock.midpointMean N
        (fun u => physicalReadout H Pi (purifiedDensity psi) (T*u)) := by
    rw [idealOutput_born Pi U a henc hstar hsq]
    simp only [Clock.midpointMean, Fintype.card_fin, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [physicalReadout_heisenberg, Matrix.trace_mul_comm]
  rw [hb]
  exact midpoint_quadrature H hH Pi (purifiedDensity psi)
    (purifiedDensity_posSemidef psi) htr alpha T halpha hT N hN

theorem approximate_history_integral_error (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (Pi : Matrix I I ℂ) (U : Matrix (A × I) (A × I) ℂ) (a : A)
    (henc : ProjectedUnitaryEncoding Pi U (encodingFiber a) (encodingFiber a))
    (hstar : Piᴴ = Pi) (hsq : Pi * Pi = Pi)
    (psi : QState (E × I)) (hpsi : Normalized psi)
    (alpha T : ℝ) (halpha : ‖H‖ ≤ alpha) (hT : 0 ≤ T)
    (N : ℕ) (hN : 0 < N)
    (actual : QState (Fin N × (E × (A × I)))) (hactual : Normalized actual)
    (delta : ℝ)
    (herr : ‖toEuclidean_fromVec (actual - idealOutput U a
      (fun j : Fin N => HamiltonianEvolution H
        (T * Clock.midpoint N j)) psi)‖ ≤ delta) :
    |(∫ t in (0:ℝ)..T, physicalReadout H Pi (purifiedDensity psi) t) -
      T * MeasureProb actual {x | x.2.2.1 = a}| ≤
      alpha * ‖Pi‖ * T^2 / (2*N) + 2*T*delta := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let ideal := idealOutput U a (fun j : Fin N => HamiltonianEvolution H
    (T * Clock.midpoint N j)) psi
  let S : Finset (Fin N × (E × (A × I))) := {x | x.2.2.1 = a}
  have he := whole_event_error U a henc.unitary
    (fun j : Fin N => HamiltonianEvolution H (T * Clock.midpoint N j))
    (fun j => hamiltonianEvolution_unitary hH _) psi hpsi actual hactual delta herr
  have hq := midpoint_born_quadrature H hH Pi U a henc hstar hsq psi hpsi
    alpha T halpha hT N hN
  have hm : |T * MeasureProb ideal S - T * MeasureProb actual S| ≤ 2*T*delta := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hT, abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left he hT).trans_eq (by ring)
  exact (abs_sub_le _ (T * MeasureProb ideal S) _).trans
    ((add_le_add hq hm).trans_eq (by ring))

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorHistoryBorn
