/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.ActualDiagonalization
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder RealInnerProductSpace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Papers.KoopmanSim26.SpectralRep

namespace Qatlib.Papers.QGradient20.PhaseOracle
variable {I : Type} [Fintype I] [DecidableEq I]

def phaseEvolution (D : Matrix I I ℂ) (τ : ℝ) : Matrix I I ℂ := HamiltonianEvolution D (2*Real.pi*τ)

theorem phaseEvolution_unitary (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ) :
    phaseEvolution D τ∈Matrix.unitaryGroup I ℂ := hamiltonianEvolution_unitary hD _

theorem phaseEvolution_power (D : Matrix I I ℂ) (τ : ℝ) (j : ℕ) :
    phaseEvolution D τ^j=HamiltonianEvolution D (2*Real.pi*(j:ℝ)*τ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ,ih,phaseEvolution,← hamiltonianEvolution_add]
    congr 1
    push_cast
    ring

theorem controlledPowers_actual_evolution (D : Matrix I I ℂ) (τ : ℝ) (M : ℕ)
    (p q : Fin M×I) :
    ControlledPowers (phaseEvolution D τ) M p q=
      if p.1=q.1 then HamiltonianEvolution D (2*Real.pi*(q.1.val:ℝ)*τ) p.2 q.2 else 0 := by
  simp only [ControlledPowers,Matrix.of_apply,phaseEvolution_power]

theorem actual_eigenbasis_orthonormal (D : Matrix I I ℂ) (hD : D.IsHermitian) :
    ∀ j k,Inner (hD.eigenvectorBasis j : I→ℂ) (hD.eigenvectorBasis k : I→ℂ)=if j=k then 1 else 0 := by
  intro j k
  rw [← inner_euclidean_fromVec]
  exact orthonormal_iff_ite.mp hD.eigenvectorBasis.orthonormal j k

theorem phaseEvolution_eigen (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ) (j : I) :
    ApplyGate (phaseEvolution D τ) (hD.eigenvectorBasis j : I→ℂ)=
      Complex.exp (2*Real.pi*Complex.I*((-τ*hD.eigenvalues j:ℝ):ℂ))•(hD.eigenvectorBasis j : I→ℂ) := by
  unfold phaseEvolution HamiltonianEvolution ApplyGate
  rw [hermitian_exp_spectral D hD]
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,← Matrix.star_eq_conjTranspose,
    hD.star_eigenvectorUnitary_mulVec]
  have hd : diagonal (fun k => Complex.exp ((-Complex.I*((2*Real.pi*τ:ℝ):ℂ))*(hD.eigenvalues k:ℂ)))*ᵥPi.single j 1=
      Complex.exp ((-Complex.I*((2*Real.pi*τ:ℝ):ℂ))*(hD.eigenvalues j:ℂ))•Pi.single j 1 := by
    ext i
    by_cases hi : i=j
    · subst i; simp
    · simp [Matrix.mulVec_diagonal,hi]
  rw [hd,Matrix.mulVec_smul,hD.eigenvectorUnitary_mulVec]
  congr 2
  push_cast
  ring

theorem actual_eigen_qpe_packet (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ) (M : ℕ) (j : I) :
    qpeOutput M (phaseEvolution D τ) (hD.eigenvectorBasis j : I→ℂ)=
      TensorState (qpeKernel M (-τ*hD.eigenvalues j)) (hD.eigenvectorBasis j : I→ℂ) :=
  qpeOutput_eigen M _ _ _ (phaseEvolution_eigen D hD τ j)

theorem actual_spectral_Born (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ)
    (M : ℕ) (hM : 0<M) (c : I→ℂ) (z : Fin M) :
    MarginalProbLeft (qpeOutput M (phaseEvolution D τ) (∑ j,c j•(hD.eigenvectorBasis j : I→ℂ))) {z}=
      ∑ j,‖c j‖^2*‖qpeKernel M (-τ*hD.eigenvalues j) z‖^2 :=
  (offgrid_qpe_eigen_and_spectral_law M (phaseEvolution D τ) 0 0 hM).2 I
    (fun j => (hD.eigenvectorBasis j : I→ℂ)) c (fun j => -τ*hD.eigenvalues j)
    (fun j k => by
      by_cases h : j=k
      · simpa [h] using actual_eigenbasis_orthonormal D hD j k
      · simpa [h] using actual_eigenbasis_orthonormal D hD j k)
    (phaseEvolution_eigen D hD τ) z

theorem actual_ongrid_readout (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ)
    (M : ℕ) (hM : 0<M) (j : I) (k : Fin M)
    (hgrid : Complex.exp (2*Real.pi*Complex.I*((-τ*hD.eigenvalues j:ℝ):ℂ))=primRoot M^(k.val:ℤ)) :
    qpeOutput M (phaseEvolution D τ) (hD.eigenvectorBasis j : I→ℂ)=
      TensorState (Ket k) (hD.eigenvectorBasis j : I→ℂ) ∧
    MarginalProbLeft (qpeOutput M (phaseEvolution D τ) (hD.eigenvectorBasis j : I→ℂ)) {k}=1 := by
  have hn : Normalized (hD.eigenvectorBasis j : I→ℂ) := by
    rw [normalized_iff_inner_self]
    simpa using actual_eigenbasis_orthonormal D hD j j
  exact qpe_exact_readout (U:=phaseEvolution D τ) hM hn k (by
    change ApplyGate (phaseEvolution D τ) (hD.eigenvectorBasis j : I→ℂ)=_
    rw [phaseEvolution_eigen,hgrid])

theorem actual_counted_run (D : Matrix I I ℂ) (τ : ℝ) (M : ℕ) (hM : 0<M) (ψ : I→ℂ) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (phaseEvolution D τ)))
      (countedPhaseCircuit M)
      (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) ψ))=
        (fun p => if p.2.1 then 0 else qpeOutput M (phaseEvolution D τ) ψ (p.1,p.2.2)) ∧
    QueryCount (countedPhaseCircuit (I:=I) M)=M-1 ∧
    GateCount (countedPhaseCircuit (I:=I) M)=2*(M-1)+2 ∧
    IsUnitaryCircuit (countedPhaseCircuit (I:=I) M) :=
  counted_offgrid_qpe_clean_flag M hM (phaseEvolution D τ) ψ

def phaseTime (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (τ : ℝ) : ℝ :=
  (QueryCount (countedPhaseCircuit (I:=I) M):ℝ)*|τ|

theorem phaseTime_eq (M : ℕ) (hM : 0<M) (τ : ℝ) : phaseTime I M τ=((M-1:ℕ):ℝ)*|τ| := by
  have h := (counted_offgrid_qpe_clean_flag (I:=I) M hM (1 : Matrix I I ℂ) 0).2.1
  simp only [phaseTime,h]

def physicalTime (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (τ : ℝ) : ℝ :=
  (QueryCount (countedPhaseCircuit (I:=I) M):ℝ)*|2*Real.pi*τ|

theorem physicalTime_eq (M : ℕ) (hM : 0<M) (τ : ℝ) :
    physicalTime I M τ=2*Real.pi*((M-1:ℕ):ℝ)*|τ| := by
  have h := (counted_offgrid_qpe_clean_flag (I:=I) M hM (1 : Matrix I I ℂ) 0).2.1
  simp only [physicalTime,h,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos (by norm_num : (0:ℝ)<2)]
  ring

end Qatlib.Papers.QGradient20.PhaseOracle
