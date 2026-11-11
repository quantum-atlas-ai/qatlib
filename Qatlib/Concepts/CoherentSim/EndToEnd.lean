/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.TaylorEncoding.LogarithmicTaylorSimulation
import Qatlib.Concepts.SpectralReadout.PhaseReadout.CleanSubroutinePhaseReadout
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator

/-!
# Taylor simulation with spectral phase readout

`logTaylorQPEPreparedWord` combines a prepared data state with clean phase estimation using
logarithmic Taylor simulation. The spectral event and energy-window bounds include explicit
query and gate counts and a dyadic simulation error, combining the method of
[BerryEtAl2015Taylor] with phase estimation [NielsenChuang2010].

## Main statements

* `log_taylor_actual_spectral_qpe_and_cost`: Spectral event probabilities with resource counts.
* `log_taylor_actual_energy_window`: A phase-window success bound for a prepared eigenstate.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CleanQPEBands
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.TaylorBounds
open Qatlib.Concepts.CoherentSim.TaylorEncoding

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
namespace Qatlib.Concepts.CoherentSim.EndToEnd
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The simulation precision obtained by adding a binary logarithmic phase-estimation overhead
to `k`. -/
def logTaylorQPEPrecision (M k : ℕ) : ℕ := k+Nat.clog 2 (max 1 (2*(M-1)))

/-- The operator applying `B` to the data register and the identity to the Taylor ancillary
registers. -/
noncomputable def logTaylorDataGate {D : ℕ} (K : ℕ) (B : Operator D) :=
  TensorGate (1 : Matrix (TaylorWordLabel J K) (TaylorWordLabel J K) ℂ)
    (TensorGate (1 : Matrix Bool Bool ℂ) (TensorGate (1 : Matrix J J ℂ) B))

/-- The clean phase-estimation word for logarithmic Taylor simulation, with an initial
data-preparation gate. -/
noncomputable def logTaylorQPEPreparedWord {D : ℕ} (h : J → ℝ) (j0 : J)
    (t : ℝ) (Lambda T M k : ℕ) (B : Operator D) :=
  let p := logTaylorQPEPrecision M k
  let K := logTaylorCutoff (taylorSegments Lambda T) p
  cleanQPEWord M (logTaylorSimulationWord (D := D) h j0 t Lambda T p) ++
    [.gate (TensorGate (1 : Operator M)
      (TensorGate (1 : Matrix Bool Bool ℂ) (logTaylorDataGate (J := J) K B)))]

/-- The output vector of the prepared Taylor phase-estimation circuit on the basis state indexed
by `j`. -/
noncomputable def logTaylorQPEOutput {D : ℕ} (h : J → ℝ) (U : J → Operator D) (j0 : J)
    (t : ℝ) (Lambda T M k : ℕ) (hM : 0 < M) (B : Operator D) (j : Fin D) :=
  let p := logTaylorQPEPrecision M k
  let K := logTaylorCutoff (taylorSegments Lambda T) p
  evaluate (TensorGate (1 : Operator M) (controlOracle (taylorQuery U K)))
    (logTaylorQPEPreparedWord h j0 t Lambda T M k B) *ᵥ
    cleanQPEInput M hM (taylorFrame j0 K *ᵥ Ket j)

/-- A unitary spectral decomposition of `A` diagonalizes its Hamiltonian evolution, with
diagonal entries `exp (-I * t * eig i)`. -/
private theorem logTaylor_evolution_spectral (D : ℕ) (A V : Operator D) (eig : Fin D → ℝ)
    (t : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : A = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) :
    hamiltonianEvolution A t =
      V * Matrix.diagonal (fun i => Complex.exp (-Complex.I * (t : ℂ) * (eig i : ℂ))) * Vᴴ := by
  let W : unitary (Operator D) := ⟨V, hV⟩
  let f := Unitary.conjStarAlgAut ℂ (Operator D) W
  let B := Matrix.diagonal (fun i => -Complex.I * (t : ℂ) * (eig i : ℂ))
  letI : NormedAlgebra ℚ (Operator D) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hm := NormedSpace.map_exp f f.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional B
  have he : f B = (-Complex.I * (t : ℂ)) • A := by
    rw [hs]
    simp only [f, Unitary.conjStarAlgAut_apply, B]
    change V * Matrix.diagonal (fun i => -Complex.I * (t : ℂ) * (eig i : ℂ)) * Vᴴ = _
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.diagonal_smul]
    rfl
  rw [he] at hm
  unfold hamiltonianEvolution
  refine hm.symm.trans ?_
  change V * NormedSpace.exp B * Vᴴ = _
  rw [Matrix.exp_diagonal]
  apply congrArg (fun B : Operator D => V * B * Vᴴ)
  apply congrArg (Matrix.diagonal : (Fin D → ℂ) → Operator D)
  funext i
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]

/-- Hamiltonian evolution multiplies each supplied spectral eigenvector by the phase with angle
`-t * eig i`. -/
private theorem logTaylor_eigen (D : ℕ) (A V : Operator D) (eig : Fin D → ℝ)
    (t : ℝ) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : A = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) (i : Fin D) :
    hamiltonianEvolution A t *ᵥ (V *ᵥ Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * ((-t * eig i / (2 * Real.pi) : ℝ) : ℂ)) •
        (V *ᵥ Ket i) := by
  have hVV : Vᴴ * V = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hV
  have huv : hamiltonianEvolution A t * V = V * Matrix.diagonal
    (fun i => Complex.exp (-Complex.I * (t : ℂ) * (eig i : ℂ))) := by
    rw [logTaylor_evolution_spectral D A V eig t hV hs, Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hp : -Complex.I * (t : ℂ) * (eig i : ℂ) =
      2 * Real.pi * Complex.I * ((-t * eig i / (2 * Real.pi) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [Matrix.mulVec_mulVec, huv, ← Matrix.mulVec_mulVec]
  have hd : Matrix.diagonal (fun j => Complex.exp (-Complex.I * (t : ℂ) * (eig j : ℂ))) *ᵥ Ket i =
      Complex.exp (-Complex.I * (t : ℂ) * (eig i : ℂ)) • Ket i := by
    funext j
    by_cases hj : j = i <;> simp [Matrix.mulVec, dotProduct, Ket, hj]
  rw [hd, Matrix.mulVec_smul, hp]

/-- The chosen simulation precision bounds the accumulated phase-estimation perturbation by
`2⁻ᵏ`. -/
theorem logTaylor_qpe_budget (M k : ℕ) :
    2 * ((M-1 : ℕ) : ℝ) * (1/2:ℝ)^logTaylorQPEPrecision M k ≤ (1/2:ℝ)^k := by
  have hb : (2 * ((M-1 : ℕ) : ℝ)) ≤ (2:ℝ)^Nat.clog 2 (max 1 (2*(M-1))) := by
    exact_mod_cast (le_max_right 1 (2*(M-1))).trans
      (Nat.le_pow_clog (by norm_num) (max 1 (2*(M-1))))
  have hp : (2:ℝ)^Nat.clog 2 (max 1 (2*(M-1))) *
      (1/2:ℝ)^Nat.clog 2 (max 1 (2*(M-1))) = 1 := by
    rw [← mul_pow]; norm_num
  have h := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (1/2:ℝ)^Nat.clog 2 (max 1 (2*(M-1))) by positivity)
  rw [hp] at h
  dsimp [logTaylorQPEPrecision]
  rw [pow_add]
  nlinarith [mul_le_mul_of_nonneg_left h (show 0 ≤ (1/2:ℝ)^k by positivity)]

/-- Applying the lifted data operator to the Taylor frame equals embedding after applying `B`. -/
theorem logTaylor_data_frame {D : ℕ} (K : ℕ) (B : Operator D) (j0 : J) :
    logTaylorDataGate (J := J) K B * taylorFrame (I := Fin D) j0 K =
      taylorFrame (I := Fin D) j0 K * B := by
  ext ⟨w,b,a,i⟩ j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  by_cases hw : w = taylorEmptyLabel J K <;> by_cases hb : b = false <;> by_cases ha : a = j0 <;>
    simp [hw, hb, ha, eq_comm, logTaylorDataGate, tensorGate_apply,
      taylorFrame, Prod.mk.injEq]
  simp_all only [eq_comm, false_and, if_false, Finset.sum_const_zero]

/-- Lifting a unitary data operator by identity factors preserves unitarity. -/
theorem logTaylor_data_unitary {D : ℕ} (K : ℕ) (B : Operator D)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    logTaylorDataGate (J := J) K B ∈ Matrix.unitaryGroup _ ℂ :=
  tensorGate_unitary (Submonoid.one_mem _) (tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (Submonoid.one_mem _) hB))

/-- Membership in the matrix unitary group is independent of the chosen decidable equality
instance. -/
private theorem logTaylor_unitary_decidableEq {X : Type} [Fintype X]
    {d e : DecidableEq X} {A : Matrix X X ℂ}
    (h : letI := d; A ∈ Matrix.unitaryGroup X ℂ) :
    letI := e; A ∈ Matrix.unitaryGroup X ℂ := by
  have hde : d = e := Subsingleton.elim _ _
  subst e
  exact h

/-- Circuit evaluation agrees with evaluation using classical decidable equality. -/
private theorem logTaylor_evaluate_classical {X : Type} [Fintype X] [d : DecidableEq X]
    (O : Matrix X X ℂ) (cs : List (AdjointStep X)) :
    evaluate O cs = @evaluate X _ (Classical.decEq X) O cs := by
  have hde : d = Classical.decEq X := Subsingleton.elim _ _
  cases hde
  rfl

/-- Well-formedness of an adjoint circuit is independent of the chosen decidable equality
instance. -/
private theorem logTaylor_wellformed_decidableEq {X : Type} [Fintype X]
    {d e : DecidableEq X} {cs : List (AdjointStep X)}
    (h : @WellFormedAdjointCircuit X _ d cs) :
    @WellFormedAdjointCircuit X _ e cs := by
  have hde : d = e := Subsingleton.elim _ _
  subst e
  exact h

/-- A unitary data-preparation operator gives a well-formed singleton preparation circuit on the
full phase-estimation register. -/
theorem logTaylor_preparation_wellformed {D : ℕ} (M K : ℕ) (B : Operator D)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    WellFormedAdjointCircuit
      [AdjointStep.gate (TensorGate (1 : Operator M)
        (TensorGate (1 : Matrix Bool Bool ℂ) (logTaylorDataGate (J := J) K B)))] := by
  letI : DecidableEq (TaylorWordLabel J K) := instDecidableEqSum
  simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
  have hphase : (1 : Operator M) ∈ Matrix.unitaryGroup (Fin M) ℂ := Submonoid.one_mem _
  have hflag : (1 : Matrix Bool Bool ℂ) ∈ Matrix.unitaryGroup Bool ℂ := Submonoid.one_mem _
  have hu := tensorGate_unitary hphase (tensorGate_unitary hflag
    (logTaylor_data_unitary (J := J) K B hB))
  exact logTaylor_unitary_decidableEq hu

/-- The prepared output equals clean phase estimation applied to the Taylor embedding of `B *ᵥ
Ket j`. -/
theorem logTaylor_output_preparation {D : ℕ} (h : J → ℝ) (U : J → Operator D)
    (j0 : J) (t : ℝ) (Lambda T M k : ℕ) (hM : 0 < M) (B : Operator D) (j : Fin D) :
    logTaylorQPEOutput h U j0 t Lambda T M k hM B j =
      evaluate (TensorGate (1 : Operator M) (controlOracle
        (taylorQuery U (logTaylorCutoff (taylorSegments Lambda T) (logTaylorQPEPrecision M k)))))
        (cleanQPEWord M (logTaylorSimulationWord h j0 t Lambda T (logTaylorQPEPrecision M k))) *ᵥ
        cleanQPEInput M hM (taylorFrame j0
          (logTaylorCutoff (taylorSegments Lambda T) (logTaylorQPEPrecision M k)) *ᵥ (B *ᵥ Ket j)) := by
  simp only [logTaylorQPEOutput, logTaylorQPEPreparedWord, evaluate_append,
    evaluate, instructionMatrix, Matrix.mul_one, ← Matrix.mulVec_mulVec, cleanQPEInput,
    TensorGate, kronecker_mulVec_tensorState, Matrix.one_mulVec]
  rw [Matrix.mulVec_mulVec,
      logTaylor_data_frame (J := J)
      (logTaylorCutoff (taylorSegments Lambda T) (logTaylorQPEPrecision M k)) B j0, ← Matrix.mulVec_mulVec]

/-- For Hermitian unitary summands and the supplied spectral decomposition, the prepared Taylor
phase-estimation circuit is well formed with the stated exact query and gate counts. Its
event mass differs from the spectral mixture of ideal phase-estimation kernels by at most
`2⁻ᵏ`. -/
theorem log_taylor_actual_spectral_qpe_and_cost : ∀ (D : ℕ) (h : J → ℝ) (U : J → Operator D) (j0 : J)
    (t : ℝ) (Lambda T M k : ℕ) (hM : 2 ≤ M) (B S : Operator D)
    (eig : Fin D → ℝ) (j : Fin D) (E : Finset (Fin M)),
  (∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (U a).IsHermitian) →
  (∑ a, |h a|) ≤ Lambda → |t| ≤ T →
  B ∈ Matrix.unitaryGroup (Fin D) ℂ → S ∈ Matrix.unitaryGroup (Fin D) ℂ →
  (∑ a, (h a:ℂ) • U a) = S * Matrix.diagonal (fun i => (eig i:ℂ)) * Sᴴ →
  let p := logTaylorQPEPrecision M k
  let s := taylorSegments Lambda T
  let K := logTaylorCutoff s p
  let word := logTaylorQPEPreparedWord h j0 t Lambda T M k B
  let beta := Sᴴ *ᵥ (B *ᵥ Ket j)
  let out := logTaylorQPEOutput h U j0 t Lambda T M k (by omega) B j
  WellFormedAdjointCircuit word ∧
  adjointQueryCount word = (M-1)*3*s*K ∧
  adjointGateCount word = 2*(M-1)+3+(M-1)*s*(6*K+13) ∧
  |cleanQPEEventMass M out E -
    (∑ i, ‖beta i‖^2 * (∑ z ∈ E, ‖qpeKernel M (-t*eig i/(2*Real.pi)) z‖^2))| ≤ (1/2:ℝ)^k := by
  intro D h U j0 t Lambda T M k hM B S eig j E hU hL hT hB hS hs
  let p := logTaylorQPEPrecision M k
  let K := logTaylorCutoff (taylorSegments Lambda T) p
  let R := taylorFrame (I := Fin D) j0 K
  let body := logTaylorSimulationWord (D := D) h j0 t Lambda T p
  let O := taylorQuery U K
  let A : Operator D := ∑ a, (h a:ℂ) • U a
  let beta := Sᴴ *ᵥ (B *ᵥ Ket j)
  have hSp : Sᴴ * S = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hS
  have hSS : S * Sᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using! hS
  have hA : A.IsHermitian := by
    apply isSelfAdjoint_sum
    intro a _
    exact (hU a).2.smul (by simp [IsSelfAdjoint])
  have hb := log_taylor_actual_program_and_inverse_cost D h U j0 t Lambda T p hU hL hT
  have hw := clean_qpe_actual_expansion_semantics_and_paid_inverse _ M O body (by omega) hb.1
  have hprep := logTaylor_preparation_wellformed (J := J) M K B hB
  have hsum : (∑ i, beta i • (S *ᵥ Ket i)) = B *ᵥ Ket j := by
    simp_rw [← Matrix.mulVec_smul]
    rw [← Matrix.mulVec_sum]
    have hket : (∑ i, beta i • Ket i) = beta := by
      funext x
      simp [Finset.sum_apply, Pi.smul_apply, Ket, smul_eq_mul]
    rw [hket, Matrix.mulVec_mulVec, hSS, Matrix.one_mulVec]
  have hc : (∑ i, ‖beta i‖^2) = 1 := by
    exact normalized_applyGate (conjTranspose_mem_unitaryGroup hS)
      (normalized_applyGate hB (normalized_ket j))
  have herr := clean_qpe_actual_spectral_born_event_error
    (TaylorWordLabel J K × (Bool × (J × Fin D))) (Fin D) (Fin D) M (by omega)
    O R (hamiltonianEvolution A t) body ((1/2:ℝ)^p)
    (fun i => S *ᵥ Ket i) beta (fun i => -t*eig i/(2*Real.pi))
    (taylorQuery_unitary U (fun a => (hU a).1) K)
    (taylorFrame_isIsometry j0 K) (hamiltonianEvolution_unitary hA t) (hb.1)
    (by positivity) (log_taylor_coherent_full_workspace_error D h U j0 t Lambda T p hU hL hT)
    (by
      intro i l
      simpa only [ApplyGate] using!
        (inner_applyGate hS (Ket i) (Ket l)).trans (inner_ket_ket i l)) hc (logTaylor_eigen D A S eig t hS hs) E
  try dsimp only at herr
  rw [hsum] at herr
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply WellFormedAdjointCircuit.append
    · exact logTaylor_wellformed_decidableEq hw.1
    · exact logTaylor_wellformed_decidableEq hprep
  · change adjointQueryCount (cleanQPEWord M body ++ _) = _
    rw [adjointQueryCount_append, hw.2.1, hb.2.1]
    simp only [adjointQueryCount]
    ring
  · change adjointGateCount (cleanQPEWord M body ++ _) = _
    rw [adjointGateCount_append, hw.2.2.1, hb.2.2.1]
    simp only [adjointGateCount]
    ring
  · rw [logTaylor_output_preparation]
    simpa only [logTaylor_evaluate_classical] using! herr.trans (logTaylor_qpe_budget M k)

/-- For a prepared eigenstate, the Taylor phase-estimation mass within phase distance `1 / M` of
its eigenphase is at least `8 / π² - 2⁻ᵏ` under the stated coefficient and time bounds. -/
theorem log_taylor_actual_energy_window : ∀ (D : ℕ) (h : J → ℝ) (U : J → Operator D) (j0 : J)
    (t : ℝ) (Lambda T M k : ℕ) (hM : 2 ≤ M) (B S : Operator D)
    (eig : Fin D → ℝ) (j i : Fin D),
  (∀ a, U a ∈ Matrix.unitaryGroup (Fin D) ℂ ∧ (U a).IsHermitian) →
  (∑ a, |h a|) ≤ Lambda → |t| ≤ T →
  B ∈ Matrix.unitaryGroup (Fin D) ℂ → S ∈ Matrix.unitaryGroup (Fin D) ℂ →
  (∑ a, (h a:ℂ) • U a) = S * Matrix.diagonal (fun l => (eig l:ℂ)) * Sᴴ →
  B *ᵥ Ket j = S *ᵥ Ket i →
  let E := Finset.univ.filter (fun z : Fin M =>
    phaseDistance (-t*eig i/(2*Real.pi)) ((z.val:ℝ)/(M:ℝ)) ≤ 1/(M:ℝ))
  cleanQPEEventMass M (logTaylorQPEOutput h U j0 t Lambda T M k (by omega) B j) E ≥
    8/Real.pi^2-(1/2:ℝ)^k := by
  intro D h U j0 t Lambda T M k hM B S eig j i hU hL hT hB hS hs hi
  let E := Finset.univ.filter (fun z : Fin M =>
    phaseDistance (-t*eig i/(2*Real.pi)) ((z.val:ℝ)/(M:ℝ)) ≤ 1/(M:ℝ))
  have herr := (log_taylor_actual_spectral_qpe_and_cost D h U j0 t Lambda T M k hM
    B S eig j E hU hL hT hB hS hs).2.2.2
  have hSp : Sᴴ * S = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hS
  have hb : Sᴴ *ᵥ (B *ᵥ Ket j) = Ket i := by
    rw [hi, Matrix.mulVec_mulVec, hSp, Matrix.one_mulVec]
  try dsimp only at herr
  rw [hb] at herr
  have hn (x : Fin D) : ‖Ket i x‖^2 = if x=i then (1:ℝ) else 0 := by
    by_cases hx : x=i <;> simp [Ket, hx]
  simp_rw [hn] at herr
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at herr
  have hl : 8/Real.pi^2 ≤ ∑ z ∈ E, ‖qpeKernel M (-t*eig i/(2*Real.pi)) z‖^2 :=
    offgrid_phase_window_probability M (-t*eig i/(2*Real.pi)) hM
  have hh := (abs_le.mp herr).1
  change 8/Real.pi^2-(1/2:ℝ)^k ≤ _
  linarith

end Qatlib.Concepts.CoherentSim.EndToEnd
