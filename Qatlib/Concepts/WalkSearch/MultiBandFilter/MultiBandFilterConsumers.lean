/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MultiBandFilter.MultiBandPhaseFilter

/-!
# Consequences of multiband phase filtering

Derives success and conditional-state estimates from the coherent multiband branch-error bound.
The module also counts the forward and inverse oracle uses of `bandReflectionWord` and bounds
its sensitivity to unitary access errors, using phase-estimation constructions described in
[NielsenChuang2010].

## Main statements

* `multiband_derived_success_and_conditional_state`: For target spectral mass `a` and branch
  error `e = 1 / (2 * Real.sqrt M * eta)` with `e < Real.sqrt a`, proves accepted squared norm
  at least `(Real.sqrt a - e) ^ 2` and normalized-state error at most `2 * e / Real.sqrt a`
  under the stated spectral and classification hypotheses.
* `multiband_actual_word_forward_inverse_ledger`: For `M ≥ 2`, the multiband reflection word is
  well formed and contains exactly `2 * (M - 1)` oracle queries and `4 * (M - 1) + 5` gates.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability

namespace Qatlib.Concepts.WalkSearch.MultiBandFilter
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For target spectral mass `a` and branch error `e = 1 / (2 * Real.sqrt M * eta)` with `e <
Real.sqrt a`, proves accepted squared norm at least `(Real.sqrt a - e) ^ 2` and
normalized-state error at most `2 * e / Real.sqrt a` under the stated spectral and
classification hypotheses. -/
theorem multiband_derived_success_and_conditional_state :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
      let a := ∑ j∈T, ‖c j‖^2
      let e := 1/(2*Real.sqrt M*eta)
      let z := bandAccepted U M (by omega) S (∑ j,c j • v j)
      e < Real.sqrt a → (Real.sqrt a-e)^2 ≤ ‖toEuclidean_fromVec z‖^2 ∧
      ‖NormedSpace.normalize (toEuclidean_fromVec z)-
        NormedSpace.normalize (toEuclidean_fromVec (bandEmbed M (by omega) (spectralTargetState v c T)))‖ ≤
        2*e/Real.sqrt a := by
  intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  (try dsimp only)
  intro hmassgap
  have herr := multiband_actual_full_uncomputed_branch_error I J U M hM S v c phi T eta
    hU heta heta1 hgap hv hc he
  let z := bandAccepted U M (by omega) S (∑ j,c j • v j)
  let target := bandEmbed M (by omega) (spectralTargetState v c T)
  have ht : ‖toEuclidean_fromVec target‖^2=∑ j∈T, ‖c j‖^2 := by
    rw [bandEmbed_norm, spectralTargetState_norm_sq v c T hv]
  have hn : ‖toEuclidean_fromVec target‖=Real.sqrt (∑ j∈T, ‖c j‖^2) := by
    rw [← ht, Real.sqrt_sq (norm_nonneg _)]
  have hclose : ‖toEuclidean_fromVec z-toEuclidean_fromVec target‖ ≤ 1/(2*Real.sqrt M*eta) := herr
  have hg : 1/(2*Real.sqrt M*eta) < ‖toEuclidean_fromVec target‖ := by rwa [hn]
  have hout := Qatlib.Concepts.BlockEncoding.Postselection.normalize_error_of_gap hclose hg
  have hnorm := norm_sub_norm_le (toEuclidean_fromVec target) (toEuclidean_fromVec z)
  rw [norm_sub_rev] at hnorm
  have hlower : Real.sqrt (∑ j∈T, ‖c j‖^2)-1/(2*Real.sqrt M*eta) ≤ ‖toEuclidean_fromVec z‖ := by
    rw [hn] at hnorm
    linarith
  refine ⟨pow_le_pow_left₀ (by linarith) hlower 2, ?_⟩
  simpa only [hn] using! hout.2

/-- The diagonal sign matrix `bandSign M S` is unitary. -/
theorem bandSign_unitary {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)) :
    bandSign (I := I) M S ∈ Matrix.unitaryGroup _ ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [bandSign, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext p q
  by_cases hpq : p=q
  · subst q
    by_cases hs : p.1∈S <;> simp [hs]
  · simp [hpq]

/-- For `M ≥ 2`, the multiband reflection word is well formed and contains exactly `2 * (M - 1)`
oracle queries and `4 * (M - 1) + 5` gates. -/
theorem multiband_actual_word_forward_inverse_ledger :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)), 2 ≤ M →
      WellFormedAdjointCircuit (bandReflectionWord (I:=I) M S) ∧
      adjointQueryCount (bandReflectionWord (I:=I) M S)=2*(M-1) ∧
      adjointGateCount (bandReflectionWord (I:=I) M S)=4*(M-1)+5 := by
  intro I _ _ M S hM
  have h := counted_offgrid_qpe_clean_flag M (by omega) (1 : Matrix I I ℂ) (0 : QState I)
  have hwf := phaseCompileCircuit_wellFormed h.2.2.2
  have hcounts := phaseCompileCircuit_counts (countedPhaseCircuit (I := I) M)
  refine ⟨?_, ?_, ?_⟩
  · simp only [bandReflectionWord, WellFormedAdjointCircuit.append_iff,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨hwf.adjointCircuit, bandSign_unitary M S⟩, hwf⟩
  · rw [bandReflectionWord, adjointQueryCount_append, adjointQueryCount_append,
      adjointQueryCount_adjointCircuit, hcounts.1, h.2.1]
    simp only [adjointQueryCount]; omega
  · rw [bandReflectionWord, adjointGateCount_append, adjointGateCount_append,
      adjointGateCount_adjointCircuit, hcounts.2, h.2.2.1]
    simp only [adjointGateCount]; omega

/-- For unitary accesses `U` and `W` and a normalized input, the corresponding multiband
reflection outputs differ in norm by at most `2 * (M - 1) * ‖U - W‖`. -/
theorem multiband_same_word_access_perturbation :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M))
      (U W : Matrix I I ℂ) (psi : QState I), U∈Matrix.unitaryGroup I ℂ → W∈Matrix.unitaryGroup I ℂ →
      Normalized psi →
      ‖toEuclidean_fromVec (bandReflected U M (by omega) S psi-bandReflected W M (by omega) S psi)‖ ≤
        2*(M-1)*‖U-W‖ := by
  intro I _ _ M hM S U W psi hU hW hpsi
  have hword := multiband_actual_word_forward_inverse_ledger I M S hM
  have hO :=
      tensorGate_unitary (Submonoid.one_mem (Matrix.unitaryGroup (Fin M) ℂ))
      (controlOracle_unitary hU)
  have hP :=
      tensorGate_unitary (Submonoid.one_mem (Matrix.unitaryGroup (Fin M) ℂ))
      (controlOracle_unitary hW)
  have h := norm_evaluate_sub_evaluate_le _ _ hO hP _ hword.1 (bandEmbed M (by omega) psi)
  rw [hword.2.1, bandEmbed_norm, (normalized_iff_norm_toEuclidean_fromVec psi).mp hpsi,
      mul_one] at h
  have hdist : ‖TensorGate (1 : Operator M) (controlOracle U)-TensorGate (1 : Operator M) (controlOracle W)‖ ≤
      ‖U-W‖ := by
    rw [tensorGate_sub_right, l2_norm_tensorGate]
    exact ((mul_le_mul_of_nonneg_right l2_norm_one_le (norm_nonneg _)).trans_eq (one_mul _)).trans
      (norm_controlOracle_sub U W)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, Nat.cast_sub (by omega : 1 ≤ M)] at h
  have hnon : 0 ≤ 2*((M:ℝ)-1) := by
    have hm : (2:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    linarith
  exact h.trans (mul_le_mul_of_nonneg_left hdist hnon)
end Qatlib.Concepts.WalkSearch.MultiBandFilter
