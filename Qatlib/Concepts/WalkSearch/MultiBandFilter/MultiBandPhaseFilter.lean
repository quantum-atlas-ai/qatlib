/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter.DegeneratePhaseFilter
import Qatlib.Concepts.HhlAlgorithms.UniformHHL.UniformHHLFilter
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm

/-!
# Coherent multiband phase filters

Defines phase-estimation filters for unions of rational intervals and their coherent
sign-reflection circuits. A geometric separation condition produces `bandClassificationGap`;
eigenstate misclassification estimates then bound the accepted branch and coherent reflection
errors using phase estimation as in [NielsenChuang2010].

## Main statements

* `multiband_actual_full_uncomputed_branch_error`: For a normalized orthonormal eigenstate
  superposition satisfying the classification gap, the uncomputed accepted branch differs from
  the embedded target spectral state by at most `1 / (2 * Real.sqrt M * eta)`.
* `multiband_actual_coherent_reflection_error`: For a normalized orthonormal eigenstate
  superposition satisfying the classification gap, the coherent reflection differs from the
  embedded ideal target-sign reflection by at most `1 / (Real.sqrt M * eta)`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.UniformHHL

namespace Qatlib.Concepts.WalkSearch.MultiBandFilter
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

/-- Membership in the union of the closed real intervals specified by the rational endpoint
pairs in `bands`. -/
def bandContains (bands : List (ℚ × ℚ)) (x : ℝ) : Prop :=
  ∃ b ∈ bands,(b.1:ℝ) ≤ x ∧ x ≤ (b.2:ℝ)

/-- The finite set of phase-estimation labels whose signed decoded values lie in one of the
specified bands. -/
noncomputable def bandLabels (M : ℕ) (bands : List (ℚ × ℚ)) : Finset (Fin M) :=
  Finset.univ.filter (fun y => bandContains bands (uniformHHLDecode M y))

/-- The matrix evaluation of the compiled counted phase-estimation circuit with controlled
access to `U`. -/
noncomputable def bandQPEMatrix {I : Type} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (M : ℕ) :
    Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ :=
  evaluate (TensorGate (1 : Operator M) (controlOracle U)) (phaseCompileCircuit (countedPhaseCircuit M))

/-- The event consisting of labels in `S` with the auxiliary Boolean flag equal to `false`. -/
def bandEvent {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)) :
    Finset (Fin M × (Bool × I)) := Finset.univ.filter (fun p => p.1∈S ∧ p.2.1=false)

/-- Embeds `psi` with the phase register initialized to zero and the auxiliary flag embedded by
`phaseFlagEmbed`. -/
noncomputable def bandEmbed {I : Type} (M : ℕ) (hM : 0 < M) (psi : QState I) : QState (Fin M × (Bool × I)) :=
  phaseFlagEmbed M (TensorState (Ket (⟨0,hM⟩ : Fin M)) psi)

/-- The unnormalized state obtained by phase estimation, projection onto `bandEvent M S`, and
application of the adjoint phase-estimation matrix. -/
noncomputable def bandAccepted {I : Type} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (M : ℕ)
    (hM : 0 < M) (S : Finset (Fin M)) (psi : QState I) : QState (Fin M × (Bool × I)) :=
  (bandQPEMatrix U M)ᴴ *ᵥ Collapse (bandQPEMatrix U M *ᵥ bandEmbed M hM psi) (bandEvent M S)

/-- The diagonal matrix assigning sign `1` to phase labels in `S` and sign `-1` to all other
phase labels. -/
noncomputable def bandSign {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)) :
    Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ :=
  Matrix.diagonal (fun p => if p.1∈S then 1 else -1)

/-- The adjoint-circuit word combining the compiled phase-estimation circuit and its adjoint
with the diagonal band-sign gate. -/
noncomputable def bandReflectionWord {I : Type} [Fintype I] [DecidableEq I] (M : ℕ) (S : Finset (Fin M)) :
    List (AdjointStep (Fin M × (Bool × I))) :=
  adjointCircuit (phaseCompileCircuit (countedPhaseCircuit M)) ++ [.gate (bandSign M S)] ++
    phaseCompileCircuit (countedPhaseCircuit M)

/-- The state produced by evaluating `bandReflectionWord` with controlled access to `U` on the
embedded input. -/
noncomputable def bandReflected {I : Type} [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (M : ℕ)
    (hM : 0 < M) (S : Finset (Fin M)) (psi : QState I) : QState (Fin M × (Bool × I)) :=
  evaluate (TensorGate (1 : Operator M) (controlOracle U)) (bandReflectionWord M S) *ᵥ bandEmbed M hM psi

/-- The condition that every phase-grid label within circular distance `eta` of `phi j` has
membership in `S` exactly when `j` belongs to the target set `T`. -/
def bandClassificationGap {J : Type} [Fintype J] [DecidableEq J] (M : ℕ) (S : Finset (Fin M))
    (phi : J  →  ℝ) (T : Finset J) (eta : ℝ) : Prop :=
  ∀ j y, phaseDistance (phi j) ((y.val:ℝ)/M) ≤ eta  →  (y∈S ↔ j∈T)

/-- If `|lam| ≤ 1 / 4` and a grid phase is within circular distance `w ≤ 1 / 16` of `lam`, its
signed decoded value differs from `lam` by at most `w`. -/
theorem bandDecode_good (M : ℕ) (y : Fin M) (lam w : ℝ) (hM : 2 ≤ M)
    (hlam' : |lam| ≤ 1/4) (hw : w ≤ 1/16)
    (hgood : phaseDistance lam ((y.val:ℝ)/M) ≤ w) : |uniformHHLDecode M y-lam| ≤ w := by
  have hm : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hr0 : 0 ≤ (y.val : ℝ) / (M : ℝ) := by positivity
  have hr1 : (y.val : ℝ) / (M : ℝ) < 1 := by
    rw [div_lt_one hm]
    exact_mod_cast y.isLt
  have hl := abs_le.mp hlam'
  have hw' : w < 1 / 4 := by linarith
  let n : ℤ := ⌊lam - (y.val : ℝ) / (M : ℝ) + 1 / 2⌋
  have hg : |lam - (y.val : ℝ) / (M : ℝ) - (n : ℝ)| ≤ w := hgood
  have hg' := abs_le.mp hg
  unfold uniformHHLDecode
  split_ifs with hy
  · have hrhalf : (y.val : ℝ) / (M : ℝ) ≤ 1 / 2 := by
      apply (div_le_iff₀ hm).mpr
      have hh : (2 : ℝ) * y.val ≤ M := by exact_mod_cast hy
      linarith
    have hn0 : (-1 : ℝ) < n := by linarith
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn : n = 0 := by
      have h0 : (-1 : ℤ) < n := by exact_mod_cast hn0
      have h1 : n < (1 : ℤ) := by exact_mod_cast hn1
      omega
    rw [hn, Int.cast_zero, sub_zero] at hg
    rwa [abs_sub_comm]
  · have hrhalf : 1 / 2 < (y.val : ℝ) / (M : ℝ) := by
      apply (lt_div_iff₀ hm).mpr
      have hh : (M : ℝ) < (2 : ℝ) * y.val := by exact_mod_cast (by omega : M < 2 * y.val)
      linarith
    have hn0 : (-2 : ℝ) < n := by linarith
    have hn1 : (n : ℝ) < 0 := by linarith
    have hn : n = -1 := by
      have h0 : (-2 : ℤ) < n := by exact_mod_cast hn0
      have h1 : n < (0 : ℤ) := by exact_mod_cast hn1
      omega
    rw [hn] at hg
    have he : (y.val : ℝ) / (M : ℝ) - 1 - lam =
        -(lam - (y.val : ℝ) / (M : ℝ) - ((-1 : ℤ) : ℝ)) := by push_cast; ring
    rw [he, abs_neg]
    exact hg

/-- The stated signed-phase bounds and `2 * eta` separation from every band endpoint imply
`bandClassificationGap` for the decoded band labels and the phases lying in the bands. -/
theorem multiband_signed_classifier_from_geometric_margin :
    ∀ (J : Type) [Fintype J] [DecidableEq J] (M : ℕ) (bands : List (ℚ × ℚ))
      (phi : J → ℝ) (eta : ℝ), 2 ≤ M → 0 < eta → eta ≤ 1/16 →
      (∀ j, |phi j| ≤ 1/4) → (∀ b ∈ bands, -1/4 ≤ (b.1:ℝ) ∧ (b.2:ℝ) ≤ 1/4) →
      (∀ j b, b∈bands → ((b.1:ℝ)+2*eta ≤ phi j ∧ phi j ≤ (b.2:ℝ)-2*eta) ∨
        (phi j ≤ (b.1:ℝ)-2*eta ∨ (b.2:ℝ)+2*eta ≤ phi j)) →
      bandClassificationGap M (bandLabels M bands) phi
        (Finset.univ.filter (fun j => bandContains bands (phi j))) eta := by
  intro J _ _ M bands phi eta hM heta heta1 hphi _hbands hmargin j y hdist
  have hx := abs_le.mp (bandDecode_good M y (phi j) eta hM (hphi j) heta1 hdist)
  simp only [bandLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b,hb,hleft,hright⟩
    rcases hmargin j b hb with hi | ho
    · exact ⟨b,hb,by linarith [hi.1],by linarith [hi.2]⟩
    · rcases ho with ho | ho <;> exfalso <;> linarith
  · rintro ⟨b,hb,hleft,hright⟩
    rcases hmargin j b hb with hi | ho
    · exact ⟨b,hb,by linarith [hi.1],by linarith [hi.2]⟩
    · rcases ho with ho | ho <;> exfalso <;> linarith

/-- Under `bandClassificationGap` with `M ≥ 2` and `0 < eta ≤ 1 / 2`, the total phase-estimation
kernel weight on misclassified labels is at most `1 / (4 * M * eta ^ 2)` for each phase. -/
theorem multiband_actual_eigenstate_misclassification :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (_U : Matrix I I ℂ) (M : ℕ) (S : Finset (Fin M)) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      2 ≤ M → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      ∀ j, (∑ y ∈ Finset.univ.filter (fun y : Fin M => ¬(y∈S ↔ j∈T)), ‖qpeKernel M (phi j) y‖^2) ≤
        1/(4*(M:ℝ)*eta^2) := by
  intro I J _ _ _ _ _U M S phi T eta hM heta heta1 hgap j
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => sq_nonneg _))
    (uniform_phase_kernel_derived_tail M (phi j) eta hM heta heta1)
  intro y hy
  have hbad := (Finset.mem_filter.mp hy).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra h
  exact hbad (hgap j y (le_of_not_gt h))

/-- Adding the auxiliary flag with `phaseFlagEmbed` preserves the Euclidean norm. -/
theorem bandScratch_norm {I : Type} [Fintype I] (M : ℕ) (a : QState (Fin M × I)) :
    ‖toEuclidean_fromVec (phaseFlagEmbed M a)‖=‖toEuclidean_fromVec a‖ := by
  have hs : ‖toEuclidean_fromVec (phaseFlagEmbed M a)‖^2=‖toEuclidean_fromVec a‖^2 := by
    simp [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, phaseFlagEmbed]
  nlinarith [norm_nonneg (toEuclidean_fromVec (phaseFlagEmbed M a)), norm_nonneg (toEuclidean_fromVec a)]

/-- The zero-phase-register and flag embedding `bandEmbed` preserves the Euclidean norm. -/
theorem bandEmbed_norm {I : Type} [Fintype I] (M : ℕ) (hM : 0 < M) (psi : QState I) :
    ‖toEuclidean_fromVec (bandEmbed M hM psi)‖=‖toEuclidean_fromVec psi‖ := by
  rw [bandEmbed, bandScratch_norm, tensorState_l2_norm, norm_toEuclidean_fromVec_ket, one_mul]

/-- For a unitary `U` and positive phase-register size, the compiled band phase-estimation
matrix is unitary. -/
theorem bandQPEMatrix_unitary {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    bandQPEMatrix U M ∈ Matrix.unitaryGroup _ ℂ := by
  apply (phaseCompileCircuit_wellFormed (counted_offgrid_qpe_clean_flag M hM U (0 : QState I)).2.2.2).evaluate_unitary
  exact tensorGate_unitary (Submonoid.one_mem _) (controlOracle_unitary hU)

/-- Applying `bandQPEMatrix` to the embedded input gives the flagged phase-estimation output. -/
theorem bandQPE_output {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (psi : QState I) :
    bandQPEMatrix U M *ᵥ bandEmbed M hM psi = phaseFlagEmbed M (qpeOutput M U psi) := by
  have hi : bandEmbed M hM psi =
      TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) psi) := by
    funext ⟨y,b,i⟩
    cases b <;> simp [bandEmbed, phaseFlagEmbed, TensorState, Ket]
  rw [hi, bandQPEMatrix]
  change ApplyGate _ _ = _
  rw [phaseCompileCircuit_evaluate, (counted_offgrid_qpe_clean_flag M hM U psi).1]
  rfl

/-- On a superposition of eigenvectors of `U`, the compiled phase-estimation output has the
stated expansion in the kernels `qpeKernel M (phi j)`. -/
theorem bandQPE_packet {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (v : J → QState I) (c : J → ℂ) (phi : J → ℝ)
    (he : ∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) :
    bandQPEMatrix U M *ᵥ bandEmbed M hM (∑ j,c j • v j) =
      phaseFlagEmbed M (fun p : Fin M × I => ∑ j, (c j*qpeKernel M (phi j) p.1)*v j p.2) := by
  rw [bandQPE_output, qpeOutput_sum]
  simp_rw [qpeOutput_eigen M U (v _) (phi _) (he _)]
  congr 1
  funext ⟨y,i⟩
  simp [TensorState, Pi.smul_apply, mul_assoc]

/-- Expands the difference between the accepted phase-estimation branch and the phase-estimated
target state into eigenvector coefficients supported on classification discrepancies. -/
theorem bandMasked_error_packet {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (S : Finset (Fin M))
    (v : J → QState I) (c : J → ℂ) (phi : J → ℝ) (T : Finset J)
    (he : ∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) :
    Collapse (bandQPEMatrix U M *ᵥ bandEmbed M hM (∑ j,c j • v j)) (bandEvent M S) -
      bandQPEMatrix U M *ᵥ bandEmbed M hM (spectralTargetState v c T) =
      phaseFlagEmbed M (fun p : Fin M × I => ∑ j,
        ((if p.1∈S then c j*qpeKernel M (phi j) p.1 else 0) -
          (if j∈T then c j*qpeKernel M (phi j) p.1 else 0))*v j p.2) := by
  have ht : spectralTargetState v c T = ∑ j, (if j∈T then c j else 0) • v j := by
    simp [spectralTargetState, ite_smul, Finset.sum_ite_mem]
  rw [ht, bandQPE_packet U M hM v c phi he, bandQPE_packet U M hM v _ phi he]
  funext ⟨y,b,i⟩
  cases b <;> simp [collapse_apply, bandEvent, phaseFlagEmbed, Pi.sub_apply,
    Finset.sum_sub_distrib, sub_mul, ite_mul, mul_assoc]

/-- For an orthonormal eigenvector family, the squared masked-branch error equals the sum of
coefficient masses times their phase-estimation misclassification weights. -/
theorem bandMasked_norm_sq {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (S : Finset (Fin M))
    (v : J → QState I) (c : J → ℂ) (phi : J → ℝ) (T : Finset J)
    (hv : ∀ j l, Inner (v j) (v l)=if j=l then 1 else 0)
    (he : ∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) :
    ‖toEuclidean_fromVec (Collapse (bandQPEMatrix U M *ᵥ bandEmbed M hM (∑ j,c j • v j)) (bandEvent M S) -
      bandQPEMatrix U M *ᵥ bandEmbed M hM (spectralTargetState v c T))‖^2 =
      ∑ j, ‖c j‖^2*(∑ y ∈ Finset.univ.filter (fun y : Fin M => ¬(y∈S ↔ j∈T)), ‖qpeKernel M (phi j) y‖^2) := by
  let d : Fin M → J → ℂ := fun y j =>
    (if y∈S then c j*qpeKernel M (phi j) y else 0) - (if j∈T then c j*qpeKernel M (phi j) y else 0)
  rw [bandMasked_error_packet U M hM S v c phi T he, bandScratch_norm, norm_toEuclidean_fromVec_sq,
    Fintype.sum_prod_type]
  have hy (y : Fin M) : (∑ i : I, ‖∑ j, d y j*v j i‖^2)=∑ j, ‖d y j‖^2 := by
    have h := degenerate_packet_norm_sq v (d y) hv
    rw [norm_toEuclidean_fromVec_sq] at h
    simpa only [Fintype.sum_apply, Pi.smul_apply, smul_eq_mul] using! h
  change (∑ y : Fin M, ∑ i : I, ‖∑ j, d y j*v j i‖^2)=_
  simp_rw [hy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hs : y∈S <;> by_cases ht : j∈T <;>
    simp [d, hs, ht, mul_pow]

/-- For a normalized orthonormal eigenstate superposition satisfying the classification gap, the
uncomputed accepted branch differs from the embedded target spectral state by at most `1 /
(2 * Real.sqrt M * eta)`. -/
theorem multiband_actual_full_uncomputed_branch_error :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
      ‖toEuclidean_fromVec (bandAccepted U M (by omega) S (∑ j,c j • v j)-
        bandEmbed M (by omega) (spectralTargetState v c T))‖ ≤ 1/(2*Real.sqrt M*eta) := by
  intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  let Q := bandQPEMatrix U M
  let psi := bandEmbed M (by omega) (∑ j,c j • v j)
  let target := bandEmbed M (by omega) (spectralTargetState v c T)
  let err := Collapse (Q*ᵥ psi) (bandEvent M S)-Q*ᵥ target
  have hQ := bandQPEMatrix_unitary U M (by omega) hU
  have hstar : Qᴴ*Q=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hQ
  have htarget : Qᴴ*ᵥ (Q*ᵥ target)=target := by
    rw [Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]
  have herr : bandAccepted U M (by omega) S (∑ j,c j • v j)-target=Qᴴ*ᵥ err := by
    rw [bandAccepted]
    dsimp only [err]
    rw [Matrix.mulVec_sub, htarget]
  have hb : ‖toEuclidean_fromVec err‖^2 ≤ 1/(4*(M:ℝ)*eta^2) := by
    rw [bandMasked_norm_sq U M (by omega) S v c phi T hv he]
    calc
      _ ≤ ∑ j, ‖c j‖^2*(1/(4*(M:ℝ)*eta^2)) := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left
          (multiband_actual_eigenstate_misclassification I J U M S phi T eta hM heta heta1 hgap j) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, hc, one_mul]
  have hMreal : 0 < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hE2 : (1/(2*Real.sqrt M*eta))^2=1/(4*(M:ℝ)*eta^2) := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hMreal.le]
    norm_num
  have hE : ‖toEuclidean_fromVec err‖ ≤ 1/(2*Real.sqrt M*eta) := by
    rw [← hE2] at hb
    nlinarith [norm_nonneg (toEuclidean_fromVec err), show 0 ≤ 1/(2*Real.sqrt M*eta) by positivity]
  rw [herr]
  have hQt : ‖Qᴴ‖ ≤ 1 := by
    rw [← Matrix.star_eq_conjTranspose, norm_star]
    exact l2_norm_unitary_le_one hQ
  calc
    _ ≤ ‖Qᴴ‖*‖toEuclidean_fromVec err‖ := l2_norm_mulVec_fromVec_le _ _
    _ ≤ 1*‖toEuclidean_fromVec err‖ := mul_le_mul_of_nonneg_right hQt (norm_nonneg _)
    _ ≤ _ := by simpa only [one_mul] using! hE

/-- The band embedding preserves subtraction. -/
theorem bandEmbed_sub {I : Type} (M : ℕ) (hM : 0 < M) (x y : QState I) :
    bandEmbed M hM (x-y)=bandEmbed M hM x-bandEmbed M hM y := by
  funext ⟨a,b,i⟩
  cases b <;> simp [bandEmbed, phaseFlagEmbed, TensorState, mul_sub]

/-- The band embedding commutes with complex scalar multiplication. -/
theorem bandEmbed_smul {I : Type} (M : ℕ) (hM : 0 < M) (c : ℂ) (x : QState I) :
    bandEmbed M hM (c • x)=c • bandEmbed M hM x := by
  funext ⟨a,b,i⟩
  cases b <;> simp [bandEmbed, phaseFlagEmbed, TensorState, mul_comm, mul_assoc]

/-- For unitary `U`, the coherent band-reflection output is twice the accepted uncomputed branch
minus the embedded input. -/
theorem bandReflected_eq_branch {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (M : ℕ) (hM : 0 < M) (S : Finset (Fin M)) (psi : QState I)
    (hU : U∈Matrix.unitaryGroup I ℂ) :
    bandReflected U M hM S psi=(2:ℂ) • bandAccepted U M hM S psi-bandEmbed M hM psi := by
  let Q := bandQPEMatrix U M
  let a := bandEmbed M hM psi
  have hQ := bandQPEMatrix_unitary U M hM hU
  have hstar : Qᴴ*Q=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hQ
  have hclean : Qᴴ*ᵥ (Q*ᵥ a)=a := by rw [Matrix.mulVec_mulVec, hstar, Matrix.one_mulVec]
  have hsign : bandSign M S *ᵥ (Q*ᵥ a)=(2:ℂ) • Collapse (Q*ᵥ a) (bandEvent M S)-Q*ᵥ a := by
    dsimp [Q,a]
    rw [bandQPE_output]
    funext ⟨y,b,i⟩
    by_cases hy : y∈S <;> cases b <;>
      simp [bandSign, Matrix.mulVec_diagonal, collapse_apply, bandEvent,
        phaseFlagEmbed, hy, Pi.smul_apply]
    all_goals ring
  have heval : evaluate (TensorGate (1 : Operator M) (controlOracle U)) (bandReflectionWord M S)=
      Qᴴ*(bandSign M S*Q) := by
    rw [bandReflectionWord, evaluate_append, evaluate_append, evaluate_adjointCircuit]
    simp only [evaluate, instructionMatrix, mul_one]
    dsimp [Q, bandQPEMatrix]
    noncomm_ring
  rw [bandReflected, heval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hsign,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hclean]
  rfl

/-- For a normalized orthonormal eigenstate superposition satisfying the classification gap, the
coherent reflection differs from the embedded ideal target-sign reflection by at most `1 /
(Real.sqrt M * eta)`. -/
theorem multiband_actual_coherent_reflection_error :
    ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (U : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M) (S : Finset (Fin M)) (v : J → QState I)
      (c : J → ℂ) (phi : J → ℝ) (T : Finset J) (eta : ℝ),
      U∈Matrix.unitaryGroup I ℂ → 0 < eta → eta ≤ 1/2 → bandClassificationGap M S phi T eta →
      (∀ j l, Inner (v j) (v l)=if j=l then 1 else 0) → (∑ j, ‖c j‖^2)=1 →
      (∀ j, U*ᵥ v j=Complex.exp (2*Real.pi*Complex.I*(phi j:ℂ)) • v j) →
      ‖toEuclidean_fromVec (bandReflected U M (by omega) S (∑ j,c j • v j)-
        bandEmbed M (by omega) (∑ j,(if j∈T then c j else -c j) • v j))‖ ≤ 1/(Real.sqrt M*eta) := by
  intro I J _ _ _ _ U M hM S v c phi T eta hU heta heta1 hgap hv hc he
  have herr := multiband_actual_full_uncomputed_branch_error I J U M hM S v c phi T eta
    hU heta heta1 hgap hv hc he
  have ht : (∑ j,(if j∈T then c j else -c j) • v j)=
      (2:ℂ) • spectralTargetState v c T-(∑ j,c j • v j) := by
    have htarget : spectralTargetState v c T=∑ j,(if j∈T then c j else 0) • v j := by
      simp [spectralTargetState, ite_smul, Finset.sum_ite_mem]
    rw [htarget, Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j∈T <;> simp [hj]
    all_goals module
  rw [bandReflected_eq_branch U M (by omega) S _ hU, ht, bandEmbed_sub, bandEmbed_smul]
  have hd : (2:ℂ) • bandAccepted U M (by omega) S (∑ j,c j • v j) -
      bandEmbed M (by omega) (∑ j,c j • v j) -
      ((2:ℂ) • bandEmbed M (by omega) (spectralTargetState v c T)-
        bandEmbed M (by omega) (∑ j,c j • v j)) =
      (2:ℂ) • (bandAccepted U M (by omega) S (∑ j,c j • v j)-
        bandEmbed M (by omega) (spectralTargetState v c T)) := by module
  rw [hd]
  change ‖(2:ℂ) • toEuclidean_fromVec _‖ ≤ _
  rw [norm_smul]
  norm_num only [Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
end Qatlib.Concepts.WalkSearch.MultiBandFilter
