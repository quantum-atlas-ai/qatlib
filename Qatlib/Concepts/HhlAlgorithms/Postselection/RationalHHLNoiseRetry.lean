/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.Postselection.RationalSignedHHLConsumers

/-!
# Joint precision and noise budgets for rational HHL

`numericHHLAccuracy`, `numericHHLGrid`, `numericHHLBits`, and `numericHHLNoise` select rational
HHL parameters from a spectral gap, an overlap lower bound, and a target precision. The
estimates combine phase-grid error, rational-rotation error, and unitary-oracle perturbation for
the linear-systems construction of [HarrowHassidimLloyd2009].

## Main statements

* `rational_hhl_noisy_full_workspace_and_legality`: normalization, circuit legality, and the
  combined workspace error bound.
* `rational_hhl_noisy_actual_ls_gap`: success and least-squares direction bounds when the error
  is below the overlap gap.
* `rational_hhl_native_joint_precision_budget`: the computed parameters meet the joint error
  budget.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.QlsReadoutSpec.LowRankHHL
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.RationalProgram
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.HhlAlgorithms.UniformHHL

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.HhlAlgorithms.Postselection
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The rational analytic-error budget `min 1 (d * theta * (1 / 2)^k / 8)`. -/
def numericHHLAccuracy (d theta : ℚ) (k : ℕ) : ℚ := min 1 (d*theta*(1/2)^k/8)

/-- The phase-grid size obtained by rounding up `4096 / (d^2 * (numericHHLAccuracy d theta
k)^4)`, with a minimum of two. -/
def numericHHLGrid (d theta : ℚ) (k : ℕ) : ℕ := max 2 ⌈4096/(d^2*(numericHHLAccuracy d theta k)^4)⌉₊

/-- The binary precision chosen by a ceiling logarithm to control the rational rotation error. -/
def numericHHLBits (d theta : ℚ) (k : ℕ) : ℕ :=
  Nat.clog 2 (max 1 ⌈256*(2:ℚ)^k/(d*theta)⌉₊)

/-- The rational oracle-noise budget `d * theta * (1 / 2)^k / (16 * (numericHHLGrid d theta k -
1))`. -/
def numericHHLNoise (d theta : ℚ) (k : ℕ) : ℚ :=
  d*theta*(1/2)^k/(16*((numericHHLGrid d theta k:ℚ)-1))

/-- The rational HHL run is normalized when the oracle and input preparation are unitary and `d
> 0`. -/
theorem rationalHHLRun_normalized {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U B : Operator D)
    (j : Fin D) (d : ℚ) (bits : ℕ) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) (hd : 0 < d) :
    Normalized (rationalHHLRun M hM U d bits B j) := by
  have hc := rational_hhl_table_and_actual_forward_inverse D M bits d B hM hd hB
  have hu := hc.2.2.1.evaluate_unitary (countedHHLOracleLift_unitary hU)
  apply (normalized_iff_norm_toEuclidean_fromVec _).2
  unfold rationalHHLRun
  change ‖toEuclidean_fromVec (ApplyGate _ _)‖ = 1
  rw [norm_applyGate_of_mem_unitaryGroup hu]
  exact norm_countedHHLBranchInput D M (by omega) j

/-- Replacing one unitary oracle by another changes the rational HHL output by at most `2 * (M -
1)` times their operator-norm distance. -/
theorem rationalHHLRun_oracle_noise {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U W B : Operator D)
    (j : Fin D) (d : ℚ) (bits : ℕ) (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) :
    ‖toEuclidean_fromVec (rationalHHLRun M hM W d bits B j-rationalHHLRun M hM U d bits B j)‖ ≤
      2*((M-1 : ℕ) : ℝ)*‖W-U‖ := by
  have hc := rational_hhl_table_and_actual_forward_inverse D M bits d B hM hd hB
  have h := norm_evaluate_sub_evaluate_le
    (countedHHLOracleLift (D := D) (M := M) W) (countedHHLOracleLift (D := D) (M := M) U)
    (countedHHLOracleLift_unitary hW) (countedHHLOracleLift_unitary hU)
    (rationalHHLWord M d bits B) hc.2.2.1
    (TensorState (Ket (⟨0,by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (Ket j))))
  rw [hc.2.2.2.1, norm_countedHHLBranchInput D M (by omega) j, mul_one] at h
  apply h.trans
  push_cast
  exact mul_le_mul_of_nonneg_left (norm_oracleLift_sub D M (by omega) W U) (by positivity)

/-- Under the signed spectral and grid assumptions, the noisy rational HHL circuit is well
formed and its output is normalized. Its full-workspace error is at most `eta + 32 / 2^bits
+ 2 * (M - 1) * δ`. -/
theorem rational_hhl_noisy_full_workspace_and_legality : ∀ (D M bits : ℕ) (hM : 2≤M) (eig : Fin D→ℝ) (V B W : Operator D)
  (j : Fin D) (d : ℚ) (eta δ : ℝ),
  V∈Matrix.unitaryGroup (Fin D) ℂ → B∈Matrix.unitaryGroup (Fin D) ℂ →
  W∈Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < eta → eta≤1 → 0≤δ →
  (∀ i,eig i=0 ∨ ((d:ℝ)≤|eig i| ∧ |eig i|≤1/4)) →
  4096/((d:ℝ)^2*eta^4)≤(M:ℝ) → ‖W-continuousHHLOracle eig V‖≤δ →
  let out := rationalHHLRun M hM W d bits B j
  Normalized out ∧ WellFormedAdjointCircuit (rationalHHLWord M d bits B) ∧
  ‖toEuclidean_fromVec (out-uniformHHLIdeal M hM eig V (d:ℝ) B j)‖≤
    eta+32/2^bits+2*((M-1:ℕ):ℝ)*δ := by

  intro D M bits hM eig V B W j d eta δ hV hB hW hd heta heta1 hδ heig hbudget hnoise
  (try dsimp only)
  have hc := rational_hhl_table_and_actual_forward_inverse D M bits d B hM hd hB
  have hwf := hc.2.2.1
  have hunit := hwf.evaluate_unitary (countedHHLOracleLift_unitary hW)
  have hn : Normalized (rationalHHLRun M hM W d bits B j) := by
    apply (normalized_iff_norm_toEuclidean_fromVec _).2
    unfold rationalHHLRun
    change ‖toEuclidean_fromVec (ApplyGate _ _)‖ = 1
    rw [norm_applyGate_of_mem_unitaryGroup hunit]
    exact norm_countedHHLBranchInput D M (by omega) j
  have he := norm_evaluate_sub_evaluate_le
    (countedHHLOracleLift (D := D) (M := M) W)
    (countedHHLOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
    (countedHHLOracleLift_unitary hW)
    (countedHHLOracleLift_unitary (continuous_hhl_oracle_unitary eig V hV))
    (rationalHHLWord M d bits B) hwf
    (TensorState (Ket (⟨0,by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket false) (Ket j))))
  rw [hc.2.2.2.1, norm_countedHHLBranchInput D M (by omega) j, mul_one] at he
  have hl := norm_oracleLift_sub D M (by omega) W (continuousHHLOracle eig V)
  have hdiff : ‖toEuclidean_fromVec
      (rationalHHLRun M hM W d bits B j -
        rationalHHLRun M hM (continuousHHLOracle eig V) d bits B j)‖ ≤
      2*((M-1 : ℕ) : ℝ)*δ := by
    apply he.trans
    push_cast
    exact mul_le_mul_of_nonneg_left (hl.trans hnoise) (by positivity)
  have hbase := rational_hhl_low_rank_full_program_error D M bits hM eig V B j d eta
    hV hB hd heta heta1 heig hbudget
  refine ⟨hn, hwf, ?_⟩
  have ht : toEuclidean_fromVec
      (rationalHHLRun M hM W d bits B j-uniformHHLIdeal M hM eig V (d : ℝ) B j) =
      toEuclidean_fromVec (rationalHHLRun M hM W d bits B j-
        rationalHHLRun M hM (continuousHHLOracle eig V) d bits B j) +
      toEuclidean_fromVec (rationalHHLRun M hM (continuousHHLOracle eig V) d bits B j-
        uniformHHLIdeal M hM eig V (d : ℝ) B j) := by
    simp only [toEuclidean_fromVec, ← WithLp.toLp_add]
    congr 1
    abel
  rw [ht]
  exact (norm_add_le _ _).trans ((add_le_add hdiff hbase).trans_eq (by ring))

/-- If the combined error `E` is below `d * tau`, the noisy rational HHL success probability is
at least `(d * tau - E)^2` and its postselected least-squares direction error is at most `2
* E / (d * tau)`. -/
theorem rational_hhl_noisy_actual_ls_gap : ∀ (D M bits : ℕ) (hM : 2≤M) (eig : Fin D→ℝ) (V B W : Operator D)
  (j : Fin D) (d : ℚ) (eta δ : ℝ),
  V∈Matrix.unitaryGroup (Fin D) ℂ → B∈Matrix.unitaryGroup (Fin D) ℂ →
  W∈Matrix.unitaryGroup (Fin D) ℂ → 0 < d → 0 < eta → eta≤1 → 0≤δ →
  (∀ i,eig i=0 ∨ ((d:ℝ)≤|eig i| ∧ |eig i|≤1/4)) →
  4096/((d:ℝ)^2*eta^4)≤(M:ℝ) → ‖W-continuousHHLOracle eig V‖≤δ →
  let E := eta+32/2^bits+2*((M-1:ℕ):ℝ)*δ
  let tau := leastSquaresOverlap (continuousHHLMatrix eig V) (B*ᵥKet j)
  let out := rationalHHLRun M hM W d bits B j
  E < (d:ℝ)*tau → ((d:ℝ)*tau-E)^2≤MeasureProb out (flagSuccessSet D M) ∧
    ‖toEuclidean_fromVec (PostMeasure out (flagSuccessSet D M)-
      uniformHHLSolutionTarget M hM eig V B j)‖≤2*E/((d:ℝ)*tau) := by

  intro D M bits hM eig V B W j d eta δ hV hB hW hd heta heta1 hδ heig hbudget hnoise
  (try dsimp only)
  intro hgap
  have h := rational_hhl_noisy_full_workspace_and_legality D M bits hM eig V B W j d eta δ
    hV hB hW hd heta heta1 hδ heig hbudget hnoise
  have ho := lowRank_output_from_error hM eig V B j d (eta+32/2^bits+2*((M-1 : ℕ) : ℝ)*δ)
    hV (by exact_mod_cast hd) (by positivity) heig (rationalHHLRun M hM W d bits B j) h.2.2 hgap
  exact ⟨ho.1, ho.2.2⟩

/-- The computed accuracy, grid, bit precision, and positive oracle-noise budget satisfy the
grid requirement and bound their combined output error by `d * theta * (1 / 2)^k / 2`. -/
theorem rational_hhl_native_joint_precision_budget : ∀ (d theta : ℚ) (k : ℕ),
    0 < d → d ≤ 1/4 → 0 < theta → theta ≤ 1 →
    let eta := numericHHLAccuracy d theta k
    let M := numericHHLGrid d theta k
    let bits := numericHHLBits d theta k
    0 < eta ∧ eta ≤ 1 ∧ 2 ≤ M ∧ 4096/(d^2*eta^4) ≤ (M : ℚ) ∧
      0 < numericHHLNoise d theta k ∧
      (eta : ℝ)+32/2^bits+2*((M-1 : ℕ) : ℝ)*(numericHHLNoise d theta k : ℝ) ≤
        (d : ℝ)*(theta : ℝ)*(1/2 : ℝ)^k/2 := by
  intro d theta k hd hd1 ht ht1
  (try dsimp only)
  let x : ℚ := d*theta*(1/2)^k
  let M := numericHHLGrid d theta k
  let bits := numericHHLBits d theta k
  have hx : 0 < x := by dsimp [x]; positivity
  have hhalf : (1/2 : ℚ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hdt : d*theta ≤ d := by nlinarith
  have hx1 : x ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left hhalf (le_of_lt (mul_pos hd ht))
    dsimp [x]
    nlinarith
  have heta : numericHHLAccuracy d theta k = x/8 := by
    unfold numericHHLAccuracy
    apply min_eq_right
    change x/8 ≤ 1
    linarith
  have heta0 : 0 < numericHHLAccuracy d theta k := by rw [heta]; positivity
  have heta1 : numericHHLAccuracy d theta k ≤ 1 := by rw [heta]; linarith
  have hM : 2 ≤ M := le_max_left _ _
  have hgrid : 4096/(d^2*(numericHHLAccuracy d theta k)^4) ≤ (M : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 2 _))
  have hpbits : 0 < (2 : ℚ)^bits := by positivity
  have hbits : 256*(2 : ℚ)^k/(d*theta) ≤ (2 : ℚ)^bits := by
    apply (Nat.le_ceil _).trans
    have hb := (le_max_right 1 ⌈256*(2 : ℚ)^k/(d*theta)⌉₊).trans
      (Nat.le_pow_clog (by omega : 1 < 2) (max 1 ⌈256*(2 : ℚ)^k/(d*theta)⌉₊))
    have hq := (Nat.cast_le (α := ℚ)).mpr hb
    simpa only [Nat.cast_pow, Nat.cast_ofNat, bits, numericHHLBits] using! hq
  have hprod : (256*(2 : ℚ)^k/(d*theta))*x = 256 := by
    dsimp [x]
    rw [one_div, inv_pow]
    field_simp
  have htable : 32/(2 : ℚ)^bits ≤ x/8 := by
    have hb := mul_le_mul_of_nonneg_right hbits hx.le
    rw [hprod] at hb
    apply (div_le_iff₀ hpbits).mpr
    nlinarith
  have hMpos : 0 < ((M : ℚ)-1) := by
    have h : (2 : ℚ) ≤ M := by exact_mod_cast hM
    linarith
  have hnoise : 0 < numericHHLNoise d theta k := by
    change 0 < x/(16*((M : ℚ)-1))
    positivity
  have hnoiseEq : 2*((M-1 : ℕ) : ℚ)*numericHHLNoise d theta k = x/8 := by
    change 2*((M-1 : ℕ) : ℚ)*(x/(16*((M : ℚ)-1))) = x/8
    rw [Nat.cast_sub (by omega : 1 ≤ M), Nat.cast_one]
    field_simp
    ring
  have htotal : numericHHLAccuracy d theta k+32/(2 : ℚ)^bits+
      2*((M-1 : ℕ) : ℚ)*numericHHLNoise d theta k ≤ x/2 := by
    rw [heta, hnoiseEq]
    linarith
  refine ⟨heta0, heta1, hM, hgrid, hnoise, ?_⟩
  have hr : ((numericHHLAccuracy d theta k+32/(2 : ℚ)^bits+
      2*((M-1 : ℕ) : ℚ)*numericHHLNoise d theta k : ℚ) : ℝ) ≤ ((x/2 : ℚ) : ℝ) :=
    Rat.cast_le.mpr htotal
  push_cast at hr
  dsimp only [x, M, bits] at hr
  push_cast at hr
  exact hr

end Qatlib.Concepts.HhlAlgorithms.Postselection
