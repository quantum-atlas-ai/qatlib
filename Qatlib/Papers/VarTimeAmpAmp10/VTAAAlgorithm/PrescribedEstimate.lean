/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationContracts
import Qatlib.Foundations.BornMetrics.EventProbability

/-!
# Prescribed accuracy for variable-time estimates

The radius `vtEstimateRadius` bounds the standard amplitude-estimation error and defines a
success event of mass at least `8 / π²`. This module also proves support exactness at zero
probability and connects the sampling law with the counted circuit, providing the estimation
primitive used in the variable-time framework of [Ambainis2012].

## Main statements

* `vt_prescribed_estimate_success`: the prescribed-radius success bound.
* `vt_prescribed_estimate_zero_support`: exactness for zero success mass.
* `vt_prescribed_estimate_circuit_and_count`: Born semantics and the count `6 * M - 3`.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix
open scoped Classical
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The prescribed estimation radius `a / 4 + 8 * sqrt a / M + 10 / M²`. -/
def vtEstimateRadius (a : ℝ) (M : ℕ) : ℝ :=
  a / 4 + 8 / (M : ℝ) * Real.sqrt a + 10 / (M : ℝ) ^ 2

/-- For nonnegative `a` and positive `M`, the standard amplitude-estimation error expression is
bounded by `vtEstimateRadius a M`. -/
theorem vt_bhmt_error_le_radius (a : ℝ) (ha0 : 0 ≤ a)
    (M : ℕ) (hM : 0 < M) :
    2*Real.pi*Real.sqrt (a*(1-a))/(M : ℝ)+Real.pi^2/(M : ℝ)^2 ≤ vtEstimateRadius a M := by
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hroot : Real.sqrt (a*(1-a)) ≤ Real.sqrt a := Real.sqrt_le_sqrt (by nlinarith)
  have hpi2 : Real.pi^2 ≤ 10 := by nlinarith [Real.pi_lt_d2,Real.pi_pos]
  have hfirst : 2*Real.pi*Real.sqrt (a*(1-a)) ≤ 8*Real.sqrt a := by
    calc
      _ ≤ 2*Real.pi*Real.sqrt a := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) (Real.sqrt_nonneg a)
  have h1 := div_le_div_of_nonneg_right hfirst hm.le
  have h2 := div_le_div_of_nonneg_right hpi2 (sq_nonneg (M : ℝ))
  unfold vtEstimateRadius
  calc
    _ ≤ (8*Real.sqrt a)/(M : ℝ)+10/(M : ℝ)^2 := add_le_add h1 h2
    _ ≤ _ := by
      rw [show (8*Real.sqrt a)/(M : ℝ)=8/(M : ℝ)*Real.sqrt a from by ring]
      linarith

/-- For unitary preparation and `M ≥ 2`, the amplitude estimate lies within the prescribed
radius with probability at least `8 / π²`. -/
theorem vt_prescribed_estimate_success (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) :
    8/Real.pi^2 ≤ ∑ z∈Finset.univ.filter
      (fun z : Fin M=>|aeEstimate M z-MeasureProb (preparedAAState A j) S| ≤
        vtEstimateRadius (MeasureProb (preparedAAState A j) S) M),
      (aeLaw M A j S hA hM).prob z := by
  have hb := (prepared_ae_bhmt_error_and_endpoints M hM A j S hA).1
  refine hb.trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => (aeLaw M A j S hA hM).nonneg z))
  intro z hz
  obtain ⟨_,hz⟩ := Finset.mem_filter.mp hz
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz.trans ?_⟩
  have hbounds := prepared_aa_good_bad_geometry A j S hA
  exact vt_bhmt_error_le_radius _ hbounds.2.2.2.2.1 M (by omega)

/-- If the prepared success mass is zero, every outcome label of positive probability has
estimate zero. -/
theorem vt_prescribed_estimate_zero_support (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I)
    (ha : MeasureProb (preparedAAState A j) S=0) (z : Fin M)
    (hz : 0 < (aeLaw M A j S hA hM).prob z) : aeEstimate M z=0 := by
  have hk : qpeKernel M 0 z=Ket (⟨0,by omega⟩ : Fin M) z := by
    simpa using (offgrid_phase_geometric_and_periodic M 0 z (by omega)).2.2 (⟨0,by omega⟩ : Fin M)
  rw [aeLaw_zero_mass M hM A j S hA ha, hk] at hz
  have he : z=(⟨0,by omega⟩ : Fin M) := by
    by_contra hn
    simp [Ket,hn] at hz
  subst z
  simp [aeEstimate]

/-- For unitary preparation and `M ≥ 2`, the estimation law equals the counted circuit's label
measurement law, and the total query and gate count is `6 * M - 3`. -/
theorem vt_prescribed_estimate_circuit_and_count (M : ℕ) (hM : 2 ≤ M)
    (A : Matrix I I ℂ) (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) :
    (∀ z,(aeLaw M A j S hA hM).prob z =
      MeasureProb (Run (aeControlledGate M (preparedMark S)) (countedAECircuit M A j)
        (TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (Ket j))))
        (Finset.univ.filter (fun p=>p.1=z))) ∧
    QueryCount (countedAECircuit M A j)+GateCount (countedAECircuit M A j)=6*M-3 := by
  constructor
  · intro z
    rfl
  · obtain ⟨hq,hg,-,-⟩ := prepared_ae_access_ledger M (by omega) A j
    rw [hq,hg]
    omega
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
