/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector

/-!
# A Boolean-chain detection example

The module evaluates the corrected detector for the uniform transition matrix on `Bool` with
marked set `{true}`. It computes the initial amplitudes, the unmarked projector, and one walk
step.

For every unitary realizing the required row preparation,
`corrected_szegedy_uniform_boolean_actual_consumer` proves exact acceptance at power one and the
corresponding instruction counts. See [MagniezNayakRolandSantha2011] for the mathematical
background.

## Main statements

* `detection_uniform_boolean_gap`: gap parameter 1 for the Boolean chain.
* `corrected_szegedy_uniform_boolean_actual_consumer`: acceptance probability 1 and counts `(5,
  5, 6)`.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.WalkSearch.Detection
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.WalkSearch.Detection
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Kronecker Matrix.Norms.L2Operator

/-- The uniform Boolean transition matrix with every entry `1 / 2` satisfies `SymmetricChainGap`
with gap parameter 1. -/
theorem detection_uniform_boolean_gap :
    SymmetricChainGap (fun _ _ : Bool => (1/2:ℝ)) 1 := by
  refine ⟨⟨by intro i j; norm_num,by intro i; norm_num⟩,by intro i j; rfl,?_⟩
  intro v hv
  simp only [Fintype.sum_bool] at hv ⊢
  nlinarith

/-- Every coordinate of the uniform Boolean chain's detector initial state is `1 / 2`. -/
private theorem detection_uniform_boolean_initial (xy : Bool×Bool) :
    detectionInitial (fun _ _ : Bool => (1/2:ℝ)) xy=(1/2:ℂ) := by
  rw [detectionInitial_apply]
  norm_num [chainUniform,Real.sqrt_div]
  rw [← pow_two,inv_pow,sqrt2_sq]
  norm_num

/-- For marked set `{true}`, the unmarked row projector has entry `1 / 2` exactly when both row
indices agree and are false, and zero otherwise. -/
private theorem detection_uniform_boolean_projector (xy zw : Bool×Bool) :
    (unmarkedRowFrame (fun _ _ : Bool => (1/2:ℝ)) {true} *
      (unmarkedRowFrame (fun _ _ : Bool => (1/2:ℝ)) {true})ᴴ) xy zw =
      if xy.1=zw.1 ∧ xy.1=false then (1/2:ℂ) else 0 := by
  rw [detection_unmarked_projector_entry]
  have hs : (Real.sqrt (1/2:ℝ):ℂ)*(Real.sqrt (1/2:ℝ):ℂ)=(1/2:ℂ) := by
    rw [← pow_two,← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [hs]
  cases xy.1 <;> cases zw.1 <;> simp

/-- One corrected marked-walk step on the uniform Boolean initial state gives amplitude `1 / 2`
at pairs with true first coordinate and `-1 / 2` at pairs with false first coordinate. -/
theorem detection_uniform_boolean_walk (xy : Bool×Bool) :
    ((correctedMarkedWalk (fun _ _ : Bool => (1/2:ℝ)) {true}) *ᵥ
      detectionInitial (fun _ _ : Bool => (1/2:ℝ))) xy =
      if xy.1 then (1/2:ℂ) else -(1/2:ℂ) := by
  simp only [correctedMarkedWalk,← Matrix.mulVec_mulVec,applyGate_swapGate]
  rcases xy with ⟨x,y⟩
  cases x <;> cases y <;>
    simp only [ReflectionAbout,Matrix.mulVec_sub,Matrix.smul_mulVec,Matrix.one_mulVec,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
      Fintype.sum_bool,Matrix.one_apply,Matrix.sub_apply,Matrix.smul_apply,
      Prod.swap_prod_mk,detection_uniform_boolean_projector,detection_uniform_boolean_initial] <;>
      norm_num

/-- For any unitary preparing the uniform Boolean row states, the chain has gap parameter 1 and
the power-one detector with marked set `{true}` accepts with probability 1 using counts `(5,
5, 6)`. See [MagniezNayakRolandSantha2011]. -/
theorem corrected_szegedy_uniform_boolean_actual_consumer :
    ∀ (j : Bool) (U : Matrix (Bool×Bool) (Bool×Bool) ℂ),
    U∈unitaryGroup (Bool×Bool) ℂ →
    (∀ i,U*ᵥTensorState (Ket i) (Ket j)=SzegedyIsometry (fun _ _ : Bool=>(1/2:ℝ))*ᵥKet i) →
    SymmetricChainGap (fun _ _ : Bool=>(1/2:ℝ)) 1 ∧
    detectionProbability U {true} j 1=1 ∧
    detectionCounts (detectionProgram j 1)=(5,5,6) := by
  intro j U hU hp
  refine ⟨detection_uniform_boolean_gap,?_,detectionProgram_actual_counts j 1⟩
  unfold detectionProbability
  rw [(corrected_szegedy_actual_detector_and_counts Bool _ {true} j U 1
    detection_uniform_boolean_gap.1 hU hp).2.1]
  have hout (v : DetectionSpace Bool) :
      (detectionMarkGate {true} *ᵥ
        detectionInterference (correctedMarkedWalk (fun _ _ : Bool => (1/2:ℝ)) {true})
          (detectionInitial (fun _ _ : Bool => (1/2:ℝ))) 1) v =
      if v.1=(!v.2.2.1) ∧ v.2.1=v.2.2.1 then (1/2:ℂ) else 0 := by
    change ApplyGate (permMatrix (detectionMarkPermutation {true})) _ v = _
    rw [applyGate_permMatrix (detectionMarkPermutation_involutive {true})]
    rcases v with ⟨b,c,x,y⟩
    cases b <;> cases c <;> cases x <;>
      norm_num [detectionInterference,detectionMarkPermutation,
        detection_uniform_boolean_initial,pow_one,detection_uniform_boolean_walk]
  simp only [MeasureProb,detectionAccept,Finset.sum_filter,Finset.mem_filter,
    Finset.mem_univ,true_and,BornProb]
  simp_rw [hout]
  norm_num [Fintype.sum_prod_type]

end Qatlib.Concepts.WalkSearch.Detection
