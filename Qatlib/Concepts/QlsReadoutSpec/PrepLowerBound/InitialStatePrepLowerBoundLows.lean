/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundStat

/-!
# Initial-state preparation query lower bound

This module converts accurate preparation of the Grover linear-system solution into successful
marked-item search. The corrected phase-oracle implementation and the search lower bound yield a
quadratic relation between instance size and circuit query count. Related mathematical
background is given in [BennettEtAl1997].

## Main statements

* `grover_solver_success`: Accurate solution preparation gives marked-item success probability
  at least 2/3.
* `initialStatePreparationLowerBoundSubgoalCorrected`: Proof of the corrected preparation
  lower-bound assertion.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

open Qatlib.Concepts.QueryComplexity.AdversarySearch

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- The measurement event selecting the marked data index and all ancillary and workspace
values. -/
def groverMarkedFiber (x : I) : Finset ((I×Bool)×W) :=
  Finset.univ.filter (fun p => p.1.1=x)

omit [DecidableEq W] in

/-- The marked measurement event is the Cartesian product of the marked singleton with the full
ancillary and workspace sets. -/
private theorem groverMarkedFiber_product (x : I) :
    groverMarkedFiber (W := W) x = ({x} ×ˢ (Finset.univ : Finset Bool)) ×ˢ Finset.univ := by
  ext p
  rcases p with ⟨⟨i,b⟩,w⟩
  cases b <;> simp [groverMarkedFiber]

/-- The solver starting state is normalized when its ancillary factors are normalized and the
data index type is nonempty. -/
theorem solverStart_normalized [Nonempty I] (ν : QState Bool) (ω : QState W)
    (hν : Normalized ν) (hω : Normalized ω) : Normalized (solverStart (I := I) ν ω) := by
  have hu : Normalized (uniformQState (I := I)) := by
    simpa [uniformQState,Uniform,Complex.ofReal_inv] using!
        normalized_uniform (I := I) Fintype.card_pos
  change Normalized (TensorState (TensorState (uniformQState (I := I)) ν) ω)
  exact normalized_tensorState (normalized_tensorState hu hν) hω

/-- The solution target is normalized for normalized ancillary factors and index cardinality at
least four. -/
theorem solutionTarget_normalized (ν : QState Bool) (ω : QState W) (x : I)
    (hν : Normalized ν) (hω : Normalized ω) (hcard : 4≤Fintype.card I) :
    Normalized (solutionTarget ν ω x) := by
  have hv := (grover_solution_norm_bounds x hcard).1
  have hn : Normalized (fun i => NormedSpace.normalize
      (stateVector (groverInverse (I := I)*ᵥbState x)) i) := by
    apply (normalized_iff_stateVector_norm _).mpr
    exact NormedSpace.norm_normalize (norm_pos_iff.mp hv)
  change Normalized (TensorState (TensorState
    (fun i => NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) i) ν) ω)
  exact normalized_tensorState (normalized_tensorState hn hν) hω

/-- The marked-event probability of the solution target equals the squared magnitude of its
normalized marked solution coordinate. -/
theorem solutionTarget_marked_probability (ν : QState Bool) (ω : QState W) (x : I)
    (hν : Normalized ν) (hω : Normalized ω) :
    MeasureProb (solutionTarget ν ω x) (groverMarkedFiber x) =
      ‖NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) x‖^2 := by
  rw [groverMarkedFiber_product]
  change MeasureProb (TensorState (TensorState
    (fun i => NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) i) ν) ω)
    (({x}×ˢFinset.univ)×ˢFinset.univ)=_
  rw [measureProb_tensorState_left hω,measureProb_tensorState_left hν]
  simp [MeasureProb,BornProb]

/-- Phase compilation preserves the probability of measuring the marked data index. -/
theorem phaseCompile_marked_probability (C : Circuit ((I×Bool)×W))
    (ψ : QState ((I×Bool)×W)) (x : I) :
    MeasureProb (Run (workspaceBitOracle (W := Bool×W) (fun i => decide (i=x)))
      (phaseCompile C) (phaseCompileStart ψ)) (groverMarkedFiber (W := Bool×W) x) =
    MeasureProb (Run (bOracleCorrected x) C ψ) (groverMarkedFiber x) := by
  rw [phaseCompile_run]
  have he : (groverMarkedFiber (W := W) x×ˢ(Finset.univ : Finset Bool)).map
      (phaseCompileEquiv (I := I) (W := W)).toEmbedding =
      groverMarkedFiber (W := Bool×W) x := by
    ext p
    simp only [Finset.mem_map_equiv,Finset.mem_product,Finset.mem_univ,and_true]
    simp only [groverMarkedFiber,Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  rw [← he,measureProb_relabelState,measureProb_tensorState_left normalized_minus]

/-- A unitary corrected-oracle run within error `ε ≤ 1 / 100` of the solution target finds the
marked index with probability at least `2 / 3` when the index cardinality is at least 150. -/
theorem grover_solver_success (ν : QState Bool) (ω : QState W) (ε : ℝ)
    (C : Circuit ((I×Bool)×W)) (hcard : 150≤Fintype.card I) (hε : ε≤1/100)
    (hC : IsUnitaryCircuit C) (hν : Normalized ν) (hω : Normalized ω) (x : I)
    (hclose : ‖stateVector (Run (bOracleCorrected x) C (solverStart ν ω))-
      stateVector (solutionTarget ν ω x)‖≤ε) :
    2/3 ≤ MeasureProb (Run (bOracleCorrected x) C (solverStart ν ω)) (groverMarkedFiber x) := by
  letI : Nonempty I := ⟨x⟩
  have hstart := solverStart_normalized (I := I) ν ω hν hω
  have hrun := hC.normalized_run (bOracleCorrected_unitary x) hstart
  have htarget := solutionTarget_normalized ν ω x hν hω (by omega)
  have hb := measureProb_sub_le_two_mul_l2 _ _ (groverMarkedFiber x) hrun htarget
  have he : ‖toEuclidean_fromVec (Run (bOracleCorrected x) C (solverStart ν ω)-
      solutionTarget ν ω x)‖≤ε := hclose
  have hm := grover_normalized_marked_five_sixths x hcard
  have hprob : 25/36≤MeasureProb (solutionTarget ν ω x) (groverMarkedFiber x) := by
    rw [solutionTarget_marked_probability ν ω x hν hω]
    nlinarith [norm_nonneg (NormedSpace.normalize (stateVector (groverInverse (I := I)*ᵥbState x)) x)]
  have hh := (abs_le.mp (hb.trans (mul_le_mul_of_nonneg_left he (by norm_num)))).1
  linarith

/-- Every unitary circuit meeting the corrected preparation accuracy hypotheses has index
cardinality at most 64 times its squared query count. -/
theorem initialStatePreparationLowerBoundSubgoalCorrected : InitialStatePreparationLowerBoundSubgoalCorrected := by
  intro I W _ _ _ _ ν ω ε C hcard hε hC hν hω hclose
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  have hresources := phaseCompile_counts_unitary C hC
  have hstart : Normalized (phaseCompileStart (solverStart (I := I) ν ω)) :=
    normalized_relabelState _ (normalized_tensorState (solverStart_normalized ν ω hν hω) normalized_minus)
  have hh := workspace_search_query_lower_bound (phaseCompile C)
    (phaseCompileStart (solverStart (I := I) ν ω)) (fun p => some p.1.1)
    hresources.2 hstart (by omega : 6≤Fintype.card I) (fun x => by
      simp only [Option.some.injEq]
      change 2/3≤MeasureProb _ (groverMarkedFiber (W := Bool×W) x)
      rw [phaseCompile_marked_probability]
      exact grover_solver_success ν ω ε C hcard hε hC hν hω x (hclose x))
  rwa [hresources.1] at hh

end Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
