/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.Gate.Section6SourceGateSubgoalStat
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Reflection.Basic
import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SearchStopping.KnownCount

namespace Qatlib.Concepts.SearchStopping.GateCore
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open scoped Classical BigOperators
set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

private theorem sourceGate_outer_conjugate (M : Matrix I I ℂ) (v : QState I) :
    outerProduct (M *ᵥ v) = M * outerProduct v * star M := by
  ext i j
  have starNorm : ∀ z : ℂ, (starRingEnd ℂ) z = star z := fun _ => rfl
  simp only [outerProduct_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.star_apply, map_sum, map_mul]
  simp only [starNorm]
  rw [Finset.mul_sum]
  simp only [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sourceGate_reflection_conjugate {M : Matrix I I ℂ}
    (hM : M ∈ Matrix.unitaryGroup I ℂ) {v w : QState I}
    (_hv : Normalized v) (_hw : Normalized w) (hvw : M *ᵥ v = w) :
    M * ReflectionAbout (outerProduct v) * star M = ReflectionAbout (outerProduct w) := by
  have ho : M * outerProduct v * star M = outerProduct w := by
    rw [← sourceGate_outer_conjugate, hvw]
  have hunit : M * star M = 1 := Matrix.mem_unitaryGroup_iff.mp hM
  simp only [ReflectionAbout, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, ho, hunit]

omit [DecidableEq I] in

private theorem sourceGate_uniform_outer : outerProduct (Uniform I) = AverageProjection I := by
  have hs : (Real.sqrt (Fintype.card I) : ℂ)^2 = (Fintype.card I : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast
  ext i j
  simp only [outerProduct_apply, Uniform, AverageProjection, Matrix.of_apply]
  rw [map_inv₀, Complex.conj_ofReal, ← pow_two, inv_pow, hs]

private theorem sourceGate_matrix (hN : 0 < Fintype.card I)
    (T' : Matrix I I ℂ) (v : QState I) (hT : T' ∈ Matrix.unitaryGroup I ℂ)
    (hv : Normalized v) (hvw : T' *ᵥ v = Uniform I) :
    -(T' * SourceZeroReflect v * star T') = Diffusion I := by
  have hz : SourceZeroReflect v = -ReflectionAbout (outerProduct v) := by
    rw [SourceZeroReflect, ReflectionAbout]
    module
  rw [hz, Matrix.mul_neg, Matrix.neg_mul, neg_neg,
    sourceGate_reflection_conjugate hT hv (normalized_uniform hN) hvw,
    sourceGate_uniform_outer]
  rfl

omit [DecidableEq I] in

private theorem sourceGate_run_smul (O : Matrix I I ℂ) (C : Circuit I)
    (a : ℂ) (ψ : QState I) : Run O C (a • ψ) = a • Run O C ψ := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [Run, ApplyGate, Matrix.mulVec_smul, ih]

omit [DecidableEq I] in

private theorem sourceGate_plain_repeat (O D : Matrix I I ℂ) (ψ : QState I) (j : ℕ) :
    Run O (RepeatCircuit [Step.query, Step.gate (-D)] j) ψ =
      (-1 : ℂ)^j • Run O (RepeatCircuit [Step.query, Step.gate D] j) ψ := by
  induction j generalizing ψ with
  | zero => simp [RepeatCircuit]
  | succ j ih =>
    simp only [RepeatCircuit, run_append, run_query, run_gate, run_nil,
      ApplyGate, Matrix.neg_mulVec]
    rw [show -(D *ᵥ (O *ᵥ ψ)) = (-1 : ℂ) • (D *ᵥ (O *ᵥ ψ)) from
      (neg_one_smul ℂ _).symm, sourceGate_run_smul, ih, smul_smul, pow_succ]
    congr 1
    ring

theorem section6SourceGateSubgoal : Section6SourceGateSubgoal := by
  intro I _ _ hN T' v hT hv hvw A j
  have hm := sourceGate_matrix hN T' v hT hv hvw
  have hb : SourceGateBlock T' v = GroverStep I := by
    rw [SourceGateBlock, GroverStep, hm]
  have hc (k : ℕ) : SourceGateCircuit T' v k = GroverCircuit I k := by
    rw [SourceGateCircuit, hb]
    rfl
  have hp : SourceGatePlainBlock T' v = [Step.query, Step.gate (-Diffusion I)] := by
    rw [SourceGatePlainBlock, (neg_eq_iff_eq_neg.mp hm)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc]
    exact isUnitaryCircuit_groverCircuit hN j
  · rw [hc]
    exact queryCount_groverCircuit j
  · rw [hc]
    rfl
  · simp only [SourceGatePlainCircuit, hp, GroverState, GroverCircuit, GroverStep]
    exact sourceGate_plain_repeat (SetOracle A) (Diffusion I) (Uniform I) j
  · intro θ hθ hs hcos
    rw [hc]
    exact measureProb_groverState hN A θ hθ hs hcos j

end Qatlib.Concepts.SearchStopping.GateCore
