/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.SqEstimation.RejectionSample.SQRejectionAndNorm
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.SqEstimation.RejectionSample
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def sqClosureToyInputs (j b : Bool) : ℂ := if j && !b then -1 else 1
noncomputable def sqClosureToyEnvelope (_j _b : Bool) : ℂ := 1

noncomputable def sqClosureToySource : FinDist Bool where
  prob _ := 1/2
  nonneg _ := by norm_num
  sum_one := by norm_num [Fintype.sum_bool]

noncomputable def sqClosureToyCoin (b : Bool) : FinDist Bool where
  prob z := if z=b then 1 else 0
  nonneg z := by split_ifs <;> norm_num
  sum_one := by cases b <;> simp

theorem sqClosureToyInputs_envelope (j : Bool) : SQEnvelope (sqClosureToyInputs j) (sqClosureToyEnvelope j) := by
  cases j <;> constructor
  all_goals first
    | norm_num [sqClosureToyInputs,sqClosureToyEnvelope,Fintype.sum_bool,Complex.normSq_apply]
    | (intro b;cases b <;> norm_num [sqClosureToyInputs,sqClosureToyEnvelope,Complex.normSq_apply])

theorem sqClosureToy_linear (b : Bool) :
    sqLinearValue (fun _ : Bool => (1 : ℂ)) sqClosureToyInputs b=if b then 2 else 0 := by
  cases b <;> simp [sqLinearValue,sqClosureToyInputs,Fintype.sum_bool]

theorem sqClosureToy_linearEnvelope (b : Bool) :
    sqLinearEnvelope (fun _ : Bool => (1 : ℂ)) sqClosureToyEnvelope b=2 := by
  norm_num [sqLinearEnvelope,sqClosureToyEnvelope,Fintype.sum_bool,Complex.normSq_apply]

theorem sq_rejection_cancellation_actual_consumer : (∀ j : Bool,SQEnvelope (sqClosureToyInputs j) (sqClosureToyEnvelope j)) ∧
  (∀ b : Bool,sqLinearValue (fun _ : Bool=>(1:ℂ)) sqClosureToyInputs b= if b then 2 else 0) ∧
  (∀ b : Bool,sqLinearEnvelope (fun _ : Bool=>(1:ℂ)) sqClosureToyEnvelope b=2) ∧
  (∀ b : Bool,(sqLinearQuery (fun _ : Bool=>(1:ℂ)) sqClosureToyInputs b).2=2) ∧
  ∃ (p : FinDist Bool) (coin : Bool→FinDist Bool),
    (∀ b,p.prob b=1/2) ∧ (∀ b,(coin b).prob true= if b then 1 else 0) ∧
    (∀ B : ℕ,
      (∑ ω∈Finset.univ.filter (fun ω : Fin B→Bool×Bool => (sqRejectRun ω).1= none),
        sqTrialProduct p coin ω)=(1/2:ℝ)^B ∧
      (∑ ω∈Finset.univ.filter (fun ω : Fin B→Bool×Bool => (sqRejectRun ω).1= some true),
        sqTrialProduct p coin ω)=1-(1/2:ℝ)^B ∧
      (∑ ω∈Finset.univ.filter (fun ω : Fin B→Bool×Bool => (sqRejectRun ω).1= some false),
        sqTrialProduct p coin ω)=0 ∧
      (∑ ω : Fin B→Bool×Bool,sqTrialProduct p coin ω*((sqRejectRun ω).2:ℝ))≤8)
 := by
  have hl := sqClosureToy_linear
  have he := sqClosureToy_linearEnvelope
  refine ⟨sqClosureToyInputs_envelope,hl,he,?_,?_⟩
  · intro b
    exact (sqLinearQuery_value_count (fun _ : Bool => 1) sqClosureToyInputs b).2
  · refine ⟨sqClosureToySource,sqClosureToyCoin,fun _ => rfl,?_,?_⟩
    · intro b
      cases b <;> simp [sqClosureToyCoin]
    · intro B
      let u := sqLinearValue (fun _ : Bool => (1 : ℂ)) sqClosureToyInputs
      let uh := sqLinearEnvelope (fun _ : Bool => (1 : ℂ)) sqClosureToyEnvelope
      have hen : SQEnvelope u uh := by
        constructor
        · norm_num [u,hl,Fintype.sum_bool,Complex.normSq_apply]
        · intro b
          cases b <;> norm_num [u,uh,hl,he,Complex.normSq_apply]
      have hp : ∀ b,sqClosureToySource.prob b=Complex.normSq (uh b)/(∑ b,Complex.normSq (uh b)) := by
        intro b
        norm_num [sqClosureToySource,uh,he,Fintype.sum_bool,Complex.normSq_apply]
      have hc : ∀ b,(sqClosureToyCoin b).prob true=sqRatio u uh b := by
        intro b
        cases b <;> norm_num [sqClosureToyCoin,sqRatio,u,uh,hl,he,Complex.normSq_apply]
      have h :=
          sq_rejection_actual_capped_law_and_cost Bool u uh sqClosureToySource sqClosureToyCoin B hen hp hc
      norm_num [u,uh,hl,he,Fintype.sum_bool,Complex.normSq_apply] at h
      exact ⟨h.2.1,h.2.2.1.2,h.2.2.1.1,h.2.2.2.2.1⟩

end Qatlib.Concepts.SqEstimation.RejectionSample
