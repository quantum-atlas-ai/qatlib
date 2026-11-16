/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath
public import Qatlib.Papers.BoolHidShift11.RandomFunctions.SeparationMath

@[expose] public section


/-! # Complete old existential interfaces without execution coupling

These literal targets admit zero query fields. Their proofs are model
checks, not certifications of the source algorithm, its expected cost,
or its average-case separation. Actual circuit semantics is separate.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.RankGrowth.WeakContracts
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath
open Qatlib.Papers.BoolHidShift11.RandomFunctions.SeparationMath

/-- The old Theorem 1 record has no link from its real cost to execution. -/
theorem oldQueries {n : ℕ} (inst : BHSPInstance n)
    (_hγ : 0<minInfluence (signedFun inst.f)) :
    ∃ (outputDist : Reg n × Bool → ℝ) (expectedQueries : ℝ),
      (∀ (b : Bool) (u : Reg n),
        outputDist (u,b)=sampleDist (signedFun inst.f) inst.shift b u) ∧
      (∀ (b : Bool) (u : Reg n),
        outputDist (u,b)≠0 → b=parityDot inst.shift u) ∧
      0≤expectedQueries ∧ expectedQueries≤
        2*(n:ℝ)/Real.sqrt (minInfluence (signedFun inst.f))+1 := by
  refine ⟨fun p => sampleDist (signedFun inst.f) inst.shift p.2 p.1,0,
    fun _ _ => rfl,fun _ _ h => sampleConsist _ _ h,le_refl _,?_⟩
  positivity

/-- The old corollary's success and query scalars are likewise unconstrained by a run. -/
theorem oldCorollary {n : ℕ} (_inst : BHSPInstance n) (δ ε : ℝ)
    (_hδ : 0<δ) (hε0 : 0<ε) (hε1 : ε<1)
    (_hpromise : ∀ v : Reg n, v≠ZeroStr n → δ ≤ influence (signedFun _inst.f) v) :
    ∃ (successProb C queries : ℝ), 0<C ∧ 1-ε≤successProb ∧ 0≤queries ∧
      queries≤C*(n:ℝ)*Real.log (1/ε)/Real.sqrt δ := by
  have hl : 0≤Real.log (1/ε) := Real.log_nonneg (by
    rw [le_div_iff₀ hε0]
    linarith)
  refine ⟨1,1,0,by norm_num,by linarith,le_refl _,?_⟩
  positivity

/-- A nonnegative zero-query record satisfying exactly the old data fields. -/
def freeRecord : FreeAlgorithm where
  successProb := 1
  queryCount := fun _ => 0
  success_ge := by norm_num
  query_nonneg := fun _ => le_refl _

/-- The old average-case target only combines a free record with conditional arithmetic. -/
theorem oldSeparation : ∃ (alg : FreeAlgorithm) (C : ℝ),
    0<C ∧ (∀ n : ℕ, alg.queryCount n≤C*(n:ℝ)) ∧
      (∀ (n t : ℕ), 16≤n → (2:ℝ)^n≤3*(t:ℝ)^2+2 → 4*(n:ℝ)<(t:ℝ)) := by
  refine ⟨freeRecord,1,by norm_num,?_,?_⟩
  · intro n
    simp [freeRecord]
  · intro n t hn hc
    exact exceedLinear hn hc

end Qatlib.Papers.BoolHidShift11.RankGrowth.WeakContracts
