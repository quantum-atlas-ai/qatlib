/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeDefs
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Foundations.BornMetrics.EventProbability

/-!
# Growing stopping histories

`GrowingVtLegal` describes stages that fix the already reached stopped basis states while the
history grows from the empty set to the full payload space. The module defines
`reachedStoppedMass`, its increments, and `reachedTav`, and proves preservation and monotonicity
laws.

This development concerns variable-time amplitude amplification in [Ambainis2012].

## Main statements

* `growing_stage_preserves_reached`: preservation of previously reached stopped components.
* `reached_stopped_mass_mono` and `reached_pstop_nonneg`: monotonicity and nonnegative
  increments.
* `growing_prefix_unitary`: unitarity of every prefix.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LinearCombination

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Matrix
open scoped Classical
variable {C : Type} [Fintype C] [DecidableEq C]

/-- The stopped basis labels whose payload lies in the history at prefix `k`. -/
def reachedStoppedSet (history : ℕ → Finset C) (k : ℕ) : Finset (VtSpace C) :=
  Finset.univ.filter fun p=>p.1≠vtRunningFlag ∧ p.2∈history k

/-- A unitary stage that fixes each basis state in the currently reached stopped set. -/
def IsGrowingVtStage (history : ℕ → Finset C) (k : ℕ) (U : Matrix (VtSpace C) (VtSpace C) ℂ) : Prop :=
  U∈Matrix.unitaryGroup (VtSpace C) ℂ ∧
    ∀ p∈reachedStoppedSet history k,∀ q,U q p=if q=p then 1 else 0

/-- A stage sequence with an increasing history, empty initial history, full final history, and
a valid growing-history stage at each index. -/
def GrowingVtLegal (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C) : Prop :=
  history 0=∅ ∧ (∀ k,history k⊆history (k+1)) ∧ history stages.length=Finset.univ ∧
    ∀ k,(h : k < stages.length) → IsGrowingVtStage history k stages[k]

/-- The measurement mass of the reached stopped set after the first `k` stages applied to `ψ`. -/
def reachedStoppedMass (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (ψ : QState (VtSpace C)) (k : ℕ) : ℝ :=
  MeasureProb (vtState stages k ψ) (reachedStoppedSet history k)

/-- The increase in reached stopped mass from prefix `k` to prefix `k + 1`. -/
def reachedPstop (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (ψ : QState (VtSpace C)) (k : ℕ) : ℝ :=
  reachedStoppedMass stages history ψ (k+1)-reachedStoppedMass stages history ψ k

/-- The square root of the sum of reached stopping increments weighted by squared dyadic
stopping times, starting from `Ket j₀`. -/
def reachedTav (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (j₀ : VtSpace C) : ℝ :=
  Real.sqrt (∑ j∈Finset.range stages.length,reachedPstop stages history (Ket j₀) j*(stopTime j)^2)

/-- Inclusion of consecutive history sets implies inclusion of the corresponding reached stopped
sets. -/
theorem reachedStoppedSet_mono (history : ℕ → Finset C) (k : ℕ) (h : history k⊆history (k+1)) :
    reachedStoppedSet history k⊆reachedStoppedSet history (k+1) := by
  intro p hp
  obtain ⟨_,hflag,hpay⟩:=Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hflag,h hpay⟩

/-- A growing-history stage fixes every basis ket in the reached stopped set. -/
theorem growing_stage_reached_ket {history : ℕ → Finset C} {k : ℕ} {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsGrowingVtStage history k U) (p : VtSpace C) (hp : p∈reachedStoppedSet history k) :
    U*ᵥKet p=Ket p := by
  funext q
  rw [mulVec_ket_apply,hU.2 p hp q]
  rfl

/-- The matrix row of a growing-history stage at a reached stopped label equals the
corresponding identity row. -/
theorem growing_stage_reached_row {history : ℕ → Finset C} {k : ℕ} {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsGrowingVtStage history k U) (p : VtSpace C) (hp : p∈reachedStoppedSet history k) (q : VtSpace C) :
    U p q=if p=q then 1 else 0 := by
  have hunit : Uᴴ*U=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] using hU.1
  have ha : Uᴴ*ᵥKet p=Ket p := by
    calc
      _ = Uᴴ*ᵥ(U*ᵥKet p) := by rw [growing_stage_reached_ket hU p hp]
      _ = _ := by rw [Matrix.mulVec_mulVec,hunit,Matrix.one_mulVec]
  have he:=congrArg star (congrFun ha q)
  simpa [mulVec_ket_apply,Matrix.conjTranspose_apply,Ket,eq_comm] using he

/-- A growing-history stage preserves the collapse of any state onto the currently reached
stopped set. -/
theorem growing_stage_preserves_reached {history : ℕ → Finset C} {k : ℕ} {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsGrowingVtStage history k U) (ψ : QState (VtSpace C)) :
    Collapse (ApplyGate U ψ) (reachedStoppedSet history k)=Collapse ψ (reachedStoppedSet history k) := by
  funext p
  rw [collapse_apply,collapse_apply]
  by_cases hp : p∈reachedStoppedSet history k
  · simp only [if_pos hp]
    simp [ApplyGate,Matrix.mulVec,dotProduct,growing_stage_reached_row hU p hp]
  · simp [hp]

/-- A growing-history stage preserves measurement mass on the currently reached stopped set. -/
theorem growing_stage_reached_mass {history : ℕ → Finset C} {k : ℕ} {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsGrowingVtStage history k U) (ψ : QState (VtSpace C)) :
    MeasureProb (ApplyGate U ψ) (reachedStoppedSet history k)=MeasureProb ψ (reachedStoppedSet history k) := by
  rw [← sum_normSq_collapse,growing_stage_preserves_reached hU,sum_normSq_collapse]

/-- The prefix matrix at `k + 1` equals the stage at index `k` multiplied by the prefix matrix
at `k`. -/
theorem vt_prefix_step (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (k : ℕ) (hk : k < stages.length) :
    vtRunMatrix stages (k+1)=stages[k]*vtRunMatrix stages k := by
  rw [vtRunMatrix,List.take_succ_eq_append_getElem hk,List.foldl_append]
  rfl

/-- For a legal growing-history run, reached stopped mass cannot decrease between consecutive
valid prefixes. -/
theorem reached_stopped_mass_mono (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hlegal : GrowingVtLegal stages history) (ψ : QState (VtSpace C)) (k : ℕ) (hk : k < stages.length) :
    reachedStoppedMass stages history ψ k ≤ reachedStoppedMass stages history ψ (k+1) := by
  have hU:=hlegal.2.2.2 k hk
  have he : vtState stages (k+1) ψ=ApplyGate stages[k] (vtState stages k ψ) := by
    rw [vtState,vt_prefix_step stages k hk,← Matrix.mulVec_mulVec]
    rfl
  unfold reachedStoppedMass
  rw [he,← growing_stage_reached_mass hU (vtState stages k ψ)]
  exact measureProb_mono _ (reachedStoppedSet_mono history k (hlegal.2.1 k))

/-- Every valid reached stopping increment of a legal growing-history run is nonnegative. -/
theorem reached_pstop_nonneg (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hlegal : GrowingVtLegal stages history) (ψ : QState (VtSpace C)) (k : ℕ) (hk : k < stages.length) :
    0 ≤ reachedPstop stages history ψ k := sub_nonneg.mpr (reached_stopped_mass_mono stages history hlegal ψ k hk)

/-- Every prefix matrix of a legal growing-history run is unitary. -/
theorem growing_prefix_unitary (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C)
    (hlegal : GrowingVtLegal stages history) (k : ℕ) : vtRunMatrix stages k∈Matrix.unitaryGroup (VtSpace C) ℂ := by
  have hs : ∀ U∈stages,U∈Matrix.unitaryGroup (VtSpace C) ℂ := by
    intro U hU
    obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hU
    exact he ▸ (hlegal.2.2.2 i hi).1
  have hf : ∀ (us : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (A : Matrix (VtSpace C) (VtSpace C) ℂ),
      (∀ U∈us,U∈Matrix.unitaryGroup (VtSpace C) ℂ) → A∈Matrix.unitaryGroup (VtSpace C) ℂ →
      us.foldl (fun A U=>U*A) A∈Matrix.unitaryGroup (VtSpace C) ℂ := by
    intro us
    induction us with
    | nil=>intro A _ hA;exact hA
    | cons U us ih=>
      intro A hU hA
      exact ih (U*A) (fun V hV=>hU V (List.mem_cons_of_mem U hV))
          ((Matrix.unitaryGroup _ _).mul_mem (hU U List.mem_cons_self) hA)
  exact hf (stages.take k) 1 (fun U hU=>hs U (List.mem_of_mem_take hU))
      (Matrix.unitaryGroup _ _).one_mem
end Qatlib.Papers.VarTimeAmpAmp10.StopModel
