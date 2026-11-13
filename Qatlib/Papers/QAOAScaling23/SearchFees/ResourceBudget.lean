/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.LowQBudget
import Qatlib.Papers.QAOAScaling23.SearchFees.HighQBudget

/-!
# Inverse-square-root native resource budgets

The low- and high-mass resource estimates combine into `actual_sqrt_mass_budget`, expressed
directly in terms of the marked Born mass. The endpoint of mass one is handled separately, while
intermediate masses are represented by a first-quadrant amplification angle.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `actual_mass_angle`: Every `Q` strictly between zero and one has an angle `0 < θ < π/2` with
  `sin θ = sqrt Q`.
* `actual_sqrt_mass_budget`: With exact validation, positive marked mass `Q`, and `M * sqrt Q ≥
  1`, every non-stage ledger of interleaved geometric search has expectation at most
  `ENNReal.ofReal (1000 / sqrt Q)`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchFees
variable {I:Type} [Fintype I] [DecidableEq I]

/-- With exact validation, marked mass `sin θ` squared for `0 < θ < π/2`, and `M * sin θ ≥ 1`,
each non-stage ledger of interleaved geometric search has expectation at most
`ENNReal.ofReal (1000 / sin θ)`. -/
theorem interleaved_budget_theta (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T:ℕ) (θ:ℝ)
    (h0:0<θ) (h1:θ<Real.pi/2) (hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (hcap:1≤(M:ℝ)*Real.sin θ) (f:Fee) (hf:f≠.stages) :
    expected U hU seed S valid f (interleavePlain (geometricSearchSchedule M T))≤ENNReal.ofReal (1000/Real.sin θ) := by
  by_cases hQ:(Real.sin θ)^2≤1/2
  · exact lowQ_interleaved_budget U hU seed S valid hvalid M T θ h0 h1 hmass hQ hcap f hf
  · have hh:(1/2:ℝ)≤MeasureProb (preparedAAState U seed) S := by rw [hmass];linarith
    have hs:0<Real.sin θ:=Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    refine (highQ_interleaved_budget U hU seed S valid hvalid hh f M T).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hs).mpr
    nlinarith [Real.sin_le_one θ]

/-- The marked mass of a state prepared by a unitary is at most one. -/
theorem prepared_mass_le_one (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) :
    MeasureProb (preparedAAState U seed) S≤1 := by
  let p:=preparedAASampled U hU seed S (Nat.clog 2 1) 1 3
  let P:=fun out:Option (I×ℕ)×ℕ×ℕ=>∃y g,out.1=some (y,g) ∧ y∈S
  have he:=event_compl p P
  have hp:event p P≤1:=(le_add_right le_rfl).trans he.le
  change event (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3) _≤1 at hp
  rw [plain_marked_mass] at hp
  have h:=ENNReal.toReal_mono (by norm_num : (1:ℝ≥0∞)≠⊤) hp
  simpa only [ENNReal.toReal_one,ENNReal.toReal_ofReal (measureProb_nonneg _ _)] using h

/-- Every `Q` strictly between zero and one has an angle `0 < θ < π/2` with `sin θ = sqrt Q`. -/
theorem actual_mass_angle (Q:ℝ) (hQ0:0<Q) (hQ1:Q<1) :
    ∃θ:ℝ,0<θ ∧ θ<Real.pi/2 ∧ Real.sin θ=Real.sqrt Q := by
  have hs:0<Real.sqrt Q:=Real.sqrt_pos.mpr hQ0
  have hsq:Real.sqrt Q<1:=by nlinarith [Real.sq_sqrt hQ0.le]
  exact ⟨Real.arcsin (Real.sqrt Q),Real.arcsin_pos.mpr hs,Real.arcsin_lt_pi_div_two.mpr hsq,
    Real.sin_arcsin (by linarith) hsq.le⟩

/-- With exact validation and marked mass one, a nonempty interleaved schedule has expected
ledger equal to that of its first plain trial. -/
theorem Q_one_expected (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:MeasureProb (preparedAAState U seed) S=1)
    (f:Fee) (m:ℕ) (ms:List ℕ) :
    expected U hU seed S valid f (interleavePlain (m::ms))=slot U hU seed S f 1 := by
  rw [interleaved_expected_cons,plain_Q_one U hU seed S valid hvalid hQ,zero_mul,add_zero]

/-- With exact validation and marked mass one, every expected ledger of interleaved geometric
search is at most one. -/
theorem Q_one_budget (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:MeasureProb (preparedAAState U seed) S=1)
    (f:Fee) (M T:ℕ) : expected U hU seed S valid f (interleavePlain (geometricSearchSchedule M T))≤1 := by
  cases T with
  | zero=>simp [geometricSearchSchedule,interleavePlain,expected_nil]
  | succ T=>
    rw [← schedFrom_zero,schedFrom_succ,Q_one_expected U hU seed S valid hvalid hQ]
    exact plain_slot_le_one U hU seed S f

/-- With exact validation, positive marked mass `Q`, and `M * sqrt Q ≥ 1`, every non-stage
ledger of interleaved geometric search has expectation at most `ENNReal.ofReal (1000 / sqrt
Q)`. -/
theorem actual_sqrt_mass_budget (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T:ℕ)
    (hQ:0<MeasureProb (preparedAAState U seed) S)
    (hcap:1≤(M:ℝ)*Real.sqrt (MeasureProb (preparedAAState U seed) S)) (f:Fee) (hf:f≠.stages) :
    expected U hU seed S valid f (interleavePlain (geometricSearchSchedule M T))≤
      ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) := by
  have hQ1:=prepared_mass_le_one U hU seed S
  rcases eq_or_lt_of_le hQ1 with he|hl
  · rw [he]
    refine (Q_one_budget U hU seed S valid hvalid he f M T).trans ?_
    norm_num
  · obtain ⟨θ,h0,h1,hθ⟩:=actual_mass_angle _ hQ hl
    have hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2 := by
      rw [hθ,Real.sq_sqrt hQ.le]
    have hc:1≤(M:ℝ)*Real.sin θ:=by simpa only [hθ] using hcap
    simpa only [hθ] using
        interleaved_budget_theta U hU seed S valid hvalid M T θ h0 h1 hmass hc f hf
end Qatlib.Papers.QAOAScaling23.SearchFees
