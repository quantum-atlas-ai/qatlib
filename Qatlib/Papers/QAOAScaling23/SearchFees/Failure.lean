/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.PlainSlot
import Qatlib.Papers.QAOAScaling23.SearchFees.AngleSplit

/-!
# Failure probabilities of interleaved search

`failure` records the probability that a scheduled search produces no result and satisfies a
multiplicative recurrence. Plain-trial interleaving improves this probability, leading to
separate bounds for large marked mass and for schedules whose amplification windows pass the
low-mass cutoff.

This development accompanies the study of QAOA-assisted minimum finding in [ShaydulinEtAl2024].

## Main statements

* `highQ_failure`: With exact validation and marked mass at least `1/2`, interleaved geometric
  search with `T` stages has failure probability at most `(1/2)^T`.
* `lowQ_failure_cutoff`: With exact validation and marked mass `sin θ` squared for `0 < θ <
  π/2`, a window satisfying `geometricWindow M j * sin (2 * θ) ≥ 1` bounds real failure
  probability by `(25/32)^(T - j)`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchFees
variable {I:Type} [Fintype I] [DecidableEq I]

/-- The probability that scheduled search returns no candidate. -/
def failure (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (ms:List ℕ) : ℝ≥0∞ := event (searchForSchedule U hU seed S valid ms) (fun tr=>tr.result=none)

/-- Failure on a nonempty schedule is the product of first-stage failure and tail failure. -/
theorem failure_cons (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (m:ℕ) (ms:List ℕ) :
    failure U hU seed S valid (m::ms)=fail U hU seed S valid m*failure U hU seed S valid ms :=
  search_event_none_recursion U hU seed S valid m ms

/-- Search with an empty schedule fails with probability one. -/
theorem failure_nil (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) : failure U hU seed S valid []=1 := by
  unfold failure searchForSchedule
  rw [Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq,expectation_pure]
  simp [emptySearchTrace]

/-- Interleaving plain trials cannot increase the failure probability of a schedule. -/
theorem interleaved_failure_le_original (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (ms:List ℕ) :
    failure U hU seed S valid (interleavePlain ms)≤failure U hU seed S valid ms := by
  induction ms with
  | nil=>simp [interleavePlain]
  | cons m ms ih=>
    simp only [interleavePlain,List.flatMap_cons,List.cons_append,List.nil_append,failure_cons] at *
    calc
      _ ≤ 1*(fail U hU seed S valid m*failure U hU seed S valid ms) :=
        mul_le_mul' (by
          have h:=event_compl (preparedAASampled U hU seed S (Nat.clog 2 1) 1 3)
              (searchSlotFail valid)
          exact (le_add_right le_rfl).trans h.le) (mul_le_mul_right ih _)
      _ = _ := one_mul _

/-- The failure probability of an interleaved schedule is at most the plain-trial failure
probability raised to the original schedule length. -/
theorem interleaved_failure_plain_power (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (ms:List ℕ) :
    failure U hU seed S valid (interleavePlain ms)≤(fail U hU seed S valid 1)^ms.length := by
  induction ms with
  | nil=>simp [interleavePlain,failure_nil]
  | cons m ms ih=>
    simp only [interleavePlain,List.flatMap_cons,List.cons_append,List.nil_append,failure_cons,List.length_cons]
    have hm:fail U hU seed S valid m≤1 := by
      have h:=event_compl (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (searchSlotFail valid)
      exact (le_add_right le_rfl).trans h.le
    calc
      _ ≤ fail U hU seed S valid 1*(1*(fail U hU seed S valid 1)^ms.length) :=
        mul_le_mul_right (mul_le_mul' hm ih) _
      _ = _ := by rw [one_mul,pow_succ']

/-- With exact validation and marked mass at least `1/2`, interleaved geometric search with `T`
stages has failure probability at most `(1/2)^T`. -/
theorem highQ_failure (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:(1/2:ℝ)≤MeasureProb (preparedAAState U seed) S)
    (M T:ℕ) :
    failure U hU seed S valid (interleavePlain (geometricSearchSchedule M T))≤(1/2:ℝ≥0∞)^T := by
  have h:=interleaved_failure_plain_power U hU seed S valid (geometricSearchSchedule M T)
  have hf:fail U hU seed S valid 1≤(1/2:ℝ≥0∞) := by
    rw [plain_failure U hU seed S valid hvalid]
    have hh:(1/2:ℝ≥0∞)≤ENNReal.ofReal (MeasureProb (preparedAAState U seed) S) := by
      convert ENNReal.ofReal_le_ofReal hQ using 1
      norm_num [ENNReal.ofReal_div_of_pos]
    have hs:=tsub_le_tsub_left hh 1
    have hhalf:(1/2:ℝ≥0∞)+(1/2:ℝ≥0∞)=1 := by
      calc
        _ = 2*(2:ℝ≥0∞)⁻¹ := by simp only [div_eq_mul_inv,one_mul];ring
        _ = _ := ENNReal.mul_inv_cancel (by norm_num) (by finiteness)
    have he:(1/2:ℝ≥0∞)=1-(1/2:ℝ≥0∞) := ENNReal.eq_sub_of_add_eq (by finiteness) hhalf
    exact hs.trans_eq he.symm
  simpa only [geometricSearchSchedule,List.length_ofFn] using h.trans (ENNReal.pow_le_pow_left hf)

/-- With exact validation and marked mass `sin θ` squared for `0 < θ < π/2`, a window satisfying
`geometricWindow M j * sin (2 * θ) ≥ 1` bounds real failure probability by `(25/32)^(T -
j)`. -/
theorem lowQ_failure_cutoff (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T j:ℕ) (θ:ℝ)
    (h0:0<θ) (h1:θ<Real.pi/2) (hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2)
    (hwin:1≤(geometricWindow M j:ℝ)*Real.sin (2*θ)) :
    (failure U hU seed S valid (interleavePlain (geometricSearchSchedule M T))).toReal≤(25/32:ℝ)^(T-j) := by
  have hle:=interleaved_failure_le_original U hU seed S valid (geometricSearchSchedule M T)
  have hf:failure U hU seed S valid (geometricSearchSchedule M T)≠⊤ := by
    have hp:=event_compl (searchForSchedule U hU seed S valid (geometricSearchSchedule M T))
        (fun tr=>tr.result=none)
    exact ne_top_of_le_ne_top (by norm_num : (1:ℝ≥0∞)≠⊤) ((le_add_right le_rfl).trans hp.le)
  exact (ENNReal.toReal_mono hf hle).trans
    (geometric_search_actual_cutoff_failure_probability U hU seed S valid M T j θ hvalid h0 h1 hmass hwin)

/-- With exact validation and marked mass one, interleaving any nonempty schedule gives failure
probability zero. -/
theorem Q_one_failure (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:MeasureProb (preparedAAState U seed) S=1)
    (m:ℕ) (ms:List ℕ) : failure U hU seed S valid (interleavePlain (m::ms))=0 := by
  simp only [interleavePlain,List.flatMap_cons,List.cons_append,List.nil_append,failure_cons,
    plain_Q_one U hU seed S valid hvalid hQ,zero_mul]
end Qatlib.Papers.QAOAScaling23.SearchFees
