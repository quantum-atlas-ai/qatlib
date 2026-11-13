/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
import Qatlib.Concepts.ShadowModels.ShadowChannel.ObservedInstrument
import Qatlib.Concepts.GibbsMetropolis.RationalBath.RationalRejectionConsumers
import Qatlib.Concepts.GibbsMetropolis.RationalBath.DiagonalMetropolisKernel

/-!
# Rational heat-bath instruments and mixing

`rationalHeatBathProgram` measures a basis label and applies a permutation determined by a
classical rejection-sampling outcome. Weighted Kraus operators define
`rationalHeatBathInstrument` and connect its branch probabilities to the recorded classical
events.

The channel is an explicit mixture of replacement by `rationalHeatBathDensity` and dephasing.
Closed formulas for its powers yield trace-norm mixing bounds with an arbitrary finite reference
system. See [TemmeEtAl2011] for background.

## Main statements

* `rational_heat_bath_derived_channel_and_stationarity`: The heat-bath target is stationary, the
  rejection probability is at most one half, and the channel has the explicit
  replacement-and-dephasing formula.
* `rational_heat_bath_derived_reference_mixing_budget`: For positive semidefinite
  system-reference inputs and positive step count, the replacement error is at most twice the
  rejection factor times the input trace norm, yielding the stated binary precision budget.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.ShadowModels.ShadowChannel

namespace Qatlib.Concepts.GibbsMetropolis.RationalBath

open Matrix
open scoped ComplexOrder Classical BigOperators Matrix.Norms.L2Operator ENNReal

/-- The diagonal density with entries equal to the integer weights divided by their positive
total. -/
noncomputable def rationalHeatBathDensity {N : ℕ} (w : Fin N → ℕ) (hW : 0 < weightTotal w) :
    Operator N :=
  Matrix.diagonal fun i => Complex.ofReal ((w i : ℝ) / (weightTotal w : ℝ))

/-- The matrix swapping basis labels `i` and `j` and fixing all other labels. -/
noncomputable def rationalHeatBathSwap {N : ℕ} (i j : Fin N) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if a = j then (if b = i then (1 : ℂ) else 0)
    else if a = i then (if b = j then (1 : ℂ) else 0)
    else if a = b then (1 : ℂ) else 0

/-- Swap the measured label with the selected label, or apply the identity when no label is
selected. -/
noncomputable def rationalHeatBathPerm {N : ℕ} (choice : Option (Fin N)) (i : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  match choice with
  | some j => rationalHeatBathSwap i j
  | none => 1

/-- Measure the computational basis label and apply the permutation determined by the optional
sampled label. -/
noncomputable def rationalHeatBathProgram {N : ℕ} (choice : Option (Fin N)) :
    ObservedCircuit (Fin N) :=
  .measure N (fun i => i) (fun i => .step (.gate (rationalHeatBathPerm choice i)) (.halt true))

/-- The real one-trial rejection probability using the ceiling binary logarithm of the total
weight as the bit width. -/
noncomputable def rationalHeatBathReject {N : ℕ} (w : Fin N → ℕ) : ℝ :=
  (rationalRejectMass w (Nat.clog 2 (weightTotal w))).toReal

/-- The event that a sampler configuration returns the specified label, or remains pending when
the choice is `none`. -/
noncomputable def rationalHeatBathEvent {N : ℕ} (R : ℕ) (choice : Option (Fin N)) :
    (Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution.Configuration (ℕ × ℕ) (Fin N × ℕ × ℕ) × ℕ) → Prop :=
  fun z => match choice with
    | some j => rejectionOutcome z.1 = Sum.inl j
    | none => rejectionOutcome z.1 = Sum.inr ()

/-- Every natural number is at most two raised to its ceiling binary logarithm. -/
theorem clog2_ge (n : ℕ) : n ≤ 2 ^ Nat.clog 2 n :=
  (Nat.clog_le_iff_le_pow (b := 2) (x := n) (y := Nat.clog 2 n) (by omega)).mp le_rfl

/-- Flattening singleton lists obtained by mapping is the same as mapping their entries
directly. -/
theorem flatten_singleton_map {α β : Type*} :
    ∀ (l : List α) (g : α → β), (l.map (fun a => [g a])).flatten = l.map g := by
  intro l
  induction l with
  | nil => intro g; rfl
  | cons a l ih => intro g; simp [ih]

/-- The observed Kraus leaves are the basis projectors followed by the selected permutations,
each with zero queries, one gate, and one measurement. -/
theorem rationalHeatBathLeaves {N : ℕ} (choice : Option (Fin N)) :
    observedKrausLeaves (1 : Operator N) (rationalHeatBathProgram choice) =
      List.ofFn (fun o : Fin N =>
        ObservedKrausLeaf.mk
          (rationalHeatBathPerm choice o *
            Projector (Finset.univ.filter (fun i : Fin N => i = o)))
          true 0 1 1 [(N, o.val)]) := by
  simp only [rationalHeatBathProgram, observedKrausLeaves, ObservedKrausLeaf.prepend,
    List.map_cons, List.map_nil, List.append_nil]
  norm_num
  have key : ∀ (x : Fin N → ObservedKrausLeaf N),
      (List.ofFn (fun o : Fin N => [x o])).flatten = List.ofFn x := by
    intro x
    rw [List.ofFn_eq_map, flatten_singleton_map, List.ofFn_eq_map]
  exact key _

/-- Casting a finite sum of natural numbers to extended nonnegative reals commutes with the sum. -/
theorem sumNatCast {α : Type*} [Fintype α] (f : α → ℕ) :
    (∑ i, ((f i : ℕ) : ENNReal)) = ((∑ i, f i : ℕ) : ENNReal) := by
  classical
  induction (Finset.univ : Finset α) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [ih]
      simp only [Nat.cast_add]

/-- Natural-number weights divided by their positive total sum to one in extended nonnegative
reals. -/
theorem sumWeightDiv {N : ℕ} (w : Fin N → ℕ) (hW : 0 < weightTotal w) :
    (∑ i : Fin N, ((w i : ℕ) : ENNReal) / ((weightTotal w : ℕ) : ENNReal)) = 1 := by
  have hc : (∑ i : Fin N, ((w i : ℕ) : ENNReal)) = ((weightTotal w : ℕ) : ENNReal) := by
    rw [sumNatCast]
    rfl
  calc (∑ i : Fin N, ((w i : ℕ) : ENNReal) / ((weightTotal w : ℕ) : ENNReal))
      = ∑ i : Fin N, ((w i : ℕ) : ENNReal) * ((weightTotal w : ℕ) : ENNReal)⁻¹ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [div_eq_mul_inv]
    _ = (∑ i : Fin N, ((w i : ℕ) : ENNReal)) * ((weightTotal w : ℕ) : ENNReal)⁻¹ := by
        rw [Finset.sum_mul]
    _ = 1 := by
        rw [hc]
        exact ENNReal.mul_inv_cancel (by positivity) (by simp)

/-- The masses of all accepted-label events and the pending event sum to one. -/
theorem rationalHeatBathEvent_sum {N R : ℕ} (w : Fin N → ℕ) (hW : 0 < weightTotal w) :
    (∑ c : Option (Fin N),
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
          (rationalHeatBathEvent R c)) = 1 := by
  have hclog := clog2_ge (weightTotal w)
  have h :=
      rational_finite_return_pending_and_first_stop N w (Nat.clog 2 (weightTotal w)) R hW hclog
  have hsplit : (∑ c : Option (Fin N), Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R) (rationalHeatBathEvent R c))
      = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
          (rationalHeatBathEvent R (none))
        + ∑ i : Fin N, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
          (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R) (rationalHeatBathEvent R (some i)) :=
    Fintype.sum_option _
  rw [hsplit]
  have hn : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
        (rationalHeatBathEvent R (none))
      = rationalRejectMass w (Nat.clog 2 (weightTotal w)) ^ R := h.1
  have hs : ∀ i : Fin N, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event
        (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R) (rationalHeatBathEvent R (some i))
      = ((w i : ℕ) : ENNReal) / ((weightTotal w : ℕ) : ENNReal) *
          (1 - rationalRejectMass w (Nat.clog 2 (weightTotal w)) ^ R) := by
    intro i
    exact h.2.1 i
  rw [hn, Finset.sum_congr rfl fun i _ => hs i]
  set q : ENNReal := rationalRejectMass w (Nat.clog 2 (weightTotal w)) with hq
  have hfact : (∑ i : Fin N, ((w i : ℕ) : ENNReal) / ((weightTotal w : ℕ) : ENNReal) *
        (1 - q ^ R)) = 1 * (1 - q ^ R) := by
    calc (∑ i : Fin N, ((w i : ℕ) : ENNReal) / ((weightTotal w : ℕ) : ENNReal) * (1 - q ^ R))
        = ((∑ i : Fin N, ((w i : ℕ) : ENNReal) / ((weightTotal w : ℕ) : ENNReal)) * (1 - q ^ R)) := by
          rw [Finset.sum_mul]
      _ = _ := by rw [sumWeightDiv w hW]
  rw [hfact]
  simp only [one_mul]
  have hqle : q ≤ 1 :=
    (rational_effective_truncation_consumer N w R hW).2.1.trans (by norm_num)
  exact add_tsub_cancel_of_le (pow_le_one₀ (by positivity) hqle)

/-- Normalized nonnegative integer weights with positive total define a density operator. -/
theorem rationalHeatBathDensity_isDensity {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) : IsDensityOperator (rationalHeatBathDensity w hW) := by
  unfold rationalHeatBathDensity
  refine ⟨Matrix.PosSemidef.diagonal (fun i => ?_), ?_⟩
  · exact RCLike.ofReal_nonneg.mpr (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · rw [Matrix.trace_diagonal]
    have hs : (∑ i, (w i : ℝ)) = (weightTotal w : ℝ) := by
      simp [weightTotal]
    have h : (∑ i, (w i : ℝ) / (weightTotal w : ℝ)) = 1 := by
      rw [← Finset.sum_div, hs, div_self (by positivity)]
    exact_mod_cast h

/-- The explicit heat-bath swap matrix equals the permutation matrix of `Equiv.swap i j`. -/
theorem rationalHeatBathSwap_eq {N : ℕ} (i j : Fin N) :
    rationalHeatBathSwap i j = permMatrix (Equiv.swap i j) := by
  ext a b
  by_cases hij : i = j
  · subst j
    simp [rationalHeatBathSwap, permMatrix]
    by_cases hai : a = i <;> simp_all [eq_comm]
  · by_cases hbi : b = i <;> by_cases hbj : b = j <;>
      by_cases hai : a = i <;> by_cases haj : a = j <;>
      simp_all [rationalHeatBathSwap, permMatrix, Equiv.swap_apply_def, eq_comm]

/-- Every optional-choice heat-bath permutation matrix is unitary. -/
theorem rationalHeatBathPerm_unitary {N : ℕ} (c : Option (Fin N)) (i : Fin N) :
    rationalHeatBathPerm c i ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  cases c with
  | none => exact (Matrix.unitaryGroup (Fin N) ℂ).one_mem
  | some j =>
    rw [rationalHeatBathPerm, rationalHeatBathSwap_eq]
    exact permMatrix_unitary (fun k => Equiv.swap_apply_self i j k)

/-- The observed heat-bath program is well formed and has exactly one leaf per basis label. -/
theorem rationalHeatBathProgram_spec {N : ℕ} (c : Option (Fin N)) :
    observedWellFormed (rationalHeatBathProgram c) ∧
      observedLeafCount (rationalHeatBathProgram c) = N := by
  constructor
  · intro i
    exact ⟨rationalHeatBathPerm_unitary c i, trivial⟩
  · simp [rationalHeatBathProgram, observedLeafCount]

/-- The branch operator obtained by projecting onto the measured label and then applying its
chosen permutation. -/
noncomputable def rationalHeatBathLeaf {N : ℕ} (c : Option (Fin N)) (i : Fin N) :
    Operator N := rationalHeatBathPerm c i * Projector ({i} : Finset (Fin N))

/-- The operator of the corresponding observed program leaf is `rationalHeatBathLeaf`. -/
theorem rationalHeatBathLeaf_actual {N : ℕ} (c : Option (Fin N)) (i : Fin N) :
    (observedLeaf 1 (rationalHeatBathProgram c)
      (Fin.cast (rationalHeatBathProgram_spec c).2.symm i)).operator =
        rationalHeatBathLeaf c i := by
  unfold observedLeaf
  simp [rationalHeatBathLeaves, rationalHeatBathLeaf, Finset.filter_eq']

/-- For a fixed optional choice, the heat-bath leaf operators satisfy the Kraus completeness
identity. -/
theorem rationalHeatBathLeaf_complete {N : ℕ} (c : Option (Fin N)) :
    (∑ i, (rationalHeatBathLeaf c i)ᴴ * rationalHeatBathLeaf c i) = 1 := by
  have h := observedKrausLeaves_complete (1 : Operator N)
    (Matrix.unitaryGroup (Fin N) ℂ).one_mem (rationalHeatBathProgram c)
    (rationalHeatBathProgram_spec c).1
  rw [rationalHeatBathLeaves, List.map_ofFn, List.sum_ofFn] at h
  simpa [rationalHeatBathLeaf, Finset.filter_eq'] using h

/-- The real mass of an optional label outcome after `R` rejection-sampling trials. -/
noncomputable def rationalHeatBathMass {N : ℕ} (w : Fin N → ℕ) (R : ℕ)
    (c : Option (Fin N)) : ℝ :=
  (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
    (rationalHeatBathEvent R c)).toReal

/-- The real masses of all optional heat-bath choices sum to one. -/
theorem rationalHeatBathMass_sum {N : ℕ} (w : Fin N → ℕ) (hW : 0 < weightTotal w)
    (R : ℕ) : ∑ c, rationalHeatBathMass w R c = 1 := by
  unfold rationalHeatBathMass
  rw [← ENNReal.toReal_sum (fun c _ => ne_of_lt
    ((Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_le_one _ _).trans_lt ENNReal.one_lt_top)),
    rationalHeatBathEvent_sum w hW, ENNReal.toReal_one]

/-- The observed heat-bath leaf operator scaled by the square root of its classical choice
probability. -/
noncomputable def rationalHeatBathKraus {N : ℕ} (w : Fin N → ℕ) (R : ℕ)
    (z : Fin N × Option (Fin N)) : Operator N :=
  (Real.sqrt (rationalHeatBathMass w R z.2) : ℂ) •
    (observedLeaf 1 (rationalHeatBathProgram z.2)
      (Fin.cast (rationalHeatBathProgram_spec z.2).2.symm z.1)).operator

/-- Complex conjugation fixes the cast of any real number. -/
private theorem star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) := by
  simp [RCLike.star_def, Complex.conj_ofReal]

/-- The square of the complex cast of the square root of a heat-bath mass equals that mass. -/
private theorem heatBath_sqrt_sq {N : ℕ} (w : Fin N → ℕ) (R : ℕ)
    (c : Option (Fin N)) :
    (Real.sqrt (rationalHeatBathMass w R c) : ℂ) *
      (Real.sqrt (rationalHeatBathMass w R c) : ℂ) = (rationalHeatBathMass w R c : ℂ) := by
  rw [← Complex.ofReal_mul, ← pow_two,
      Real.sq_sqrt (show 0 ≤ rationalHeatBathMass w R c from ENNReal.toReal_nonneg)]

/-- The classically weighted heat-bath Kraus operators satisfy the completeness identity. -/
theorem rationalHeatBathKraus_complete {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) :
    (∑ z, (rationalHeatBathKraus w R z)ᴴ * rationalHeatBathKraus w R z) = 1 := by
  have hs : ∑ c, (rationalHeatBathMass w R c : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, rationalHeatBathMass_sum w hW R, Complex.ofReal_one]
  simp only [rationalHeatBathKraus, rationalHeatBathLeaf_actual, Matrix.conjTranspose_smul, star_real,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, heatBath_sqrt_sq]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [← Finset.smul_sum, rationalHeatBathLeaf_complete]
  rw [← Finset.sum_smul, hs, one_smul]

/-- The quantum instrument defined by the weighted heat-bath Kraus family. -/
noncomputable def rationalHeatBathInstrument {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) : Instrument (Fin N × Option (Fin N)) N N :=
  Instrument.ofKraus (rationalHeatBathKraus w R) (rationalHeatBathKraus_complete w hW R)

/-- Each instrument branch is the corresponding leaf conjugation multiplied by its classical
choice probability. -/
theorem rationalHeatBathInstrument_branch {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) (i : Fin N) (c : Option (Fin N)) (X : Operator N) :
    (rationalHeatBathInstrument w hW R).branch (i,c) X =
      (rationalHeatBathMass w R c : ℂ) •
        (rationalHeatBathLeaf c i * X * (rationalHeatBathLeaf c i)ᴴ) := by
  simp only [rationalHeatBathInstrument, Instrument.ofKraus_branch, rationalHeatBathKraus, rationalHeatBathLeaf_actual,
    Matrix.conjTranspose_smul, star_real, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, heatBath_sqrt_sq]

/-- The trace of a leaf-conjugated operator equals its diagonal entry at the measured label. -/
theorem rationalHeatBathLeaf_trace {N : ℕ} (c : Option (Fin N)) (i : Fin N)
    (X : Operator N) : Matrix.trace
      (rationalHeatBathLeaf c i * X * (rationalHeatBathLeaf c i)ᴴ) = X i i := by
  have h : rationalHeatBathLeaf c i * X * (rationalHeatBathLeaf c i)ᴴ =
      conjBranch (rationalHeatBathPerm c i)
        (conjBranch (Projector ({i} : Finset (Fin N))) X) := by
    simp only [rationalHeatBathLeaf, conjBranch_apply, Matrix.conjTranspose_mul,
      Matrix.mul_assoc]
  rw [h, trace_conjBranch_unitary _ (rationalHeatBathPerm_unitary c i),
    conjBranch_projector_apply, Matrix.trace_diagonal]
  simp

/-- The weight-normalized target is a density, the observed programs are well formed, and branch
probabilities equal classical choice masses times the real input diagonal entries. -/
theorem rational_heat_bath_actual_instrument_and_program :
    ∀ (N R : ℕ) (w : Fin N → ℕ) (hW : 0 < weightTotal w),
      IsDensityOperator (rationalHeatBathDensity w hW) ∧
      (∀ c : Option (Fin N), observedWellFormed (rationalHeatBathProgram c) ∧
        observedLeafCount (rationalHeatBathProgram c) = N) ∧
      ∀ (i : Fin N) (c : Option (Fin N)) (X : Operator N),
        instrumentProb (rationalHeatBathInstrument w hW R) X (i,c) =
          ((Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
            (fun z => match c with
              | some j => rejectionOutcome z.1 = Sum.inl j
              | none => rejectionOutcome z.1 = Sum.inr ())).toReal) * (X i i).re := by
  intro N R w hW
  refine ⟨rationalHeatBathDensity_isDensity w hW, rationalHeatBathProgram_spec, ?_⟩
  intro i c X
  rw [instrumentProb, rationalHeatBathInstrument_branch, Matrix.trace_smul,
    rationalHeatBathLeaf_trace]
  change ((rationalHeatBathMass w R c : ℂ) * X i i).re =
    rationalHeatBathMass w R c * (X i i).re
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- A heat-bath leaf is the matrix unit sending the measured label to the selected label, with
the measured label used as default. -/
theorem rationalHeatBathLeaf_eq_single {N : ℕ} (c : Option (Fin N)) (i : Fin N) :
    rationalHeatBathLeaf c i = Matrix.single (c.getD i) i (1 : ℂ) := by
  ext a b
  simp only [rationalHeatBathLeaf, Projector, Finset.mem_singleton, Matrix.mul_diagonal,
    Matrix.single, Matrix.of_apply]
  cases c with
  | none =>
    by_cases hbi : b = i <;> by_cases hai : a = i <;>
      simp_all [rationalHeatBathPerm, Matrix.one_apply, eq_comm]
  | some j =>
    by_cases hbi : b = i <;> by_cases hai : a = i <;> by_cases haj : a = j <;>
      simp_all [rationalHeatBathPerm, rationalHeatBathSwap, eq_comm]

/-- Conjugation by a heat-bath leaf places the measured diagonal entry at its selected output
label and zero elsewhere. -/
theorem rationalHeatBathLeaf_conj {N : ℕ} (c : Option (Fin N)) (i : Fin N)
    (X : Operator N) :
    rationalHeatBathLeaf c i * X * (rationalHeatBathLeaf c i)ᴴ =
      Matrix.diagonal (fun a => if a = c.getD i then X i i else 0) := by
  rw [rationalHeatBathLeaf_eq_single]
  ext a b
  by_cases hab : a = b <;> by_cases ha : a = c.getD i <;> by_cases hb : b = c.getD i <;>
    simp_all [Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply, eq_comm]

/-- With positive total weight, the one-trial heat-bath rejection probability lies between zero
and one half. -/
theorem rationalHeatBathReject_bounds {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) :
    0 ≤ rationalHeatBathReject w ∧ rationalHeatBathReject w ≤ 1/2 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h := (rational_effective_truncation_consumer N w 0 hW).2.1
  have h' := ENNReal.toReal_mono (show (1/2 : ℝ≥0∞) ≠ ⊤ by norm_num) h
  norm_num [rationalHeatBathReject] at h' ⊢
  exact h'

/-- The probability of no accepted label after `R` trials is the one-trial rejection probability
raised to `R`. -/
theorem rationalHeatBathMass_none {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) :
    rationalHeatBathMass w R none = rationalHeatBathReject w ^ R := by
  unfold rationalHeatBathMass
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
      (rationalHeatBathEvent R none) = rationalRejectMass w (Nat.clog 2 (weightTotal w)) ^ R from
    (rational_finite_return_pending_and_first_stop N w _ R hW (clog2_ge _)).1,
    ENNReal.toReal_pow]
  rfl

/-- The mass of an accepted label is its normalized weight times one minus the probability that
all trials reject. -/
theorem rationalHeatBathMass_some {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) (j : Fin N) :
    rationalHeatBathMass w R (some j) =
      (w j : ℝ) / (weightTotal w : ℝ) * (1 - rationalHeatBathReject w ^ R) := by
  have hq := (rational_effective_truncation_consumer N w R hW).2.1
  have hp : rationalRejectMass w (Nat.clog 2 (weightTotal w)) ^ R ≤ 1 :=
    pow_le_one₀ (by positivity) (hq.trans (by norm_num))
  unfold rationalHeatBathMass
  rw [show Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (rationalRejectionRun w (Nat.clog 2 (weightTotal w)) R)
      (rationalHeatBathEvent R (some j)) =
      (w j : ℝ≥0∞) / (weightTotal w : ℝ≥0∞) *
        (1 - rationalRejectMass w (Nat.clog 2 (weightTotal w)) ^ R) from
    (rational_finite_return_pending_and_first_stop N w _ R hW (clog2_ge _)).2.1 j,
    ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_sub_of_le hp (by simp),
    ENNReal.toReal_pow]
  simp [rationalHeatBathReject]

/-- Forgetting the heat-bath outcome gives a mixture of trace-weighted target replacement and
computational-basis dephasing. -/
theorem rationalHeatBathInstrument_map {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) (X : Operator N) :
    (rationalHeatBathInstrument w hW R).forget.map X =
      (1 - rationalHeatBathReject w ^ R : ℂ) • (Matrix.trace X • rationalHeatBathDensity w hW) +
      (rationalHeatBathReject w ^ R : ℂ) • Matrix.diagonal (fun i => X i i) := by
  rw [Instrument.forget_apply, Fintype.sum_prod_type]
  simp_rw [rationalHeatBathInstrument_branch, rationalHeatBathLeaf_conj]
  ext a b
  simp only [Matrix.sum_apply, Fintype.sum_option, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, rationalHeatBathMass_none w hW, rationalHeatBathMass_some w hW]
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq, Option.getD_none, Option.getD_some,
      rationalHeatBathDensity, Matrix.trace, Matrix.diag_apply]
    simp only [mul_ite, mul_zero, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_pow]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.mul_sum]
    ring
  · simp [rationalHeatBathDensity, hab]

/-- The heat-bath target is stationary, the rejection probability is at most one half, and the
channel has the explicit replacement-and-dephasing formula. -/
theorem rational_heat_bath_derived_channel_and_stationarity :
    ∀ (N R : ℕ) (w : Fin N → ℕ) (hW : 0 < weightTotal w),
      0 ≤ rationalHeatBathReject w ∧ rationalHeatBathReject w ≤ 1/2 ∧
      (rationalHeatBathInstrument w hW R).forget.map (rationalHeatBathDensity w hW) =
        rationalHeatBathDensity w hW ∧
      ∀ X : Operator N, (rationalHeatBathInstrument w hW R).forget.map X =
        (1 - rationalHeatBathReject w ^ R : ℂ) • (Matrix.trace X • rationalHeatBathDensity w hW) +
        (rationalHeatBathReject w ^ R : ℂ) • Matrix.diagonal (fun i => X i i) := by
  intro N R w hW
  refine ⟨(rationalHeatBathReject_bounds w hW).1,
    (rationalHeatBathReject_bounds w hW).2, ?_, rationalHeatBathInstrument_map w hW R⟩
  rw [rationalHeatBathInstrument_map, (rationalHeatBathDensity_isDensity w hW).2, one_smul]
  have hd : Matrix.diagonal (fun i => rationalHeatBathDensity w hW i i) =
      rationalHeatBathDensity w hW := by simp [rationalHeatBathDensity]
  rw [hd, ← add_smul]
  simp

/-- The iterated heat-bath quantum channel, starting with the identity at power zero. -/
noncomputable def rationalHeatBathPower {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R : ℕ) : ℕ → QuantumChannel N N
  | 0 => QuantumChannel.id N
  | m + 1 => (rationalHeatBathPower w hW R m).comp
      (rationalHeatBathInstrument w hW R).forget

/-- Forgetting the computational-basis projective measurement gives the diagonal part of an
operator. -/
theorem rationalHeatBath_projective_map {N : ℕ} (X : Operator N) :
    (projectiveInstrument (D := N)).forget.map X = Matrix.diagonal (fun i => X i i) := by
  rw [Instrument.forget_apply]
  simp only [projectiveInstrument, conjBranch_projector_apply]
  ext a b
  by_cases hab : a = b <;> simp [Matrix.sum_apply, hab]

/-- After `m + 1` heat-bath steps, the residual dephasing coefficient is the rejection
probability raised to `R * (m + 1)`. -/
theorem rationalHeatBathPower_succ_map {N : ℕ} (w : Fin N → ℕ)
    (hW : 0 < weightTotal w) (R m : ℕ) (X : Operator N) :
    (rationalHeatBathPower w hW R (m+1)).map X =
      (1 - rationalHeatBathReject w ^ (R*(m+1)) : ℂ) •
        (Matrix.trace X • rationalHeatBathDensity w hW) +
      (rationalHeatBathReject w ^ (R*(m+1)) : ℂ) • Matrix.diagonal (fun i => X i i) := by
  induction m generalizing X with
  | zero => simpa [rationalHeatBathPower, QuantumChannel.comp, QuantumChannel.id] using
      rationalHeatBathInstrument_map w hW R X
  | succ m ih =>
    change (rationalHeatBathPower w hW R (m+1)).map
      ((rationalHeatBathInstrument w hW R).forget.map X) = _
    rw [ih, (rationalHeatBathInstrument w hW R).forget.tracePreserving,
      rationalHeatBathInstrument_map]
    have hp : (rationalHeatBathReject w : ℂ) ^ (R*(m+1+1)) =
        (rationalHeatBathReject w : ℂ) ^ (R*(m+1)) * (rationalHeatBathReject w : ℂ)^R := by
      rw [Nat.mul_add, Nat.mul_one, pow_add]
    ext a b
    by_cases hab : a = b
    · subst b
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul]
      rw [hp]
      ring
    · simp [Matrix.add_apply, Matrix.smul_apply, rationalHeatBathDensity, hab]

/-- For a positive number of heat-bath steps, the channel tensored with a reference identity is
the stated mixture of target replacement and local dephasing. -/
theorem rational_heat_bath_actual_reference_power_formula :
    ∀ (N R m r : ℕ) (w : Fin N → ℕ) (hW : 0 < weightTotal w)
      (X : Matrix (Fin N × Fin r) (Fin N × Fin r) ℂ), 0 < m →
      tensorLeft (rationalHeatBathPower w hW R m).map X =
        (1 - rationalHeatBathReject w ^ (R*m) : ℂ) •
          TensorGate (rationalHeatBathDensity w hW) (Matrix.traceLeft X) +
        (rationalHeatBathReject w ^ (R*m) : ℂ) •
          tensorLeft (projectiveInstrument (D := N)).forget.map X := by
  intro N R m r w hW X hm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  ext ⟨a,u⟩ ⟨b,v⟩
  simp only [tensorLeft, rationalHeatBathPower_succ_map, rationalHeatBath_projective_map,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  change (1 - (rationalHeatBathReject w : ℂ)^(R*(m+1))) *
      ((∑ i, X (i,u) (i,v)) * rationalHeatBathDensity w hW a b) + _ =
    (1 - (rationalHeatBathReject w : ℂ)^(R*(m+1))) *
      (rationalHeatBathDensity w hW a b * (∑ i, X (i,u) (i,v))) + _
  simp only [Nat.succ_eq_add_one]
  ring

/-- The trace norm of a positive semidefinite matrix equals the real part of its trace. -/
private theorem heatBath_psd_norm {I : Type*} [Fintype I] [DecidableEq I]
    (X : Matrix I I ℂ) (hX : X.PosSemidef) : Matrix.traceNorm X = (Matrix.trace X).re := by
  have h := congrArg Complex.re hX.traceNorm_eq_trace
  simpa using h

/-- For positive semidefinite system-reference inputs and positive step count, the replacement
error is at most twice the rejection factor times the input trace norm, yielding the stated
binary precision budget. -/
theorem rational_heat_bath_derived_reference_mixing_budget :
    ∀ (N R m s r : ℕ) (w : Fin N → ℕ) (hW : 0 < weightTotal w)
      (X : Matrix (Fin N × Fin r) (Fin N × Fin r) ℂ), 0 < m → X.PosSemidef →
      Matrix.traceNorm (tensorLeft (rationalHeatBathPower w hW R m).map X -
        TensorGate (rationalHeatBathDensity w hW) (Matrix.traceLeft X)) ≤
          2 * rationalHeatBathReject w ^ (R*m) * Matrix.traceNorm X ∧
      (s+1 ≤ R*m → Matrix.traceNorm (tensorLeft (rationalHeatBathPower w hW R m).map X -
        TensorGate (rationalHeatBathDensity w hW) (Matrix.traceLeft X)) ≤
          ((2:ℝ)⁻¹)^s * Matrix.traceNorm X) := by
  intro N R m s r w hW X hm hX
  let Y := TensorGate (rationalHeatBathDensity w hW) (Matrix.traceLeft X)
  let Z := tensorLeft (projectiveInstrument (D := N)).forget.map X
  have hYn : Matrix.traceNorm Y = Matrix.traceNorm X := by
    rw [heatBath_psd_norm Y (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate
      (rationalHeatBathDensity_isDensity w hW).1 hX.traceLeft), heatBath_psd_norm X hX]
    congr 1
    rw [Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate, (rationalHeatBathDensity_isDensity w hW).2,
      Matrix.traceLeft_trace, one_mul]
  have hZn : Matrix.traceNorm Z = Matrix.traceNorm X := by
    rw [heatBath_psd_norm Z (tensorLeft_posSemidef
      (projectiveInstrument (D := N)).forget.completelyPositive hX), heatBath_psd_norm X hX]
    congr 1
    exact tensorLeft_trace_map _ (projectiveInstrument (D := N)).forget.tracePreserving X
  have htri : Matrix.traceNorm (Z - Y) ≤ 2 * Matrix.traceNorm X := by
    rw [sub_eq_add_neg]
    calc _ ≤ Matrix.traceNorm Z + Matrix.traceNorm (-Y) := Matrix.traceNorm_add_le _ _
      _ = 2 * Matrix.traceNorm X := by rw [Matrix.traceNorm_neg, hYn, hZn]; ring
  have heq : tensorLeft (rationalHeatBathPower w hW R m).map X - Y =
      (rationalHeatBathReject w ^ (R*m) : ℂ) • (Z - Y) := by
    rw [rational_heat_bath_actual_reference_power_formula N R m r w hW X hm]
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hq := rationalHeatBathReject_bounds w hW
  have herr : Matrix.traceNorm (tensorLeft (rationalHeatBathPower w hW R m).map X - Y) ≤
      2 * rationalHeatBathReject w ^ (R*m) * Matrix.traceNorm X := by
    rw [heq, Matrix.traceNorm_smul, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hq.1 _)]
    calc _ ≤ rationalHeatBathReject w ^ (R*m) * (2 * Matrix.traceNorm X) :=
        mul_le_mul_of_nonneg_left htri (pow_nonneg hq.1 _)
      _ = _ := by ring
  refine ⟨herr, fun hs => herr.trans ?_⟩
  have hp : rationalHeatBathReject w ^ (R*m) ≤ (1/2:ℝ)^(s+1) :=
    (pow_le_pow_left₀ hq.1 hq.2 _).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hs)
  have hb : 2 * rationalHeatBathReject w ^ (R*m) ≤ ((2:ℝ)⁻¹)^s := by
    calc _ ≤ 2 * (1/2:ℝ)^(s+1) := mul_le_mul_of_nonneg_left hp (by norm_num)
      _ = _ := by rw [pow_succ]; norm_num; ring
  exact mul_le_mul_of_nonneg_right hb (Matrix.traceNorm_nonneg X)

end Qatlib.Concepts.GibbsMetropolis.RationalBath
