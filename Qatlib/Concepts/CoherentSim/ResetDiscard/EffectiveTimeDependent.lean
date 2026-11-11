/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.EffectiveTimeDependentDefs

/-!
# Effective time-grid identities and circuit counts

This module proves coefficient, multiplicity, and resource identities for the time-grid encoding
defined by `timeLCUWord`. It also verifies that `effectiveTimeGrid` meets its discretization
budget; these ingredients support the time-dependent extension of truncated Taylor simulation
[BerryEtAl2015Taylor].

## Main statements

* `timeLCUWord_counts`: Exact query and gate counts for the time-grid word.
* `effectiveTimeGrid_budget`: The chosen grid size meets the prescribed error budget.
* `clause45_complete`: The combined coefficient, unitarity, counting, and grid-budget results.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.CoherentSim.TaylorEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Qatlib.Concepts.RiskEstimation.PopulationGap
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator
set_option warningAsError false

variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- A time word whose time indices are not canonical has coefficient zero. -/
theorem timeCoeff_noncanonical (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ)
    {l : Fin (K + 1)} {letters : Fin l.val → (Fin M × J)}
    (hnot : ¬ timeCanonical letters) :
    timeCoeff h τ M K (Sum.inl ⟨l, letters⟩) = 0 := by
  simp [timeCoeff, hnot]

/-- A canonical time word has its Taylor coefficient multiplied by the number of time sequences
with the same multiplicities. -/
theorem timeCoeff_canonical (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ)
    {l : Fin (K + 1)} {letters : Fin l.val → (Fin M × J)}
    (hc : timeCanonical letters) :
    timeCoeff h τ M K (Sum.inl ⟨l, letters⟩) =
      (taylorWordCoefficient (timeScale h τ M) τ ⟨l, letters⟩) *
        ((timeMultiplicity l.val M (wordTimeCount letters) : ℝ)) := by
  simp [timeCoeff, hc]

/-- For a positive grid size, the rescaled Taylor-word coefficient equals the product of sampled
Hamiltonian coefficients divided by the grid size, with the Taylor phase and factorial
factor. -/
theorem timeScale_wordCoefficient (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (hM : 0 < M)
    {K : ℕ} {l : Fin (K + 1)} {letters : Fin l.val → (Fin M × J)} :
    taylorWordCoefficient (timeScale h τ M) τ ⟨l, letters⟩ =
      ((-Complex.I * (τ : ℂ)) ^ (l.val : ℕ) / (l.val.factorial : ℂ)) *
        ∏ a, ((h (gridTime τ M (letters a).1) (letters a).2 : ℂ) / (M : ℂ)) := by
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  simp only [taylorWordCoefficient]
  have hfac : ∀ a : Fin l, (timeScale h τ M (letters a) : ℂ) =
      ((h (gridTime τ M (letters a).1) (letters a).2 : ℂ) / (M : ℂ)) := by
    intro a
    simp only [timeScale]
    push_cast
    ring
  rw [Finset.prod_congr rfl (fun a ha => hfac a)]

/-- The two padding coefficients are the opposite signed halves of the deficit from Taylor mass
two. -/
theorem timeCoeff_padding (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ) (b : Bool) :
    timeCoeff h τ M K (Sum.inr b) =
      ((if b then (2 - taylorS0 (timeScale h τ M) τ K) / 2
        else -(2 - taylorS0 (timeScale h τ M) τ K) / 2) : ℂ) := by
  cases b <;> rfl

/-- The two padding coefficients sum to zero. -/
theorem timeCoeff_padding_sum (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ) :
    timeCoeff h τ M K (Sum.inr false) + timeCoeff h τ M K (Sum.inr true) = 0 := by
  simp [timeCoeff]
  ring

/-- For a positive grid size, the coefficient mass of `timeScale` multiplied by `M` equals the
total absolute sampled coefficient mass. -/
theorem timeScale_lambda (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (hM : 0 < M) :
    taylorLambda (timeScale h τ M) * (M : ℝ) =
      ∑ j : Fin M, ∑ m : J, |h (gridTime τ M j) m| := by
  have hpos : (0 : ℝ) < M := by exact_mod_cast hM
  classical
  simp only [taylorLambda, timeScale]
  rw [Fintype.sum_prod_type]
  have habs : ∀ (j : Fin M) (m : J),
      |h (gridTime τ M j) m / (M : ℝ)| = |h (gridTime τ M j) m| / (M : ℝ) := by
    intro j m
    rw [abs_div, abs_of_pos hpos]
  rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun m hm => habs j m))]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  field_simp

/-- The truncated mass for `timeScale` is the finite exponential sum in its coefficient mass
times `|τ|`. -/
theorem timeScale_s0 (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (K : ℕ) :
    taylorS0 (timeScale h τ M) τ K =
      ∑ l ∈ Finset.range (K + 1),
        (taylorLambda (timeScale h τ M) * |τ|) ^ l / l.factorial := rfl

/-- A product over a time sequence equals the product over grid points with exponents given by
their occurrence counts. -/
theorem timeCount_prod {l M : ℕ} (f : Fin M → ℝ) (t : Fin l → Fin M) :
    (∏ a : Fin l, f (t a)) = ∏ j : Fin M, (f j) ^ (timeCount t j) := by
  classical
  have h := Finset.prod_fiberwise (Finset.univ : Finset (Fin l)) t (fun a => f (t a))
  rw [← h]
  apply Finset.prod_congr rfl
  intro j _
  have hinner : (∏ i ∈ (Finset.univ : Finset (Fin l)).filter (fun i => t i = j), f (t i))
      = (f j) ^ ((Finset.univ : Finset (Fin l)).filter (fun i => t i = j)).card := by
    have hconst := Finset.prod_const (s := (Finset.univ : Finset (Fin l)).filter
      (fun i => t i = j)) (b := f j)
    calc
      (∏ i ∈ (Finset.univ : Finset (Fin l)).filter (fun i => t i = j), f (t i))
          = ∏ i ∈ (Finset.univ : Finset (Fin l)).filter (fun i => t i = j), f j := by
            apply Finset.prod_congr rfl
            intro i hi
            have : t i = j := (Finset.mem_filter.mp hi).2
            simp [this]
      _ = _ := hconst
  rw [hinner]
  rfl

/-- Summing products of absolute weights over all length-`l` time sequences gives the `l`th
power of the total absolute weight. -/
theorem time_sum_prod_abs {M : ℕ} (f : Fin M → ℝ) (l : ℕ) :
    (∑ t : Fin l → Fin M, ∏ a, |f (t a)|) = (∑ j : Fin M, |f j|) ^ l := by
  have h := taylor_sum_prod_abs (J := Fin M) f l
  simpa [taylorLambda] using! h

/-- The multiplicity of an element in a finite sum of multisets is the sum of its
multiplicities. -/
private theorem multiset_count_sum {ι α : Type} [DecidableEq α]
    (s : Finset ι) (f : ι → Multiset α) (a : α) :
    Multiset.count a (s.sum f) = s.sum (fun i => Multiset.count a (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
      simp only [Finset.sum_insert hb, Multiset.count_add, ih]

/-- The cardinality of a finite sum of multisets is the sum of their cardinalities. -/
private theorem multiset_card_sum {ι α : Type}
    (s : Finset ι) (f : ι → Multiset α) :
    (s.sum f).card = s.sum (fun i => (f i).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
      simp only [Finset.sum_insert hb, Multiset.card_add, ih]

/-- The multiset underlying the canonical time list is the sum of the prescribed repeated grid
indices. -/
theorem canonTimes_multiset {M : ℕ} (c : Fin M → ℕ) :
    ((canonTimes c : List (Fin M)) : Multiset (Fin M))
      = ∑ j : Fin M, Multiset.replicate (c j) j := by
  classical
  have hgen : ∀ (n : ℕ) (α : Type) (f : Fin n → List α),
      ((List.ofFn f).flatten : Multiset α) = ∑ j : Fin n, (f j : Multiset α) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro α f
        have hsplit : (List.ofFn f).flatten = f 0 ++ (List.ofFn fun i => f i.succ).flatten := by
          simp [List.ofFn_succ]
        rw [hsplit, ← Multiset.coe_add, ih, Fin.sum_univ_succ]
        all_goals (congr 1; funext j; simp)
  have h := hgen M (Fin M) (fun j => List.replicate (c j) j)
  show ((List.ofFn (fun j => List.replicate (c j) j)).flatten : Multiset (Fin M))
      = ∑ j : Fin M, Multiset.replicate (c j) j
  simpa [canonTimes, Multiset.coe_replicate] using! h

/-- The length of the canonical time list is the sum of its prescribed multiplicities. -/
theorem canonTimes_length {M : ℕ} (c : Fin M → ℕ) : (canonTimes c).length = ∑ j, c j := by
  classical
  rw [← Multiset.coe_card, canonTimes_multiset, multiset_card_sum (Finset.univ : Finset (Fin M))]
  simp only [Multiset.card_replicate]

/-- Each grid index occurs in the canonical time list with exactly its prescribed multiplicity. -/
theorem canonTimes_count {M : ℕ} (c : Fin M → ℕ) (j : Fin M) :
    Multiset.count j (↑(canonTimes c)) = c j := by
  classical
  rw [canonTimes_multiset, multiset_count_sum (Finset.univ : Finset (Fin M))]
  simp only [Multiset.count_replicate]
  simpa [eq_comm] using! (Fintype.sum_ite_eq j c)

/-- The diagonal coefficient-phase gate for the time-grid encoding is unitary. -/
theorem timePhaseGate_unitary (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ) :
    timePhaseGate h τ M K ∈ Matrix.unitaryGroup (TimeWordLabel J K M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, timePhaseGate,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  exact coefficientPhase_unit _

/-- A length-`n` Taylor block list uses `n` queries and `2 * n` gates. -/
private theorem timeBlockList_counts (M : ℕ) (j0 : Fin M × J) (K : ℕ) : ∀ (n : ℕ) (hn : n ≤ K),
    adjointQueryCount (taylorBlockList (I := I) j0 K n hn) = n ∧
    adjointGateCount (taylorBlockList (I := I) j0 K n hn) = 2 * n := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ m ih =>
      intro hm
      have hblock : taylorBlockList (I := I) j0 K (m + 1) hm
          = taylorQueryRouteStep (I := I) j0 (K := K) ⟨m, Nat.lt_of_succ_le hm⟩ ++
            taylorBlockList (I := I) j0 K m (Nat.le_of_succ_le hm) := rfl
      rw [hblock, adjointQueryCount_append, adjointGateCount_append,
        (ih (Nat.le_of_succ_le hm)).1, (ih (Nat.le_of_succ_le hm)).2]
      simp only [taylorQueryRouteStep, adjointQueryCount, adjointGateCount]
      exact ⟨by omega, by omega⟩

/-- The time-grid LCU word uses `K` queries and `2 * K + 3` gates. -/
theorem timeLCUWord_counts (h : ℝ → J → ℝ) (U : J → Matrix I I ℂ) (M : ℕ)
    (j0 : Fin M × J) (τ : ℝ) (K : ℕ) :
    adjointQueryCount (timeLCUWord h U M j0 τ K) = K ∧
    adjointGateCount (timeLCUWord h U M j0 τ K) = 2 * K + 3 := by
  have hq := timeBlockList_counts (I := I) M j0 K K le_rfl
  unfold timeLCUWord
  simp only [List.nil_append, List.cons_append]
  simp only [adjointQueryCount]
  rw [adjointQueryCount_append, hq.1]
  simp only [adjointQueryCount]
  simp only [adjointGateCount]
  rw [adjointGateCount_append, hq.2]
  simp only [adjointGateCount]
  simp

/-- The query count of an instruction prepended to a circuit is the sum of the singleton and
tail query counts. -/
private theorem adjointQueryCount_cons {H : Type} (c : AdjointStep H) (cs : List (AdjointStep H)) :
    adjointQueryCount (c :: cs) = adjointQueryCount cs + adjointQueryCount [c] := by
  cases c <;> simp [adjointQueryCount]

/-- The gate count of an instruction prepended to a circuit is the sum of the singleton and tail
gate counts. -/
private theorem adjointGateCount_cons {H : Type} (c : AdjointStep H) (cs : List (AdjointStep H)) :
    adjointGateCount (c :: cs) = adjointGateCount cs + adjointGateCount [c] := by
  cases c <;> simp [adjointGateCount]

/-- Taking the adjoint of one instruction preserves its query and gate counts. -/
private theorem adjointInstruction_counts {H : Type} (c : AdjointStep H) :
    adjointQueryCount [adjointInstruction c] = adjointQueryCount [c] ∧
    adjointGateCount [adjointInstruction c] = adjointGateCount [c] := by
  cases c <;> simp [adjointInstruction, adjointQueryCount, adjointGateCount]

/-- Taking the adjoint of a circuit preserves its query and gate counts. -/
private theorem adjointCircuit_counts {H : Type} (cs : List (AdjointStep H)) :
    adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) = adjointQueryCount cs ∧
    adjointGateCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit cs) = adjointGateCount cs := by
  induction cs with
  | nil => simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, adjointQueryCount, adjointGateCount]
  | cons c cs ih =>
      cases c <;>
        simp [Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit, adjointInstruction,
            adjointQueryCount, adjointGateCount, ih]

/-- The adjoint time-grid LCU word uses `K` queries and `2 * K + 3` gates. -/
theorem timeLCUWord_inverse_counts (h : ℝ → J → ℝ) (U : J → Matrix I I ℂ) (M : ℕ)
    (j0 : Fin M × J) (τ : ℝ) (K : ℕ) :
    adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (timeLCUWord h U M j0 τ K)) = K ∧
    adjointGateCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (timeLCUWord h U M j0 τ K)) = 2 * K + 3 := by
  have hac := adjointCircuit_counts (timeLCUWord h U M j0 τ K)
  rw [hac.1, hac.2]
  exact timeLCUWord_counts h U M j0 τ K

/-- For positive error tolerance and nonnegative coefficient, regularity, and time parameters,
the chosen grid bounds `(2 * Λ² + L) * τ² / M` by the tolerance. -/
theorem effectiveTimeGrid_budget (Λ L τ ε : ℝ) (hε : 0 < ε) (hΛ : 0 ≤ Λ)
    (hL : 0 ≤ L) (hτ : 0 ≤ τ) :
    (2 * Λ ^ 2 + L) * τ ^ 2 / (effectiveTimeGrid Λ L τ ε : ℝ) ≤ ε := by
  have hA : 0 ≤ (2 * Λ ^ 2 + L) * τ ^ 2 := by positivity
  have hG : (0 : ℝ) < (effectiveTimeGrid Λ L τ ε : ℝ) := by
    have h1 : (1 : ℕ) ≤ effectiveTimeGrid Λ L τ ε := by
      unfold effectiveTimeGrid
      omega
    exact_mod_cast h1
  have hceil : (Nat.ceil ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) : ℝ) ≥
      (2 * Λ ^ 2 + L) * τ ^ 2 / ε := Nat.le_ceil _
  have hbig : (effectiveTimeGrid Λ L τ ε : ℝ) >
      (2 * Λ ^ 2 + L) * τ ^ 2 / ε := by
    have h1 : (Nat.ceil ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) : ℝ) ≥
        (2 * Λ ^ 2 + L) * τ ^ 2 / ε := Nat.le_ceil _
    have h3 : ((effectiveTimeGrid Λ L τ ε : ℝ)) =
        (Nat.ceil ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) : ℝ) + 1 := by
      unfold effectiveTimeGrid
      push_cast
      ring
    rw [h3]
    linarith
  rw [div_le_iff₀ hG]
  have hmul : ε * (effectiveTimeGrid Λ L τ ε : ℝ) > ε * ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) :=
    (mul_lt_mul_of_pos_left hbig hε)
  have hrw : ε * ((2 * Λ ^ 2 + L) * τ ^ 2 / ε) = (2 * Λ ^ 2 + L) * τ ^ 2 := by
    field_simp
  linarith

/-- The effective time-grid size is positive whenever the error tolerance is positive. -/
theorem effectiveTimeGrid_pos (Λ L τ ε : ℝ) (hε : 0 < ε) :
    0 < effectiveTimeGrid Λ L τ ε := by
  simp only [effectiveTimeGrid]
  positivity

/-- The canonical and noncanonical coefficient formulas, padding cancellation, mass identity,
phase-gate unitarity, forward and adjoint counts, and effective grid budget hold together. -/
theorem clause45_complete :
    (∀ (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ) {l : Fin (K + 1)}
        {letters : Fin l.val → (Fin M × J)} (hc : timeCanonical letters),
      timeCoeff h τ M K (Sum.inl ⟨l, letters⟩) =
        (taylorWordCoefficient (timeScale h τ M) τ ⟨l, letters⟩) *
          ((timeMultiplicity l.val M (wordTimeCount letters) : ℝ))) ∧
    (∀ (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ) {l : Fin (K + 1)}
        {letters : Fin l.val → (Fin M × J)} (hc : ¬ timeCanonical letters),
      timeCoeff h τ M K (Sum.inl ⟨l, letters⟩) = 0) ∧
    (∀ (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ),
      timeCoeff h τ M K (Sum.inr false) + timeCoeff h τ M K (Sum.inr true) = 0) ∧
    (∀ (h : ℝ → J → ℝ) (τ : ℝ) (M : ℕ) (hM : 0 < M),
      taylorLambda (timeScale h τ M) * (M : ℝ) =
        ∑ j : Fin M, ∑ m : J, |h (gridTime τ M j) m|) ∧
    (∀ (h : ℝ → J → ℝ) (τ : ℝ) (M K : ℕ),
      timePhaseGate h τ M K ∈ Matrix.unitaryGroup (TimeWordLabel J K M) ℂ) ∧
    (∀ (h : ℝ → J → ℝ) (U : J → Matrix I I ℂ) (M : ℕ) (j0 : Fin M × J) (τ : ℝ) (K : ℕ),
      adjointQueryCount (timeLCUWord h U M j0 τ K) = K ∧
        adjointGateCount (timeLCUWord h U M j0 τ K) = 2 * K + 3) ∧
    (∀ (h : ℝ → J → ℝ) (U : J → Matrix I I ℂ) (M : ℕ) (j0 : Fin M × J) (τ : ℝ) (K : ℕ),
      adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (timeLCUWord h U M j0 τ K)) = K ∧
        adjointGateCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (timeLCUWord h U M j0 τ K)) = 2 * K + 3) ∧
    (∀ (Λ L τ ε : ℝ), 0 < ε → 0 ≤ Λ → 0 ≤ L → 0 ≤ τ →
      (2 * Λ ^ 2 + L) * τ ^ 2 / (effectiveTimeGrid Λ L τ ε : ℝ) ≤ ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h τ M K l letters hc
    exact timeCoeff_canonical h τ M K hc
  · intro h τ M K l letters hc
    exact timeCoeff_noncanonical h τ M K hc
  · intro h τ M K
    exact timeCoeff_padding_sum h τ M K
  · intro h τ M hM
    exact timeScale_lambda h τ M hM
  · intro h τ M K
    exact timePhaseGate_unitary h τ M K
  · intro h U M j0 τ K
    exact timeLCUWord_counts h U M j0 τ K
  · intro h U M j0 τ K
    exact timeLCUWord_inverse_counts h U M j0 τ K
  · intro Λ L τ ε hε hΛ hL hτ
    exact effectiveTimeGrid_budget Λ L τ ε hε hΛ hL hτ

end Qatlib.Concepts.CoherentSim.ResetDiscard
