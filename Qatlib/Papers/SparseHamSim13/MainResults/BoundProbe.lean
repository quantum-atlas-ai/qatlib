/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseHamSim13.MainResults.Model.FractionalQueryModel
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Domain diagnostics for the retired precision bounds

The source arXiv:1312.1414v2 uses asymptotic O(log(1/ε)/loglog(1/ε)).
The old headers replaced this by a pointwise positive-constant inequality for every
0 < ε < 1. At ε=1/2 that expression is negative. This diagnoses the old headers,
and makes no assertion that the source's asymptotic theorem is false.
-/

set_option autoImplicit false

namespace Qatlib.Papers.SparseHamSim13.MainResults

open Qatlib.Papers.SparseHamSim13.MainResults
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.CoherentSim.CoherentOAA
open scoped Matrix.Norms.L2Operator

/-- The literal precision rate at one half is negative rather than a query budget. -/
theorem half_rate_neg : queryBound 1 (1 / 2) < 0 := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hn : Real.log (Real.log 2) < 0 := Real.log_neg hp hl
  simpa [queryBound] using div_neg_of_pos_of_neg hp hn

/-- No nonnegative counted word can obey a positive multiple of that negative budget. -/
theorem no_half_budget {n : ℕ} (out : List (FracStep n)) (C : ℝ) (hC : 0 < C) :
    ¬ (fracQueryCount out : ℝ) ≤ C * queryBound 1 (1 / 2) := by
  have hneg := mul_neg_of_pos_of_neg hC half_rate_neg
  have hnn : (0 : ℝ) ≤ fracQueryCount out := Nat.cast_nonneg _
  exact not_le.mpr (lt_of_lt_of_le hneg hnn)

/-- A one-dimensional identity has a realizable one-sparse oracle and tau=1, yet
the old sparse upper-bound conclusion at ε=1/2 is impossible for every counted word. -/
theorem sparse_refuted :
    SparseRowOracle 0 1 (1 : Matrix (Fin (2^0)) (Fin (2^0)) ℂ)
      (fun _ _ => 0) (fun _ _ => 1) ∧
    tau 1 (sparseMaxEntry (1 : Matrix (Fin (2^0)) (Fin (2^0)) ℂ)) 1 = 1 ∧
    ¬ ∃ (W : SparseSimulationWord 0 1 (by norm_num) 1
        (fun _ _ => 0) (fun _ _ => 1) 1 (1 / 2)) (C : ℝ), 0 < C ∧
      (adjointQueryCount W.body : ℝ) ≤
        C * queryBound (tau 1 (sparseMaxEntry (1 : Matrix (Fin (2^0)) (Fin (2^0)) ℂ)) 1)
          (1 / 2) := by
  have hone : (1 : Matrix (Fin (2^0)) (Fin (2^0)) ℂ) = fun _ _ => 1 := by
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) = fun _ _ => 1
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have hm : sparseMaxEntry (1 : Matrix (Fin (2^0)) (Fin (2^0)) ℂ) = 1 := by
    norm_num [sparseMaxEntry, hone]
  refine ⟨?_, by norm_num [tau, hm], ?_⟩
  · norm_num [SparseRowOracle, hm, hone]
  · rintro ⟨W, C, hC, hb⟩
    have hneg := mul_neg_of_pos_of_neg hC half_rate_neg
    have hnn : (0 : ℝ) ≤ adjointQueryCount W.body := Nat.cast_nonneg _
    have heq : tau 1 (sparseMaxEntry (1 : Matrix (Fin (2^0)) (Fin (2^0)) ℂ)) 1 = 1 := by
      norm_num [tau, hm]
    rw [heq] at hb
    linarith

/-- The empty input satisfies every numerical premise of the old multiple-query lemma,
but its complete existential conclusion is impossible at T=1 and ε=1/2. -/
theorem multi_refuted :
    fracCost ([] : List (FracStep 0)) ≤ 1 ∧ (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 ∧
    ¬ ∃ (out : List (FracStep 0)) (C : ℝ), 0 < C ∧ WellFormedFracWord out ∧
      (fracQueryCount out : ℝ) ≤
        C * 1 * Real.log (1 / (1 / 2)) / Real.log (Real.log (1 / (1 / 2))) ∧
      ‖evalFracWord out - evalFracWord ([] : List (FracStep 0))‖ ≤ 1 / 2 := by
  refine ⟨by norm_num [fracCost], by norm_num, by norm_num, ?_⟩
  rintro ⟨out, C, hC, _, hb, _⟩
  apply no_half_budget out C hC
  simpa [queryBound, mul_div_assoc] using hb

/-- Arbitrary target-dependent unitary gates cost zero queries in the actual old vocabulary.
An oracle-independence and elementary-gate discipline is needed for source complexity credit. -/
theorem free_gate_bypass {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) (hU : IsUnitary U) :
    WellFormedFracWord [FracStep.gate U] ∧
      fracQueryCount [FracStep.gate U] = 0 ∧ evalFracWord [FracStep.gate U] = U := by
  refine ⟨?_, rfl, ?_⟩
  · intro V hV
    simp only [List.mem_singleton, FracStep.gate.injEq] at hV
    simpa [hV] using hU
  · simp [evalFracWord, FracStep.eval]

/-- A finite continuous segment list has an exact fractional-word representation.
This statement does not assert the source's normalized query cost or discretization bound. -/
theorem continuous_frac_exact {n : ℕ} (P : ContinuousProgram n) :
    evalFracWord (P.segments.map (fun p => FracStep.query p.1 (-p.2))) = P.eval := by
  unfold evalFracWord ContinuousProgram.eval
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp [FracStep.eval, HamiltonianEvolution]

/-- A finite timeline of nonnegative durations summing to zero evaluates to identity. -/
theorem timeline_zero {n : ℕ}
    (S : List (Matrix (Reg n) (Reg n) ℂ × ℝ))
    (hn : ∀ p ∈ S, 0 ≤ p.2) (ht : (S.map (·.2)).sum = 0) :
    (S.map (fun p => HamiltonianEvolution p.1 p.2)).prod = 1 := by
  induction S with
  | nil => simp
  | cons p S ih =>
    have hpn : 0 ≤ p.2 := hn p (by simp)
    have hSn : ∀ q ∈ S, 0 ≤ q.2 := fun q hq => hn q (by simp [hq])
    have hsum : 0 ≤ (S.map (·.2)).sum := by
      apply List.sum_nonneg
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact hSn q hq
    have ht' : p.2 + (S.map (·.2)).sum = 0 := by simpa using ht
    have hp0 : p.2 = 0 := by linarith
    have htail : (S.map (·.2)).sum = 0 := by linarith
    simpa [hp0, HamiltonianEvolution] using ih hSn htail

/-- The old fractional-to-continuous header allows a zero matrix fixed gate. Its
zero-cost word cannot be approximated within one half by a zero-time continuous program. -/
theorem converse_refuted :
    ¬ ∃ P : ContinuousProgram 0,
      P.totalTime = fracCost [FracStep.gate (0 : Matrix (Reg 0) (Reg 0) ℂ)] ∧
      ‖P.eval - evalFracWord [FracStep.gate (0 : Matrix (Reg 0) (Reg 0) ℂ)]‖ ≤ 1 / 2 := by
  rintro ⟨P, ht, herr⟩
  have ht0 : P.totalTime = 0 := by simpa [fracCost] using ht
  have hev : P.eval = 1 := timeline_zero P.segments P.duration_nonneg ht0
  have hh : (1 : ℝ) ≤ 1 / 2 := by simpa [hev, evalFracWord, FracStep.eval] using herr
  norm_num at hh

/-- The dense four-dimensional matrix allowed by the old existential lower-bound header
cannot have the required two-sparse row oracle. -/
theorem dense_no_oracle (f : Fin (2^2) → Fin 2 → Fin (2^2))
    (v : Fin (2^2) → Fin 2 → ℂ) :
    ¬ SparseRowOracle 2 2 (fun _ _ => (1 / 4 : ℂ)) f v := by
  intro h
  have hr := h.2.1 (0 : Fin (2^2))
  norm_num at hr

/-- The literal old lower-bound conclusion holds through an impossible oracle premise.
This exposes the missing sparsity witness and grants no Hamiltonian lower-bound credit. -/
theorem legacy_lower_vacuous (ε : ℝ) :
    ∃ (H : Matrix (Fin (2^2)) (Fin (2^2)) ℂ) (t0 c : ℝ),
      0 < t0 ∧ 0 < c ∧ H.IsHermitian ∧ sparseMaxEntry H < 1 ∧
      ∀ (f : Fin (2^2) → Fin 2 → Fin (2^2)) (v : Fin (2^2) → Fin 2 → ℂ),
        SparseRowOracle 2 2 H f v →
        ∀ (W : SparseSimulationWord 2 2 (by norm_num) H f v t0 ε),
          c * lowerBoundRate ε ≤ (adjointQueryCount W.body : ℝ) := by
  refine ⟨fun _ _ => (1 / 4 : ℂ), 1, 1, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · ext i j
    change star (1 / 4 : ℂ) = (1 / 4 : ℂ)
    norm_num
  · norm_num [sparseMaxEntry]
  · intro f v h
    exact (dense_no_oracle f v h).elim

end Qatlib.Papers.SparseHamSim13.MainResults
