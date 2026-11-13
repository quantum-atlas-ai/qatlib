/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.WalkSearch.QuantumAccess.GeometricSearchBudget
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation

/-!
# Geometric search for a four-label Fourier source

This module specializes randomized amplitude-amplification search to the four-dimensional
Fourier source with the singleton marked set `{0}`, an explicit setting for the search analysis
of [BoyerEtAl1998]. The initial marked mass is `1/4`, and one amplification iteration succeeds
with probability one.

For the capped schedule consisting of one window of size one followed by windows of size two,
`geometric_search_quarter_mass_actual_consumer` gives the exact failure probability and uniform
expected phase, validation, and total query bounds.

## Main statements

* `qft4_round_one`: certain success after one amplification iteration.
* `qft4_tail_fail`: failure probability `(3/8)^r` for `r` window-two stages.
* `geometric_search_quarter_mass_actual_consumer`: the complete finite-schedule probability and
  query bounds.

## References

* [Boyer et al., Lemma 2][BoyerEtAl1998]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped ENNReal Classical

/-- Every entry in the zeroth row of the four-dimensional Fourier matrix is `1/2`. -/
private theorem qft4_entry_zero (y : Fin 4) : QFTMatrix 4 0 y = (2:ℂ)⁻¹ := by
  rw [qftMatrix_apply]
  have h0 : ((0 : Fin 4).val : ℤ) * ((y : Fin 4).val : ℤ) = 0 := by omega
  have h1 : primRoot 4 ^ (((0 : Fin 4).val : ℤ) * ((y : Fin 4).val : ℤ)) = 1 := by
    rw [h0, zpow_zero]
  rw [h1, mul_one]
  norm_num

/-- The Fourier-prepared state on four labels assigns marked mass `1/4` to the singleton `{0}`. -/
private theorem qft4_quarter_mass :
    MeasureProb (preparedAAState (QFTMatrix 4) (0 : Fin 4)) ({0} : Finset (Fin 4)) = 1/4 := by
  have hemp : (preparedAAState (QFTMatrix 4) (0 : Fin 4)) 0 = (2:ℂ)⁻¹ := by
    show (QFTMatrix 4).mulVec (Ket (0 : Fin 4)) 0 = _
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    rw [qft4_entry_zero 0, qft4_entry_zero 1, qft4_entry_zero 2, qft4_entry_zero 3]
    simp [Ket]
  have hsingle : MeasureProb (preparedAAState (QFTMatrix 4) (0 : Fin 4)) ({0} : Finset (Fin 4))
      = BornProb (preparedAAState (QFTMatrix 4) (0 : Fin 4)) 0 := by
    simp [MeasureProb]
  rw [hsingle, BornProb, hemp]
  norm_num

/-- One prepared amplitude-amplification iteration for the four-dimensional Fourier source and
marked set `{0}` succeeds with probability one. -/
private theorem qft4_round_one :
    MeasureProb (Run (preparedMark ({0} : Finset (Fin 4)))
        (preparedAACircuit (QFTMatrix 4) (0 : Fin 4) 1) (Ket (0 : Fin 4))) {0} = 1 := by
  have hA : QFTMatrix 4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := qftMatrix_unitary (by decide)
  have hθ0 : (0:ℝ) < Real.pi / 6 := by positivity
  have hθ1 : Real.pi / 6 < Real.pi / 2 := by
    rw [div_lt_div_iff₀ (by norm_num : (0:ℝ) < 6) (by norm_num : (0:ℝ) < 2)]
    linarith [Real.pi_pos]
  have hprob : MeasureProb (preparedAAState (QFTMatrix 4) (0 : Fin 4)) {0}
      = (Real.sin (Real.pi / 6))^2 := by
    rw [qft4_quarter_mass, Real.sin_pi_div_six]
    norm_num
  rw [prepared_aa_born_success (QFTMatrix 4) (0 : Fin 4) {0} (Real.pi / 6) 1 hA hθ0 hθ1 hprob]
  have hang : (2*((1:ℕ):ℝ)+1)*(Real.pi/6) = Real.pi/2 := by
    field_simp
    ring
  rw [hang, Real.sin_pi_div_two]
  norm_num

/-- The initial geometric search window with cap two is one. -/
private theorem window_cap2_zero : geometricWindow 2 0 = 1 := by
  show max 1 (min 2 ((6^(0:ℕ)+5^(0:ℕ)-1)/5^(0:ℕ))) = 1
  norm_num

/-- Every positive-index geometric search window with cap two equals two. -/
private theorem window_cap2_succ (j : ℕ) : geometricWindow 2 (j+1) = 2 := by
  have h5 : (0:ℕ) < 5^(j+1) := Nat.pow_pos (by norm_num)
  have h61 : 5^(j+1) + 1 ≤ 6^(j+1) := by
    induction j with
    | zero => norm_num
    | succ j ih =>
        have h5' : (0:ℕ) < 5^(j+1) := Nat.pow_pos (by norm_num)
        have h6' : (0:ℕ) < 6^(j+1) := Nat.pow_pos (by norm_num)
        have g1 : (5:ℕ)^(j+1+1) = 5 * 5^(j+1) := by rw [pow_succ]; ring
        have g2 : (6:ℕ)^(j+1+1) = 6 * 6^(j+1) := by rw [pow_succ]; ring
        rw [g1, g2]
        nlinarith [ih h5', h5', h6']
  have hkey : 2 * 5^(j+1) ≤ 6^(j+1) + 5^(j+1) - 1 := by omega
  have hdiv : 2 ≤ (6^(j+1) + 5^(j+1) - 1)/5^(j+1) := (Nat.le_div_iff_mul_le h5).mpr hkey
  show max 1 (min 2 ((6^(j+1)+5^(j+1)-1)/5^(j+1))) = 2
  omega

/-- A cap-two schedule starting at a positive offset consists of `T` copies of the window two. -/
theorem schedFrom_cap2_shifted : ∀ (T off : ℕ), 1 ≤ off →
    schedFrom 2 off T = List.replicate T 2 := by
  intro T off hoff
  induction T generalizing off with
  | zero => rfl
  | succ T ih =>
      have hoff' : geometricWindow 2 off = 2 := by
        have h := window_cap2_succ (off - 1)
        rw [show off - 1 + 1 = off from by omega] at h
        exact h
      rw [schedFrom_succ, hoff', ih (off + 1) (by omega)]
      rfl

/-- The Boolean test for label zero accepts exactly the marked singleton `{0}`. -/
private theorem qft4_valid_iff (y : Fin 4) : (decide (y = 0) : Bool) = true ↔ y ∈ ({0} : Finset (Fin 4)) := by
  constructor
  · intro h
    have hy : y = 0 := of_decide_eq_true h
    rw [hy]
    simp
  · intro h
    have hy : y = 0 := by
      simpa using h
    rw [hy]
    simp

/-- A successful marked output in the four-label example is precisely an output containing label
zero with some gate count. -/
private theorem qft4_success_conv (x : Option (Fin 4 × ℕ) × ℕ × ℕ) :
    (∃ y gates, x.1 = some (y, gates) ∧ y ∈ ({0} : Finset (Fin 4)))
      ↔ ∃ g, x.1 = some (0, g) := by
  constructor
  · rintro ⟨y, g, h1, h2⟩
    have hy : y = 0 := by simpa using h2
    rw [hy] at h1
    exact ⟨g, h1⟩
  · rintro ⟨g, h1⟩
    exact ⟨0, g, h1, by simp⟩

/-- The sampled four-label search slot with window one and three rejection attempts has failure
probability `3/4`. -/
private theorem qft4_fail_slot_zero :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (Nat.clog 2 1) 1 3)
      (fun out => searchSlotFail (fun y => decide (y = 0)) out) = 3/4 := by
  have hA : QFTMatrix 4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := qftMatrix_unitary (by decide)
  have hm : (0:ℕ) < 1 := by norm_num
  have hm2 : 1 ≤ 2 ^ Nat.clog 2 1 := Nat.le_pow_clog (by norm_num : 1 < 2) 1
  have hq : (coinRejectMass 0 1)^3 = 0 := by
    norm_num [coinRejectMass]
  have hE := prepared_aa_sampled_success (QFTMatrix 4) (0 : Fin 4) {0} hA
    (Nat.clog 2 1) 1 3 hm hm2
  rw [show Nat.clog 2 1 = 0 from Nat.clog_one_right 2] at hE
  rw [hq] at hE
  simp at hE
  have hrun : Run (preparedMark ({0} : Finset (Fin 4)))
      (preparedAACircuit (QFTMatrix 4) (0 : Fin 4) 0) (Ket (0 : Fin 4))
      = preparedAAState (QFTMatrix 4) (0 : Fin 4) := by
    have h :=
        (prepared_aa_actual_circuit (QFTMatrix 4) (0 : Fin 4) ({0} : Finset (Fin 4)) 0 hA).2.2.2
    rw [pow_zero, applyGate_one] at h
    exact h
  rw [hrun, qft4_quarter_mass] at hE
  have hquarter : ENNReal.ofReal ((1/4:ℝ)) = (1/4:ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
    norm_num
  rw [hquarter] at hE
  have hpart : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (QFTMatrix 4) hA (0 : Fin 4) {0}
      (Nat.clog 2 1) 1 3) (fun out => searchSlotFail (fun y => decide (y = 0)) out)
      + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (QFTMatrix 4) hA (0 : Fin 4) {0}
        (Nat.clog 2 1) 1 3) (fun out => ¬ searchSlotFail (fun y => decide (y = 0)) out)
      = 1 := event_compl _ _
  rw [slot_success_event_congr (QFTMatrix 4) hA (0 : Fin 4) {0}
    (fun y => decide (y = 0)) 1 qft4_valid_iff,
    show Nat.clog 2 1 = 0 from Nat.clog_one_right 2,
    ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun x => (qft4_success_conv x).symm), hE] at hpart
  have h34 : (1:ℝ≥0∞) - (1/4:ℝ≥0∞) = (3/4:ℝ≥0∞) := by
    rw [show (1/4:ℝ≥0∞) = ENNReal.ofReal ((1/4:ℝ)) from hquarter.symm,
      show (3/4:ℝ≥0∞) = ENNReal.ofReal ((3/4:ℝ)) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]; norm_num,
      show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub (1) (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)]
    congr 1
    norm_num
  have hr := ENNReal.eq_sub_of_add_eq (by
    rw [show (1/4:ℝ≥0∞) = ENNReal.ofReal ((1/4:ℝ)) from hquarter.symm]
    exact ENNReal.ofReal_ne_top) hpart
  rw [show Nat.clog 2 1 = 0 from Nat.clog_one_right 2, hr, h34]

/-- The sampled four-label search slot with window two and three rejection attempts has failure
probability `3/8`. -/
private theorem qft4_fail_slot_two :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (Nat.clog 2 2) 2 3)
      (fun out => searchSlotFail (fun y => decide (y = 0)) out) = 3/8 := by
  have hA : QFTMatrix 4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := qftMatrix_unitary (by decide)
  have hm : (0:ℕ) < 2 := by norm_num
  have hm2 : 2 ≤ 2 ^ Nat.clog 2 2 := Nat.le_pow_clog (by norm_num : 1 < 2) 2
  have hq : (coinRejectMass 1 2)^3 = 0 := by
    norm_num [coinRejectMass]
  have hE := prepared_aa_sampled_success (QFTMatrix 4) (0 : Fin 4) {0} hA
    (Nat.clog 2 2) 2 3 hm hm2
  rw [show Nat.clog 2 2 = 1 from by norm_num] at hE
  rw [hq] at hE
  simp at hE
  have hrun0 : Run (preparedMark ({0} : Finset (Fin 4)))
      (preparedAACircuit (QFTMatrix 4) (0 : Fin 4) 0) (Ket (0 : Fin 4))
      = preparedAAState (QFTMatrix 4) (0 : Fin 4) := by
    have h :=
        (prepared_aa_actual_circuit (QFTMatrix 4) (0 : Fin 4) ({0} : Finset (Fin 4)) 0 hA).2.2.2
    rw [pow_zero, applyGate_one] at h
    exact h
  have hmass0 : MeasureProb (Run (preparedMark ({0} : Finset (Fin 4)))
      (preparedAACircuit (QFTMatrix 4) (0 : Fin 4) 0) (Ket (0 : Fin 4))) {0} = 1/4 := by
    rw [hrun0, qft4_quarter_mass]
  rw [hmass0, qft4_round_one] at hE
  have hval : ((2:ℝ≥0∞))⁻¹ * (ENNReal.ofReal ((1/4:ℝ)) + ENNReal.ofReal ((1:ℝ)))
      = (5/8:ℝ≥0∞) := by
    have hq14 : ENNReal.ofReal ((1/4:ℝ)) = (1/4:ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
      norm_num
    have hsum : ENNReal.ofReal ((1/4:ℝ)) + ENNReal.ofReal ((1:ℝ))
        = ENNReal.ofReal ((5/4:ℝ)) := by
      rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (0:ℝ) ≤ 1)]
      congr 1
      norm_num
    have h2i : ((2:ℝ≥0∞))⁻¹ = ENNReal.ofReal (((2:ℝ))⁻¹) := by
      rw [show ((2:ℝ≥0∞)) = ENNReal.ofReal ((2:ℝ)) from by norm_num, inv_eq_one_div,
        show ((1:ℝ≥0∞)) / (ENNReal.ofReal ((2:ℝ))) = ENNReal.ofReal (((1:ℝ)/2)) from by
          rw [show ((1:ℝ≥0∞)) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
            ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]]
      congr 1
      norm_num
    have hfin : ENNReal.ofReal (((2:ℝ))⁻¹) * ENNReal.ofReal ((5/4:ℝ))
        = ENNReal.ofReal ((5/8:ℝ)) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2:ℝ)⁻¹)]
      field_simp
      norm_num
    rw [hsum, h2i, hfin]
    rw [show ENNReal.ofReal ((5/8:ℝ)) = (5/8:ℝ≥0∞) from by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
      norm_num]
  have hpart : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (QFTMatrix 4) hA (0 : Fin 4) {0}
      (Nat.clog 2 2) 2 3) (fun out => searchSlotFail (fun y => decide (y = 0)) out)
      + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (preparedAASampled (QFTMatrix 4) hA (0 : Fin 4) {0}
        (Nat.clog 2 2) 2 3) (fun out => ¬ searchSlotFail (fun y => decide (y = 0)) out)
      = 1 := event_compl _ _
  rw [slot_success_event_congr (QFTMatrix 4) hA (0 : Fin 4) {0}
    (fun y => decide (y = 0)) 2 qft4_valid_iff,
    show Nat.clog 2 2 = 1 from by norm_num,
    ← Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr (fun x => (qft4_success_conv x).symm), hE] at hpart
  have h38 : (1:ℝ≥0∞) - (5/8:ℝ≥0∞) = (3/8:ℝ≥0∞) := by
    rw [show (5/8:ℝ≥0∞) = ENNReal.ofReal ((5/8:ℝ)) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]; norm_num,
      show (3/8:ℝ≥0∞) = ENNReal.ofReal ((3/8:ℝ)) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]; norm_num,
      show (1:ℝ≥0∞) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
      ← ENNReal.ofReal_sub (1) (by norm_num : (0:ℝ) ≤ (5:ℝ)/8)]
    congr 1
    norm_num
  have h58 : ((2:ℝ≥0∞))⁻¹ * (ENNReal.ofReal ((1/4:ℝ)) + ENNReal.ofReal ((1:ℝ)))
      ≠ (⊤:ℝ≥0∞) := by
    rw [hval,
      show (5/8:ℝ≥0∞) = ENNReal.ofReal ((5/8:ℝ)) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
        norm_num]
    exact ENNReal.ofReal_ne_top
  have hr := ENNReal.eq_sub_of_add_eq h58 hpart
  rw [show Nat.clog 2 2 = 1 from by norm_num, hr, hval, h38]

/-- The validation function `fun y => decide (y = 0)` accepts exactly the marked set `{0}`. -/
private theorem qft4_valid (y : Fin 4) : (fun y => decide (y = 0)) y = true ↔ y ∈ ({0} : Finset (Fin 4)) :=
  qft4_valid_iff y

/-- The cap-two geometric schedule of length `r + 1` is an initial window one followed by `r`
windows two. -/
private theorem qft4_schedule_eq (r : ℕ) :
    geometricSearchSchedule 2 (r+1) = 1 :: List.replicate r 2 := by
  rw [← schedFrom_zero, schedFrom_succ, window_cap2_zero, schedFrom_cap2_shifted r 1 (by omega)]

/-- The expected phase-query increment of the sampled four-label slot with window two is `1/2`. -/
private theorem qft4_phase_inc_two :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} 1 2 3) (fun out => (out.2.2 : ℝ≥0∞)) = 1/2 := by
  have hA : QFTMatrix 4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := qftMatrix_unitary (by decide)
  have hm : (0:ℕ) < 2 := by norm_num
  have hm2 : 2 ≤ 2 ^ 1 := by norm_num
  have hL := (prepared_aa_sampled_three_ledgers (QFTMatrix 4) (0 : Fin 4) {0} hA 1 2 3 hm hm2).2.1
  have hq : (coinRejectMass 1 2)^3 = 0 := by norm_num [coinRejectMass]
  rw [hq] at hL
  simp at hL
  rw [hL, show ((2:ℝ≥0∞))⁻¹ = (1/2:ℝ≥0∞) from by rw [inv_eq_one_div]]

/-- For any number of window-two stages in the four-label search, the expected phase-query count
is at most `4/5`. -/
private theorem qft4_tail_phase : ∀ r : ℕ,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (fun y => decide (y = 0)) (List.replicate r 2))
      (fun tr => (tr.phaseQueries : ℝ≥0∞)) ≤ (4/5:ℝ≥0∞) := by
  intro r
  induction r with
  | zero =>
      rw [show (List.replicate 0 2) = [] from rfl,
        show searchForSchedule (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
          (0 : Fin 4) {0} (fun y => decide (y = 0)) [] = PMF.pure emptySearchTrace from rfl,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      norm_num [emptySearchTrace]
  | succ r ih =>
      rw [List.replicate_succ, search_ledger_recursion (QFTMatrix 4)
        (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (fun y => decide (y = 0)) (fun tr => tr.phaseQueries)
        (fun out => out.2.2) (fun m out tr => rfl) (fun m out y => rfl) 2
        (List.replicate r 2),
        qft4_fail_slot_two, show Nat.clog 2 2 = 1 from by norm_num, qft4_phase_inc_two]
      have h38 : (3/8:ℝ≥0∞) * (4/5:ℝ≥0∞) + 1/2 = (4/5:ℝ≥0∞) := by
        have h1 : (3/8:ℝ≥0∞) = ENNReal.ofReal ((3/8:ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
          norm_num
        have h2 : (4/5:ℝ≥0∞) = ENNReal.ofReal ((4/5:ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
          norm_num
        have h3 : (1/2:ℝ≥0∞) = ENNReal.ofReal ((1/2:ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
          norm_num
        rw [h1, h2, h3,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/8),
          ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ (3:ℝ)/8*((4:ℝ)/5)) (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)]
        rw [show ((3/8:ℝ)*(4/5:ℝ) + (1/2:ℝ)) = ((4/5:ℝ)) from by norm_num]
      calc (1/2:ℝ≥0∞) + (3/8:ℝ≥0∞) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
            (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0}
            (fun y => decide (y = 0)) (List.replicate r 2)) (fun tr => (tr.phaseQueries:ℝ≥0∞))
          ≤ 1/2 + (3/8:ℝ≥0∞) * (4/5:ℝ≥0∞) :=
            add_le_add (le_refl _) (mul_le_mul' (le_refl _) ih)
        _ = 4/5 := by rw [add_comm]; exact h38

/-- For any number of window-two stages in the four-label search, the expected validation-query
count is at most `8/5`. -/
private theorem qft4_tail_val : ∀ r : ℕ,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (fun y => decide (y = 0)) (List.replicate r 2))
      (fun tr => (tr.validationQueries : ℝ≥0∞)) ≤ (8/5:ℝ≥0∞) := by
  intro r
  induction r with
  | zero =>
      rw [show (List.replicate 0 2) = [] from rfl,
        show searchForSchedule (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
          (0 : Fin 4) {0} (fun y => decide (y = 0)) [] = PMF.pure emptySearchTrace from rfl,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      norm_num [emptySearchTrace]
  | succ r ih =>
      have hrw : List.replicate (r+1) 2 = 2 :: List.replicate r 2 := List.replicate_succ
      have hinc : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (QFTMatrix 4)
            (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} 1 2 3)
            (fun out => ((if out.1.isSome then 1 else 0 : ℕ) : ℝ≥0∞)) ≤ 1 :=
        expectation_le_of_support _ _ _ (fun out _ => by
          cases out.1 with
          | none => simp
          | some _ => simp)
      rw [List.replicate_succ, search_ledger_recursion (QFTMatrix 4)
        (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (fun y => decide (y = 0)) (fun tr => tr.validationQueries)
        (fun out => if out.1.isSome then 1 else 0) (fun m out tr => rfl)
        (fun m out y => rfl) 2 (List.replicate r 2),
        qft4_fail_slot_two, show Nat.clog 2 2 = 1 from by norm_num]
      have h58 : (3/8:ℝ≥0∞) * (8/5:ℝ≥0∞) + 1 = (8/5:ℝ≥0∞) := by
        have h1 : (3/8:ℝ≥0∞) = ENNReal.ofReal ((3/8:ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
          norm_num
        have h2 : (8/5:ℝ≥0∞) = ENNReal.ofReal ((8/5:ℝ)) := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
          norm_num
        rw [h1, h2,
          show ((1:ℝ≥0∞)) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/8),
          ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ (3:ℝ)/8*((8:ℝ)/5)) (by norm_num : (0:ℝ) ≤ 1),
          show ((3:ℝ)/8*((8:ℝ)/5) + (1:ℝ)) = ((8:ℝ)/5) from by norm_num]
      calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (QFTMatrix 4)
            (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} 1 2 3)
            (fun out => ((if out.1.isSome then 1 else 0 : ℕ) : ℝ≥0∞))
            + (3/8:ℝ≥0∞) *
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
            (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0}
            (fun y => decide (y = 0)) (List.replicate r 2)) (fun tr => (tr.validationQueries:ℝ≥0∞))
          ≤ 1 + (3/8:ℝ≥0∞) * (8/5:ℝ≥0∞) :=
            add_le_add hinc (mul_le_mul' (le_refl _) ih)
        _ = 8/5 := by rw [add_comm]; exact h58

/-- The four-label search with `r` consecutive window-two stages fails with probability
`(3/8)^r`. -/
private theorem qft4_tail_fail : ∀ r : ℕ,
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} (fun y => decide (y = 0)) (List.replicate r 2))
      (fun tr => tr.result = none) = (3/8:ℝ≥0∞)^r := by
  intro r
  induction r with
  | zero =>
      rw [show (List.replicate 0 2) = [] from rfl,
        show searchForSchedule (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
          (0 : Fin 4) {0} (fun y => decide (y = 0)) [] = PMF.pure emptySearchTrace from rfl,
        Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_eq, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_pure]
      norm_num [emptySearchTrace]
  | succ r ih =>
      rw [List.replicate_succ, search_event_none_recursion, qft4_fail_slot_two, ih, pow_succ,
        mul_comm]

/-- The sampled four-label slot with window one has expected phase-query increment zero. -/
private theorem qft4_phase_inc_one :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (QFTMatrix 4) (qftMatrix_unitary (by decide : 0<4))
        (0 : Fin 4) {0} 0 1 3) (fun out => (out.2.2 : ℝ≥0∞)) = 0 := by
  have hA : QFTMatrix 4 ∈ Matrix.unitaryGroup (Fin 4) ℂ := qftMatrix_unitary (by decide)
  have hm : (0:ℕ) < 1 := by norm_num
  have hm2 : 1 ≤ 2 ^ 0 := by norm_num
  have hL := (prepared_aa_sampled_three_ledgers (QFTMatrix 4) (0 : Fin 4) {0} hA 0 1 3 hm hm2).2.1
  have hq : (coinRejectMass 0 1)^3 = 0 := by norm_num [coinRejectMass]
  rw [hq] at hL
  simp at hL
  exact hL

/-- For the four-label Fourier source with marked set `{0}`, the cap-two schedule of length `r +
1` fails with probability `(3/4)(3/8)^r`. Its expected phase, validation, and combined query
counts are at most `3/5`, `11/5`, and `14/5`, respectively, giving a concrete instance of
randomized quantum search [Boyer et al., Lemma 2][BoyerEtAl1998]. -/
theorem geometric_search_quarter_mass_actual_consumer :
    ∀ (r : ℕ),
      let A := QFTMatrix 4
      let hA := qftMatrix_unitary (by decide : 0<4)
      let p :=
          searchForSchedule A hA (0:Fin 4) {0} (fun y => decide (y=0))
          (geometricSearchSchedule 2 (r+1))
      (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event p (fun tr => tr.result=none)).toReal = (3/4:ℝ)*(3/8:ℝ)^r ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.phaseQueries:ℝ≥0∞)) ≤ ENNReal.ofReal (3/5:ℝ) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => (tr.validationQueries:ℝ≥0∞)) ≤ ENNReal.ofReal (11/5:ℝ) ∧
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation p (fun tr => ((tr.phaseQueries+tr.validationQueries):ℝ≥0∞)) ≤ ENNReal.ofReal (14/5:ℝ) := by
  intro r
  have hfail : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (searchForSchedule (QFTMatrix 4)
      (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
      (geometricSearchSchedule 2 (r+1))) (fun tr => tr.result = none)
      = (3/4:ℝ≥0∞) * (3/8:ℝ≥0∞)^r := by
    rw [qft4_schedule_eq, search_event_none_recursion, qft4_fail_slot_zero, qft4_tail_fail]
  have hphase : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
      (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
      (geometricSearchSchedule 2 (r+1))) (fun tr => (tr.phaseQueries:ℝ≥0∞))
      ≤ ENNReal.ofReal ((3/5:ℝ)) := by
    rw [qft4_schedule_eq, search_ledger_recursion (QFTMatrix 4)
      (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
      (fun tr => tr.phaseQueries) (fun out => out.2.2) (fun m out tr => rfl)
      (fun m out y => rfl) 1 (List.replicate r 2), qft4_fail_slot_zero,
      show Nat.clog 2 1 = 0 from Nat.clog_one_right 2, qft4_phase_inc_one]
    rw [zero_add]
    have h35 : (3/4:ℝ≥0∞) * (4/5:ℝ≥0∞) = ENNReal.ofReal ((3/5:ℝ)) := by
      have h1 : (3/4:ℝ≥0∞) = ENNReal.ofReal ((3/4:ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
        norm_num
      have h2 : (4/5:ℝ≥0∞) = ENNReal.ofReal ((4/5:ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
        norm_num
      rw [h1, h2, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4),
        show ((3:ℝ)/4*((4:ℝ)/5) ) = ((3:ℝ)/5) from by norm_num]
    calc (3/4:ℝ≥0∞) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
          (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0}
          (fun y => decide (y = 0)) (List.replicate r 2)) (fun tr => (tr.phaseQueries:ℝ≥0∞))
        ≤ (3/4:ℝ≥0∞) * (4/5:ℝ≥0∞) := mul_le_mul' (le_refl _) (qft4_tail_phase r)
      _ = ENNReal.ofReal ((3/5:ℝ)) := h35
  have hval : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
      (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
      (geometricSearchSchedule 2 (r+1))) (fun tr => (tr.validationQueries:ℝ≥0∞))
      ≤ ENNReal.ofReal ((11/5:ℝ)) := by
    rw [qft4_schedule_eq, search_ledger_recursion (QFTMatrix 4)
      (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
      (fun tr => tr.validationQueries) (fun out => if out.1.isSome then 1 else 0)
      (fun m out tr => rfl) (fun m out y => rfl) 1 (List.replicate r 2), qft4_fail_slot_zero,
      show Nat.clog 2 1 = 0 from Nat.clog_one_right 2]
    have hinc : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (QFTMatrix 4)
        (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} 0 1 3)
        (fun out => ((if out.1.isSome then 1 else 0 : ℕ) : ℝ≥0∞)) ≤ 1 :=
      expectation_le_of_support _ _ _ (fun out _ => by
        cases out.1 with
        | none => simp
        | some _ => simp)
    have h115 : 1 + (3/4:ℝ≥0∞) * (8/5:ℝ≥0∞) = ENNReal.ofReal ((11/5:ℝ)) := by
      have h1 : (3/4:ℝ≥0∞) = ENNReal.ofReal ((3/4:ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
        norm_num
      have h2 : (8/5:ℝ≥0∞) = ENNReal.ofReal ((8/5:ℝ)) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)]
        norm_num
      rw [h1, h2,
        show ((1:ℝ≥0∞)) = ENNReal.ofReal ((1:ℝ)) from ENNReal.ofReal_one.symm,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3/4),
        ← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ (3:ℝ)/4*((8:ℝ)/5)),
        show ((1:ℝ) + (3:ℝ)/4*((8:ℝ)/5)) = ((11:ℝ)/5) from by norm_num]
    calc Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (preparedAASampled (QFTMatrix 4)
          (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} 0 1 3)
          (fun out => ((if out.1.isSome then 1 else 0 : ℕ) : ℝ≥0∞))
        + (3/4:ℝ≥0∞) *
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
          (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0}
          (fun y => decide (y = 0)) (List.replicate r 2)) (fun tr => (tr.validationQueries:ℝ≥0∞))
        ≤ 1 + (3/4:ℝ≥0∞) * (8/5:ℝ≥0∞) :=
          add_le_add hinc (mul_le_mul' (le_refl _) (qft4_tail_val r))
      _ = ENNReal.ofReal ((11/5:ℝ)) := h115
  refine ⟨?_, hphase, hval, ?_⟩
  · rw [hfail]
    rw [show ((3/4:ℝ≥0∞) * (3/8:ℝ≥0∞)^r).toReal = ((3/4:ℝ≥0∞)).toReal * ((3/8:ℝ≥0∞)^r).toReal from
      ENNReal.toReal_mul]
    rw [show ((3/4:ℝ≥0∞)).toReal = (3/4:ℝ) from by
      rw [show (3/4:ℝ≥0∞) = ENNReal.ofReal ((3/4:ℝ)) from by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
        norm_num]
      exact ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 3/4)]
    rw [show ((3/8:ℝ≥0∞)^r).toReal = ((3/8:ℝ))^r from by
      rw [show ((3/8:ℝ≥0∞)^r) = ENNReal.ofReal (((3/8:ℝ))^r) from by
        rw [show (3/8:ℝ≥0∞) = ENNReal.ofReal ((3/8:ℝ)) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 8)]
          norm_num, ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 3/8)]]
      exact ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (3/8:ℝ)^r)]
  · have hsplit : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
          (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
          (geometricSearchSchedule 2 (r+1)))
          (fun tr => (tr.phaseQueries:ℝ≥0∞) + (tr.validationQueries:ℝ≥0∞))
        = Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
            (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
            (geometricSearchSchedule 2 (r+1))) (fun tr => (tr.phaseQueries:ℝ≥0∞))
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
            (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
            (geometricSearchSchedule 2 (r+1))) (fun tr => (tr.validationQueries:ℝ≥0∞)) :=
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation_add _ _ _
    rw [hsplit]
    have hsum : Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
          (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
          (geometricSearchSchedule 2 (r+1))) (fun tr => (tr.phaseQueries:ℝ≥0∞))
        + Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (searchForSchedule (QFTMatrix 4)
          (qftMatrix_unitary (by decide : 0<4)) (0 : Fin 4) {0} (fun y => decide (y = 0))
          (geometricSearchSchedule 2 (r+1))) (fun tr => (tr.validationQueries:ℝ≥0∞))
        ≤ ENNReal.ofReal ((14/5:ℝ)) := by
      have h14 : ENNReal.ofReal ((3/5:ℝ)) + ENNReal.ofReal ((11/5:ℝ))
          = ENNReal.ofReal ((14/5:ℝ)) := by
        rw [← ENNReal.ofReal_add (by norm_num : (0:ℝ) ≤ 3/5) (by norm_num : (0:ℝ) ≤ 11/5)]
        congr 1
        norm_num
      rw [← h14]
      exact add_le_add hphase hval
    exact hsum

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
