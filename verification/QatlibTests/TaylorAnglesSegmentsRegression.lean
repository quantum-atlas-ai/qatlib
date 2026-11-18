/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor
public import Qatlib.Papers.TruncTaylor14.PrepareSelectOracle

@[expose] public section

/-! Regression consumers for the explicit factorial amplitudes and segment ledger. -/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor
open Qatlib.Papers.TruncTaylor14.PrepareSelectAmplitude
open Qatlib.Papers.TruncTaylor14.PrepareSelectCount
open Qatlib.Papers.TruncTaylor14.PrepareSelectOracle
open Qatlib.Papers.TruncTaylor14.ResourceCount
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace QatlibTests.TaylorAnglesSegmentsRegression

open scoped Matrix.Norms.L2Operator

example : taylorWeight (1 / 2) 3 = 1 / 48 := by
  norm_num [taylorWeight, Nat.factorial]

example : taylorMass 1 2 = 5 / 2 := by
  norm_num [taylorMass, taylorTail, taylorWeight, Finset.sum_range_succ, Nat.factorial]

example : taylorAmplitude 1 2 0 = Real.sqrt (2 / 5) := by
  norm_num [taylorAmplitude, taylorMass, taylorTail, taylorWeight,
    Finset.sum_range_succ, Nat.factorial]

example (k : Fin 5) :
    cascadePrepared 4 (fun i => taylorAngle (1 / 2) 4 i.val) (unaryReg 4 k) =
      (taylorAmplitude (1 / 2) 4 k.val : ℂ) :=
  taylor_prepared_entry (by norm_num) 4 k

example :
    ‖cascadePrepared 2 (fun i => taylorAngle 1 2 i.val) (unaryReg 2 (2 : Fin 3))‖ ^ 2 =
      1 / 5 := by
  rw [taylor_prepared_born (by norm_num)]
  norm_num [taylorWeight, taylorMass, taylorTail, Finset.sum_range_succ, Nat.factorial]

example : Summable (fun j : ℕ => taylorWeight (1 / 2) (4 + j)) ∧
    (∑' j : ℕ, taylorWeight (1 / 2) (4 + j)) ≤ 1 / 192 := by
  have h := taylor_remainder_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) 3
  refine ⟨h.1, h.2.trans_eq ?_⟩
  norm_num [taylorWeight, Nat.factorial]

-- Order zero requires no wires and still prepares exactly the normalized constant term.
example : cascadePrepared 0 (fun i => taylorAngle 1 0 i.val) (unaryReg 0 0) =
    (taylorAmplitude 1 0 0 : ℂ) :=
  taylor_prepared_entry (by norm_num) 0 0

-- Truncation at positive time has a genuine omitted contribution.
example : 0 < taylorWeight 1 3 := taylorWeight_pos (by norm_num) 3

example : ¬ taylorWeight 1 3 = 0 := ne_of_gt (taylorWeight_pos (by norm_num) 3)

-- The strict positivity premise is necessary for the division-based tail angles.
example : ¬ 0 < taylorTail 0 2 1 := by
  norm_num [taylorTail, taylorWeight, Finset.sum_range_succ, Nat.factorial]

example (O : TermOracle 2 Bool) (θ : Fin 3 → ℝ)
    (b : Matrix (Fin 2) (Fin 2) ℂ) (gs : List (ReflectionGate 3)) :
    QueryCount (RepeatCircuit (segmentOraWord 3 2 Bool θ b O gs) 5) = 15 ∧
      GateCount (RepeatCircuit (segmentOraWord 3 2 Bool θ b O gs) 5) =
        5 * (12 + gs.length) := by
  simpa [← Nat.add_assoc] using repeated_fine_segment_cost 3 2 5 Bool θ b O gs

-- The concrete factorial-angle prescription feeds the very same measured word.
example (O : TermOracle 2 Bool) (b : Matrix (Fin 2) (Fin 2) ℂ)
    (gs : List (ReflectionGate 3)) :
    QueryCount (RepeatCircuit
      (segmentOraWord 3 2 Bool (fun i => taylorAngle (1 / 2) 3 i.val) b O gs) 5) = 15 := by
  exact (repeated_fine_segment_cost 3 2 5 Bool _ b O gs).1

-- Coarse SELECT and fine term-oracle queries remain distinct on the same parameters.
example (O : TermOracle 2 Bool) (θ : Fin 3 → ℝ)
    (b : Matrix (Fin 2) (Fin 2) ℂ) (gs : List (ReflectionGate 3)) :
    QueryCount (RepeatCircuit (segmentWord 3 2 Bool θ b O gs) 5) = 5 := by
  rw [queryCount_repeatCircuit, segmentQC, Nat.mul_one]

-- The joint error/resource interface is usable at an exact target without
-- postulating any source Taylor/OAA correctness for an arbitrary reflection.
example (O : TermOracle 2 Bool) (θ : Fin 3 → ℝ)
    (b : Matrix (Fin 2) (Fin 2) ℂ) (gs : List (ReflectionGate 3))
    (hb : b ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hgs : reflectionLegal gs) :
    ‖Denote (taylorSelect 3 2 Bool (termV O))
      (RepeatCircuit (segmentWord 3 2 Bool θ b O gs) 7) -
        Denote (taylorSelect 3 2 Bool (termV O)) (segmentWord 3 2 Bool θ b O gs) ^ 7‖ ≤ 0 := by
  have hs : taylorSelect 3 2 Bool (termV O) ∈
      Matrix.unitaryGroup (TTWs 3 2 Bool) ℂ := by
    rw [← selectDenote]
    exact selectUniDen 3 2 Bool (termV O) (termV_family O)
  have hu := denote_unitary _ hs (segmentUni 3 2 Bool θ b O gs hb hgs)
  have h := repeated_segment_error_cost 3 2 7 Bool θ b O gs hb hgs
    (Denote (taylorSelect 3 2 Bool (termV O)) (segmentWord 3 2 Bool θ b O gs))
    hu 0 (by simp)
  simpa using h.2.2

-- Zero repetitions are free, independent of the oracle, load, angles and reflection.
example (O : TermOracle 2 Bool) (θ : Fin 3 → ℝ)
    (b : Matrix (Fin 2) (Fin 2) ℂ) (gs : List (ReflectionGate 3)) :
    QueryCount (RepeatCircuit (segmentOraWord 3 2 Bool θ b O gs) 0) = 0 := rfl

end QatlibTests.TaylorAnglesSegmentsRegression
