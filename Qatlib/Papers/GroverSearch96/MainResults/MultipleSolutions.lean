/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3SourceFamilyTigh
import Qatlib.Concepts.SearchStopping.KnownCount.Section3RotationSubgoal
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.GroverSearch96.MainResults

open Matrix
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

theorem multipleSolutions_rotation (n : ℕ) (A : Finset (Reg n)) (θ u : ℝ)
    (hθ : (Real.sin θ) ^ 2 = (A.card : ℝ) / (Fintype.card (Reg n) : ℝ))
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (j : ℕ) (x : ℝ) :
    Run (SetOracle A) (GroverCircuit (Reg n) j)
        (MarkedVector A (u * Real.sin x / Real.sin θ : ℂ)
          (u * Real.cos x / Real.cos θ : ℂ)) =
      MarkedVector A (u * Real.sin (x + 2 * j * θ) / Real.sin θ : ℂ)
        (u * Real.cos (x + 2 * j * θ) / Real.cos θ : ℂ) :=
  run_groverCircuit_markedVector Fintype.card_pos A θ u hθ hs hc j x

theorem multipleSolutions_knownCount_success (n : ℕ) (A : Finset (Reg n))
    (hA : A.Nonempty) (hAc : A.card < Fintype.card (Reg n)) :
    1 - (A.card : ℝ) / (Fintype.card (Reg n) : ℝ) ≤
      MeasureProb (GroverState A
        (groverIterations (knownCountAngle
          ((A.card : ℝ) / (Fintype.card (Reg n) : ℝ))))) A :=
  knownCount_success (I := Reg n) Fintype.card_pos A rfl
    (Finset.card_pos.mpr hA) hAc

open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

theorem multipleSolutions_unknown_actual (n : ℕ) (A : Finset (Reg n))
    (hA : 0 < A.card) :
    let sizes := SourceSizes (Fintype.card (Reg n)) (6/5)
    HasSum (TerminalMass A sizes) 1 ∧
    (∀ x : TerminalTrace (Reg n) sizes, 0 ≤ TerminalMass A sizes x ∧
      (TerminalOutput x ∉ A → TerminalMass A sizes x = 0)) ∧
    (∀ i : Reg n, HasSum (fun x : TerminalTrace (Reg n) sizes =>
      if TerminalOutput x = i then TerminalMass A sizes x else 0)
      (if i ∈ A then 1/(A.card : ℝ) else 0)) ∧
    (∃ q : ℝ, HasSum (fun x : TerminalTrace (Reg n) sizes =>
      TerminalMass A sizes x * (TerminalBooleanQueries sizes x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (29/2 : ℝ)*Real.sqrt ((2^n : ℝ)/A.card)) := by
  have h := (theorem3SourceFamily (I := Reg n) Fintype.card_pos (6/5)
    (by norm_num) (by norm_num)).1 A hA
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  have hc := search_source_terminal_boolean_cost (6/5 : ℝ)
    (by norm_num) (by norm_num) A hA
  have hconst : (1 : ℝ) + 3 * SourcePhaseConstant (6/5) = 29/2 := by
    norm_num [SourcePhaseConstant]
  simpa only [hconst, card_reg, Nat.cast_pow, Nat.cast_ofNat] using hc

end Qatlib.Papers.GroverSearch96.MainResults
