/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateTables.GrayUniversal.Section8GrayTwoLevelStat
import Qatlib.Concepts.GateTables.GrayUniversal.GrayPhaseSynthesis

/-!
# Exact Gray two-level synthesis

`section8GrayTwoLevel` proves the uniform synthesis specification `Section8GrayTwoLevel`. It
combines arbitrary-pair and single-address phase tables to implement every legal two-level
instruction on the original register.

The construction has zero oracle queries and an explicit word-length bound, in the elementary
gate synthesis setting of [BarencoEtAl1995].

## Main statements

* `section8GrayTwoLevel`: establishes the full legality, count, and whole-state semantics
  specification.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal
open Matrix
open scoped Classical BigOperators

/-- For every `n ≥ 1`, each legal two-level instruction has a legal reflection-word
implementation of length at most `(2 * n - 1) * (256 * n^2 + 2 * n - 2)`. The circuit has
zero queries, one gate per word entry, and the required action on every state. -/
theorem section8GrayTwoLevel : Section8GrayTwoLevel := by
  intro n hn
  cases n with
  | zero => omega
  | succ k =>
    intro g hg
    have hcost : 256*(k+1)^2+2*k = 256*(k+1)^2+2*(k+1)-2 := by omega
    have hblocks : 1 ≤ 2*(k+1)-1 := by omega
    have hlocal : ∃ gs : List (ReflectionGate (k+1)), reflectionLegal gs ∧
        gs.length ≤ (2*(k+1)-1)*(256*(k+1)^2+2*(k+1)-2) ∧
        ∀ ψ : QState (Reg (k+1)), Run 1 (reflectionCompile gs) ψ = twoLevelMatrix g *ᵥ ψ := by
      cases g with
      | pair x y B =>
        obtain ⟨gs,hgs,hlen,hr⟩ := grayPair_table x y hg.1 B hg.2
        refine ⟨gs,hgs,hlen.trans ?_,hr⟩
        rw [hcost]
        apply Nat.mul_le_mul_right
        apply Nat.sub_le_sub_right
        apply Nat.mul_le_mul_left
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
      | phase x z =>
        obtain ⟨gs,hgs,hlen,hr⟩ := grayPhase_table x z hg
        refine ⟨gs,hgs,hlen.trans ?_,hr⟩
        rw [hcost]
        exact Nat.le_mul_of_pos_left _ hblocks
    obtain ⟨gs,hgs,hlen,hr⟩ := hlocal
    exact ⟨gs,hgs,hlen,queryCount_reflectionCompile _,gateCount_reflectionCompile _,hr⟩

end Qatlib.Concepts.GateTables.GrayUniversal
