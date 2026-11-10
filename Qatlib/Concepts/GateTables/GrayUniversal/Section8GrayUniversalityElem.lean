/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateTables.GrayUniversal.Section8GrayUniversalityStat
import Qatlib.Concepts.GateTables.GrayUniversal.Section8GrayTwoLevelElem
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.GateTables.GrayUniversal
open Matrix
open scoped Classical BigOperators

theorem section8GrayUniversality : Section8GrayUniversality := by
  intro n hn U hU
  let C := (2*n-1)*(256*n^2+2*n-2)
  obtain ⟨ts,hts,hlen,hprog⟩ := known_unitary_two_level_factorization (Reg n) U hU
  have hcount : ts.length ≤ 2^(n-1)*(2^n+1) := by
    have hc : Fintype.card (Reg n) = 2^n := by simp [Reg]
    rw [hc] at hlen
    have hp : 2^n = 2^(n-1)*2 := by
      conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
    have he : 2^n*(2^n+1)/2 = 2^(n-1)*(2^n+1) := by
      calc
        _ = (2^(n-1)*(2^n+1)*2)/2 := by congr 1; rw [hp]; ring
        _ = _ := Nat.mul_div_cancel _ (by decide : 0 < 2)
    exact hlen.trans_eq he
  obtain ⟨gs,hgs,hglen,hr⟩ := noWork_program_table_of_instruction_tables n C ts hts (by
    intro g _ hg
    obtain ⟨as,has,halen,_,_,ha⟩ := section8GrayTwoLevel n hn g hg
    exact ⟨as,has,halen,ha⟩)
  refine ⟨gs,hgs,?_,queryCount_reflectionCompile _,gateCount_reflectionCompile _,?_⟩
  · exact hglen.trans ((Nat.mul_le_mul_left C hcount).trans_eq (Nat.mul_comm _ _))
  · intro ψ
    rw [hr,hprog]

end Qatlib.Concepts.GateTables.GrayUniversal
