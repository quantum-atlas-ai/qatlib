/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.Phi3Universal.ImplementationMachineDefs
import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffective
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.Phi3Universal

open Matrix
open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis
open Qatlib.Concepts.CircuitImpl.GateSynthesis
open scoped Classical BigOperators ENNReal

theorem clause13_clock_window {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) :
    MachineClock k = k ∧
      windowAcceptance m k qf a
        = ((qtmTransition m) ^ k) (m.start, m.blank) (qf, a) := by
  exact ⟨rfl, rfl⟩

theorem clause13_work_tape_copy {N : ℕ} {base inW work : ℕ}
    (hin : inW < N) (hwork : work < N) (hne : inW ≠ work) (x : Reg N) :
    Run (1 : Matrix (Reg N) (Reg N) ℂ) (finiteCodeCircuit N (opsGates (copyProgram inW work)))
        (Ket x) =
      Ket (liveRun base (copyProgram inW work) ⟨x, List.range base⟩).bits :=
  clause11_copy_program_quantum hin hwork hne x

theorem clause13_paid_reverse_restores (n : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg n))
    (hg : finiteWordLegal n gs = true) :
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (finiteCodeCircuit n (reverseWord gs)) ψ = ψ := by
  obtain ⟨_, _, hstate, _⟩ := finite_gate_word_paid_adjoint_semantics n gs ψ hg
  exact hstate

theorem clause13_paid_reverse_cost (n : ℕ) (gs : List FiniteGateCode) (ψ : QState (Reg n))
    (hg : finiteWordLegal n gs = true) :
    GateCount (finiteCodeCircuit n (reverseWord gs)) = 2 * gs.length := by
  obtain ⟨_, _, _, hcount⟩ := finite_gate_word_paid_adjoint_semantics n gs ψ hg
  exact hcount

theorem clause13_five_round_ledger (c : ℕ) :
    fiveRoundCost c = 7 * c ∧ 7 * c ≤ 2 * (5 * c) := by
  simp only [fiveRoundCost]
  omega

end Qatlib.Concepts.CircuitImpl.Phi3Universal

end
