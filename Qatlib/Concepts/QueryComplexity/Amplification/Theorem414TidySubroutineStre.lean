/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Amplification.Theorem414TidySubroutineStat
import Qatlib.Concepts.QueryComplexity.Amplification.Theorem413MajorityVoteAmpStre
import Qatlib.Concepts.QueryComplexity.Amplification.SubroutineCleaning
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Tidy subroutine amplification theorem

This module proves `theorem4_14TidySubroutine` by amplifying a circuit with zero queries,
copying the majority answer, and reversing the amplified computation. The squared success
identity yields probability at least 1 − ε of recovering the original input copies with the
desired answer, within the stated gate budget, as in the cleaning argument of [BennettEtAl1997].

## Main statements

* `theorem4_14TidySubroutine`: construct a unitary circuit with zero queries that restores its
  inputs with the correct answer.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.CircuitReversal.ReversalAlgebra
open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.QueryComplexity.Amplification

open Matrix

open scoped Classical

/-- The identity matrix is unitary. -/
private theorem one_mem_unitaryGroup' {I : Type} [Fintype I] [DecidableEq I] :
    (1 : Matrix I I ℂ) ∈ Matrix.unitaryGroup I ℂ := by
  refine Matrix.mem_unitaryGroup_iff'.mpr ?_
  simp

/-- A unitary circuit with zero queries and success probability at least 2/3 can achieve
probability at least 1 − ε of restoring all input copies and producing the desired answer
bit, using at most twice the repeated circuit's gate count plus one. This proves the finite
circuit cleaning statement associated with [Bennett et al., Theorem 4.14][BennettEtAl1997]. -/
theorem theorem4_14TidySubroutine : Theorem4_14TidySubroutine := by
  intro I _ _ C x₀ v b ε hC hC0 hb hε

  obtain ⟨r, C₁, hC₁u, hC₁q, hC₁g, hmass₁⟩ :=
    theorem4_13MajorityVoteAmplification C x₀ v b (ε / 2) hC hC0 hb (by linarith)
  refine ⟨r, LiftCircuit C₁ ++ [Step.gate
      (AnswerCopyGate (fun ω : Fin (2 * r + 1) → I => MajorityBit (fun j => v (ω j))))]
      ++ LiftCircuit (ReverseCircuit C₁), ?_, ?_, ?_, ?_⟩
  · refine (isUnitaryCircuit_append _ _).mpr ⟨?_, (isUnitaryCircuit_reverseCircuit hC₁u).lift⟩
    exact (isUnitaryCircuit_append _ _).mpr ⟨hC₁u.lift,
      (isUnitaryCircuit_gate _ _).mpr ⟨answerCopyGate_unitary _, isUnitaryCircuit_nil⟩⟩
  · rw [queryCount_append, queryCount_append, queryCount_liftCircuit,
      queryCount_liftCircuit, queryCount_reverseCircuit, hC₁q]
    norm_num
  · rw [gateCount_append, gateCount_append, gateCount_liftCircuit,
      gateCount_liftCircuit, gateCount_reverseCircuit, hC₁g]
    simp only [GateCount]
    omega
  · have hclean := subroutine_cleaning_mass (1 : Matrix (Fin (2 * r + 1) → I)
        (Fin (2 * r + 1) → I) ℂ) one_mem_unitaryGroup' (by simp [Matrix.conjTranspose_one])
      C₁ hC₁u (fun _ => x₀) (fun ω => MajorityBit (fun j => v (ω j))) b
    have hbigq : QueryCount (LiftCircuit C₁ ++ [Step.gate
          (AnswerCopyGate (fun ω : Fin (2 * r + 1) → I =>
            MajorityBit (fun j => v (ω j))))]
          ++ LiftCircuit (ReverseCircuit C₁)) = 0 := by
      rw [queryCount_append, queryCount_append, queryCount_liftCircuit,
        queryCount_liftCircuit, queryCount_reverseCircuit, hC₁q]
      norm_num
    have hrunEq : Run 1 (LiftCircuit C₁ ++ [Step.gate
          (AnswerCopyGate (fun ω : Fin (2 * r + 1) → I =>
            MajorityBit (fun j => v (ω j))))]
          ++ LiftCircuit (ReverseCircuit C₁)) (Ket (fun _ => x₀, false))
        = Run (LiftGate (1 : Matrix (Fin (2 * r + 1) → I)
            (Fin (2 * r + 1) → I) ℂ)) (LiftCircuit C₁ ++ [Step.gate
              (AnswerCopyGate (fun ω : Fin (2 * r + 1) → I =>
                MajorityBit (fun j => v (ω j))))]
              ++ LiftCircuit (ReverseCircuit C₁)) (Ket (fun _ => x₀, false)) :=
      (run_eq_of_queryCount_eq_zero (LiftGate (1 : Matrix (Fin (2 * r + 1) → I)
        (Fin (2 * r + 1) → I) ℂ)) 1 _ hbigq _).symm
    have hsingle : MeasureProb (Run 1 (LiftCircuit C₁ ++ [Step.gate
          (AnswerCopyGate (fun ω : Fin (2 * r + 1) → I =>
            MajorityBit (fun j => v (ω j))))]
          ++ LiftCircuit (ReverseCircuit C₁)) (Ket (fun _ => x₀, false)))
          {(fun _ => x₀, b)}
        = BornProb (Run (LiftGate (1 : Matrix (Fin (2 * r + 1) → I)
            (Fin (2 * r + 1) → I) ℂ)) (LiftCircuit C₁ ++ [Step.gate
              (AnswerCopyGate (fun ω : Fin (2 * r + 1) → I =>
                MajorityBit (fun j => v (ω j))))]
              ++ LiftCircuit (ReverseCircuit C₁)) (Ket (fun _ => x₀, false)))
          (fun _ => x₀, b) := by
      unfold MeasureProb
      rw [Finset.sum_singleton, hrunEq]
    rw [hsingle, hclean]
    have hm : (1 : ℝ) - ε / 2
        ≤ MeasureProb (Run 1 C₁ (Ket (fun _ => x₀)))
          (Finset.univ.filter fun ω => MajorityBit (fun j => v (ω j)) = b) := hmass₁
    nlinarith [sq_nonneg (ε / 2)]

end Qatlib.Concepts.QueryComplexity.Amplification
