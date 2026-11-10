/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
import Mathlib.Data.Nat.Bitwise
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Matrix
open scoped Matrix.Norms.L2Operator

theorem effectiveNatBits_injective : Function.Injective effectiveNatBits := by
  intro n m h
  have hlen : n.bits.length=m.bits.length := by
    have hh := congrArg List.length h
    simp [effectiveNatBits] at hh
    omega
  have hb : n.bits=m.bits := by
    unfold effectiveNatBits at h
    rw [hlen] at h
    exact List.append_cancel_left h
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_eq_inth,Nat.testBit_eq_inth,hb]

theorem effectiveIntFields_injective : Function.Injective effectiveIntFields := by
  intro a b h
  cases a <;> cases b <;> simp_all [effectiveIntFields]

theorem effectiveStoppedRun_matrix (n : ℕ) (E : EffectiveEnvironment)
    (steps : List EffectiveStep) (ψ : QState (Reg n)) :
    (effectiveStoppedRun n E steps ψ).1 =
      ((steps.map (effectiveStepMatrix n E)).reverse.prod) *ᵥ ψ := by
  induction steps generalizing ψ with
  | nil => simp [effectiveStoppedRun]
  | cons s rest ih =>
    simp only [effectiveStoppedRun, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
    cases s <;> (try dsimp only) <;> rw [← Matrix.mulVec_mulVec] <;> exact ih _

theorem effectiveInstruction_partition (p : EffectiveProgram) :
    effectiveGates p + effectiveQueries p + effectivePostselects p = p.steps.length := by
  rcases p with ⟨n,l⟩
  unfold effectiveGates effectiveQueries effectivePostselects
  (try dsimp only)
  induction l with
  | nil => simp
  | cons s l ih => cases s <;> simp_all <;> omega

theorem effectiveFixedProgram_unitary (p : EffectiveProgram) (E : EffectiveEnvironment)
    (hleg : effectiveLegal p) (hcoh : effectiveCoherent p) (hq : effectiveQueries p=0) :
    effectiveMatrix p E ∈ Matrix.unitaryGroup (Reg p.width) ℂ := by
  have hs (s : EffectiveStep) (hm : s ∈ p.steps) :
      effectiveStepMatrix p.width E s ∈ Matrix.unitaryGroup (Reg p.width) ℂ := by
    have hl := hleg s hm
    cases s with
    | fixed g => exact finiteCodeMatrix_unitary p.width g hl
    | phase w a b axis =>
      have hw : w<p.width := hl
      simp only [effectiveStepMatrix,dif_pos hw]
      apply wireGate_unitary
      cases axis
      · exact rz_unitary _
      · exact (Matrix.unitaryGroup Bool ℂ).mul_mem
          ((Matrix.unitaryGroup Bool ℂ).mul_mem hadamard_unitary (rz_unitary _)) hadamard_unitary
    | query slot ws cs adj =>
      have he : p.steps.filter (fun s => match s with | .query .. => true | _ => false) = [] :=
        List.length_eq_zero_iff.mp hq
      have hh : EffectiveStep.query slot ws cs adj ∈
          p.steps.filter (fun s => match s with | .query .. => true | _ => false) := by
        simp [hm]
      rw [he] at hh
      exact (List.not_mem_nil hh).elim
    | postselect ws => exact (hcoh ws hm).elim
  unfold effectiveMatrix
  apply Submonoid.list_prod_mem
  intro A hA
  simp only [List.mem_reverse,List.mem_map] at hA
  obtain ⟨s,hm,rfl⟩ := hA
  exact hs s hm

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
