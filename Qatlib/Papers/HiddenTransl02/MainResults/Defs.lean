/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Field.ZMod

namespace Qatlib.Papers.HiddenTransl02.MainResults.Defs

open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Classical

set_option autoImplicit false

structure QAlg (Reg Inst Out : Type*) [Fintype Reg] [DecidableEq Reg] where

  circuit : Circuit Reg

  out : Inst → Out

  failProb : Inst → ℝ

  qcost : ℕ

  tcost : ℕ

  qcost_eq : qcost = QueryCount circuit

  tcost_eq : tcost = GateCount circuit

def dot {p n : ℕ} (y u : Fin n → ZMod p) : ZMod p :=
  ∑ i, y i * u i

def IsTranslation {p n : ℕ} {S : Type*} (f : (Fin n → ZMod p) × Bool → S)
    (u : Fin n → ZMod p) : Prop :=
  ∀ x, f (x, false) = f (x + u, true)

def IsOmega (t : ℕ) (a : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c * a ≤ (t : ℝ)

noncomputable def uniformState {I : Type*} [DecidableEq I] (S : Finset I) : I → ℂ :=
  fun i => if i ∈ S then (((Real.sqrt (S.card : ℝ) : ℝ)) : ℂ)⁻¹ else 0

def IsSubgroupSet {G : Type*} [Group G] (S : Finset G) : Prop :=
  1 ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, a⁻¹ ∈ S)

def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, ∀ m, f m ≤ (m + 1) ^ c

def PolyP (n p t : ℕ) : Prop :=
  ∃ c : ℕ, t ≤ (n + p) ^ (c * p)

def PolyEll (ℓ t : ℕ) : Prop :=
  ∃ c : ℕ, t ≤ (ℓ + 1) ^ c

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section

variable {Reg Inst Out : Type*}

section Events

variable [Fintype Reg] [DecidableEq Reg]

def outcomeProb (ψ : QState Reg) (S : Finset Reg) : ℝ := MeasureProb ψ S

theorem outcomeProb_nonneg (ψ : QState Reg) (S : Finset Reg) :
    0 ≤ outcomeProb ψ S := measureProb_nonneg ψ S

theorem outcomeProb_mono {ψ : QState Reg} {S T : Finset Reg} (hST : S ⊆ T) :
    outcomeProb ψ S ≤ outcomeProb ψ T := by
  unfold outcomeProb MeasureProb
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun i _ _ => bornProb_nonneg ψ i)

theorem outcomeProb_univ {ψ : QState Reg} (hψ : Normalized ψ) :
    outcomeProb ψ Finset.univ = 1 :=
  measureProb_univ hψ

theorem outcomeProb_le_one {ψ : QState Reg} (hψ : Normalized ψ) (S : Finset Reg) :
    outcomeProb ψ S ≤ 1 := by
  rw [← outcomeProb_univ hψ]
  exact outcomeProb_mono (Finset.subset_univ S)

theorem outcomeProb_union_le (ψ : QState Reg) (S T : Finset Reg) :
    outcomeProb ψ (S ∪ T) ≤ outcomeProb ψ S + outcomeProb ψ T := by
  unfold outcomeProb MeasureProb
  rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  have h : ∑ i ∈ T \ S, BornProb ψ i ≤ ∑ i ∈ T, BornProb ψ i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _ => bornProb_nonneg ψ i)
  linarith

theorem outcomeProb_add_compl (ψ : QState Reg) (S : Finset Reg) :
    outcomeProb ψ S + outcomeProb ψ (Finset.univ \ S) = outcomeProb ψ Finset.univ := by
  unfold outcomeProb MeasureProb
  rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union]
  rw [show S ∪ (Finset.univ : Finset Reg) = Finset.univ by ext i; simp]

end Events

section CircuitEvents

variable [Fintype Reg] [DecidableEq Reg]

def circuitOutcomeProb (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S : Finset Reg) : ℝ :=
  outcomeProb (Run oracle C init) S

theorem circuitOutcomeProb_nonneg (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S : Finset Reg) : 0 ≤ circuitOutcomeProb oracle C init S :=
  outcomeProb_nonneg _ _

theorem circuitOutcomeProb_le_one (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S : Finset Reg)
    (hψ : Normalized (Run oracle C init)) :
    circuitOutcomeProb oracle C init S ≤ 1 :=
  outcomeProb_le_one hψ S

theorem circuitOutcomeProb_le_one_of_unitary (oracle : Matrix Reg Reg ℂ)
    (C : Circuit Reg) (init : QState Reg) (S : Finset Reg)
    (horacle : oracle ∈ Matrix.unitaryGroup Reg ℂ) (hC : IsUnitaryCircuit C)
    (hinit : Normalized init) :
    circuitOutcomeProb oracle C init S ≤ 1 :=
  circuitOutcomeProb_le_one _ _ _ _ (IsUnitaryCircuit.normalized_run hC horacle hinit)

theorem circuitOutcomeProb_union_le (oracle : Matrix Reg Reg ℂ) (C : Circuit Reg)
    (init : QState Reg) (S T : Finset Reg) :
    circuitOutcomeProb oracle C init (S ∪ T) ≤
      circuitOutcomeProb oracle C init S + circuitOutcomeProb oracle C init T :=
  outcomeProb_union_le _ _ _

theorem circuitOutcomeProb_append (oracle : Matrix Reg Reg ℂ) (C D : Circuit Reg)
    (init : QState Reg) (S : Finset Reg) :
    circuitOutcomeProb oracle (C ++ D) init S =
      circuitOutcomeProb oracle D (Run oracle C init) S := by
  unfold circuitOutcomeProb
  rw [run_append]

end CircuitEvents

section Faithful

variable [Fintype Reg] [DecidableEq Reg] [DecidableEq Out]

def badOutcomes (decode : Reg → Out) (answer : Out) : Finset Reg :=
  Finset.univ.filter fun i => decode i ≠ answer

def goodOutcomes (decode : Reg → Out) (answer : Out) : Finset Reg :=
  Finset.univ.filter fun i => decode i = answer

theorem badOutcomes_eq_sdiff (decode : Reg → Out) (answer : Out) :
    badOutcomes decode answer = Finset.univ \ goodOutcomes decode answer := by
  unfold badOutcomes goodOutcomes
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]

structure MeasQAlg (Reg Inst Out : Type*) [Fintype Reg] [DecidableEq Reg]
    [DecidableEq Out] extends QAlg Reg Inst Out where

  oracle : Inst → Matrix Reg Reg ℂ

  init : QState Reg

  decode : Reg → Out

  failProb_eq : ∀ inst : Inst,
    failProb inst = circuitOutcomeProb (oracle inst) circuit init
      (badOutcomes decode (out inst))

def MeasQAlg.successProb (A : MeasQAlg Reg Inst Out) (inst : Inst) : ℝ :=
  circuitOutcomeProb (A.oracle inst) A.circuit A.init
    (goodOutcomes A.decode (A.out inst))

theorem MeasQAlg.failProb_nonneg (A : MeasQAlg Reg Inst Out) (inst : Inst) :
    0 ≤ A.failProb inst := by
  rw [A.failProb_eq inst]
  exact circuitOutcomeProb_nonneg _ _ _ _

theorem MeasQAlg.failProb_le_one (A : MeasQAlg Reg Inst Out) (inst : Inst)
    (hinit : Normalized A.init)
    (horacle : A.oracle inst ∈ Matrix.unitaryGroup Reg ℂ)
    (hC : IsUnitaryCircuit A.circuit) :
    A.failProb inst ≤ 1 := by
  rw [A.failProb_eq inst]
  exact circuitOutcomeProb_le_one_of_unitary _ _ _ _ horacle hC hinit

theorem MeasQAlg.successProb_eq_one_sub_failProb (A : MeasQAlg Reg Inst Out)
    (inst : Inst) (hinit : Normalized A.init)
    (horacle : A.oracle inst ∈ Matrix.unitaryGroup Reg ℂ)
    (hC : IsUnitaryCircuit A.circuit) :
    A.successProb inst = 1 - A.failProb inst := by
  have hnorm : Normalized (Run (A.oracle inst) A.circuit A.init) :=
    IsUnitaryCircuit.normalized_run hC horacle hinit
  have hpart := outcomeProb_add_compl (Run (A.oracle inst) A.circuit A.init)
    (goodOutcomes A.decode (A.out inst))
  rw [outcomeProb_univ hnorm] at hpart
  have hbad : A.failProb inst =
      circuitOutcomeProb (A.oracle inst) A.circuit A.init
        (Finset.univ \ goodOutcomes A.decode (A.out inst)) := by
    rw [A.failProb_eq inst, badOutcomes_eq_sdiff]
  unfold MeasQAlg.successProb
  rw [hbad]
  unfold circuitOutcomeProb
  linarith

end Faithful

section Identity

variable [Fintype Reg] [DecidableEq Reg] [Inhabited Reg]

def identityQAlg (Inst : Type*) : MeasQAlg Reg Inst Unit where
  circuit := []
  out := fun _ => ()
  failProb := fun _ => 0
  qcost := 0
  tcost := 0
  qcost_eq := rfl
  tcost_eq := rfl
  oracle := fun _ => 1
  init := Ket (default : Reg)
  decode := fun _ => ()
  failProb_eq := by
    intro inst
    have hbad : badOutcomes (fun _ : Reg => ()) () = ∅ := by
      unfold badOutcomes
      rw [Finset.filter_false_of_mem]
      simp
    rw [hbad]
    unfold circuitOutcomeProb outcomeProb
    simp [MeasureProb, Run]

theorem identityQAlg_successProb (Inst : Type*) (inst : Inst) :
    (identityQAlg (Reg := Reg) Inst).successProb inst = 1 := by
  have hgood : goodOutcomes (fun _ : Reg => ()) () = Finset.univ := by
    unfold goodOutcomes
    rw [Finset.filter_true_of_mem]
    simp
  unfold MeasQAlg.successProb
  rw [hgood]
  unfold circuitOutcomeProb outcomeProb
  have hrun : Run ((identityQAlg (Reg := Reg) Inst).oracle inst)
      (identityQAlg (Reg := Reg) Inst).circuit
      (identityQAlg (Reg := Reg) Inst).init = Ket (default : Reg) := rfl
  rw [hrun]
  exact measureProb_univ (normalized_ket (default : Reg))

end Identity

end
end Qatlib.Papers.HiddenTransl02.MainResults.Defs
