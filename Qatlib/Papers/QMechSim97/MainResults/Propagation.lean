/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalSynthesis
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.QMechSim97.MainResults.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMechSim97.MainResults.Propagation
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open scoped Classical BigOperators

private theorem swapFactorsAux_length {N : ℕ} (l : List (Fin N)) :
    ∀ (f : Equiv.Perm (Fin N)) (h : ∀ {x}, f x ≠ x → x ∈ l),
      (Equiv.Perm.swapFactorsAux l f h).val.length ≤ l.length := by
  induction l with
  | nil => intro f h; simp [Equiv.Perm.swapFactorsAux]
  | cons x l ih =>
    intro f h
    by_cases hx : x = f x
    · simp only [Equiv.Perm.swapFactorsAux, dif_pos hx]
      apply (ih f ?_).trans (Nat.le_succ _)
      intro y hy
      apply List.mem_of_ne_of_mem ?_ (h hy)
      intro hyx
      subst y
      exact hy hx.symm
    · simp only [Equiv.Perm.swapFactorsAux, dif_neg hx, List.length_cons]
      apply Nat.succ_le_succ (ih (Equiv.swap x (f x) * f) ?_)
      intro y hy
      have hs := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hy
      exact List.mem_of_ne_of_mem hs.2 (h hs.1)

private theorem compile_swap_factors {N : ℕ} (L : List (Equiv.Perm (Fin N)))
    (hL : ∀ g ∈ L, Equiv.Perm.IsSwap g) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧ gs.length ≤ 3 * L.length ∧
      ∀ x : Reg N, Run 1 (reflectionCompile gs) (Ket x) = Ket (x ∘ L.prod) := by
  induction L with
  | nil => exact ⟨[], by simp [reflectionLegal], by simp, by intro x; simp [reflectionCompile]⟩
  | cons g L ih =>
    obtain ⟨i,j,hij,rfl⟩ := hL g List.mem_cons_self
    obtain ⟨gs,hgs,hlen,hrun⟩ := ih (fun a ha => hL a (List.mem_cons_of_mem _ ha))
    obtain ⟨hs,hsl,hsrun⟩ := knownSwapSteps_spec i j
    refine ⟨knownSwapSteps i j ++ gs, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hs a h
      · exact hgs a h
    · simp only [List.length_append, List.length_cons]
      omega
    · intro x
      rw [reflectionCompile_append, run_append, hsrun, hrun]
      congr 1

private theorem run_sum_smul {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (C : Circuit I) (c : J → ℂ) (ψ : J → QState I) :
    Run 1 C (∑ j, c j • ψ j) = ∑ j, c j • Run 1 C (ψ j) := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [run_gate, run_query, ApplyGate, Matrix.mulVec_sum,
      Matrix.mulVec_smul, ih]

theorem permutation_propagation_word {N : ℕ} (f : Equiv.Perm (Fin N)) :
    ∃ gs : List (ReflectionGate N), reflectionLegal gs ∧
      IsUnitaryCircuit (reflectionCompile gs) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) ≤ 3 * N ∧
      ∀ ψ : QState (Reg N), Run 1 (reflectionCompile gs) ψ =
        ∑ x : Reg N, ψ x • Ket (x ∘ f) := by
  let F := Equiv.Perm.swapFactors f
  have hlen : F.val.length ≤ N := by
    have h := swapFactorsAux_length (Finset.univ.sort (· ≤ ·) : List (Fin N)) f
      (fun {_ _} => (Finset.mem_sort _).mpr (Finset.mem_univ _))
    simpa [F, Equiv.Perm.swapFactors] using! h
  obtain ⟨gs,hgs,hslen,hrun⟩ := compile_swap_factors F.val F.property.2
  obtain ⟨hU,hQ,hG⟩ := local_reflection_gate_support_unitarity_counts N gs hgs
  refine ⟨gs,hgs,hU,hQ,?_,?_⟩
  · rw [hG]
    exact hslen.trans (Nat.mul_le_mul_left _ hlen)
  · intro ψ
    conv_lhs => arg 3; rw [state_ket_expansion ψ]
    rw [run_sum_smul]
    apply Finset.sum_congr rfl
    intro x _
    rw [hrun, F.property.1]

def occupation {N : ℕ} (x : Reg N) : ℕ := Fintype.card {i : Fin N // x i = true}

theorem propagation_occupation {N : ℕ} (f : Equiv.Perm (Fin N)) (x : Reg N) :
    occupation (x ∘ f) = occupation x :=
  Fintype.card_congr (Equiv.subtypeEquivOfSubtype (p := fun i => x i = true) f)

abbrev Site (d l : ℕ) := Fin d → ZMod l

abbrev LatticeWire (d l : ℕ) := Site d l × (Fin d × Bool)

def velocity (d l : ℕ) (v : Fin d × Bool) : Site d l :=
  fun j => if j = v.1 then if v.2 then 1 else -1 else 0

def latticeReadShift (d l : ℕ) : Equiv.Perm (LatticeWire d l) where
  toFun z := (z.1 - velocity d l z.2, z.2)
  invFun z := (z.1 + velocity d l z.2, z.2)
  left_inv z := by simp
  right_inv z := by simp

theorem latticeWire_card (d l : ℕ) [NeZero l] :
    Fintype.card (LatticeWire d l) = 2 * d * l ^ d := by
  simp [LatticeWire, Site, Fintype.card_prod, ZMod.card,
    mul_comm, mul_left_comm]

def latticeWireIndex (d l : ℕ) [NeZero l] :
    LatticeWire d l ≃ Fin (Defs.qubitCount d l) :=
  (Fintype.equivFin (LatticeWire d l)).trans
    (finCongr (latticeWire_card d l))

def latticePermutation (d l : ℕ) [NeZero l] :
    Equiv.Perm (Fin (Defs.qubitCount d l)) :=
  ((latticeWireIndex d l).symm.trans (latticeReadShift d l)).trans (latticeWireIndex d l)

theorem lattice_propagation_word (d l : ℕ) [NeZero l] :
    ∃ gs : List (ReflectionGate (Defs.qubitCount d l)),
      reflectionLegal gs ∧ IsUnitaryCircuit (reflectionCompile gs) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) ≤ 6 * d * l ^ d ∧
      ∀ ψ : QState (Reg (Defs.qubitCount d l)),
        Run 1 (reflectionCompile gs) ψ =
          ∑ x, ψ x • Ket (x ∘ latticePermutation d l) := by
  obtain ⟨gs,hL,hU,hQ,hG,hR⟩ := permutation_propagation_word (latticePermutation d l)
  refine ⟨gs,hL,hU,hQ,?_,hR⟩
  calc
    GateCount (reflectionCompile gs) ≤ 3 * Defs.qubitCount d l := hG
    _ = 6 * d * l ^ d := by unfold Defs.qubitCount; ring

theorem propagation_sector_from_semantics {N : ℕ} (f : Equiv.Perm (Fin N))
    (C : Circuit (Reg N))
    (hC : ∀ ψ : QState (Reg N), Run 1 C ψ = ∑ x, ψ x • Ket (x ∘ f))
    (n : ℕ) (ψ : QState (Reg N))
    (hψ : ∀ x, occupation x ≠ n → ψ x = 0) :
    ∀ y, occupation y ≠ n → Run 1 C ψ y = 0 := by
  intro y hy
  rw [hC]
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  by_cases he : y = x ∘ f
  · have hx : occupation x ≠ n := by
      rw [he, propagation_occupation] at hy
      exact hy
    simp [hψ x hx]
  · simp [Qatlib.Foundations.PureStateMath.Ket, he]

theorem lattice_propagation_number_sector (d l : ℕ) [NeZero l] :
    ∃ gs : List (ReflectionGate (Defs.qubitCount d l)),
      IsUnitaryCircuit (reflectionCompile gs) ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) ≤ 6 * d * l ^ d ∧
      ∀ (n : ℕ) (ψ : QState (Reg (Defs.qubitCount d l))),
        (∀ x, occupation x ≠ n → ψ x = 0) →
        ∀ y, occupation y ≠ n → Run 1 (reflectionCompile gs) ψ y = 0 := by
  obtain ⟨gs,_,hU,hQ,hG,hR⟩ := lattice_propagation_word d l
  exact ⟨gs,hU,hQ,hG,fun n ψ hψ =>
    propagation_sector_from_semantics (latticePermutation d l) _ hR n ψ hψ⟩

end Qatlib.Papers.QMechSim97.MainResults.Propagation
