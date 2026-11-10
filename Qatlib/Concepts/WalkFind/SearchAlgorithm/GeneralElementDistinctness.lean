/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.GeneralElementDistinctnessDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QuantumGibbs.FormAlgebra.GeneralWalkAccessDefs

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
namespace GeneralElementDistinctness

open Matrix
open Qatlib.Concepts.WalkFind.SearchAlgorithm.GeneralElementDistinctnessDefs
open Qatlib.Concepts.WalkSearch.MainResults.GeneralMnrsFindDefs
open scoped Classical BigOperators
set_option autoImplicit false

theorem compactEntries_slot_unique (e : compactEntries)
    (hwf : ∀ e₁ e₂, e₁ ∈ e → e₂ ∈ e → compactEntrySlot e₁ = compactEntrySlot e₂ → e₁ = e₂)
    (i : ℕ) : (e.filter (fun e' => compactEntrySlot e' = i)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  have hxf := Finset.mem_filter.mp hx
  have hyf := Finset.mem_filter.mp hy
  exact hwf x y hxf.1 hyf.1 (hxf.2.trans hyf.2.symm)

theorem elementDistinctness_uniform_program {V : ℕ} (K : GeneralKernel V)
    (p : GeneralVertex V) (S : Finset (GeneralVertex V)) (k : ℕ)
    (S' : Finset (GeneralVertex V)) (k' : ℕ)
    (hS : S = S') (hk : k = k') :
    generalFindDecoder S = generalFindDecoder S' ∧
      generalSetupWord K p k = generalSetupWord K p k' := by
  subst hS
  subst hk
  exact ⟨rfl, rfl⟩

theorem near_prime_power_reduction {k N p : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (h : primeInSqrtInterval k N p) :
    (N : ℝ) ≤ (p : ℝ) ^ 2 ∧
      (p : ℝ) ^ 2 ≤ (1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ) ∧
      nearPrimePower p 1 (p ^ 2) := by
  obtain ⟨hlo, hhi⟩ := h
  have hsqN : (Real.sqrt (N : ℝ)) ^ 2 = (N : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg N)
  have hk0 : (0 : ℕ) < k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hkpos : (0 : ℝ) < 2 * (k : ℝ) ^ 2 := by nlinarith [sq_pos_of_pos hkR]
  have hfrac : (0 : ℝ) < 1 / (2 * (k : ℝ) ^ 2) := div_pos (by norm_num) hkpos
  have hfac : (0 : ℝ) < 1 + 1 / (2 * (k : ℝ) ^ 2) := by nlinarith [hfrac]
  have hpos : (0 : ℝ) ≤ (1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ) := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    exact mul_nonneg hfac.le hN
  have hsqM : (Real.sqrt ((1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ))) ^ 2
      = (1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ) := Real.sq_sqrt hpos
  refine ⟨?_, ?_, ⟨hp, by omega, rfl⟩⟩
  · have hmul : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) ≤ (p : ℝ) * (p : ℝ) :=
      mul_le_mul hlo hlo (Real.sqrt_nonneg _) (Nat.cast_nonneg p)
    nlinarith [hmul, hsqN]
  · have hmul : (p : ℝ) * (p : ℝ)
        ≤ Real.sqrt ((1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ))
          * Real.sqrt ((1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ)) :=
      mul_le_mul hhi hhi (Nat.cast_nonneg p) (Real.sqrt_nonneg _)
    nlinarith [hmul, hsqM]

def elementDistinctnessResidual : List String :=
  [ "the full GeneralQueryMemoryContract with its C_k query and memory constants is not built here",
    "the full GeneralOptimizedQueriesContract with the N^(k/(k+1)) query bound is not built here",
    "the QRAMImplementationContract with nativeWidth, codeBits and precision budgets is not built here",
    "the EffectiveQRAMImplementationContract and the finite-bit-machine compiler bridge are not built here",
    "the unconditional prime-gap input for the near prime power is not available in the pinned dependency" ]

structure ElementDistinctnessAccount (V : ℕ) (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) : Prop where

  compactBound : ∀ e : compactEntries,
    (∀ e₁ e₂, e₁ ∈ e → e₂ ∈ e → compactEntrySlot e₁ = compactEntrySlot e₂ → e₁ = e₂) →
    ∀ i, (e.filter (fun e' => compactEntrySlot e' = i)).card ≤ 1

  uniformProgram : ∀ S' k', (S = S' → k = k' →
    generalFindDecoder S = generalFindDecoder S' ∧
      generalSetupWord K p k = generalSetupWord K p k')

  primePowerReduction : ∀ {k' N p'}, 2 ≤ k' → Nat.Prime p' →
    primeInSqrtInterval k' N p' →
    (N : ℝ) ≤ (p' : ℝ) ^ 2 ∧
      (p' : ℝ) ^ 2 ≤ (1 + 1 / (2 * (k' : ℝ) ^ 2)) * (N : ℝ) ∧
      nearPrimePower p' 1 (p' ^ 2)

theorem clause28_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    ElementDistinctnessAccount V K p S k := by
  refine ⟨?_, ?_, ?_⟩
  · intro e hwf i
    exact compactEntries_slot_unique e hwf i
  · intro S' k' hS hk
    exact elementDistinctness_uniform_program K p S k S' k' hS hk
  · intro k' N p' hk hp h
    exact near_prime_power_reduction hk hp h

theorem clause29_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    (∀ e : compactEntries,
      (∀ e₁ e₂, e₁ ∈ e → e₂ ∈ e → compactEntrySlot e₁ = compactEntrySlot e₂ → e₁ = e₂) →
      ∀ i, (e.filter (fun e' => compactEntrySlot e' = i)).card ≤ 1) ∧
      (∀ S' k', S = S' → k = k' →
        generalFindDecoder S = generalFindDecoder S' ∧
          generalSetupWord K p k = generalSetupWord K p k') := by
  exact ⟨fun e hwf i => compactEntries_slot_unique e hwf i,
    fun S' k' hS hk => elementDistinctness_uniform_program K p S k S' k' hS hk⟩

theorem clause30_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    ∀ S' k', S = S' → k = k' → generalSetupWord K p k = generalSetupWord K p k' := by
  intro S' k' hS hk
  exact (elementDistinctness_uniform_program K p S k S' k' hS hk).2

theorem clause31_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    ∀ S' k', S = S' → k = k' → generalFindDecoder S = generalFindDecoder S' := by
  intro S' k' hS hk
  exact (elementDistinctness_uniform_program K p S k S' k' hS hk).1

theorem clause32_complete {V : ℕ} (K : GeneralKernel V) (p : GeneralVertex V)
    (S : Finset (GeneralVertex V)) (k : ℕ) :
    ∀ e : compactEntries,
      (∀ e₁ e₂, e₁ ∈ e → e₂ ∈ e → compactEntrySlot e₁ = compactEntrySlot e₂ → e₁ = e₂) →
      ∀ i, (e.filter (fun e' => compactEntrySlot e' = i)).card ≤ 1 := by
  intro e hwf i
  exact compactEntries_slot_unique e hwf i

theorem clause33_complete {k N p : ℕ} (hk : 2 ≤ k) (hp : Nat.Prime p)
    (h : primeInSqrtInterval k N p) :
    (N : ℝ) ≤ (p : ℝ) ^ 2 ∧
      (p : ℝ) ^ 2 ≤ (1 + 1 / (2 * (k : ℝ) ^ 2)) * (N : ℝ) ∧
      nearPrimePower p 1 (p ^ 2) :=
  near_prime_power_reduction hk hp h

end GeneralElementDistinctness
end Qatlib.Concepts.WalkFind.SearchAlgorithm
