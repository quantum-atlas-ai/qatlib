/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.Defs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

def coord {n : ℕ} (j : Fin n) : BoolVec n →ₗ[ZMod 2] ZMod 2 where
  toFun := fun x => x j
  map_add' := by intro x y; rfl
  map_smul' := by intro c x; rfl

def sliceSub {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n)) (j : Fin n) :
    Submodule (ZMod 2) (BoolVec n) :=
  H ⊓ LinearMap.ker (coord j)

lemma mem_sliceSub {n : ℕ} {H : Submodule (ZMod 2) (BoolVec n)} {j : Fin n}
    {x : BoolVec n} : x ∈ sliceSub H j ↔ x ∈ H ∧ x j = 0 := Iff.rfl

abbrev StateSpace (n r : ℕ) : Type := BoolVec n × (Fin r → ZMod 2) → ℂ

def normFactor {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n)) : ℂ :=
  ((Real.sqrt (Nat.card S : ℝ) : ℂ))⁻¹

noncomputable def phiState {n : ℕ} (S : Submodule (ZMod 2) (BoolVec n)) (g : BoolVec n) :
    BoolVec n → ℂ := by
  classical
  exact fun x => if x ∈ S then normFactor S * charPair (m := fun _ => 2) g x else 0

def zeroBits (r : ℕ) : Fin r → ZMod 2 := fun _ => 0

theorem lemma6_decomposition {n : ℕ} (H : Submodule (ZMod 2) (BoolVec n))
    (y : BoolVec n) (hyH : y ∈ H) (j : Fin n) (hyj : y j = 1) :
    ∀ h ∈ H, h = (h j) • y + (h - (h j) • y) ∧ h - (h j) • y ∈ sliceSub H j := by
  intro h hh
  refine ⟨by abel, ?_⟩
  refine mem_sliceSub.mpr ⟨H.sub_mem hh (H.smul_mem _ hyH), ?_⟩
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hyj, mul_one, sub_self]

theorem lemma7_direct_sum {n m : ℕ} (H : Submodule (ZMod 2) (BoolVec n))
    (Y : Fin m → BoolVec n) (_hY : LinIndep Y) (hYH : ∀ i, Y i ∈ H) :
    ∃ K : Submodule (ZMod 2) (BoolVec n),
      K ≤ H ∧
      K ⊓ Submodule.span (ZMod 2) (Set.range Y) = ⊥ ∧
      K ⊔ Submodule.span (ZMod 2) (Set.range Y) = H := by
  classical
  let W : Submodule (ZMod 2) (BoolVec n) := Submodule.span (ZMod 2) (Set.range Y)
  have hWH : W ≤ H := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hYH i
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl W
  refine ⟨H ⊓ Q, inf_le_left, ?_, ?_⟩
  · rw [inf_assoc, inf_comm Q W, hQ.inf_eq_bot, inf_bot_eq]
  · have hsup : W ⊔ Q = ⊤ := hQ.sup_eq_top
    refine le_antisymm (sup_le inf_le_left hWH) ?_
    intro h hh
    have htop : h ∈ W ⊔ Q := by rw [hsup]; exact Submodule.mem_top
    rw [Submodule.mem_sup] at htop
    obtain ⟨w, hw, q, hq, hwq⟩ := htop
    have hqH : q ∈ H := by
      have : q = h - w := by rw [← hwq]; abel
      rw [this]
      exact H.sub_mem hh (hWH hw)
    have hqK : q ∈ H ⊓ Q := ⟨hqH, hq⟩
    rw [Submodule.mem_sup]
    exact ⟨q, hqK, w, hw, by rw [add_comm, hwq]⟩

end Qatlib.Papers.ExactSimon97.MainResults
