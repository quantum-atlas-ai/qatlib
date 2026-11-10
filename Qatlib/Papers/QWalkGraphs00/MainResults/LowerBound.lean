/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkGraphs00.MainResults.Core
import Qatlib.Papers.QWalkGraphs00.MainResults.Times
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkGraphs00.MainResults.LowerBound

open scoped BigOperators Matrix Topology
open Filter
open Qatlib.Papers.QWalkGraphs00.MainResults.Core
open Qatlib.Papers.QWalkGraphs00.MainResults.Times

variable {Coin V : Type*} [Fintype Coin] [Fintype V] [DecidableEq Coin] [DecidableEq V]

def degree (Adj : V → V → ℕ) (v : V) : ℕ := ∑ u, Adj v u

def complement (X : Finset V) : Finset V := Finset.univ.filter (fun u => u ∉ X)

def cutFlow (Adj : V → V → ℕ) (X : Finset V) : ℝ :=
  ∑ v ∈ X, ∑ u ∈ complement X, (Adj v u : ℝ)

def cutCapacity (Adj : V → V → ℕ) (X : Finset V) : ℝ :=
  ∑ v ∈ X, (degree Adj v : ℝ)

def cutConductance (Adj : V → V → ℕ) (X : Finset V) : ℝ :=
  cutFlow Adj X / cutCapacity Adj X

def boundary (Adj : V → V → ℕ) (X : Finset V) : Finset V :=
  Finset.univ.filter (fun u => u ∉ X ∧ ∃ v ∈ X, Adj v u ≠ 0)

def cutBoundaryRatio (Adj : V → V → ℕ) (X : Finset V) : ℝ :=
  ((boundary Adj X).card : ℝ) / (X.card : ℝ)

def cuts (V : Type*) [Fintype V] [DecidableEq V] : Finset (Finset V) :=
  Finset.univ.powerset.filter (fun X => X.Nonempty ∧ 2 * X.card ≤ Fintype.card V)

def conductance (Adj : V → V → ℕ) (hs : (cuts V).Nonempty) : ℝ :=
  (cuts V).inf' hs (fun X => cutConductance Adj X)

def phiPrime (Adj : V → V → ℕ) (hs : (cuts V).Nonempty) : ℝ :=
  (cuts V).inf' hs (fun X => cutBoundaryRatio Adj X)

lemma boundary_card_le_cutFlow (Adj : V → V → ℕ)
    (hsimple : ∀ v u, Adj v u = 0 ∨ Adj v u = 1) (X : Finset V) :
    ((boundary Adj X).card : ℝ) ≤ cutFlow Adj X := by
  have hstep : ∀ u ∈ boundary Adj X, (1 : ℝ) ≤ ∑ v ∈ X, (Adj v u : ℝ) := by
    intro u hu
    have hu' : u ∉ X ∧ ∃ v ∈ X, Adj v u ≠ 0 := by
      simpa [boundary] using hu
    obtain ⟨-, v, hvX, hvne⟩ := hu'
    have hv1 : Adj v u = 1 := by
      rcases hsimple v u with h | h
      · exact absurd h hvne
      · exact h
    have hle : (Adj v u : ℝ) ≤ ∑ w ∈ X, (Adj w u : ℝ) :=
      Finset.single_le_sum (f := fun w => (Adj w u : ℝ)) (fun w _ => by positivity) hvX
    simpa [hv1] using hle
  calc ((boundary Adj X).card : ℝ)
      = ∑ _u ∈ boundary Adj X, (1 : ℝ) := by simp
    _ ≤ ∑ u ∈ boundary Adj X, ∑ v ∈ X, (Adj v u : ℝ) := Finset.sum_le_sum hstep
    _ = ∑ v ∈ X, ∑ u ∈ boundary Adj X, (Adj v u : ℝ) := Finset.sum_comm
    _ ≤ ∑ v ∈ X, ∑ u ∈ complement X, (Adj v u : ℝ) := by
        refine Finset.sum_le_sum (fun v _ => Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
        · intro u hu
          simp only [boundary, complement, Finset.mem_filter, Finset.mem_univ, true_and]
            at hu ⊢
          exact hu.1
        · intro u _ _
          positivity
    _ = cutFlow Adj X := rfl

omit [DecidableEq V] in

lemma cutCapacity_le_card_mul_degree (Adj : V → V → ℕ) (d : ℕ)
    (hmax : ∀ v, degree Adj v ≤ d) (X : Finset V) :
    cutCapacity Adj X ≤ (X.card : ℝ) * (d : ℝ) := by
  calc cutCapacity Adj X = ∑ v ∈ X, (degree Adj v : ℝ) := rfl
    _ ≤ ∑ _v ∈ X, (d : ℝ) := by
        refine Finset.sum_le_sum (fun v _ => ?_)
        exact_mod_cast hmax v
    _ = (X.card : ℝ) * (d : ℝ) := by simp [Finset.sum_const, nsmul_eq_mul]

lemma cutBoundaryRatio_le_cutConductance (Adj : V → V → ℕ) (d : ℕ)
    (hmax : ∀ v, degree Adj v ≤ d) (hdeg : ∀ v, 0 < degree Adj v) (hd : 0 < d)
    (hsimple : ∀ v u, Adj v u = 0 ∨ Adj v u = 1) {X : Finset V} (hX : X ∈ cuts V) :
    cutBoundaryRatio Adj X ≤ (d : ℝ) * cutConductance Adj X := by
  have hX' : X.Nonempty ∧ 2 * X.card ≤ Fintype.card V := by
    simpa [cuts] using hX
  obtain ⟨hne, -⟩ := hX'
  have hxpos : (0 : ℝ) < (X.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hCpos : 0 < cutCapacity Adj X := by
    unfold cutCapacity
    refine Finset.sum_pos (fun v _ => ?_) hne
    exact_mod_cast hdeg v
  have hbF := boundary_card_le_cutFlow Adj hsimple X
  have hCd := cutCapacity_le_card_mul_degree Adj d hmax X
  have hb0 : (0 : ℝ) ≤ ((boundary Adj X).card : ℝ) := by positivity
  have hxd : (0 : ℝ) ≤ (X.card : ℝ) * (d : ℝ) := by positivity
  have hmain : ((boundary Adj X).card : ℝ) * cutCapacity Adj X
      ≤ (d : ℝ) * cutFlow Adj X * (X.card : ℝ) := by
    calc ((boundary Adj X).card : ℝ) * cutCapacity Adj X
        ≤ ((boundary Adj X).card : ℝ) * ((X.card : ℝ) * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hCd hb0
      _ ≤ cutFlow Adj X * ((X.card : ℝ) * (d : ℝ)) :=
          mul_le_mul_of_nonneg_right hbF hxd
      _ = (d : ℝ) * cutFlow Adj X * (X.card : ℝ) := by ring
  unfold cutBoundaryRatio cutConductance
  rw [← mul_div_assoc, div_le_div_iff₀ hxpos hCpos]
  exact hmain

lemma inf'_mul_const {β : Type*} (s : Finset β) (hs : s.Nonempty) (f : β → ℝ)
    {c : ℝ} (hc : 0 < c) : s.inf' hs (fun b => c * f b) = c * s.inf' hs f := by
  refine le_antisymm ?_ ?_
  · have h : c⁻¹ * s.inf' hs (fun b => c * f b) ≤ s.inf' hs f := by
      refine Finset.le_inf' hs f (fun b hb => ?_)
      have h1 : s.inf' hs (fun b => c * f b) ≤ c * f b :=
        Finset.inf'_le (fun b => c * f b) hb
      calc c⁻¹ * s.inf' hs (fun b => c * f b) ≤ c⁻¹ * (c * f b) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hc))
        _ = f b := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]
    calc s.inf' hs (fun b => c * f b) = c * (c⁻¹ * s.inf' hs (fun b => c * f b)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
      _ ≤ c * s.inf' hs f := mul_le_mul_of_nonneg_left h (le_of_lt hc)
  · refine Finset.le_inf' hs (fun b => c * f b) (fun b hb => ?_)
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le f hb) (le_of_lt hc)

theorem lemma_7_3 (Adj : V → V → ℕ) (d : ℕ) (hs : (cuts V).Nonempty)
    (hmax : ∀ v, degree Adj v ≤ d) (hdeg : ∀ v, 0 < degree Adj v) (hd : 0 < d)
    (hsimple : ∀ v u, Adj v u = 0 ∨ Adj v u = 1) :
    phiPrime Adj hs ≤ (d : ℝ) * conductance Adj hs := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have key : ∀ X ∈ cuts V, phiPrime Adj hs ≤ (d : ℝ) * cutConductance Adj X := by
    intro X hX
    have h1 : phiPrime Adj hs ≤ cutBoundaryRatio Adj X :=
      Finset.inf'_le (s := cuts V) (f := fun Y => cutBoundaryRatio Adj Y) hX
    have h2 : cutBoundaryRatio Adj X ≤ (d : ℝ) * cutConductance Adj X :=
      cutBoundaryRatio_le_cutConductance Adj d hmax hdeg hd hsimple hX
    linarith
  calc phiPrime Adj hs
      ≤ (cuts V).inf' hs (fun X => (d : ℝ) * cutConductance Adj X) :=
        Finset.le_inf' hs (fun X => (d : ℝ) * cutConductance Adj X) key
    _ = (d : ℝ) * (cuts V).inf' hs (fun X => cutConductance Adj X) :=
        inf'_mul_const (cuts V) hs (fun X => cutConductance Adj X) hd0
    _ = (d : ℝ) * conductance Adj hs := rfl

end Qatlib.Papers.QWalkGraphs00.MainResults.LowerBound
