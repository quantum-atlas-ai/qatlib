/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace Qatlib.Foundations.FiniteCounts.SubsetIncidence

def incidentSupports (n r : ℕ) (a : Fin n) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun s=>a∈s)

theorem incidentSupports_card (n r : ℕ) (a : Fin n) (hr : 0 < r) :
    (incidentSupports n r a).card=Nat.choose (n-1) (r-1) := by
  have h := Finset.card_filter_powersetCard_subset ({a}:Finset (Fin n)) Finset.univ r
    (by simp) (by simpa using! hr)
  simpa [incidentSupports] using h

theorem incidentSupports_fraction (n r : ℕ) (a : Fin n) (hr : 0 < r) (hrn : r≤n) :
    ((incidentSupports n r a).card:ℝ)/(Nat.choose n r:ℝ)=(r:ℝ)/n := by
  have hn : 0 < n := by omega
  have hn' : 1≤n := hn
  have hr' : 1≤r := hr
  have he := Nat.add_one_mul_choose_eq (n-1) (r-1)
  simp only [Nat.sub_add_cancel hn',Nat.sub_add_cancel hr'] at he
  have hc : (Nat.choose n r:ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hrn).ne'
  have hnr : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  rw [incidentSupports_card n r a hr]
  have her : (n:ℝ)*(Nat.choose (n-1) (r-1):ℝ)=(Nat.choose n r:ℝ)*(r:ℝ) := by exact_mod_cast he
  field_simp
  nlinarith [her]

def overlappingSupports (n r : ℕ) (s : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  ((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun t => ¬Disjoint s t)

theorem overlappingSupports_union (n r : ℕ) (s : Finset (Fin n)) :
    overlappingSupports n r s = s.biUnion (fun a => incidentSupports n r a) := by
  ext t
  simp only [overlappingSupports, incidentSupports, Finset.mem_filter,
    Finset.mem_biUnion, Finset.not_disjoint_iff]
  aesop

theorem overlappingSupports_card_le (n r : ℕ) (s : Finset (Fin n)) (hr : 0 < r) :
    (overlappingSupports n r s).card ≤ s.card * Nat.choose (n-1) (r-1) := by
  rw [overlappingSupports_union]
  calc
    _ ≤ ∑ a ∈ s, (incidentSupports n r a).card := Finset.card_biUnion_le
    _ = _ := by simp [incidentSupports_card n r _ hr]

theorem overlappingSupports_fraction_le (n r : ℕ) (s : Finset (Fin n))
    (hr : 0 < r) (hrn : r ≤ n) :
    ((overlappingSupports n r s).card : ℝ) / (Nat.choose n r : ℝ) ≤
      (s.card : ℝ) * r / n := by
  have hn : 0 < n := by omega
  let a : Fin n := ⟨0, hn⟩
  have he := incidentSupports_fraction n r a hr hrn
  rw [incidentSupports_card n r a hr] at he
  calc
    _ ≤ ((s.card : ℝ) * (Nat.choose (n-1) (r-1) : ℝ)) / (Nat.choose n r : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast overlappingSupports_card_le n r s hr
    _ = _ := by rw [mul_div_assoc, he]; ring

theorem fixed_arity_overlap_fraction (n r : ℕ) (s : Finset (Fin n))
    (hr : 0 < r) (hrn : r ≤ n) (hs : s.card = r) :
    ((overlappingSupports n r s).card : ℝ) / (Nat.choose n r : ℝ) ≤ (r : ℝ)^2 / n := by
  simpa only [hs, pow_two] using overlappingSupports_fraction_le n r s hr hrn

end Qatlib.Foundations.FiniteCounts.SubsetIncidence
