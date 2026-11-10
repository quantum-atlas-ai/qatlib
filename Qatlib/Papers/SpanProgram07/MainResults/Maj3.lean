/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgram07.MainResults.SpanProgram
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset

def maj3Program (w : ℂ) (α : Fin 3 → ℂ) : SpanProgram 3 (Fin 3) Unit (Fin 3) where
  grp j := j
  lit j := Lit.pos j
  v j k := match k with
    | none => w
    | some _ => α j

namespace maj3Program

theorem groupTrue_iff (w : ℂ) (α : Fin 3 → ℂ) (x : Fin 3 → Bool) (j : Fin 3) :
    (maj3Program w α).groupTrue x j ↔ x j = true := by
  constructor
  · intro h
    exact h j rfl
  · intro h i hi
    subst hi
    exact h

theorem accepts_iff_exists (w : ℂ) (α : Fin 3 → ℂ) (x : Fin 3 → Bool) :
    (maj3Program w α).accepts x ↔ ∃ a : Fin 3 → ℂ,
      (∀ i, x i = false → a i = 0) ∧ (∑ j, a j * w = 1) ∧ (∑ j, a j * α j = 0) := by
  have hcoord : ∀ (a : Fin 3 → ℂ),
      (∑ j, a j • (maj3Program w α).v j = target Unit) ↔
        (∑ j, a j * w = 1) ∧ (∑ j, a j * α j = 0) := by
    intro a
    constructor
    · intro h
      constructor
      · have := congr_fun h none
        simpa [Finset.sum_apply, smul_eq_mul, maj3Program, target] using this
      · have := congr_fun h (some ())
        simpa [Finset.sum_apply, smul_eq_mul, maj3Program, target] using this
    · rintro ⟨h1, h2⟩
      funext k
      cases k with
      | none => simpa [Finset.sum_apply, smul_eq_mul, maj3Program, target] using h1
      | some u =>
          have hu : u = () := Subsingleton.elim u ()
          subst hu
          simpa [Finset.sum_apply, smul_eq_mul, maj3Program, target] using h2
  constructor
  · rintro ⟨a, hsupp, hsum⟩
    exact ⟨a, (SpanProgram.supported_iff (P := maj3Program w α) x a).1 hsupp,
      (hcoord a).1 hsum⟩
  · rintro ⟨a, hsupp, hc⟩
    exact ⟨a, (SpanProgram.supported_iff (P := maj3Program w α) x a).2 hsupp, (hcoord a).2 hc⟩

theorem accepts_iff_two_le (w : ℂ) (hw : w ≠ 0) (α : Fin 3 → ℂ)
    (hinj : Function.Injective α) (hα0 : ∀ j, α j ≠ 0) (x : Fin 3 → Bool) :
    (maj3Program w α).accepts x ↔ 2 ≤ (univ.filter (fun i => x i)).card := by
  classical
  set T : Finset (Fin 3) := univ.filter (fun i => x i) with hT
  have hmemT : ∀ j, j ∈ T ↔ x j = true := by
    intro j
    simp [hT]
  rw [accepts_iff_exists]
  constructor
  · rintro ⟨a, hsupp, h1, h2⟩
    have hne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hzero : ∑ j, a j * w = 0 := by
        refine sum_eq_zero fun j _ => ?_
        have hxj : x j ≠ true := by
          intro h
          have : j ∈ T := (hmemT j).2 h
          rw [hempty] at this
          exact absurd this (by simp)
        have hxf : x j = false := by simpa using hxj
        rw [hsupp j hxf, zero_mul]
      rw [hzero] at h1
      exact zero_ne_one h1
    have hpos : 0 < T.card := T.card_pos.mpr hne
    rcases Nat.lt_or_ge T.card 2 with hlt | hge
    · exfalso
      have hle : T.card = 1 := le_antisymm (Nat.lt_succ_iff.mp hlt) hpos
      obtain ⟨j, hj⟩ := card_eq_one.1 hle
      have hsumj : ∑ t, a t * w = a j * w := by
        refine sum_eq_single j ?_ ?_
        · intro t _ ht
          have htT : t ∉ T := by
            rw [hj]
            simpa using ht
          have hxf : x t = false := by
            by_contra h
            exact htT ((hmemT t).2 (by simpa using h))
          rw [hsupp t hxf, zero_mul]
        · intro h
          exact absurd (mem_univ j) h
      have haj : a j ≠ 0 := by
        intro h0
        rw [hsumj, h0, zero_mul] at h1
        exact zero_ne_one h1
      have hsumj2 : ∑ t, a t * α t = a j * α j := by
        refine sum_eq_single j ?_ ?_
        · intro t _ ht
          have htT : t ∉ T := by
            rw [hj]
            simpa using ht
          have hxf : x t = false := by
            by_contra h
            exact htT ((hmemT t).2 (by simpa using h))
          rw [hsupp t hxf, zero_mul]
        · intro h
          exact absurd (mem_univ j) h
      rw [hsumj2] at h2
      exact hα0 j ((mul_eq_zero.1 h2).resolve_left haj)
    · exact hge
  · intro hge
    obtain ⟨j, hjT, k, hkT, hjk⟩ := one_lt_card.1 (by omega : 1 < T.card)
    have hxj : x j = true := (hmemT j).1 hjT
    have hxk : x k = true := (hmemT k).1 hkT
    have hαjk : α k - α j ≠ 0 := fun h => hjk (hinj (sub_eq_zero.1 h)).symm
    let a : Fin 3 → ℂ := fun t =>
      if t = j then w⁻¹ * (α k / (α k - α j))
      else if t = k then -(w⁻¹ * (α j / (α k - α j)))
      else 0
    have haj : a j = w⁻¹ * (α k / (α k - α j)) := by simp [a]
    have hak : a k = -(w⁻¹ * (α j / (α k - α j))) := by simp [a, Ne.symm hjk]
    have hsupp : ∀ t, x t = false → a t = 0 := by
      intro t ht
      have htj : t ≠ j := fun h => by rw [h, hxj] at ht; exact absurd ht (by simp)
      have htk : t ≠ k := fun h => by rw [h, hxk] at ht; exact absurd ht (by simp)
      simp [a, htj, htk]
    have hzero : ∀ t ∈ (univ : Finset (Fin 3)), t ∉ ({j, k} : Finset (Fin 3)) →
        a t * w = 0 := by
      intro t _ ht
      have htj : t ≠ j := fun h => ht (by simp [h])
      have htk : t ≠ k := fun h => ht (by simp [h])
      simp [a, htj, htk]
    have hzeroα : ∀ t ∈ (univ : Finset (Fin 3)), t ∉ ({j, k} : Finset (Fin 3)) →
        a t * α t = 0 := by
      intro t _ ht
      have htj : t ≠ j := fun h => ht (by simp [h])
      have htk : t ≠ k := fun h => ht (by simp [h])
      simp [a, htj, htk]
    refine ⟨a, hsupp, ?_, ?_⟩
    · rw [← sum_subset (subset_univ _) hzero, sum_pair hjk]
      rw [haj, hak]
      field_simp
      ring
    · rw [← sum_subset (subset_univ _) hzeroα, sum_pair hjk]
      rw [haj, hak]
      field_simp
      ring

end maj3Program

end Qatlib.Papers.SpanProgram07.MainResults
