/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.PenaltyExact.Pair
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Foundations.BooleanEnergy.HadamardGram

def Valid {M N : ℕ} (x : Configuration M N) : Prop := ∀ p, PairValid x p

def squareEnergy {M N : ℕ} (δ : ℝ) (x : Configuration M N) : ℝ :=
  ∑ p : ColumnPair N, squarePair δ x p

def paperEnergy {M N : ℕ} (δ : ℝ) (x : Configuration M N) : ℝ :=
  ∑ p : ColumnPair N, paperPair δ x p

def IsGround {α : Type*} (f : α → ℝ) (x : α) : Prop := ∀ y, f x ≤ f y

theorem exists_ground {M N : ℕ} (f : Configuration M N → ℝ) : ∃ x, IsGround f x := by
  classical
  obtain ⟨x,_,hx⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  exact ⟨x,fun y => hx y (Finset.mem_univ y)⟩

theorem paperEnergy_eq_squareEnergy {M N : ℕ} (δ : ℝ) (x : Configuration M N) :
    paperEnergy δ x = squareEnergy (δ-8) x := by
  apply Finset.sum_congr rfl
  intro p _
  exact paperPair_eq_squarePair δ x p

theorem squareEnergy_valid {M N : ℕ} (δ : ℝ) (x : Configuration M N)
    (h : Valid x) : squareEnergy δ x = energy (main x) := by
  apply Finset.sum_congr rfl
  intro p _
  exact squarePair_valid δ x p (h p)

theorem squareEnergy_complete {M N : ℕ} (δ : ℝ) (q : Fin M → Fin N → Bool) :
    squareEnergy δ (complete q) = energy q := by
  exact squareEnergy_valid δ (complete q) (complete_pair_valid q)

theorem energy_le_squareEnergy {M N : ℕ} (δ : ℝ) (hδ : (M : ℝ)^2 < δ)
    (x : Configuration M N) : energy (main x) ≤ squareEnergy δ x := by
  exact Finset.sum_le_sum (fun p _ => (squarePair_compare δ hδ x p).1)

theorem energy_lt_squareEnergy {M N : ℕ} (δ : ℝ) (hδ : (M : ℝ)^2 < δ)
    (x : Configuration M N) (h : ¬Valid x) : energy (main x) < squareEnergy δ x := by
  classical
  unfold Valid at h
  push Not at h
  obtain ⟨p,hp⟩ := h
  exact Finset.sum_lt_sum (fun p _ => (squarePair_compare δ hδ x p).1)
    ⟨p,Finset.mem_univ p,(squarePair_compare δ hδ x p).2 hp⟩

theorem square_ground_iff {M N : ℕ} (δ : ℝ) (hδ : (M : ℝ)^2 < δ)
    (x : Configuration M N) :
    IsGround (squareEnergy δ) x ↔ Valid x ∧ IsGround energy (main x) := by
  constructor
  · intro hx
    have hv : Valid x := by
      by_contra hn
      have hs := energy_lt_squareEnergy δ hδ x hn
      have hg := hx (complete (main x))
      rw [squareEnergy_complete] at hg
      linarith
    refine ⟨hv,?_⟩
    intro q
    have hg := hx (complete q)
    rw [squareEnergy_valid δ x hv,squareEnergy_complete] at hg
    exact hg
  · rintro ⟨hv,hg⟩ y
    rw [squareEnergy_valid δ x hv]
    exact (hg (main y)).trans (energy_le_squareEnergy δ hδ y)

theorem paper_ground_iff {M N : ℕ} (δ : ℝ) (hδ : (M : ℝ)^2 < δ-8)
    (x : Configuration M N) :
    IsGround (paperEnergy δ) x ↔ Valid x ∧ IsGround energy (main x) := by
  have he : paperEnergy (M:=M) (N:=N) δ = squareEnergy (δ-8) :=
    funext (paperEnergy_eq_squareEnergy δ)
  rw [he]
  exact square_ground_iff (δ-8) hδ x

theorem source_penalty_threshold (M : ℕ) (hM : 2 ≤ M) :
    (M : ℝ)^2 < 4*(M : ℝ)^2-8 := by
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith [sq_nonneg ((M : ℝ)-2)]

theorem source_ground_iff {M N : ℕ} (hM : 2 ≤ M) (x : Configuration M N) :
    IsGround (paperEnergy (4*(M : ℝ)^2)) x ↔
      Valid x ∧ IsGround energy (main x) :=
  paper_ground_iff _ (source_penalty_threshold M hM) x

theorem original_ground_frame {M N : ℕ} (q : Fin M → Fin N → Bool)
    (hq : IsGround energy q) (hex : ∃ q₀ : Fin M → Fin N → Bool, IsOrthogonalFrame q₀) :
    IsOrthogonalFrame q := by
  obtain ⟨q₀,h₀⟩ := hex
  apply (energy_zero_iff q).mp
  have hz := (energy_zero_iff q₀).mpr h₀
  have hb := hq q₀
  have hn := energy_nonneg q
  linarith

theorem source_ground_frame {M N : ℕ} (hM : 2 ≤ M) (x : Configuration M N)
    (hx : IsGround (paperEnergy (4*(M : ℝ)^2)) x)
    (hex : ∃ q₀ : Fin M → Fin N → Bool, IsOrthogonalFrame q₀) :
    IsOrthogonalFrame (main x) :=
  original_ground_frame (main x) ((source_ground_iff hM x).mp hx).2 hex

end Qatlib.Foundations.BooleanEnergy.PenaltyExact
