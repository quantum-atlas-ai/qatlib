/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.LegacyWeak
public import Mathlib.Order.Interval.Finset.Floor
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section


/-! # Finite interval grids in both real embeddings
Actual coefficient bounds give a finite integer box. The enumeration retains
the archived free-cost interface and has no effective runtime certification.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy

open Qatlib.Papers.AncilFreeClfT14.MainResults

/-- The two integer coordinates faithfully identify a quadratic integer. -/
theorem sqrtPairInj : Function.Injective (fun x : Zsqrt2 => (x.a, x.b)) := by
  intro x y h
  cases x
  cases y
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨ha, hb⟩
  subst ha
  subst hb
  rfl

local instance : Countable Zsqrt2 := sqrtPairInj.countable

/-- Bounds on both real embeddings give explicit real bounds on both integer coefficients. -/
theorem intervalCoords (x0 x1 y0 y1 : ℝ) (α : Zsqrt2)
    (h : OneDimGridProblem (Set.Icc x0 x1) (Set.Icc y0 y1) α) :
    (α.a : ℝ) ∈ Set.Icc ((x0 + y0) / 2) ((x1 + y1) / 2) ∧
    (α.b : ℝ) ∈ Set.Icc
      ((x0 - y1) / (2 * Real.sqrt 2))
      ((x1 - y0) / (2 * Real.sqrt 2)) := by
  change
    (x0 ≤ α.toReal ∧ α.toReal ≤ x1) ∧
    (y0 ≤ α.bullet.toReal ∧ α.bullet.toReal ≤ y1) at h
  rcases h with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  simp only [Zsqrt2.toReal, Zsqrt2.bullet, Int.cast_neg, neg_mul]
    at hx0 hx1 hy0 hy1
  have hd : 0 < 2 * Real.sqrt 2 := by positivity
  constructor
  · constructor <;> linarith
  · constructor
    · rw [div_le_iff₀ hd]
      nlinarith
    · rw [le_div_iff₀ hd]
      nlinarith

/-- Every bounded two-embedding interval grid lies in a finite integer coefficient box. -/
theorem intervalFinite (x0 x1 y0 y1 : ℝ) :
    Set.Finite {α : Zsqrt2 |
      OneDimGridProblem (Set.Icc x0 x1) (Set.Icc y0 y1) α} := by
  classical
  let box : Finset (ℤ × ℤ) :=
    (Finset.Icc ⌈(x0 + y0) / 2⌉ ⌊(x1 + y1) / 2⌋).product
      (Finset.Icc
        ⌈(x0 - y1) / (2 * Real.sqrt 2)⌉
        ⌊(x1 - y0) / (2 * Real.sqrt 2)⌋)
  have hbox : (box : Set (ℤ × ℤ)).Finite := box.finite_toSet
  have hpre :
      ((fun α : Zsqrt2 => (α.a, α.b)) ⁻¹' (box : Set (ℤ × ℤ))).Finite :=
    Set.Finite.preimage (fun α _ β _ h => sqrtPairInj h) hbox
  apply hpre.subset
  intro α hα
  change (α.a, α.b) ∈ box
  change
    (α.a, α.b) ∈
      (Finset.Icc ⌈(x0 + y0) / 2⌉ ⌊(x1 + y1) / 2⌋).product
        (Finset.Icc
          ⌈(x0 - y1) / (2 * Real.sqrt 2)⌉
          ⌊(x1 - y0) / (2 * Real.sqrt 2)⌋)
  rw [Finset.product_eq_sprod, Finset.mem_product]
  have hc := intervalCoords x0 x1 y0 y1 α hα
  exact ⟨Int.cast_mem_Icc_iff.mp hc.1, Int.cast_mem_Icc_iff.mp hc.2⟩

/-- The full literal Proposition4.5 holds: its lattice is genuinely finite and
the preserved classical enumeration carries assigned zero cost. This does not
assert the source arithmetic enumeration algorithm or its operation complexity. -/
theorem weak45 (x0 x1 y0 y1 : ℝ) (_hx : x0 ≤ x1) (_hy : y0 ≤ y1) :
    ∃ (E : Enumeration (OneDimGridProblem (Set.Icc x0 x1) (Set.Icc y0 y1)))
      (C : ℕ), 0 < C ∧ (∀ n, E.cost n ≤ C) ∧
      Set.Finite {α : Zsqrt2 |
        OneDimGridProblem (Set.Icc x0 x1) (Set.Icc y0 y1) α} := by
  refine ⟨freeEnum _, 1, Nat.zero_lt_one, ?_, intervalFinite x0 x1 y0 y1⟩
  intro n
  rw [freeEnumCost]
  exact Nat.zero_le 1

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
