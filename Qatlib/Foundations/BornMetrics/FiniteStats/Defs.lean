/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ENat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.BigOperators.Group.List.Defs

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator NNReal ENNReal
namespace Qatlib.Foundations.BornMetrics.FiniteStats

def l2norm {N : ℕ} (u : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖u i‖ ^ 2)

theorem l2norm_nonneg {N : ℕ} (u : Fin N → ℂ) : 0 ≤ l2norm u := Real.sqrt_nonneg _

def ket {N : ℕ} (b : Fin N) : Fin N → ℂ := fun j => if j = b then 1 else 0

def toEuc {N : ℕ} (u : Fin N → ℂ) : EuclideanSpace ℂ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℂ).symm u

theorem norm_toEuc {N : ℕ} (u : Fin N → ℂ) : ‖toEuc u‖ = l2norm u := by
  rw [l2norm, EuclideanSpace.norm_eq]
  congr 1

theorem l2norm_ket {N : ℕ} (b : Fin N) : l2norm (ket b) = 1 := by
  rw [l2norm]
  have h : (∑ i : Fin N, ‖ket b i‖ ^ 2) = 1 := by
    rw [Finset.sum_eq_single b]
    · simp [ket]
    · intro i _ hi; simp [ket, hi]
    · intro h; exact absurd (Finset.mem_univ b) h
  rw [h, Real.sqrt_one]

def fiberProb {N A : ℕ} (p : Fin N → Fin A) (u : Fin N → ℂ) (a : Fin A) : ℝ :=
  ∑ i, if p i = a then ‖u i‖ ^ 2 else 0

def measDist {N A : ℕ} (p : Fin N → Fin A) (u v : Fin N → ℂ) : ℝ :=
  ∑ a, |fiberProb p u a - fiberProb p v a|

def prefixMap (n l : ℕ) (hl : l ≤ n) : Fin (2 ^ n) → Fin (2 ^ l) :=
  fun i =>
    ⟨i.val / 2 ^ (n - l), by
      have hpos : 0 < 2 ^ (n - l) := pow_pos (show (0 : ℕ) < 2 by norm_num) (n - l)
      have hi : i.val < 2 ^ n := i.isLt
      rw [Nat.div_lt_iff_lt_mul hpos, ← Nat.pow_add]
      have : l + (n - l) = n := Nat.add_sub_of_le hl
      rw [this]
      exact hi⟩

def vPrefix (n l : ℕ) (hl : l ≤ n) (u v : Fin (2 ^ n) → ℂ) : ℝ :=
  measDist (prefixMap n l hl) u v

theorem measDist_nonneg {N A : ℕ} (p : Fin N → Fin A) (u v : Fin N → ℂ) :
    0 ≤ measDist p u v := Finset.sum_nonneg fun _a _ => abs_nonneg _

def maxPrefixTV (n l : ℕ) (hl : l ≤ n)
    (U V : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (k : ℕ) : ℝ :=
  ↑((Finset.univ.filter (fun b : Fin (2 ^ n) => b.val < k)).sup
    (fun b => (⟨vPrefix n l hl (U *ᵥ ket b) (V *ᵥ ket b), measDist_nonneg _ _ _⟩ : ℝ≥0)))

def norm2k {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (k : ℕ) : ℝ :=
  ↑((Finset.univ.filter (fun b : Fin N => b.val < k)).sup
    (fun b => (⟨l2norm (A *ᵥ ket b), l2norm_nonneg _⟩ : ℝ≥0)))

def Orthonormal (N k : ℕ) (u : Fin k → Fin N → ℂ) : Prop :=
  ∀ i j : Fin k, (∑ a : Fin N, star (u i a) * u j a) = if i = j then 1 else 0

def simplex (N : ℕ) : Set (EuclideanSpace ℝ (Fin N)) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

def simplexDistance {N : ℕ} (u v : simplex N) : ℝ :=
  ∑ i, |u.val i - v.val i|

end Qatlib.Foundations.BornMetrics.FiniteStats
