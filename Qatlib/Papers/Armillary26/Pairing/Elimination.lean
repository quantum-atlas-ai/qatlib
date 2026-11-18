/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodeCert.PermBlocks.Rank
import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Static and ordered elimination for paired checks

The static commutator of horizontally assembled check families splits into
per-block-column terms, so per-column vanishing eliminates the static
commutator. The ordered time sum is a separate quantity: a finite regression
with swapped roles shows static elimination alone cannot imply ordered
elimination.
-/

namespace Qatlib.Papers.Armillary26.Pairing

set_option autoImplicit false
set_option warningAsError true

open scoped Matrix

/-- The static commutator of two check families. -/
def omegaMat {κX κZ ι : Type*} [Fintype ι]
    (Hx : Matrix κX ι (ZMod 2)) (Hz : Matrix κZ ι (ZMod 2)) :
    Matrix κX κZ (ZMod 2) := Hx * Hzᵀ

/-- Horizontal assembly of a block-column family. -/
def hcat {κX ι β : Type*} (E : β → Matrix κX ι (ZMod 2)) :
    Matrix κX (β × ι) (ZMod 2) :=
  Matrix.of fun k bi => E bi.1 k bi.2

/-- The static commutator of assembled families splits into per-column sums. -/
theorem omega_hcat_entry {κX ι β : Type*} [Fintype ι] [Fintype β]
    (E Z : β → Matrix κX ι (ZMod 2)) (k l : κX) :
    ((hcat E : Matrix κX (β × ι) (ZMod 2)) * (hcat Z)ᵀ) k l
      = ∑ b : β, (E b * (Z b)ᵀ) k l := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hcat, Matrix.of_apply]
  have huniv : (Finset.univ : Finset (β × ι))
      = (Finset.univ : Finset β) ×ˢ (Finset.univ : Finset ι) := by
    ext x
    simp
  rw [huniv, Finset.sum_product]

/-- Per-column vanishing eliminates the static commutator. -/
theorem omega_pair_zero {κX ι β : Type*} [Fintype ι] [Fintype β]
    (E Z : β → Matrix κX ι (ZMod 2))
    (h : ∀ b : β, E b * (Z b)ᵀ = 0) : hcat E * (hcat Z)ᵀ = 0 := by
  ext k l
  rw [omega_hcat_entry E Z k l]
  simp [h]

/-- The ordered time sum of cross commutators. -/
def ordC {n : ℕ} {κX κZ ι : Type*} [Fintype ι]
    (Hx : Fin n → Matrix κX ι (ZMod 2)) (Hz : Fin n → Matrix κZ ι (ZMod 2)) :
    Matrix κX κZ (ZMod 2) :=
  ∑ t : Fin n, ∑ u : Fin n, if (t : ℕ) < (u : ℕ) then Hx t * (Hz u)ᵀ else 0

/-- Vanishing cross-time blocks eliminate the ordered sum. -/
theorem ordC_of_cross {n : ℕ} {κX κZ ι : Type*} [Fintype ι]
    (Hx : Fin n → Matrix κX ι (ZMod 2)) (Hz : Fin n → Matrix κZ ι (ZMod 2))
    (h : ∀ t u : Fin n, (t : ℕ) < (u : ℕ) → Hx t * (Hz u)ᵀ = 0) :
    ordC Hx Hz = 0 := by
  simp only [ordC]
  refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun u _ => ?_
  by_cases htu : (t : ℕ) < (u : ℕ)
  · simp [h t u htu]
  · simp [htu]

/-- The regression family: step `t` uses the `t`-th unit row for X. -/
def regX : Fin 2 → Matrix (Fin 1) (Fin 2) (ZMod 2) :=
  fun t => Matrix.of fun _ j => if (j : ℕ) = (t : ℕ) then 1 else 0

/-- The regression family: step `t` uses the opposite unit row for Z. -/
def regZ : Fin 2 → Matrix (Fin 1) (Fin 2) (ZMod 2) :=
  fun t => Matrix.of fun _ j => if (j : ℕ) = 1 - (t : ℕ) then 1 else 0

/-- The regression has vanishing static commutator. -/
theorem reg_omega_zero : omegaMat (hcat regX) (hcat regZ) = 0 := by decide

/-- On the original two data coordinates, the accumulated rows commute. -/
theorem reg_sum_zero : omegaMat (∑ t, regX t) (∑ t, regZ t) = 0 := by decide

/-- The regression has nonzero ordered sum: static elimination does not
imply ordered elimination. -/
theorem reg_ordC_ne : ordC regX regZ ≠ 0 := by
  intro h
  have hone : ordC regX regZ 0 0 = (1 : ZMod 2) := by decide
  rw [h] at hone
  simp at hone

/-- Static commutation on the same data coordinates does not imply ordered elimination. -/
theorem reg_static_ord :
    omegaMat (∑ t, regX t) (∑ t, regZ t) = 0 ∧ ordC regX regZ ≠ 0 :=
  ⟨reg_sum_zero, reg_ordC_ne⟩

end Qatlib.Papers.Armillary26.Pairing
