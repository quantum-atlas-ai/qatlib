/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.CommutatorProducts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MPFRootProfile

open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal
open CommutatorGrowth CommutatorProducts BCHControlled
open Qatlib.Concepts.TrotterFormula.GeneralOrder
set_option warningAsError false

variable {I : Type} [Fintype I]

def rootCoefficient (xs : List (Matrix I I ℂ)) (j l : ℕ) : ℝ :=
  (positiveProduct xs j l) ^ (((j + l : ℕ) : ℝ)⁻¹)

def rootSet (xs : List (Matrix I I ℂ)) (m : ℕ) : Set ℝ :=
  {z | ∃ j l : ℕ, Even j ∧ 2 * m ≤ j ∧ 1 ≤ l ∧ l ≤ m ∧ z = rootCoefficient xs j l}

def mu (xs : List (Matrix I I ℂ)) (m : ℕ) : ℝ := sSup (rootSet xs m)

theorem rootCoefficient_nonneg (xs : List (Matrix I I ℂ)) (j l : ℕ) :
    0 ≤ rootCoefficient xs j l := Real.rpow_nonneg (positiveProduct_nonneg xs j l) _

theorem rootCoefficient_pow (xs : List (Matrix I I ℂ)) (j l : ℕ) (hd : 0 < j + l) :
    rootCoefficient xs j l ^ (j + l) = positiveProduct xs j l :=
  Real.rpow_inv_natCast_pow (positiveProduct_nonneg xs j l) (by omega)

theorem rootSet_nonempty (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) :
    (rootSet xs m).Nonempty := by
  refine ⟨rootCoefficient xs (2 * m) m, 2 * m, m, even_two_mul m, le_refl _, ?_, le_refl _, rfl⟩
  omega

variable [DecidableEq I]

theorem rootSet_le_scale (xs : List (Matrix I I ℂ)) (m : ℕ) :
    ∀ z ∈ rootSet xs m, z ≤ boundingScale xs := by
  rintro z ⟨j, l, heven, hj, hl, hlm, rfl⟩
  obtain ⟨a, ha⟩ := heven
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = 2 * (n + l) := ⟨a - l, by omega⟩
  unfold rootCoefficient
  rw [positiveProduct_eq_raw]
  apply (Real.rpow_inv_le_iff_of_pos (rawProduct_nonneg xs l n)
    (boundingScale_pos xs).le (show (0 : ℝ) < ((2 * (n + l) + l : ℕ) : ℝ) by positivity)).mpr
  rw [Real.rpow_natCast]
  have h := rawProduct_le_scale xs l n
  convert! h using 1
  congr 1
  omega

theorem rootSet_bounded (xs : List (Matrix I I ℂ)) (m : ℕ) : BddAbove (rootSet xs m) :=
  ⟨boundingScale xs, rootSet_le_scale xs m⟩

theorem mu_nonneg (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) : 0 ≤ mu xs m := by
  have hw : rootCoefficient xs (2 * m) m ∈ rootSet xs m := by
    exact ⟨2 * m, m, even_two_mul m, le_refl _, by omega, le_refl _, rfl⟩
  exact (rootCoefficient_nonneg xs (2 * m) m).trans (le_csSup (rootSet_bounded xs m) hw)

theorem mu_le_scale (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m) :
    mu xs m ≤ boundingScale xs :=
  csSup_le (rootSet_nonempty xs m hm) (rootSet_le_scale xs m)

theorem rawProduct_le_mu (xs : List (Matrix I I ℂ)) (m l n : ℕ)
    (hl : 1 ≤ l) (hlm : l ≤ m) (hn : m ≤ n + l) :
    rawProduct xs l n ≤ mu xs m ^ (2 * n + 3 * l) := by
  have hw : rootCoefficient xs (2 * (n + l)) l ∈ rootSet xs m := by
    refine ⟨2 * (n + l), l, even_two_mul _, ?_, hl, hlm, rfl⟩
    omega
  have hroot := le_csSup (rootSet_bounded xs m) hw
  calc
    _ = positiveProduct xs (2 * (n + l)) l := (positiveProduct_eq_raw xs l n).symm
    _ = rootCoefficient xs (2 * (n + l)) l ^ (2 * (n + l) + l) :=
      (rootCoefficient_pow xs _ l (by omega)).symm
    _ ≤ mu xs m ^ (2 * (n + l) + l) :=
      pow_le_pow_left₀ (rootCoefficient_nonneg xs _ l) hroot _
    _ = _ := by congr 1; omega

omit [DecidableEq I] in

theorem rawProduct_one (xs : List (Matrix I I ℂ)) (n : ℕ) :
    rawProduct xs 1 n = pfCommAlphaSelf xs (2 * n + 3) := by
  have hf : Finset.finAntidiagonal 1 n = {(fun _ : Fin 1 => n)} := by
    ext v
    simp only [Finset.mem_finAntidiagonal, Fin.sum_univ_one, Finset.mem_singleton]
    constructor
    · intro hv
      funext i
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
      exact hv
    · intro hv
      rw [hv]
  rw [rawProduct, hf, Finset.sum_singleton, Fin.prod_univ_one]

theorem oddControl (xs : List (Matrix I I ℂ)) (m : ℕ) (hm : 0 < m)
    (r : ℝ≥0) (hr : (r : ℝ) * mu xs m ≤ 1) : OddControl xs r (2 * m + 1) := by
  intro k hk ho
  obtain ⟨a, ha⟩ := ho
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 2 * n + 3 := ⟨a - 1, by omega⟩
  have hα : pfCommAlphaSelf xs (2 * n + 3) ≤ mu xs m ^ (2 * n + 3) := by
    have h := rawProduct_le_mu xs m 1 n (by decide) (by omega) (by omega)
    rw [rawProduct_one] at h
    simpa only [mul_one] using! h
  calc
    _ ≤ (r : ℝ) ^ (2 * n + 3) * mu xs m ^ (2 * n + 3) :=
      mul_le_mul_of_nonneg_left hα (pow_nonneg r.2 _)
    _ = ((r : ℝ) * mu xs m) ^ (2 * n + 3) := (mul_pow _ _ _).symm
    _ ≤ 1 := pow_le_one₀ (mul_nonneg r.2 (mu_nonneg xs m hm)) hr

end Qatlib.Papers.CommutLCHS26.MainResults.MPFRootProfile
