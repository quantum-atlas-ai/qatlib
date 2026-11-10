/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.SignedClock.ClockSpectral
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.SignedClock

open Finset Matrix

theorem sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)

def wPlus (p : ℝ) : ℝ := (1 + (1 - 2 * p) / Real.sqrt 2) / 2

theorem wPlus_lower {p : ℝ} (hp : p ≤ 1 / 3) :
    (1 + 1 / (3 * Real.sqrt 2)) / 2 ≤ wPlus p := by
  have hs := sqrt2_pos
  have h1 : (1 : ℝ) / 3 ≤ 1 - 2 * p := by linarith
  have h2 : (1 / 3) / Real.sqrt 2 ≤ (1 - 2 * p) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right h1 (le_of_lt hs)
  have h3 : (1 / 3) / Real.sqrt 2 = 1 / (3 * Real.sqrt 2) := by
    field_simp
  unfold wPlus
  rw [← h3]
  linarith

theorem wPlus_upper {p : ℝ} (hp : 2 / 3 ≤ p) :
    wPlus p ≤ (1 - 1 / (3 * Real.sqrt 2)) / 2 := by
  have hs := sqrt2_pos
  have h1 : 1 - 2 * p ≤ -(1 / 3 : ℝ) := by linarith
  have h2 : (1 - 2 * p) / Real.sqrt 2 ≤ (-(1 / 3)) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right h1 (le_of_lt hs)
  have h3 : (-(1 / 3)) / Real.sqrt 2 = -(1 / (3 * Real.sqrt 2)) := by
    field_simp
  unfold wPlus
  rw [h3] at h2
  linarith

def InScaledInt {N : ℕ} (s : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, ∃ k : ℤ, A i j = (k : ℝ) * s

theorem inScaledInt_one {N : ℕ} :
    InScaledInt (1 : ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) := by
  intro i j
  refine ⟨if i = j then 1 else 0, ?_⟩
  rw [Matrix.one_apply]
  split_ifs <;> simp

theorem inScaledInt_mul {N : ℕ} {s t : ℝ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : InScaledInt s A) (hB : InScaledInt t B) :
    InScaledInt (s * t) (A * B) := by
  classical
  intro i j
  choose a ha using hA
  choose b hb using hB
  have hterm : ∀ l : Fin N,
      A i l * B l j = (((a i l) * (b l j) : ℤ) : ℝ) * (s * t) := by
    intro l
    rw [ha i l, hb l j]
    push_cast
    ring
  refine ⟨∑ l, a i l * b l j, ?_⟩
  calc (A * B) i j = ∑ l, A i l * B l j := by rw [Matrix.mul_apply]
    _ = ∑ l, (((a i l) * (b l j) : ℤ) : ℝ) * (s * t) :=
        Finset.sum_congr rfl fun l _ => hterm l
    _ = (∑ l, (((a i l) * (b l j) : ℤ) : ℝ)) * (s * t) := by rw [Finset.sum_mul]
    _ = (((∑ l, a i l * b l j) : ℤ) : ℝ) * (s * t) := by rw [Int.cast_sum]

theorem inScaledInt_pow {N : ℕ} {s : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : InScaledInt s A) (m : ℕ) : InScaledInt (s ^ m) (A ^ m) := by
  induction m with
  | zero => simpa using (inScaledInt_one (N := N))
  | succ m ih =>
      rw [pow_succ, pow_succ]
      exact inScaledInt_mul ih hA

theorem gateProduct_scaled {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : InScaledInt ((Real.sqrt 2)⁻¹) A) (M : ℕ) :
    InScaledInt (((Real.sqrt 2)⁻¹) ^ M) (A ^ M) :=
  inScaledInt_pow hA M

end Qatlib.Papers.BQPMixSparse06.SignedClock
