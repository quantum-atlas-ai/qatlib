/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs

open Matrix

def h3 (z z' z'' : Bool) : ℕ :=
  let s : ℕ := (if z then 1 else 0) + (if z' then 1 else 0) + (if z'' then 1 else 0)
  if s = 0 then 0 else if s = 1 then 3 else 1

theorem h3_false_false_false : h3 false false false = 0 := rfl

theorem h3_weight_one_right : h3 false false true = 3 := rfl

theorem h3_weight_two_right : h3 false true true = 1 := rfl

theorem h3_true_true_true : h3 true true true = 1 := rfl

theorem h3_nonneg (z z' z'' : Bool) : 0 ≤ h3 z z' z'' := by
  revert z z' z''
  decide

theorem h3_eq_zero_iff (z z' z'' : Bool) :
    h3 z z' z'' = 0 ↔ z = false ∧ z' = false ∧ z'' = false := by
  revert z z' z''
  decide

def cost (n : ℕ) (z : Fin n → Bool) : ℕ :=
  ∑ p : Fin n × Fin n × Fin n,
    if p.1 < p.2.1 ∧ p.2.1 < p.2.2 then h3 (z p.1) (z p.2.1) (z p.2.2) else 0

theorem cost_nonneg (n : ℕ) (z : Fin n → Bool) : 0 ≤ cost n z := by
  unfold cost
  exact Finset.sum_nonneg (fun p _ => by
    split
    · exact h3_nonneg _ _ _
    · exact Nat.zero_le _)

theorem cost_all_zero (n : ℕ) : cost n (fun _ => false) = 0 := by
  unfold cost
  refine Finset.sum_eq_zero (fun p _ => ?_)
  split
  · exact h3_false_false_false
  · rfl

theorem cost_all_zero_is_global_min (n : ℕ) :
    cost n (fun _ => false) = 0 ∧ ∀ z : Fin n → Bool, 0 ≤ cost n z :=
  ⟨cost_all_zero n, cost_nonneg n⟩

def hpEnergy (n m : ℝ) : ℝ :=
  (3 / 2) * m * (n - m) * (n - m - 1) +
    (1 / 2) * m * (m - 1) * (n - m) +
    (1 / 6) * m * (m - 1) * (m - 2)

def hpEnergyFromSz (n Sz : ℝ) : ℝ :=
  (3 / 2) * (n / 2 - Sz) * (n / 2 + Sz) * (n / 2 + Sz - 1) +
    (1 / 2) * (n / 2 - Sz) * (n / 2 - Sz - 1) * (n / 2 + Sz) +
    (1 / 6) * (n / 2 - Sz) * (n / 2 - Sz - 1) * (n / 2 - Sz - 2)

theorem hpEnergyFromSz_eq (n Sz : ℝ) :
    hpEnergyFromSz n Sz = hpEnergy n (n / 2 - Sz) := by
  unfold hpEnergyFromSz hpEnergy
  ring

def hpEnergyNat (n k : ℕ) : ℝ :=
  3 * (k : ℝ) * (((n - k).choose 2 : ℕ) : ℝ) +
    ((k.choose 2 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) +
    ((k.choose 3 : ℕ) : ℝ)

theorem cast_choose_three (k : ℕ) :
    ((k.choose 3 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) / 6 := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.cast_add, Nat.cast_choose_two ℝ n, ih]
    push_cast
    ring

theorem hpEnergyNat_eq {n k : ℕ} (hk : k ≤ n) :
    hpEnergyNat n k = hpEnergy (n : ℝ) (k : ℝ) := by
  unfold hpEnergyNat hpEnergy
  rw [Nat.cast_choose_two ℝ (n - k), Nat.cast_choose_two ℝ k,
    cast_choose_three k, Nat.cast_sub hk]
  ring

theorem hpEnergyNat_nonneg (n k : ℕ) : 0 ≤ hpEnergyNat n k := by
  unfold hpEnergyNat
  have h1 : (0 : ℝ) ≤ 3 * (k : ℝ) * (((n - k).choose 2 : ℕ) : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ ((k.choose 2 : ℕ) : ℝ) * ((n - k : ℕ) : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ ((k.choose 3 : ℕ) : ℝ) := by positivity
  linarith

theorem hpEnergy_nonneg_nat {n k : ℕ} (hk : k ≤ n) :
    0 ≤ hpEnergy (n : ℝ) (k : ℝ) := by
  rw [← hpEnergyNat_eq hk]
  exact hpEnergyNat_nonneg n k

theorem hpEnergy_zero (n : ℝ) : hpEnergy n 0 = 0 := by
  unfold hpEnergy
  ring

theorem hpEnergyFromSz_all_zero (n : ℝ) : hpEnergyFromSz n (n / 2) = 0 := by
  rw [hpEnergyFromSz_eq]
  simpa [sub_self] using hpEnergy_zero n

def V0 (θ φ s : ℝ) : ℝ :=
  2 * (1 - s) * (1 - Real.sin θ * Real.cos φ) +
    (s / 6) * (13 + 3 * Real.cos θ - 9 * Real.cos θ ^ 2 - 7 * Real.cos θ ^ 3)

def VE (θ φ s : ℝ) : ℝ :=
  -8 * s * (1 - s) * Real.cos θ * Real.sin θ * Real.cos φ

def V (θ φ s : ℝ) : ℝ := V0 θ φ s + VE θ φ s

def sourceA28 : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0, -2, -2, 0, -2, 0, 0, 0;
     -2, 0, 0, 0, 0, 0, 0, 0;
     -2, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 2;
     -2, 0, 0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 2;
     0, 0, 0, 0, 0, 0, 0, 2;
     0, 0, 0, 2, 0, 2, 2, 0]

theorem sourceA28_isSymm : sourceA28.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sourceA28_diagonal_zero (i : Fin 8) : sourceA28 i i = 0 := by
  fin_cases i <;> rfl

def IsP2Sample (A : Matrix (Fin 8) (Fin 8) ℝ) : Prop :=
  A.IsSymm ∧ ∀ i, A i i = 0

theorem sourceA28_isP2Sample :
    IsP2Sample (sourceA28.map (fun z : ℤ => (z : ℝ))) := by
  constructor
  · exact sourceA28_isSymm.map _
  · intro i
    simp [sourceA28_diagonal_zero i]

theorem p2_free_parameters :
    ((Finset.univ.filter (fun p : Fin 8 × Fin 8 => p.1 < p.2)).card = 28) := by
  decide

theorem isP2Sample_zero : IsP2Sample (0 : Matrix (Fin 8) (Fin 8) ℝ) := by
  constructor
  · exact Matrix.isSymm_zero
  · intro i
    simp

theorem isP2Sample_add {A B : Matrix (Fin 8) (Fin 8) ℝ}
    (hA : IsP2Sample A) (hB : IsP2Sample B) : IsP2Sample (A + B) := by
  constructor
  · exact hA.1.add hB.1
  · intro i
    simp [Matrix.add_apply, hA.2 i, hB.2 i]

theorem isP2Sample_smul (c : ℝ) {A : Matrix (Fin 8) (Fin 8) ℝ}
    (hA : IsP2Sample A) : IsP2Sample (c • A) := by
  constructor
  · exact hA.1.smul c
  · intro i
    simp [Matrix.smul_apply, hA.2 i]

theorem isP2Sample_determined_by_upper (A : Matrix (Fin 8) (Fin 8) ℝ)
    (hA : IsP2Sample A) (i j : Fin 8) :
    A i j = if i < j then A i j else if j < i then A j i else 0 := by
  by_cases hij : i < j
  · simp [hij]
  · by_cases hji : j < i
    · simp [hij, hji, hA.1.apply j i]
    · have heq : i = j := by
        rcases lt_trichotomy i j with h | h | h
        · exact absurd h hij
        · exact h
        · exact absurd h hji
      subst heq
      simp [hA.2 i]

end Qatlib.Papers.AdiabaticPath02.MainResults.PathDefs
