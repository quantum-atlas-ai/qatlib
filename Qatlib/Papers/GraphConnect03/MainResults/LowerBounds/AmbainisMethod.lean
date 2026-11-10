/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphConnect03.MainResults.Defs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.Defs

attribute [local instance] Classical.propDecidable

structure AmbainisRelation (n : ℕ) where

  X : Finset (Fin n → Bool)

  Y : Finset (Fin n → Bool)

  R : (Fin n → Bool) → (Fin n → Bool) → Prop

  m : ℕ

  m' : ℕ

  lmax : ℕ
  m_spec : ∀ x ∈ X, m ≤ (Y.filter (fun y => R x y)).card
  m'_spec : ∀ y ∈ Y, m' ≤ (X.filter (fun x => R x y)).card
  l_spec : ∀ x ∈ X, ∀ y ∈ Y, R x y → ∀ i : Fin n,
    (Y.filter (fun y' => R x y' ∧ y' i ≠ y i)).card *
      (X.filter (fun x' => R x' y ∧ x' i ≠ x i)).card ≤ lmax

theorem sqrt_kclique_parameters (n k : ℕ) (hk : 0 < k) :
    Real.sqrt (((n : ℝ) * (k : ℝ) ^ 2) ^ 2 / (k : ℝ) ^ 3) =
      (n : ℝ) * Real.sqrt (k : ℝ) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
  have h : ((n : ℝ) * (k : ℝ) ^ 2) ^ 2 / (k : ℝ) ^ 3 = (n : ℝ) ^ 2 * (k : ℝ) := by
    rw [div_eq_iff (pow_ne_zero 3 hkne)]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg n)]

theorem sqrt_matrix_parameters (n : ℕ) (hn : 0 < n) :
    Real.sqrt (((n : ℝ) ^ 2) ^ 2 / (n : ℝ)) =
      (n : ℝ) * Real.sqrt (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have h : ((n : ℝ) ^ 2) ^ 2 / (n : ℝ) = (n : ℝ) ^ 2 * (n : ℝ) := by
    rw [div_eq_iff hnne]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hnR)]

end Qatlib.Papers.GraphConnect03.MainResults.LowerBounds
