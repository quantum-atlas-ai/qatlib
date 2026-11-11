/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Simulation.CoordinatorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Supervised clustering — Proposition 14 (p. 9)

Fixed source: arXiv:2402.15686v3, Proposition 14 and its proof (p. 9).

The reduction is from `n`-Gap-Hamming (`Definition 6`): the points are `p = αx` and
`q_i = αy_i` with `x, y_i ∈ {±1}^d`.  The paper computes

* `‖A‖_F² = 2`,
* `‖b‖² = 2α²d`,
* `‖p - q_i‖₂² = 2α²d - 2α² (x · y_i)` (averaged over `i`),

and, choosing `α` with `α²√d = 1`, gets `ε = 1/n`, `‖b‖² = 2√d`, hence a lower bound of
`Ω(nd) = Ω(‖A‖_F⁴ ‖b‖⁴ ε⁻¹)` from the `Ω(nd)` hardness of `n`-Gap-Hamming (Proposition 7)
together with the simulation bound of Theorem 10.  The `ε⁻²` term comes from the two-player
case `n = 1`.

This file proves the distance identities, the parameter scale computation, and the final
composition with the named hardness hypothesis `GapHammingHardness` + Theorem 10.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Reductions

open Qatlib.Papers.QInspired25.MainResults.Model

/-- A vector all of whose entries are `±1`. -/
def isSignVec {d : ℕ} (v : Fin d → ℝ) : Prop := ∀ j, v j = 1 ∨ v j = -1

/-- Each coordinate of a sign vector squares to one. -/
theorem isSignVec_sq {d : ℕ} {v : Fin d → ℝ} (hv : isSignVec v) (j : Fin d) :
    v j ^ 2 = 1 := by
  rcases hv j with h | h <;> simp [h]

/-- Squared Euclidean distance. -/
def vecDistSq {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ j, (u j - v j) ^ 2

/-- **Proposition 14, distance identity (p. 9).**  For `±1` vectors,
`‖αx - αy_i‖² = 2α²d - 2α² (x · y_i)`. -/
theorem vecDistSq_smul {d n : ℕ} (x : Fin d → ℝ) (hx : isSignVec x)
    (y : Fin n → Fin d → ℝ) (hy : ∀ i, isSignVec (y i)) (α : ℝ) (i : Fin n) :
    vecDistSq (fun j => α * x j) (fun j => α * y i j)
      = 2 * α ^ 2 * (d : ℝ) - 2 * α ^ 2 * innerVec x (y i) := by
  have hsq : ∀ j : Fin d,
      (α * x j - α * y i j) ^ 2 = 2 * α ^ 2 - 2 * α ^ 2 * (x j * y i j) := by
    intro j
    have hx1 := isSignVec_sq hx j
    have hy1 := isSignVec_sq (hy i) j
    have e : (α * x j - α * y i j) ^ 2 = α ^ 2 * (x j ^ 2 - 2 * (x j * y i j) + y i j ^ 2) := by
      ring
    rw [e, hx1, hy1]; ring
  unfold vecDistSq innerVec
  simp only [hsq]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  simp only [nsmul_eq_mul]
  ring

/-- **Proposition 14, averaged distance (p. 9).**
`(1/n) Σ_i ‖p - q_i‖² = 2α²d - (2α²/n) Σ_i (x · y_i)`. -/
theorem mean_vecDistSq {d n : ℕ} (x : Fin d → ℝ) (hx : isSignVec x)
    (y : Fin n → Fin d → ℝ) (hy : ∀ i, isSignVec (y i)) (α : ℝ) (hn : (n : ℝ) ≠ 0) :
    (∑ i, vecDistSq (fun j => α * x j) (fun j => α * y i j)) / (n : ℝ)
      = 2 * α ^ 2 * (d : ℝ) - (2 * α ^ 2 / (n : ℝ)) * (∑ i, innerVec x (y i)) := by
  have h : ∀ i : Fin n,
      vecDistSq (fun j => α * x j) (fun j => α * y i j)
        = 2 * α ^ 2 * (d : ℝ) - 2 * α ^ 2 * innerVec x (y i) :=
    fun i => vecDistSq_smul x hx y hy α i
  simp only [h]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum]
  simp only [nsmul_eq_mul]
  field_simp

/-- **Proposition 14, choice of `ε` (p. 9).**  If `α²√d = 1` and the promise gives
`Σ_i (x · y_i) ≥ √d` (the far/close promise of `n`-Gap-Hamming), then the averaged squared
distance is at most `2α²d - 2/n`; in the other case it is at least `2α²d + 2/n`.  Hence
`ε = 1/n` separates the two cases. -/
theorem mean_dist_promise_high {d n : ℕ} (x : Fin d → ℝ) (hx : isSignVec x)
    (y : Fin n → Fin d → ℝ) (hy : ∀ i, isSignVec (y i)) (α : ℝ) (_hα : 0 ≤ α)
    (hn : 0 < n) (hαd : α ^ 2 * Real.sqrt (d : ℝ) = 1)
    (hS : Real.sqrt (d : ℝ) ≤ ∑ i, innerVec x (y i)) :
    (∑ i, vecDistSq (fun j => α * x j) (fun j => α * y i j)) / (n : ℝ)
      ≤ 2 * α ^ 2 * (d : ℝ) - 2 / (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [mean_vecDistSq x hx y hy α hn']
  have hd0 : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hkey : α ^ 2 * (d : ℝ) = Real.sqrt (d : ℝ) := by
    calc α ^ 2 * (d : ℝ) = α ^ 2 * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by rw [hd0]
      _ = (α ^ 2 * Real.sqrt (d : ℝ)) * Real.sqrt (d : ℝ) := by ring
      _ = 1 * Real.sqrt (d : ℝ) := by rw [hαd]
      _ = Real.sqrt (d : ℝ) := one_mul _
  have hcoef : (2 * α ^ 2 / (n : ℝ)) * Real.sqrt (d : ℝ) = 2 / (n : ℝ) := by
    have h := hαd
    field_simp at h ⊢
    linarith [h]
  have hle : (2 * α ^ 2 / (n : ℝ)) * Real.sqrt (d : ℝ)
      ≤ (2 * α ^ 2 / (n : ℝ)) * (∑ i, innerVec x (y i)) := by
    apply mul_le_mul_of_nonneg_left hS
    positivity
  linarith

/-- **Proposition 14, the `ε⁻²` (two-player) case (p. 9).**  With unit vectors
`p = x/√d`, `q = y/√d`, the squared distance is `(2/d)(d - x·y)`, so an additive `ε`
approximation of the squared distance decides Gap-Hamming. -/
theorem unit_vecDistSq {d : ℕ} (x y : Fin d → ℝ) (hx : isSignVec x) (hy : isSignVec y)
    (hd : 0 < d) :
    vecDistSq (fun j => x j / Real.sqrt (d : ℝ)) (fun j => y j / Real.sqrt (d : ℝ))
      = (2 / (d : ℝ)) * ((d : ℝ) - innerVec x y) := by
  have hd0 : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hdne : Real.sqrt (d : ℝ) ≠ 0 := by positivity
  have hsq : ∀ j : Fin d,
      (x j / Real.sqrt (d : ℝ) - y j / Real.sqrt (d : ℝ)) ^ 2
        = (2 / (d : ℝ)) * (1 - x j * y j) := by
    intro j
    have hx1 := isSignVec_sq hx j
    have hy1 := isSignVec_sq hy j
    have e : (x j / Real.sqrt (d : ℝ) - y j / Real.sqrt (d : ℝ)) ^ 2
        = (x j ^ 2 - 2 * (x j * y j) + y j ^ 2) / (d : ℝ) := by
      rw [show x j / Real.sqrt (d : ℝ) - y j / Real.sqrt (d : ℝ)
          = (x j - y j) / Real.sqrt (d : ℝ) from by ring]
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
      have hnum : (x j - y j) ^ 2 = x j ^ 2 - 2 * (x j * y j) + y j ^ 2 := by ring
      rw [hnum]
    rw [e, hx1, hy1]; ring
  unfold vecDistSq innerVec
  simp only [hsq]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp only [nsmul_eq_mul]
  ring

/-- **Proposition 14, parameter scale (p. 9).**  With `‖A‖_F² = 2` and `‖b‖² = 2α²d`, and
`α²√d = 1` so that `‖b‖² = 2√d` and `ε = 1/n`, the product
`‖A‖_F⁴ ‖b‖⁴ ε⁻¹` equals `16 n d` — of the same order as the `Ω(nd)` hardness of
`n`-Gap-Hamming. -/
theorem clustering_bound_scale (d n : ℕ) (α : ℝ) (hn : 0 < n)
    (hαd : α ^ 2 * Real.sqrt (d : ℝ) = 1) :
    (2 : ℝ) ^ 2 * (2 * α ^ 2 * (d : ℝ)) ^ 2 * (1 / (1 / (n : ℝ)))
      = 16 * (n : ℝ) * (d : ℝ) := by
  have hd0 : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hkey : α ^ 2 * (d : ℝ) = Real.sqrt (d : ℝ) := by
    calc α ^ 2 * (d : ℝ) = α ^ 2 * (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) := by rw [hd0]
      _ = (α ^ 2 * Real.sqrt (d : ℝ)) * Real.sqrt (d : ℝ) := by ring
      _ = 1 * Real.sqrt (d : ℝ) := by rw [hαd]
      _ = Real.sqrt (d : ℝ) := one_mul _
  have hb : 2 * α ^ 2 * (d : ℝ) = 2 * Real.sqrt (d : ℝ) := by linarith [hkey]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  rw [hb]
  field_simp
  nlinarith [hd0]

/-- **Proposition 14, lower bound (p. 9).**  Composing the `Ω(nd)` hardness of
`n`-Gap-Hamming (Proposition 7, named hypothesis) with the Theorem 10 simulation bound
`6(T+n)log(qm)` yields `Ω(nd) = Ω̃(‖A‖_F⁴‖b‖⁴ε⁻¹)` for any `T`-query quantum-inspired
classical algorithm solving supervised clustering on this instance family. -/
theorem supervised_clustering_lower_bound (c : ℝ) (hGH : GapHammingHardness c) (hc : 0 ≤ c)
    (n d T q m : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (C : ℝ)
    (p : RandProtocol (n + 1) (GapHammingInput n d))
    (hs : p.Succeeds gapHammingAnswer (2 / 3 : ℚ))
    (hcost : (p.worstCost : ℝ) ≤ 6 * C * ((T : ℝ) + (n : ℝ)) * (logBits (q * m) : ℝ)) :
    (n : ℝ) * (d : ℝ) ≤ 6 * c * C * ((T : ℝ) + (n : ℝ)) * (logBits (q * m) : ℝ) := by
  calc (n : ℝ) * (d : ℝ) ≤ c * (p.worstCost : ℝ) := hGH n d hn hd p hs
    _ ≤ c * (6 * C * ((T : ℝ) + (n : ℝ)) * (logBits (q * m) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcost hc
    _ = 6 * c * C * ((T : ℝ) + (n : ℝ)) * (logBits (q * m) : ℝ) := by ring

end Qatlib.Papers.QInspired25.MainResults.Reductions
