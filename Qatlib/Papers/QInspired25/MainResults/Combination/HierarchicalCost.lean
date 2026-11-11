/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Chebyshev
import Qatlib.Papers.QInspired25.MainResults.Model.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Hierarchical sampling of a linear combination — Theorem 28 (pp. 16--17)

Fixed source: arXiv:2402.15686v3, Theorem 28 and its proof (pp. 16--17).

Player `P_i` holds `b^{(i)} ∈ ℝ^m`, the coordinator's vector is `b = Σ_i μ_i b^{(i)}`, and

`b̃_j := √(k Σ_{i=1}^k |μ_i b_j^{(i)}|²)`,

`φ_b := k Σ_i ‖μ_i b^{(i)}‖² / ‖b‖²`.

The paper proves:

* `‖b̃‖² = φ_b ‖b‖²` (`bTilde_frobSq`),
* `|b̃_j| ≥ |b_j|` for all `j` (`bTilde_abs_ge`),
* the step-(c) sampling identity
  `Σ_i (‖μ_i b^{(i)}‖² / Σ_j ‖μ_j b^{(j)}‖²) · (|b_j^{(i)}|² / ‖b^{(i)}‖²)
     = |b̃_j|² / ‖b̃‖²`
  (`sampling_identity`),
* hence `T` uses of `SQ(b)` cost `O(kTφ_b log(qm))` bits (`hierarchical_cost_bound`).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Combination

open Qatlib.Papers.QInspired25.MainResults.Model

/-- The coordinator's combined vector `b = Σ_i μ_i b^{(i)}` (Theorem 28, p. 16). -/
def combinedVec {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) : Fin m → ℝ :=
  fun j => ∑ i, μ i * b i j

/-- The vector `b̃` with `b̃_j = √(k Σ_i |μ_i b_j^{(i)}|²)` (Theorem 28, p. 17). -/
def bTilde {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) : Fin m → ℝ :=
  fun j => Real.sqrt ((k : ℝ) * ∑ i, (μ i * b i j) ^ 2)

/-- The amplification factor `φ_b = k Σ_i ‖μ_i b^{(i)}‖² / ‖b‖²` (Theorem 28, p. 16). -/
def phiB {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) : ℝ :=
  (k : ℝ) * (∑ i, ∑ j, (μ i * b i j) ^ 2) / frobSqFun (combinedVec μ b)

/-! ## §1. Basic properties of `b̃` -/

/-- `b̃_j²  = k Σ_i |μ_i b_j^{(i)}|²` (underlying the definition, Theorem 28, p. 17). -/
theorem bTilde_sq {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) (j : Fin m) :
    bTilde μ b j ^ 2 = (k : ℝ) * ∑ i, (μ i * b i j) ^ 2 := by
  unfold bTilde
  rw [Real.sq_sqrt]
  have : (0 : ℝ) ≤ ∑ i, (μ i * b i j) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

/-- The squared Frobenius norm of `b̃`, expanded: `‖b̃‖² = k Σ_i Σ_j |μ_i b_j^{(i)}|²`. -/
theorem bTilde_frobSq_expand {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) :
    frobSqFun (bTilde μ b) = (k : ℝ) * ∑ i, ∑ j, (μ i * b i j) ^ 2 := by
  unfold frobSqFun
  simp only [bTilde_sq]
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- **Theorem 28, `‖b̃‖² = φ_b ‖b‖²` (p. 17).**  (The identity holds for `b ≠ 0`, the only
case where `φ_b` is finite.) -/
theorem bTilde_frobSq {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ)
    (hb : frobSqFun (combinedVec μ b) ≠ 0) :
    frobSqFun (bTilde μ b) = phiB μ b * frobSqFun (combinedVec μ b) := by
  have hb' : (∑ j, (∑ i, μ i * b i j) ^ 2) ≠ 0 := by
    simpa [frobSqFun, combinedVec] using hb
  rw [bTilde_frobSq_expand]
  unfold phiB
  simp only [frobSqFun, combinedVec]
  rw [div_mul_cancel₀ _ hb']

/-- **Theorem 28, `|b̃_j| ≥ |b_j|` (p. 17).**  Cauchy--Schwarz in the form
`(Σ_i x_i)² ≤ k Σ_i x_i²` gives the pointwise domination. -/
theorem bTilde_abs_ge {k m : ℕ} (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) (j : Fin m) :
    |combinedVec μ b j| ≤ |bTilde μ b j| := by
  have hsq : (combinedVec μ b j) ^ 2 ≤ (bTilde μ b j) ^ 2 := by
    rw [bTilde_sq]
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => μ i * b i j)
    simpa [combinedVec, Finset.card_univ, Fintype.card_fin] using h
  calc |combinedVec μ b j| = Real.sqrt ((combinedVec μ b j) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((bTilde μ b j) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |bTilde μ b j| := Real.sqrt_sq_eq_abs _

/-! ## §2. The step-(c) sampling identity -/

/-- **Theorem 28, step (2.c) (p. 17).**  Sampling `i` with probability
`‖μ_i b^{(i)}‖² / Σ_j ‖μ_j b^{(j)}‖²` and then `j` from `b^{(i)}` gives the `b̃`-law:

`Σ_i (‖μ_i b^{(i)}‖²/Σ_t ‖μ_t b^{(t)}‖²) · (b_j^{(i)}²/‖b^{(i)}‖²) = b̃_j²/‖b̃‖²`. -/
theorem sampling_identity (k m : ℕ) (μ : Fin k → ℝ) (b : Fin k → Fin m → ℝ) (j : Fin m)
    (hM : ∀ i, frobSqFun (b i) ≠ 0)
    (hS : (∑ i, (μ i) ^ 2 * frobSqFun (b i)) ≠ 0) :
    (∑ i, ((μ i) ^ 2 * frobSqFun (b i) / (∑ t, (μ t) ^ 2 * frobSqFun (b t)))
        * ((b i j) ^ 2 / frobSqFun (b i)))
      = (∑ i, (μ i * b i j) ^ 2) / (∑ t, (μ t) ^ 2 * frobSqFun (b t)) := by
  set S : ℝ := ∑ t, (μ t) ^ 2 * frobSqFun (b t) with hSdef
  have hterm : ∀ i, ((μ i) ^ 2 * frobSqFun (b i) / S) * ((b i j) ^ 2 / frobSqFun (b i))
      = (μ i * b i j) ^ 2 / S := by
    intro i
    have hMi : frobSqFun (b i) ≠ 0 := hM i
    have hS' : S ≠ 0 := hS
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_div]

/-! ## §3. Communication cost: `O(kT φ_b log(qm))` -/

/-- Communication for `T` coordinator uses of `SQ(b)` before amplification:
`T log q + kT log(qm)` bits (Theorem 28, p. 17). -/
def hierarchicalOracleCost (k T q m : ℕ) : ℕ :=
  T * logBits q + k * T * logBits (q * m)

/-- **Theorem 28, oracle cost (p. 17).**  `T log q + kT log(qm) ≤ 2kT log(qm)`, i.e. the
pre-amplification cost is `O(kT log(qm))`. -/
theorem hierarchicalOracleCost_le (k T q m : ℕ) (hk : 0 < k) (hT : 0 < T)
    (hq : 0 < q) (hm : 0 < m) :
    hierarchicalOracleCost k T q m ≤ 2 * k * T * logBits (q * m) := by
  have hL : logBits q ≤ logBits (q * m) := logBits_mono (Nat.le_mul_of_pos_right q hm)
  have h1 : T * logBits q ≤ k * T * logBits (q * m) := by
    have hTle : T ≤ k * T := by
      calc T = 1 * T := (one_mul T).symm
        _ ≤ k * T := Nat.mul_le_mul_right T hk
    calc T * logBits q ≤ T * logBits (q * m) := Nat.mul_le_mul_left T hL
      _ ≤ k * T * logBits (q * m) := Nat.mul_le_mul_right _ hTle
  unfold hierarchicalOracleCost
  calc T * logBits q + k * T * logBits (q * m)
      = T * logBits q + (k * T) * logBits (q * m) := rfl
    _ ≤ (k * T) * logBits (q * m) + (k * T) * logBits (q * m) :=
        Nat.add_le_add_right h1 _
    _ = 2 * k * T * logBits (q * m) := by ring

/-- Total communication for `T` uses of `SQ(b)`: `φ_b` amplified oracle cost
(Theorem 28, p. 17). -/
def hierarchicalCost (k T q m : ℕ) (φ : ℝ) : ℝ :=
  φ * (hierarchicalOracleCost k T q m : ℝ)

/-- **Theorem 28, main cost bound (p. 16).**  For the coordinator to use `SQ(b)` `T` times it
costs `O(kT φ_b log(qm))` bits of communication; here
`φ_b (T log q + kT log(qm)) ≤ 2 φ_b kT log(qm)`. -/
theorem hierarchical_cost_bound (k T q m : ℕ) (hk : 0 < k) (hT : 0 < T)
    (hq : 0 < q) (hm : 0 < m) (φ : ℝ) (hφ : 0 ≤ φ) :
    hierarchicalCost k T q m φ
      ≤ 2 * φ * (k : ℝ) * (T : ℝ) * (logBits (q * m) : ℝ) := by
  have h := hierarchicalOracleCost_le k T q m hk hT hq hm
  have h' : ((hierarchicalOracleCost k T q m : ℕ) : ℝ)
      ≤ 2 * (k : ℝ) * (T : ℝ) * (logBits (q * m) : ℝ) := by
    exact_mod_cast h
  unfold hierarchicalCost
  calc φ * ((hierarchicalOracleCost k T q m : ℕ) : ℝ)
      ≤ φ * (2 * (k : ℝ) * (T : ℝ) * (logBits (q * m) : ℝ)) :=
        mul_le_mul_of_nonneg_left h' hφ
    _ = 2 * φ * (k : ℝ) * (T : ℝ) * (logBits (q * m) : ℝ) := by ring

end Qatlib.Papers.QInspired25.MainResults.Combination
