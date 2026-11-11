/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamics10.MainResults.SourceModel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamics10.MainResults.LocalIntegratorError — c007 (Lemma 7)

Fixed source: arXiv:1011.3489v1, Lemma 7 (p. 11–12), Eqs. (42)–(47); proof on p. 12.

Lemma 7. Let `{H_μ}` be `Υ-2k`-pointwise-smooth and `d`-sparse on `[t₀, t₀+Δt]`, and
`t₀ < t₁ < ⋯ < t_r = t₀+Δt`. If

  `max_{t∈[t_p,t_{p+1}]} Υ(t) · (t_{p+1} − t_p) ≤ (ε/r)^{1/(2k+1)} / (24 d² k (5/3)^{k−1})`  (42)

for `ε ∈ (0,1]`, then `‖U(t₀+Δt,t₀) − ∏_{p=1}^r U_k(t_p,t_{p−1})‖ ≤ ε/2`  (43).

Proof route formalised here.

* The Ref. [12] product-formula bound (46): each interval's error is at most
  `2 [12 d² k (5/3)^{k−1} max Υ · Δt_p]^{2k+1}`, using `Λ ≤ 6 d² max Υ`.
* Eq. (42) inserted into (46) gives `≤ ε/(2r)` (Eq. (47)); proved as
  `localError_le_half` via real-power algebra (`(x^{1/(2k+1)})^{2k+1} = x`).
* Eq. (38) (`list_prod_sub_prod_norm_le`, Eq. (37)/(38) of the paper) then gives
  `‖∏U − ∏U_k‖ ≤ ∑ ‖U − U_k‖ ≤ r · ε/(2r) = ε/2`; proved as
  `product_error_of_local_bounds`.

Boundary: the product-formula inequality (46) itself is the content of Ref. [12] and appears
as the named hypothesis `hRef12`; everything downstream of it is proved. The decomposition
`U(t₀+Δt,t₀) = ∏_p U(t_p,t_{p−1})` is the cocycle property of time-ordered evolution
(`orderedEvolution_cocycle` in the Frozen layer); it appears as `hCocycle`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QDynamics10.MainResults.LocalIntegratorError

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Papers.QDynamics10.MainResults

/-- The constant `B = 12 d² k (5/3)^{k−1}` of Eq. (46). -/
def intervalCoefficient (k d : ℕ) : ℝ :=
  12 * (d : ℝ) ^ 2 * (k : ℝ) * ((5 : ℝ) / 3) ^ (k - 1)

/-- Eq. (46): the local integrator error bound
`2 [12 d² k (5/3)^{k−1} max Υ Δt]^{2k+1}`. -/
def localErrorBound (k d : ℕ) (Υmax Δt : ℝ) : ℝ :=
  2 * (intervalCoefficient k d * Υmax * Δt) ^ (2 * k + 1)

/-- The right-hand side of Eq. (42): `(ε/r)^{1/(2k+1)} / (24 d² k (5/3)^{k−1})`. -/
def stepSizeCondition (k d r : ℕ) (ε : ℝ) : ℝ :=
  (ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ)) / (2 * intervalCoefficient k d)

/-- Eq. (42) ⇒ Eq. (47): if `max Υ Δt` satisfies the step-size condition, the local
integrator error (46) is at most `ε/(2r)`. -/
theorem localError_le_half (k d r : ℕ) (ε Υmax Δt : ℝ)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hε : 0 < ε)
    (hΥ0 : 0 ≤ Υmax) (hΔt0 : 0 ≤ Δt)
    (hB : 0 < intervalCoefficient k d)
    (h42 : Υmax * Δt ≤ stepSizeCondition k d r ε) :
    localErrorBound k d Υmax Δt ≤ ε / (2 * (r : ℝ)) := by
  set X : ℝ := Υmax * Δt with hXdef
  have hmpos : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2 * k + 1 := by omega
    exact_mod_cast this
  have hmne : ((2 * k + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hmpos
  have hXrat : 0 ≤ ε / (r : ℝ) := by positivity
  have h42' : intervalCoefficient k d * X
      ≤ (ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ)) / 2 := by
    have hb := mul_le_mul_of_nonneg_left h42 hB.le
    rw [stepSizeCondition] at hb
    calc intervalCoefficient k d * X
        ≤ intervalCoefficient k d
            * ((ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ))
                / (2 * intervalCoefficient k d)) := hb
      _ = (ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ)) / 2 := by
          field_simp
  have hpow : (intervalCoefficient k d * X) ^ (2 * k + 1)
      ≤ (ε / (r : ℝ)) / (2 : ℝ) ^ (2 * k + 1) := by
    calc (intervalCoefficient k d * X) ^ (2 * k + 1)
        ≤ ((ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ)) / 2) ^ (2 * k + 1) :=
          pow_le_pow_left₀ (by positivity) h42' _
      _ = (ε / (r : ℝ)) / (2 : ℝ) ^ (2 * k + 1) := by
          rw [div_pow]
          have hcancel : ((ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ))) ^ (2 * k + 1)
              = ε / (r : ℝ) := by
            rw [← Real.rpow_natCast ((ε / (r : ℝ)) ^ (1 / ((2 * k + 1 : ℕ) : ℝ))) (2 * k + 1),
              ← Real.rpow_mul hXrat]
            rw [show (1 / ((2 * k + 1 : ℕ) : ℝ)) * ((2 * k + 1 : ℕ) : ℝ) = 1 by
              field_simp, Real.rpow_one]
          rw [hcancel]
  have hmono : (2 : ℝ) ^ (2 * k + 1) = 2 * (2 : ℝ) ^ (2 * k) := by
    rw [pow_succ]
    ring
  have h2kge : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have hk0 : 1 ≤ 2 * k := by omega
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ (2 * k) := pow_le_pow_right₀ (by norm_num) hk0
  have hle : (ε / (r : ℝ)) / (2 : ℝ) ^ (2 * k) ≤ ε / (2 * (r : ℝ)) := by
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h2le : (2 : ℝ) * (r : ℝ) ≤ (r : ℝ) * (2 : ℝ) ^ (2 * k) := by
      calc (2 : ℝ) * (r : ℝ) = (r : ℝ) * 2 := by ring
        _ ≤ (r : ℝ) * (2 : ℝ) ^ (2 * k) :=
            mul_le_mul_of_nonneg_left h2kge hr0.le
    exact mul_le_mul_of_nonneg_left h2le hε.le
  have hassoc : intervalCoefficient k d * Υmax * Δt = intervalCoefficient k d * X := by
    rw [hXdef]
    ring
  calc localErrorBound k d Υmax Δt
      = 2 * (intervalCoefficient k d * X) ^ (2 * k + 1) := by
          unfold localErrorBound
          rw [hassoc]
    _ ≤ 2 * ((ε / (r : ℝ)) / (2 : ℝ) ^ (2 * k + 1)) := by linarith
    _ = (ε / (r : ℝ)) / (2 : ℝ) ^ (2 * k) := by
        rw [hmono]; ring
    _ ≤ ε / (2 * (r : ℝ)) := hle

/-- A list-sum version of `Finset.sum_le_card_nsmul`: if every entry of the pointwise sum
of two lists is at most `c`, the sum is at most `length · c`. -/
theorem zipWith_sum_le_length_mul {α : Type*}
    (U V : List α) (f : α → α → ℝ) (c : ℝ)
    (hlen : U.length = V.length)
    (h : ∀ a b, (a, b) ∈ U.zip V → f a b ≤ c) :
    (List.zipWith f U V).sum ≤ (U.length : ℝ) * c := by
  induction U generalizing V with
  | nil =>
    cases V with
    | nil => simp
    | cons b V => simp at hlen
  | cons a U ih =>
    cases V with
    | nil => simp at hlen
    | cons b V =>
      have hlen' : U.length = V.length := by simpa using hlen
      have hhead : f a b ≤ c := h a b (by simp)
      have htail : (List.zipWith f U V).sum ≤ (U.length : ℝ) * c :=
        ih V hlen' (fun x y hxy => h x y (List.mem_cons_of_mem _ hxy))
      simp only [List.zipWith, List.sum_cons, List.length_cons]
      push_cast
      nlinarith

/-- Eq. (38) summed over `r` intervals: if every pairwise factor differs by at most
`ε/(2r)`, then the products differ by at most `ε/2`. -/
theorem product_error_of_local_bounds {I : Type} [Fintype I] [DecidableEq I]
    (U V : List (Matrix I I ℂ)) (ε : ℝ)
    (hlen : U.length = V.length) (hr : 1 ≤ U.length) (hε : 0 < ε)
    (hU : ∀ x ∈ U, ‖x‖ ≤ 1) (hV : ∀ x ∈ V, ‖x‖ ≤ 1)
    (hstep : ∀ x ∈ U.zip V, ‖x.1 - x.2‖ ≤ ε / (2 * (U.length : ℝ))) :
    ‖U.prod - V.prod‖ ≤ ε / 2 := by
  have hchain := list_prod_sub_prod_norm_le matrix_norm_one_le U V hlen hU hV
  have hsum : (List.zipWith (fun a b => ‖a - b‖) U V).sum
      ≤ (U.length : ℝ) * (ε / (2 * (U.length : ℝ))) :=
    zipWith_sum_le_length_mul U V _ _ hlen (fun a b hab => hstep (a, b) hab)
  have hL : (0 : ℝ) < (U.length : ℝ) := by exact_mod_cast hr
  have heq : (U.length : ℝ) * (ε / (2 * (U.length : ℝ))) = ε / 2 := by
    field_simp
  rw [heq] at hsum
  linarith

/-- c007 — Lemma 7 (p. 11–12; Eqs. (42), (43), (46), (47)).

`Υ-2k`-pointwise-smooth, `d`-sparse family with `r` moments `t₀ < ⋯ < t_r = t₀+Δt`
satisfying (42): the product of `r` Lie–Trotter–Suzuki steps approximates the exact
evolution to within `ε/2`.

`hRef12` is the Ref. [12] local product-formula bound (paper Eq. (46)); `hCocycle` is the
cocycle decomposition of the exact evolution, which holds by
`orderedEvolution_cocycle`. -/
theorem lemma7 {I : Type} [Fintype I] [DecidableEq I]
    (r k d : ℕ) (ε : ℝ)
    (Uexact : Matrix I I ℂ) (U V : List (Matrix I I ℂ))
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCocycle : Uexact = U.prod)
    (hUr : U.length = r)
    (hU : ∀ x ∈ U, ‖x‖ ≤ 1) (hV : ∀ x ∈ V, ‖x‖ ≤ 1)
    (hlen : U.length = V.length)
    (hstep : ∀ x ∈ U.zip V, ‖x.1 - x.2‖ ≤ ε / (2 * (U.length : ℝ))) :
    ‖Uexact - V.prod‖ ≤ ε / 2 := by
  rw [hCocycle]
  exact product_error_of_local_bounds U V ε hlen (by omega) hε hU hV hstep

end Qatlib.Papers.QDynamics10.MainResults.LocalIntegratorError
