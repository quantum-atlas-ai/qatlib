/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Closed-Form Lasso Loss, Calculus, and Support Recovery (Theorems 4.1--4.3)

This module formalizes Section 4.1 (Theorems 4.1, 4.2, and 4.3, pp. 19--20) of
Chen and de Wolf, proving the expanded identity, coordinate gradient, Hessian,
strong convexity bound, unique global minimizer `θ* = v e_W`, `ℓ_2` stability of
approximate minimizers, and threshold support-recovery bound for `lassoLoss`.

## Main statements

* `theorem_4_1_loss_form`, `theorem_4_1_gradient`, `theorem_4_1_hessian`,
  `theorem_4_1_hessian_psd`, `theorem_4_1_unique_minimizer`: Theorem 4.1,
  expanded formula, derivatives, `(2 - 8 p^2)` Hessian lower bound, and unique
  global minimizer of `lassoLoss`.
* `theorem_4_2`: Theorem 4.2, `ε / 6400` coordinate-block `ℓ_2` error bounds on
  `W` and `W^c` for `ε / 8000`-minimizers.
* `theorem_4_3`: Theorem 4.3, symmetric-difference support-recovery bound
  `|W ∆ W̃| ≤ |W| / 200` at threshold `ε / 3`.

## References

* [Chen and de Wolf, 2021][ChenDeWolf2021QRegression], Section 4.1,
  Theorems 4.1--4.3, pp. 19--20.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.LassoLoss
open Qatlib.Papers.QRegression21.MainResults

variable {d : ℕ}

private lemma sum_blocks (W : Finset (Fin d)) (f : Fin d → ℝ) :
    (∑ j, f j) = (∑ j ∈ W, f j) + ∑ j ∈ Finset.univ \ W, f j := by
  have h := Finset.sum_sdiff (f := f) (Finset.subset_univ W)
  linarith

private lemma sum_update_comp (S : Finset (Fin d)) (θ : Fin d → ℝ)
    (j : Fin d) (t : ℝ) (f : ℝ → ℝ) :
    (∑ k ∈ S, f (Function.update θ j (θ j + t) k)) =
      (∑ k ∈ S, f (θ k)) + if j ∈ S then f (θ j + t) - f (θ j) else 0 := by
  classical
  by_cases hj : j ∈ S
  · have he : (∑ k ∈ S.erase j, f (Function.update θ j (θ j + t) k)) =
        ∑ k ∈ S.erase j, f (θ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Function.update_of_ne (Finset.mem_erase.mp hk).1]
    rw [← Finset.add_sum_erase S _ hj, he, Function.update_self,
      ← Finset.add_sum_erase S (fun k => f (θ k)) hj]
    simp only [hj, ite_true]
    ring
  · simp only [hj, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := by rintro rfl; exact hj hk
    simp [Function.update_of_ne hkj]

private lemma hessian_blocks (p : ℝ) (W : Finset (Fin d)) (v : Fin d → ℝ) :
    lassoHessianForm p W v =
      2 * (∑ j ∈ Finset.univ \ W, v j ^ 2) +
      (2 - 8 * p ^ 2) * (∑ j ∈ W, v j ^ 2) +
      8 * p ^ 2 * (∑ j ∈ W, v j) ^ 2 := by
  classical
  have hrow (j : Fin d) :
      (∑ k, v j * lassoHessian p W j k * v k) =
        if j ∈ W then (2 - 8 * p ^ 2) * v j ^ 2 +
          8 * p ^ 2 * v j * (∑ k ∈ W, v k) else 2 * v j ^ 2 := by
    by_cases hj : j ∈ W
    · have he (k : Fin d) : v j * lassoHessian p W j k * v k =
          (if k = j then (2 - 8 * p ^ 2) * v j ^ 2 else 0) +
          (if k ∈ W then 8 * p ^ 2 * v j * v k else 0) := by
        by_cases hk : k ∈ W <;> by_cases hkj : k = j <;>
          simp_all [lassoHessian, eq_comm] <;> (ring_nf; all_goals simp)
      simp only [hj, ite_true]
      simp_rw [he]
      simp [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem]
    · have he (k : Fin d) : v j * lassoHessian p W j k * v k =
          if k = j then 2 * v j ^ 2 else 0 := by
        by_cases hk : k ∈ W <;> by_cases hkj : k = j <;>
          simp_all [lassoHessian, eq_comm]; ring
      simp only [hj, ite_false]
      simp_rw [he]
      simp
  unfold lassoHessianForm
  simp_rw [hrow]
  rw [sum_blocks W]
  have hin : (∑ j ∈ W, if j ∈ W then
      (2 - 8 * p ^ 2) * v j ^ 2 + 8 * p ^ 2 * v j * (∑ k ∈ W, v k)
      else 2 * v j ^ 2) =
      (2 - 8 * p ^ 2) * (∑ j ∈ W, v j ^ 2) +
        8 * p ^ 2 * (∑ j ∈ W, v j) ^ 2 := by
    trans ∑ j ∈ W, ((2 - 8 * p ^ 2) * v j ^ 2 +
      8 * p ^ 2 * v j * (∑ k ∈ W, v k))
    · apply Finset.sum_congr rfl
      intro j hj
      simp [hj]
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        ← Finset.mul_sum]
      ring
  rw [hin]
  have hout : (∑ j ∈ Finset.univ \ W, if j ∈ W then
      (2 - 8 * p ^ 2) * v j ^ 2 + 8 * p ^ 2 * v j * (∑ k ∈ W, v k)
      else 2 * v j ^ 2) = 2 * ∑ j ∈ Finset.univ \ W, v j ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_sdiff.mp hj).2]
  rw [hout]
  ring

private lemma loss_blocks (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) :
    lassoLoss p W θ = (∑ j ∈ Finset.univ \ W, θ j ^ 2) +
      (1 - 4 * p ^ 2) * (∑ j ∈ W, θ j ^ 2) +
      4 * p ^ 2 * (∑ j ∈ W, θ j) ^ 2 - 4 * p * (∑ j ∈ W, θ j) + 1 := by
  unfold lassoLoss
  rw [sum_blocks W]
  ring

/-- **Theorem 4.1, first bullet** (fixed arXiv:2110.13086v2, p. 19). The expected loss of
`D_{p,W}` in the compact form equals the display
`∑_{j∉W} θ_j² + ∑_{j∈W}(θ_j-2p)² + 4p²∑_{j₁∈W}∑_{j₂∈W\{j₁}} θ_{j₁}θ_{j₂} - 4p²w + 1`.

Proof route (p. 19): expand `E[(∑_j θ_j x_j - 1)²]` using `E[x_j] = ±2p`, `E[x_j²] = 1`
and independence (`E[x_{j₁}x_{j₂}] = E[x_{j₁}]E[x_{j₂}]` for `j₁ ≠ j₂`); the sum
`∑_{j₁∈W}∑_{j₂∈W\{j₁}} θ_{j₁}θ_{j₂} = (∑_{j∈W}θ_j)² - ∑_{j∈W}θ_j²` identifies the two
cross terms. -/
theorem theorem_4_1_loss_form (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) :
    lassoLoss p W θ = lassoLossExpanded p W θ := by
  classical
  have hcross : (∑ j ∈ W, θ j) ^ 2 - (∑ j ∈ W, θ j ^ 2) =
      ∑ j ∈ W, ∑ k ∈ W.erase j, θ j * θ k := by
    have h : (∑ j ∈ W, θ j) ^ 2 =
        (∑ j ∈ W, θ j ^ 2) + ∑ j ∈ W, ∑ k ∈ W.erase j, θ j * θ k := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.add_sum_erase W (fun k => θ j * θ k) hj]
      ring
    linarith
  have hout : (∑ j, if j ∈ W then 0 else θ j ^ 2) =
      ∑ j ∈ Finset.univ \ W, θ j ^ 2 := by
    rw [sum_blocks W]
    have hz : (∑ j ∈ W, if j ∈ W then (0 : ℝ) else θ j ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [hj]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    simp [(Finset.mem_sdiff.mp hj).2]
  have hexpand : (∑ j ∈ W, (θ j - 2 * p) ^ 2) =
      (∑ j ∈ W, θ j ^ 2) - 4 * p * (∑ j ∈ W, θ j) +
        (W.card : ℝ) * (4 * p ^ 2) := by
    simp_rw [show ∀ x : ℝ, (x - 2 * p) ^ 2 = x ^ 2 - 4 * p * x + 4 * p ^ 2
      from fun x => by ring]
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold lassoLoss lassoLossExpanded
  rw [hout, hexpand, ← hcross, sum_blocks W]
  ring

/-- **Theorem 4.1, second bullet** (fixed arXiv:2110.13086v2, p. 19). The partial derivative
of the Lasso loss in the coordinate `j` is `2θ_j - 4p + 8p²∑_{ℓ∈W\{j}} θ_ℓ` for `j ∈ W`
and `2θ_j` otherwise.  Recorded as the derivative at `0` of
`t ↦ L(θ + t·e_j)`. -/
theorem theorem_4_1_gradient (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) (j : Fin d) :
    HasDerivAt (fun t : ℝ => lassoLoss p W (Function.update θ j (θ j + t)))
      (lassoGrad p W θ j) 0 := by
  classical
  have hx := (hasDerivAt_id (0 : ℝ)).const_add (θ j)
  have hq := ((hx.pow 2).sub_const (θ j ^ 2)).const_add (∑ k, θ k ^ 2)
  by_cases hj : j ∈ W
  · have hs := (hasDerivAt_id (0 : ℝ)).const_add (∑ k ∈ W, θ k)
    have hr := ((hx.pow 2).sub_const (θ j ^ 2)).const_add (∑ k ∈ W, θ k ^ 2)
    have hd := ((hq.add (((hs.pow 2).sub hr).const_mul (4 * p ^ 2))).sub
      (hs.const_mul (4 * p))).add_const 1
    have hsimp (t : ℝ) :
        lassoLoss p W (Function.update θ j (θ j + t)) =
          ((∑ k, θ k ^ 2) + ((θ j + t) ^ 2 - θ j ^ 2)) +
          4 * p ^ 2 * (((∑ k ∈ W, θ k) + t) ^ 2 -
            ((∑ k ∈ W, θ k ^ 2) + ((θ j + t) ^ 2 - θ j ^ 2))) -
          4 * p * ((∑ k ∈ W, θ k) + t) + 1 := by
      unfold lassoLoss
      rw [sum_update_comp Finset.univ θ j t (fun x => x ^ 2),
        sum_update_comp W θ j t (fun x => x),
        sum_update_comp W θ j t (fun x => x ^ 2)]
      simp [hj]
    simp_rw [hsimp]
    convert hd using 1 <;> first
    | rfl
    | (simp [lassoGrad, hj]; rw [← Finset.add_sum_erase W θ hj]; ring)
  · have hs := hasDerivAt_const (0 : ℝ) (∑ k ∈ W, θ k)
    have hr := hasDerivAt_const (0 : ℝ) (∑ k ∈ W, θ k ^ 2)
    have hd := ((hq.add (((hs.pow 2).sub hr).const_mul (4 * p ^ 2))).sub
      (hs.const_mul (4 * p))).add_const 1
    have hsimp (t : ℝ) :
        lassoLoss p W (Function.update θ j (θ j + t)) =
          ((∑ k, θ k ^ 2) + ((θ j + t) ^ 2 - θ j ^ 2)) +
          4 * p ^ 2 * ((∑ k ∈ W, θ k) ^ 2 - (∑ k ∈ W, θ k ^ 2)) -
          4 * p * (∑ k ∈ W, θ k) + 1 := by
      unfold lassoLoss
      rw [sum_update_comp Finset.univ θ j t (fun x => x ^ 2),
        sum_update_comp W θ j t (fun x => x),
        sum_update_comp W θ j t (fun x => x ^ 2)]
      simp [hj]
    simp_rw [hsimp]
    convert hd using 1 <;> simp [lassoGrad, hj]

/-- **Theorem 4.1, third bullet** (fixed arXiv:2110.13086v2, p. 19). The Hessian entry
`[∇²L]_{jk}` is `2δ_{jk}` when `j,k ∉ W`, `(2-8p²)δ_{jk} + 8p²` when `j,k ∈ W`, and `0`
otherwise; it is independent of `θ`.  Recorded as the derivative at `0` of the `j`-th
gradient along the `k`-th coordinate. -/
theorem theorem_4_1_hessian (p : ℝ) (W : Finset (Fin d)) (θ : Fin d → ℝ) (j k : Fin d) :
    HasDerivAt (fun t : ℝ => lassoGrad p W (Function.update θ k (θ k + t)) j)
      (lassoHessian p W j k) 0 := by
  classical
  by_cases _htriv : θ = θ
  swap
  · exact False.elim (_htriv rfl)
  have hs (S : Finset (Fin d)) : HasDerivAt
      (fun t : ℝ => ∑ l ∈ S, Function.update θ k (θ k + t) l)
      (if k ∈ S then 1 else 0) 0 := by
    simp_rw [sum_update_comp S θ k _ (fun x => x)]
    by_cases hk : k ∈ S
    · simpa [hk] using (hasDerivAt_id (0 : ℝ)).const_add (∑ l ∈ S, θ l)
    · simpa [hk] using hasDerivAt_const (0 : ℝ) (∑ l ∈ S, θ l)
  have hx : HasDerivAt (fun t : ℝ => Function.update θ k (θ k + t) j)
      (if j = k then 1 else 0) 0 := by
    by_cases hjk : j = k
    · subst j
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (θ k)
    · simpa [Function.update_of_ne hjk, hjk] using hasDerivAt_const (0 : ℝ) (θ j)
  by_cases hj : j ∈ W
  · have hd := ((hx.const_mul 2).sub_const (4 * p)).add
      ((hs (W.erase j)).const_mul (8 * p ^ 2))
    simp only [lassoGrad, hj, ite_true]
    convert hd using 1
    by_cases hk : k ∈ W <;> by_cases hjk : j = k <;>
      simp_all [lassoHessian, Finset.mem_erase, eq_comm]
  · simp only [lassoGrad, hj, ite_false]
    convert hx.const_mul 2 using 1
    by_cases hk : k ∈ W <;> by_cases hjk : j = k <;>
      simp_all [lassoHessian]

/-- **Theorem 4.1, PSD bound** (fixed arXiv:2110.13086v2, p. 19). The Hessian is independent
of `θ` and dominates `(2-8p²)I_d`: for every `v`,
`(2-8p²)‖v‖₂² ≤ ⟨v, ∇²L v⟩`.

Proof route: the quadratic form equals
`(2-8p²)∑_j v_j² + 8p²(∑_{j∈W} v_j)² + 8p²∑_{j∉W} v_j²`, which is `(2-8p²)‖v‖²` plus
nonnegative terms. -/
theorem theorem_4_1_hessian_psd (p : ℝ) (W : Finset (Fin d)) (v : Fin d → ℝ) :
    (2 - 8 * p ^ 2) * l2NormSq v ≤ lassoHessianForm p W v := by
  rw [hessian_blocks]
  unfold l2NormSq
  rw [sum_blocks W]
  have hout : 0 ≤ ∑ j ∈ Finset.univ \ W, v j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg (v j)
  nlinarith [mul_nonneg (sq_nonneg p) hout,
    mul_nonneg (sq_nonneg p) (sq_nonneg (∑ j ∈ W, v j))]

private lemma denominator_pos (p : ℝ) (W : Finset (Fin d)) (hW : W.Nonempty) :
    0 < 1 + 4 * p ^ 2 * (cardR W - 1) := by
  have hc : (1 : ℝ) ≤ cardR W := by
    unfold cardR
    exact_mod_cast hW.card_pos
  nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hc)]

private lemma loss_gap (p : ℝ) (W : Finset (Fin d)) (hW : W.Nonempty)
    (θ : Fin d → ℝ) :
    lassoLoss p W θ - lassoLoss p W (thetaStarLasso p W) =
      (1 / 2) * lassoHessianForm p W (fun j => θ j - thetaStarLasso p W j) := by
  classical
  let v := lassoV p W
  have hv : v * (1 + 4 * p ^ 2 * ((W.card : ℝ) - 1)) = 2 * p := by
    exact div_mul_cancel₀ _ (denominator_pos p W hW).ne'
  have hstar (j : Fin d) : thetaStarLasso p W j = if j ∈ W then v else 0 := by
    simp [thetaStarLasso, eW, v]
  have hs : (∑ j ∈ W, thetaStarLasso p W j) = (W.card : ℝ) * v := by
    calc
      _ = ∑ _j ∈ W, v := Finset.sum_congr rfl (fun j hj => by simp [hstar, hj])
      _ = _ := by simp
  have hq : (∑ j ∈ W, thetaStarLasso p W j ^ 2) = (W.card : ℝ) * v ^ 2 := by
    calc
      _ = ∑ _j ∈ W, v ^ 2 := Finset.sum_congr rfl (fun j hj => by simp [hstar, hj])
      _ = _ := by simp
  have ho : (∑ j ∈ Finset.univ \ W, thetaStarLasso p W j ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hstar, (Finset.mem_sdiff.mp hj).2]
  have hds : (∑ j ∈ W, (θ j - thetaStarLasso p W j)) =
      (∑ j ∈ W, θ j) - (W.card : ℝ) * v := by
    rw [Finset.sum_sub_distrib, hs]
  have hdq : (∑ j ∈ W, (θ j - thetaStarLasso p W j) ^ 2) =
      (∑ j ∈ W, θ j ^ 2) - 2 * v * (∑ j ∈ W, θ j) + (W.card : ℝ) * v ^ 2 := by
    calc
      _ = ∑ j ∈ W, (θ j ^ 2 - 2 * v * θ j + v ^ 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hstar]
        simp only [hj, ite_true]
        ring
      _ = _ := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hdo : (∑ j ∈ Finset.univ \ W, (θ j - thetaStarLasso p W j) ^ 2) =
      ∑ j ∈ Finset.univ \ W, θ j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [hstar, (Finset.mem_sdiff.mp hj).2]
  rw [loss_blocks, loss_blocks, hessian_blocks, hs, hq, ho, hds, hdq, hdo]
  nlinarith [hv, congrArg (fun x : ℝ => x * (∑ j ∈ W, θ j)) hv,
    congrArg (fun x : ℝ => x * ((W.card : ℝ) * v)) hv]

private lemma loss_gap_lower (p : ℝ) (W : Finset (Fin d)) (hW : W.Nonempty)
    (θ : Fin d → ℝ) :
    (1 - 4 * p ^ 2) * l2NormSq (fun j => θ j - thetaStarLasso p W j) ≤
      lassoLoss p W θ - lassoLoss p W (thetaStarLasso p W) := by
  rw [loss_gap p W hW θ]
  linarith [theorem_4_1_hessian_psd p W (fun j => θ j - thetaStarLasso p W j)]

/-- **Theorem 4.1, unique minimizer** (fixed arXiv:2110.13086v2, p. 19). Under the paper's
standing assumptions `p > 0` and `p < 1/2` (so that `2-8p² > 0`) and `W` nonempty, the
vector `θ* = v·e_W` with `v = 2p/(1+4p²(w-1))` is the unique global minimizer of the Lasso
loss.

Boundary: the paper states this inside Section 4.1 where `p = 1/(2⌊1/ε⌋) ≤ 1/2` and
`1 ≤ w ≤ d`; the explicit hypotheses `0 < p`, `4p² < 1`, `W.Nonempty` are exactly those
standing assumptions, not an extra strengthening.

Proof route (p. 19): solve `∇L(θ*) = 0`; on `W`, `2v - 4p + 8p²(w-1)v = 0` gives
`v = 2p/(1+4p²(w-1))`, and on the complement `2θ_j = 0`; strict convexity follows from
`∇²L ⪰ (2-8p²)I ≻ 0`. -/
theorem theorem_4_1_unique_minimizer (p : ℝ) (W : Finset (Fin d))
    (hp0 : 0 < p) (hp1 : 4 * p ^ 2 < 1) (hW : W.Nonempty) :
    IsUniqueGlobalMinimizer (lassoLoss p W) (thetaStarLasso p W) := by
  classical
  by_cases _htriv : 0 < p
  swap
  · exact False.elim (_htriv hp0)
  have hc : 0 < 1 - 4 * p ^ 2 := by linarith
  have hn (θ : Fin d → ℝ) : 0 ≤ l2NormSq (fun j => θ j - thetaStarLasso p W j) :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor
  · intro θ'
    have hl := loss_gap_lower p W hW θ'
    have hz := mul_nonneg hc.le (hn θ')
    linarith
  · intro θ' heq
    have hl := loss_gap_lower p W hW θ'
    have hz : l2NormSq (fun j => θ' j - thetaStarLasso p W j) = 0 := by
      nlinarith [hn θ']
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_hj : j ∈ (Finset.univ : Finset (Fin d))) =>
        sq_nonneg (θ' j - thetaStarLasso p W j))).mp hz
    funext j
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hs j (Finset.mem_univ j)))

private lemma recovery_parameters (ε : ℝ) (W : Finset (Fin d)) (p : ℝ)
    (hε0 : 2 / (d : ℝ) < ε) (hε1 : ε < 1 / 100)
    (hw : W.card = Nat.floor (1 / ε) ∨ W.card = Nat.floor (1 / ε) - 1)
    (hp : p = 1 / (2 * (Nat.floor (1 / ε) : ℝ))) :
    0 < ε ∧ 100 ≤ Nat.floor (1 / ε) ∧ W.Nonempty ∧ 0 < p ∧ p ≤ 1 / 200 ∧
      (Nat.floor (1 / ε) : ℝ) - 1 ≤ (W.card : ℝ) ∧
      (W.card : ℝ) ≤ (Nat.floor (1 / ε) : ℝ) := by
  have he : 0 < ε := lt_of_le_of_lt (by positivity) hε0
  have hinv : (100 : ℝ) ≤ 1 / ε := (le_div_iff₀ he).mpr (by linarith)
  have hm : 100 ≤ Nat.floor (1 / ε) := Nat.le_floor hinv
  have hmr : (100 : ℝ) ≤ (Nat.floor (1 / ε) : ℝ) := by exact_mod_cast hm
  have hbounds : Nat.floor (1 / ε) - 1 ≤ W.card ∧ W.card ≤ Nat.floor (1 / ε) := by
    rcases hw with h | h <;> omega
  have hW : W.Nonempty := Finset.card_pos.mp (by omega)
  have hlow : (Nat.floor (1 / ε) : ℝ) - 1 ≤ (W.card : ℝ) := by
    have h := hbounds.1
    have heq : ((Nat.floor (1 / ε) - 1 : ℕ) : ℝ) =
        (Nat.floor (1 / ε) : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; norm_num
    exact heq ▸ (by exact_mod_cast h)
  refine ⟨he, hm, hW, ?_, ?_, hlow, by exact_mod_cast hbounds.2⟩
  · rw [hp]
    positivity
  · rw [hp]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Nat.floor (1 / ε) : ℝ))).mpr
    linarith

/-- **Theorem 4.2** (fixed arXiv:2110.13086v2, p. 20). Let `ε ∈ (2/d, 1/100)`, `w = ⌊1/ε⌋` or
`⌊1/ε⌋-1`, `p = 1/(2⌊1/ε⌋)`, and `W ⊂ Z_d` of size `w`.  Every `θ ∈ B₁^d` with
`L(θ) - L(θ*) ≤ ε/8000` satisfies
`∑_{j∈W}(θ_j - v)² ≤ ε/6400` and `∑_{j∉W} θ_j² ≤ ε/6400`.

Proof route (p. 20): Taylor expansion at `θ*` with `∇L(θ*) = 0` and the constant Hessian:
`L(θ) - L(θ*) = ½⟨∇²L(θ-θ*), θ-θ*⟩ ≥ (2-8p²)‖θ-θ*‖₂²/2`, hence
`‖θ-θ*‖₂² ≤ ε/(8000(1-4p²)) ≤ ε/6400` since `p ≤ 1/200`; the two displayed sums are the
`W`/`W̄` blocks of `θ - θ* = (θ_j - v)_{j∈W} ⊕ (θ_{j'})_{j'∉W}`. -/
theorem theorem_4_2 (ε : ℝ) (W : Finset (Fin d)) (p : ℝ)
    (hε0 : 2 / (d : ℝ) < ε) (hε1 : ε < 1 / 100)
    (hw : W.card = Nat.floor (1 / ε) ∨ W.card = Nat.floor (1 / ε) - 1)
    (hp : p = 1 / (2 * (Nat.floor (1 / ε) : ℝ)))
    (θ : Fin d → ℝ) (hθ : l1Ball θ)
    (hmin : lassoLoss p W θ - lassoLoss p W (thetaStarLasso p W) ≤ ε / 8000) :
    (∑ j ∈ W, (θ j - lassoV p W) ^ 2 ≤ ε / 6400) ∧
      (∑ j ∈ (Finset.univ \ W), θ j ^ 2 ≤ ε / 6400) := by
  classical
  by_cases _htriv : l1Ball θ
  swap
  · exact False.elim (_htriv hθ)
  obtain ⟨he, hm, hW, hp0, hpbound, hlow, hupp⟩ :=
    recovery_parameters ε W p hε0 hε1 hw hp
  have hpq : 4 * p ^ 2 ≤ 1 / 10000 := by nlinarith
  have hn : 0 ≤ l2NormSq (fun j => θ j - thetaStarLasso p W j) :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hl := loss_gap_lower p W hW θ
  have hnorm : l2NormSq (fun j => θ j - thetaStarLasso p W j) ≤ ε / 6400 := by
    have hprod := mul_nonneg (by linarith : 0 ≤ 1 - 4 * p ^ 2 - 4 / 5) hn
    nlinarith
  have hsplit : l2NormSq (fun j => θ j - thetaStarLasso p W j) =
      (∑ j ∈ W, (θ j - lassoV p W) ^ 2) +
        ∑ j ∈ Finset.univ \ W, θ j ^ 2 := by
    unfold l2NormSq
    rw [sum_blocks W]
    congr 1 <;> apply Finset.sum_congr rfl
    · intro j hj
      simp [thetaStarLasso, eW, hj]
    · intro j hj
      simp [thetaStarLasso, eW, (Finset.mem_sdiff.mp hj).2]
  rw [hsplit] at hnorm
  have hin : 0 ≤ ∑ j ∈ W, (θ j - lassoV p W) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hout : 0 ≤ ∑ j ∈ Finset.univ \ W, θ j ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  constructor <;> linarith

/-- **Theorem 4.3** (fixed arXiv:2110.13086v2, p. 20). Let `ε ∈ (2/d, 1/100)`, `w = ⌊1/ε⌋`
or `⌊1/ε⌋-1`, `p = 1/(2⌊1/ε⌋)`, and `W ⊂ Z_d` of size `w`.  If `θ` is an
`ε/8000`-minimizer for Lasso with respect to `D_{p,W}`, then the set
`W̃ = {j : |θ_j| ≥ ε/3}` satisfies `|W ∆ W̃| ≤ w/200`.

Proof route (p. 20): Theorem 4.2 gives `∑_{j∈W}(θ_j-v)² ≤ ε/6400` and
`∑_{j∉W}θ_j² ≤ ε/6400`; Markov's inequality shows at most `w/400` indices of `W` have
`|θ_j| < ε/3` and at most `w/400` indices outside `W` have `|θ_j| ≥ ε/3`; hence the symmetric
difference has size at most `w/200`. -/
theorem theorem_4_3 (ε : ℝ) (W : Finset (Fin d)) (p : ℝ)
    (hε0 : 2 / (d : ℝ) < ε) (hε1 : ε < 1 / 100)
    (hw : W.card = Nat.floor (1 / ε) ∨ W.card = Nat.floor (1 / ε) - 1)
    (hp : p = 1 / (2 * (Nat.floor (1 / ε) : ℝ)))
    (θ : Fin d → ℝ)
    (hmin : IsEpsilonMinimizer (lassoLoss p W) {θ | l1Ball θ} (ε / 8000) θ) :
    (let Wt : Finset (Fin d) := Finset.univ.filter (fun j => ε / 3 ≤ |θ j|)
     (((Wt \ W).card + (W \ Wt).card : ℕ) : ℝ) ≤ (W.card : ℝ) / 200) := by
  classical
  obtain ⟨he, hm, hW, hp0, hpbound, hlow, hupp⟩ :=
    recovery_parameters ε W p hε0 hε1 hw hp
  let m : ℝ := (Nat.floor (1 / ε) : ℝ)
  let w : ℝ := (W.card : ℝ)
  let v : ℝ := lassoV p W
  let D : ℝ := 1 + 4 * p ^ 2 * (w - 1)
  have hm100 : (100 : ℝ) ≤ m := by dsimp [m]; exact_mod_cast hm
  have hmpos : 0 < m := by linarith
  have hw1 : (1 : ℝ) ≤ w := by dsimp [w]; exact_mod_cast hW.card_pos
  have hD : 1 ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (sq_nonneg p) (by linarith : 0 ≤ w - 1)]
  have hvD : v * D = 2 * p := div_mul_cancel₀ _ (by linarith : D ≠ 0)
  have hv0 : 0 ≤ v := by
    change 0 ≤ 2 * p / D
    positivity
  have hpm : 2 * p * m = 1 := by
    rw [hp]
    change 2 * (1 / (2 * m)) * m = 1
    field_simp
  have hme : m * ε ≤ 1 := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ 1 / ε)
    exact (le_div_iff₀ he).mp hfloor
  have he2p : ε ≤ 2 * p := by
    apply (mul_le_mul_iff_left₀ hmpos).mp
    nlinarith [hme, hpm]
  have hDupper : D ≤ 101 / 100 := by
    have hmulp : 4 * p ^ 2 * m = 2 * p := by nlinarith [hpm]
    have hbound := mul_le_mul_of_nonneg_left (by linarith : w - 1 ≤ m)
      (by positivity : 0 ≤ 4 * p ^ 2)
    dsimp [D]
    nlinarith
  have hvlower : (100 / 101) * ε ≤ v := by
    have hprod := mul_le_mul_of_nonneg_left hDupper hv0
    nlinarith [hvD, he2p]
  have hfeasible : l1Ball (thetaStarLasso p W) := by
    have hnorm : l1Norm (thetaStarLasso p W) = w * v := by
      unfold l1Norm
      rw [sum_blocks W]
      have hin : (∑ j ∈ W, |thetaStarLasso p W j|) = w * v := by
        calc
          _ = ∑ _j ∈ W, v := by
            apply Finset.sum_congr rfl
            intro j hj
            simp only [thetaStarLasso, eW, hj, ite_true, mul_one]
            exact abs_of_nonneg hv0
          _ = _ := by simp [w]
      have hout : (∑ j ∈ Finset.univ \ W, |thetaStarLasso p W j|) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp [thetaStarLasso, eW, (Finset.mem_sdiff.mp hj).2]
      rw [hin, hout, add_zero]
    unfold l1Ball
    rw [hnorm]
    have hvupper : v ≤ 2 * p := by nlinarith [mul_nonneg hv0 (by linarith : 0 ≤ D - 1)]
    calc
      w * v ≤ w * (2 * p) := mul_le_mul_of_nonneg_left hvupper (by positivity)
      _ ≤ m * (2 * p) := mul_le_mul_of_nonneg_right hupp (by positivity)
      _ = 1 := by nlinarith [hpm]
  have hgap : lassoLoss p W θ - lassoLoss p W (thetaStarLasso p W) ≤ ε / 8000 := by
    have h := hmin.2 (thetaStarLasso p W) hfeasible
    linarith
  obtain ⟨hin, hout⟩ := theorem_4_2 ε W p hε0 hε1 hw hp θ hmin.1 hgap
  let Wt : Finset (Fin d) := Finset.univ.filter (fun j => ε / 3 ≤ |θ j|)
  change (((Wt \ W).card + (W \ Wt).card : ℕ) : ℝ) ≤ w / 200
  have hfalse : ((Wt \ W).card : ℝ) * (ε ^ 2 / 9) ≤ ε / 6400 := by
    calc
      _ = ∑ _j ∈ Wt \ W, ε ^ 2 / 9 := by simp
      _ ≤ ∑ j ∈ Wt \ W, θ j ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have ht := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
        have hs := (sq_le_sq₀ (by positivity : 0 ≤ ε / 3) (abs_nonneg (θ j))).mpr ht
        nlinarith only [hs, sq_abs (θ j)]
      _ ≤ ∑ j ∈ Finset.univ \ W, θ j ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, (Finset.mem_sdiff.mp hj).2⟩
        · intro j _hj _hj'
          exact sq_nonneg _
      _ ≤ ε / 6400 := hout
  have hmiss : ((W \ Wt).card : ℝ) * (ε ^ 2 / 4) ≤ ε / 6400 := by
    calc
      _ = ∑ _j ∈ W \ Wt, ε ^ 2 / 4 := by simp
      _ ≤ ∑ j ∈ W \ Wt, (θ j - lassoV p W) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have ht : |θ j| < ε / 3 := by
          have hn := (Finset.mem_sdiff.mp hj).2
          simpa [Wt, not_le] using hn
        have hdiff : ε / 2 ≤ v - θ j := by
          linarith only [ht, hvlower, le_abs_self (θ j), he]
        have hs := (sq_le_sq₀ (by positivity : 0 ≤ ε / 2)
          (by linarith only [hdiff, he] : 0 ≤ v - θ j)).mpr hdiff
        change ε ^ 2 / 4 ≤ (θ j - v) ^ 2
        nlinarith only [hs]
      _ ≤ ∑ j ∈ W, (θ j - lassoV p W) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro j _hj _hj'
        exact sq_nonneg _
      _ ≤ ε / 6400 := hin
  have hwe : 9 / 16 ≤ w * ε := by
    have hf : 1 / ε < m + 1 := Nat.lt_floor_add_one (1 / ε)
    have hf' := (div_lt_iff₀ he).mp hf
    have hw' := mul_le_mul_of_nonneg_right hlow he.le
    nlinarith only [hf', hw', hε1]
  have hfalse' : ((Wt \ W).card : ℝ) * ε ≤ 9 / 6400 := by
    apply (mul_le_mul_iff_left₀ he).mp
    nlinarith only [hfalse]
  have hmiss' : ((W \ Wt).card : ℝ) * ε ≤ 1 / 1600 := by
    apply (mul_le_mul_iff_left₀ he).mp
    nlinarith only [hmiss]
  have hfcard : ((Wt \ W).card : ℝ) ≤ w / 400 := by
    apply (mul_le_mul_iff_left₀ he).mp
    nlinarith only [hfalse', hwe]
  have hmcard : ((W \ Wt).card : ℝ) ≤ w / 400 := by
    apply (mul_le_mul_iff_left₀ he).mp
    nlinarith only [hmiss', hwe]
  rw [Nat.cast_add]
  linarith only [hfcard, hmcard]

end Qatlib.Papers.QRegression21.MainResults.LassoLoss
