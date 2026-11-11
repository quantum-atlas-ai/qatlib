/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6Aux4
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6Stat

/-!
# Taylor history approximation of the ODE solution

`theorem6V2` proves `Theorem6V2`, the factorially decreasing error estimate for the time blocks
of a V2 Taylor-system solution. Coordinatewise estimates are combined in the Euclidean state
norm and transported through the diagonalizing basis. See [BerryEtAl2017ODE] for the paper's
setting.

## Main statements

* `theorem6V2`: Under the hypotheses of `Theorem6V2`, each time block `j ≤ m` approximates the
  reference solution at time `j*h` with error at most `2.8 * (‖V‖ * ‖V⁻¹‖) * j * (‖x_in‖₂ +
  m*h*‖b‖₂) / (k+1)!`.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix
open scoped Matrix.Norms.L2Operator

/-- Under the hypotheses of `Theorem6V2`, each time block `j ≤ m` approximates the reference
solution at time `j*h` with error at most `2.8 * (‖V‖ * ‖V⁻¹‖) * j * (‖x_in‖₂ + m*h*‖b‖₂) /
(k+1)!`. See [BerryEtAl2017ODE]. -/
theorem theorem6V2 : Theorem6V2 := by
  intro N _ _ m k p A V D h x_in b x hm hk _hp hFfac hh hd hA hV1 hV2 hdre hnormA hx j hjm
  classical
  have hz1 : ∀ n : N, ‖(h : ℂ) * D n n‖ ≤ 1 :=
    fun n => hA_eigen_norm_le A V D hA hV1 hV2 hd h hh hnormA n
  have hblockV : taylorBlock x (taylorTimeLabel m k p j hjm)
      = V *ᵥ conjSeq k h D (V⁻¹ *ᵥ x_in) (V⁻¹ *ᵥ b) j :=
    taylorV2_block_conj m k p A V D h x_in b x hx hA hV1 hV2 hd j hjm
  have hsol : taylorODESolution A b x_in ((j : ℝ) * h)
      = V *ᵥ (fun n => duhamelCoord (D n n) ((V⁻¹ *ᵥ x_in) n) ((V⁻¹ *ᵥ b) n)
          ((j : ℝ) * h)) := by
    have h0 := taylorODESolution_eq_diag A V D hA hV1 hV2 hd b x_in ((j : ℝ) * h)
    rw [h0]
    congr 1
    funext n
    simp only [neg_mul]
    rfl

  set ε : QState N := (fun n => duhamelCoord (D n n) ((V⁻¹ *ᵥ x_in) n) ((V⁻¹ *ᵥ b) n)
      ((j : ℝ) * h) - conjSeq k h D (V⁻¹ *ᵥ x_in) (V⁻¹ *ᵥ b) j n) with hε
  have hMP : ∀ ψ : QState N, MeasureProb ψ Finset.univ = ∑ n : N, ‖ψ n‖ ^ 2 := fun _ => rfl
  have hrepr : stateVector (taylorODESolution A b x_in ((j : ℝ) * h))
      - stateVector (taylorBlock x (taylorTimeLabel m k p j hjm)) = stateVector (V *ᵥ ε) := by
    rw [hsol, hblockV]
    show stateVector ((V *ᵥ (fun n => duhamelCoord (D n n) ((V⁻¹ *ᵥ x_in) n)
        ((V⁻¹ *ᵥ b) n) ((j : ℝ) * h))) - V *ᵥ conjSeq k h D (V⁻¹ *ᵥ x_in)
      (V⁻¹ *ᵥ b) j) = stateVector (V *ᵥ ε)
    rw [← Matrix.mulVec_sub]
    rfl

  set c : ℝ := 2.8 * (j : ℝ) / ((Nat.factorial (k + 1) : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity

  have herrcoord : ∀ n : N, ‖ε n‖ ≤ c * (‖(V⁻¹ *ᵥ x_in) n‖
      + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)) := by
    intro n
    have h1 := per_coordinate_error m k hk hm hFfac h hh D (V⁻¹ *ᵥ x_in) (V⁻¹ *ᵥ b) n
      (hdre n) (hz1 n) j hjm
    calc ‖ε n‖ ≤ 2.8 * (j : ℝ) * (‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖))
          / ((Nat.factorial (k + 1) : ℕ) : ℝ) := h1
      _ = c * (‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)) := by rw [hc]; ring

  set u : QState N := fun n => ((‖(V⁻¹ *ᵥ x_in) n‖ : ℝ) : ℂ) with hu
  set w : QState N := fun n => ((‖(V⁻¹ *ᵥ b) n‖ : ℝ) : ℂ) with hw
  have hunorm : ∀ n : N, ‖(u + ((m : ℝ) * h) • w) n‖
      = ‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * h * ‖(V⁻¹ *ᵥ b) n‖ := by
    intro n
    have hcast : (u + ((m : ℝ) * h) • w) n
        = (((‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * h * ‖(V⁻¹ *ᵥ b) n‖ : ℝ) : ℂ)) := by
      rw [Pi.add_apply, Pi.smul_apply, Complex.real_smul, hu, hw]
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hsqε : ‖stateVector ε‖^2 ≤ (c * ‖stateVector (u + ((m : ℝ) * h) • w)‖)^2 := by
    have h1 : ∑ n : N, ‖ε n‖^2
        ≤ ∑ n : N, (c * (‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)))^2 := by
      refine Finset.sum_le_sum fun n _ => ?_
      have hn : 0 ≤ c * (‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)) := by
        rw [hc]
        positivity
      nlinarith [norm_nonneg (ε n), hn, herrcoord n]
    have h2 : ∑ n : N, (c * (‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)))^2
        = c^2 * ‖stateVector (u + ((m : ℝ) * h) • w)‖^2 := by
      rw [Finset.sum_congr rfl fun n _ =>
        show (c * (‖(V⁻¹ *ᵥ x_in) n‖ + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)))^2
          = c^2 * ‖(u + ((m : ℝ) * h) • w) n‖^2 from by rw [hunorm n]; ring,
        ← Finset.mul_sum, stateVector_norm_sq,
        hMP]
    rw [stateVector_norm_sq]
    calc ∑ n : N, ‖ε n‖^2 ≤ ∑ n : N, (c * (‖(V⁻¹ *ᵥ x_in) n‖
          + (m : ℝ) * (h * ‖(V⁻¹ *ᵥ b) n‖)))^2 := h1
      _ = c^2 * ‖stateVector (u + ((m : ℝ) * h) • w)‖^2 := h2
      _ = (c * ‖stateVector (u + ((m : ℝ) * h) • w)‖)^2 := by ring
  have hcnn : 0 ≤ c * ‖stateVector (u + ((m : ℝ) * h) • w)‖ :=
    mul_nonneg hc0 (norm_nonneg _)
  have hεle : ‖stateVector ε‖ ≤ c * ‖stateVector (u + ((m : ℝ) * h) • w)‖ := by
    nlinarith [hsqε, norm_nonneg (stateVector ε), hcnn]

  have hupeq : ‖stateVector u‖ = ‖stateVector (V⁻¹ *ᵥ x_in)‖ := by
    have h1 : ‖stateVector u‖^2 = ‖stateVector (V⁻¹ *ᵥ x_in)‖^2 := by
      rw [stateVector_norm_sq, stateVector_norm_sq, hMP, hMP]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hu]
      simp
    nlinarith [norm_nonneg (stateVector u), norm_nonneg (stateVector (V⁻¹ *ᵥ x_in)), h1]
  have hwpeq : ‖stateVector w‖ = ‖stateVector (V⁻¹ *ᵥ b)‖ := by
    have h1 : ‖stateVector w‖^2 = ‖stateVector (V⁻¹ *ᵥ b)‖^2 := by
      rw [stateVector_norm_sq, stateVector_norm_sq, hMP, hMP]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hw]
      simp
    nlinarith [norm_nonneg (stateVector w), norm_nonneg (stateVector (V⁻¹ *ᵥ b)), h1]
  have hmink : ‖stateVector (u + ((m : ℝ) * h) • w)‖
      ≤ ‖stateVector (V⁻¹ *ᵥ x_in)‖ + (m : ℝ) * h * ‖stateVector (V⁻¹ *ᵥ b)‖ := by
    calc ‖stateVector (u + ((m : ℝ) * h) • w)‖
        ≤ ‖stateVector u‖ + ‖stateVector (((m : ℝ) * h) • w)‖ := by
          have h1 : ‖stateVector (u + ((m : ℝ) * h) • w)‖
              ≤ ‖stateVector u‖ + ‖stateVector (((m : ℝ) * h) • w)‖ := by
            have h2 : stateVector (u + ((m : ℝ) * h) • w)
                = stateVector u + stateVector (((m : ℝ) * h) • w) := rfl
            rw [h2]
            exact norm_add_le _ _
          exact h1
      _ = ‖stateVector u‖ + (m : ℝ) * h * ‖stateVector w‖ := by
          rw [show stateVector (((m : ℝ) * h) • w)
              = (((m : ℝ) * h) • stateVector w : EuclideanSpace ℂ N) from rfl,
            norm_smul, Real.norm_eq_abs, abs_of_nonneg
            (mul_nonneg (show (0 : ℝ) ≤ ((m : ℕ) : ℝ) from Nat.cast_nonneg m) hh.le)]
      _ = ‖stateVector (V⁻¹ *ᵥ x_in)‖ + (m : ℝ) * h * ‖stateVector (V⁻¹ *ᵥ b)‖ := by
          rw [hupeq, hwpeq]
  have hyb : ‖stateVector (V⁻¹ *ᵥ x_in)‖ ≤ ‖V⁻¹‖ * ‖stateVector x_in‖ :=
    stateVector_mulVec_norm_le V⁻¹ x_in
  have hβb : ‖stateVector (V⁻¹ *ᵥ b)‖ ≤ ‖V⁻¹‖ * ‖stateVector b‖ :=
    stateVector_mulVec_norm_le V⁻¹ b

  rw [hrepr]
  refine le_trans (stateVector_mulVec_norm_le V ε) ?_
  calc ‖V‖ * ‖stateVector ε‖
      ≤ ‖V‖ * (c * (‖stateVector (V⁻¹ *ᵥ x_in)‖
        + (m : ℝ) * h * ‖stateVector (V⁻¹ *ᵥ b)‖)) :=
        mul_le_mul_of_nonneg_left (hεle.trans (by
          refine mul_le_mul_of_nonneg_left hmink hc0)) (norm_nonneg _)
    _ ≤ ‖V‖ * (c * (‖V⁻¹‖ * ‖stateVector x_in‖
        + (m : ℝ) * h * (‖V⁻¹‖ * ‖stateVector b‖))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hc0) (norm_nonneg _)
          exact add_le_add hyb (mul_le_mul_of_nonneg_left hβb (by positivity))
    _ = 2.8 * (‖V‖ * ‖V⁻¹‖) * (j : ℝ) * (‖stateVector x_in‖
        + (m : ℝ) * h * ‖stateVector b‖) / ((Nat.factorial (k + 1) : ℕ) : ℝ) := by
          rw [hc]
          ring

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
