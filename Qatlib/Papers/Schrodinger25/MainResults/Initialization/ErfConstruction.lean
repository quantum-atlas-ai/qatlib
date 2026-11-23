/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Error-function initialization for Schrödingerization

[JinEtAl2025Schrodinger], §4.2 constructs a smooth profile by multiplying
`exp (-p)` by a rescaled Gaussian cumulative integral. For `0 < ε ≤ 1`,
the profile approximates `exp (-p)` on the entire half-line `p ≥ 1/2`,
which supplies (H2) of Theorem 4.1. The two-sided spatial truncation and
the high-order derivative estimates (H1) and (H3) are outside this module.

Paper: [arXiv:2505.00370v4](https://arxiv.org/abs/2505.00370v4), pp. 23–25.
-/

namespace Qatlib.Papers.Schrodinger25.MainResults.Initialization

open MeasureTheory Set

noncomputable section

/-- The normalized integral of the Gaussian from zero to `p`. -/
def erfFun (p : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..p, Real.exp (-(t ^ 2))

/-- The rescaled Gaussian cumulative profile of Eq. (4.6). -/
def phiErf (a p : ℝ) : ℝ := (erfFun (a * p) + 1) / 2

/-- The initial profile of Theorem 4.1 with scale `2√log(1/ε)`. -/
def psiErf (ε p : ℝ) : ℝ :=
  phiErf (2 * Real.sqrt (Real.log (1 / ε))) p * Real.exp (-p)

/-- On the nonnegative half-line, the complementary error function lies
between zero and `exp (-x²)`. Translate the tail to zero and compare
the integrands using `(t+x)² ≥ t²+x²` for `t ≥ 0`. -/
theorem one_sub_erfFun_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 - erfFun x ∧ 1 - erfFun x ≤ Real.exp (-(x ^ 2)) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2))
  have hg : Integrable g := by
    simpa [g] using integrable_exp_neg_mul_sq (b := 1) zero_lt_one
  have htotal : (∫ t in Ioi (0 : ℝ), g t) = Real.sqrt Real.pi / 2 := by
    simpa [g] using integral_gaussian_Ioi (1 : ℝ)
  have hshiftEmbedding : MeasurableEmbedding (fun t : ℝ => t + x) :=
    (Homeomorph.addRight x).isClosedEmbedding.measurableEmbedding
  have hshiftMeasure : MeasurePreserving (fun t : ℝ => t + x) volume volume :=
    measurePreserving_add_right volume x
  have hpreimage : (fun t : ℝ => t + x) ⁻¹' Ioi x = Ioi 0 := by
    ext t
    simp
  have hshift : (∫ t in Ioi (0 : ℝ), g (t + x)) = ∫ t in Ioi x, g t := by
    rw [← hpreimage]
    exact hshiftMeasure.setIntegral_preimage_emb hshiftEmbedding g (Ioi x)
  have htail : (∫ t in Ioi x, g t) ≤ Real.exp (-(x ^ 2)) * (Real.sqrt Real.pi / 2) := by
    rw [← hshift, ← htotal, ← integral_const_mul]
    apply setIntegral_mono_on
      (hshiftMeasure.integrable_comp_of_integrable hg).integrableOn
      (hg.const_mul _).integrableOn measurableSet_Ioi
    intro t ht
    change Real.exp (-((t + x) ^ 2)) ≤ Real.exp (-(x ^ 2)) * Real.exp (-(t ^ 2))
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have ht' : 0 ≤ t := (mem_Ioi.mp ht).le
    nlinarith [mul_nonneg ht' hx]
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsplit := intervalIntegral.integral_interval_add_Ioi
    (a := 0) (b := x) hg.integrableOn hg.integrableOn
  rw [htotal] at hsplit
  have hnorm : (2 / Real.sqrt Real.pi) * (Real.sqrt Real.pi / 2) = 1 := by
    field_simp
  have hsub : 1 - erfFun x = (2 / Real.sqrt Real.pi) * (∫ t in Ioi x, g t) := by
    change 1 - (2 / Real.sqrt Real.pi) * (∫ t in (0 : ℝ)..x, g t) = _
    rw [← hnorm, ← hsplit, mul_add, add_sub_cancel_left]
  rw [hsub]
  refine ⟨mul_nonneg (by positivity) (integral_nonneg fun t => (Real.exp_pos _).le), ?_⟩
  calc
    _ ≤ (2 / Real.sqrt Real.pi) * (Real.exp (-(x ^ 2)) * (Real.sqrt Real.pi / 2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = Real.exp (-(x ^ 2)) := by
      rw [mul_left_comm, hnorm, mul_one]

/-- The accuracy condition (H2) of Theorem 4.1, on every `p ≥ 1/2`.
The Gaussian tail bound in fact gives an error at most `ε/2`. -/
theorem abs_psiErf_sub_exp_neg_le {ε p : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hp : 1 / 2 ≤ p) :
    |psiErf ε p - Real.exp (-p)| ≤ ε / 2 := by
  let s := Real.sqrt (Real.log (1 / ε))
  let x := (2 * s) * p
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsx : s ≤ x := by
    dsimp [x]
    nlinarith [mul_nonneg hs (show 0 ≤ p - 1 / 2 by linarith)]
  have hx : 0 ≤ x := hs.trans hsx
  have hlog : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).2 (by simpa using hε₁))
  have hs_sq : s ^ 2 = Real.log (1 / ε) := Real.sq_sqrt hlog
  have hgauss : Real.exp (-(x ^ 2)) ≤ ε := by
    calc
      _ ≤ Real.exp (-(s ^ 2)) := Real.exp_le_exp.mpr (neg_le_neg ((sq_le_sq₀ hs hx).2 hsx))
      _ = ε := by
        have hratio : 0 < 1 / ε := by positivity
        rw [hs_sq, Real.exp_neg, Real.exp_log hratio, one_div, inv_inv]
  obtain ⟨herf₀, herf⟩ := one_sub_erfFun_bounds hx
  have he : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hform : psiErf ε p - Real.exp (-p) =
      -((1 - erfFun x) / 2 * Real.exp (-p)) := by
    change (erfFun x + 1) / 2 * Real.exp (-p) - Real.exp (-p) = _
    ring
  have herror : 0 ≤ (1 - erfFun x) / 2 * Real.exp (-p) :=
    mul_nonneg (div_nonneg herf₀ (by positivity)) (Real.exp_pos (-p)).le
  rw [hform, abs_neg, abs_of_nonneg herror]
  calc
    _ ≤ (1 - erfFun x) / 2 * 1 :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ ε / 2 := by linarith [herf.trans hgauss]

end

end Qatlib.Papers.Schrodinger25.MainResults.Initialization
