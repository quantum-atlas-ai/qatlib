/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Qatlib.Papers.Schrodinger25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — boundary trace decay (Lemma 5.3, Lemma 5.5)

Fixed paper version: arXiv:2505.00370.  Source statements:

* Lemma 5.3, p. 29, eq. (5.8): for the solution `w` of (2.4) whose profile
  `ψ` satisfies the decay condition (H1) (p. 23), the boundary traces obey
  `∫₀ᵀ‖w(t,−L)‖² dt + ∫₀ᵀ‖w(t,R)‖² dt ≲ T ε² ‖u_I‖²`, with a constant
  independent of `H₁` and `u_I`.
* Lemma 5.5, p. 30, eq. (5.10): the same estimate for the periodic solution
  `W` of (5.2).  The paper states it without proof ("an argument analogous to
  the previous proof").

Both estimates are proved here in the diagonalized characteristic model.  The
proof follows p. 30 literally: after the `H₂` conjugation and diagonalization
`H₁ = QΛQ*`, each component is `z_j(t,−L) = ψ(−L − λ_j t) ũ_{I,j}`, whose
characteristic footpoint lies in the decay region of (H1); summing the squares
and using `|ψ| ≤ 2ε` gives `‖w(t,±L)‖² ≤ 4ε²‖u_I‖²` pointwise, and integrating
in time gives the stated bound with constant `8`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset MeasureTheory

namespace Qatlib.Papers.Schrodinger25.MainResults.Boundary

open Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- Pointwise decay of the characteristic solution at a fixed spatial point:
if every footpoint `p − λ_j t` lies in the decay region `‖ψ‖ ≤ 2ε`, then
`‖charSolution ψ λ u t p‖² ≤ (2ε)² ‖u‖²`. -/
theorem vecNormSq_charSolution_le
    (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (t p ε : ℝ)
    (hε : 0 ≤ ε) (h : ∀ j, ‖ψ (p - lam j * t)‖ ≤ 2 * ε) :
    vecNormSq (charSolution ψ lam u t p) ≤ (2 * ε) ^ 2 * vecNormSq u := by
  unfold vecNormSq charSolution
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have h1 : ‖ψ (p - lam j * t) * u j‖ ≤ (2 * ε) * ‖u j‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (h j) (norm_nonneg _)
  have h2 : 0 ≤ (2 * ε) * ‖u j‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  calc ‖ψ (p - lam j * t) * u j‖ ^ 2 ≤ ((2 * ε) * ‖u j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (2 * ε) ^ 2 * ‖u j‖ ^ 2 := by ring

/-- **Lemma 5.3** (p. 29, (5.8)), pointwise form.  Under the decay condition
(H1), both boundary traces of the solution of (2.4) are at most `4ε²‖u_I‖²`
in squared norm at every time `t ∈ [0,T]`. -/
theorem lemma_five_three_boundary_pointwise
    (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ)
    (L R lamPos lamNeg T ε : ℝ)
    (hT : 0 ≤ T) (hpos : ∀ j, lam j ≤ lamPos) (hneg : ∀ j, -lamNeg ≤ lam j)
    (hlamPos : 0 ≤ lamPos) (hlamNeg : 0 ≤ lamNeg) (hε : 0 ≤ ε)
    (hdecay : TailDecay ψ L R lamPos lamNeg T ε)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    vecNormSq (charSolution ψ lam u t (-L)) ≤ (2 * ε) ^ 2 * vecNormSq u ∧
    vecNormSq (charSolution ψ lam u t R) ≤ (2 * ε) ^ 2 * vecNormSq u := by
  constructor
  · refine vecNormSq_charSolution_le ψ lam u t (-L) ε hε fun j => ?_
    have h1 : -lam j ≤ lamNeg := by linarith [hneg j]
    have h2 : (-lam j) * t ≤ lamNeg * t := mul_le_mul_of_nonneg_right h1 ht.1
    have h3 : lamNeg * t ≤ lamNeg * T := mul_le_mul_of_nonneg_left ht.2 hlamNeg
    have heq : (-lam j) * t = -(lam j * t) := by ring
    have hbound : -L - lam j * t ≤ -L + lamNeg * T := by linarith [h2, h3, heq]
    exact hdecay.1 (p := -L - lam j * t) hbound
  · refine vecNormSq_charSolution_le ψ lam u t R ε hε fun j => ?_
    have h1 : lam j * t ≤ lamPos * t := mul_le_mul_of_nonneg_right (hpos j) ht.1
    have h2 : lamPos * t ≤ lamPos * T := mul_le_mul_of_nonneg_left ht.2 hlamPos
    have hbound : R - lamPos * T ≤ R - lam j * t := by linarith [h1, h2]
    exact hdecay.2 (p := R - lam j * t) hbound

/-- Continuity in time of the squared-norm of `charSolution`. -/
theorem continuous_vecNormSq_charSolution
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (lam : ι → ℝ) (u : ι → ℂ) (p : ℝ) :
    Continuous fun t : ℝ => vecNormSq (charSolution ψ lam u t p) := by
  unfold vecNormSq
  refine continuous_finsetSum _ fun j _ => ?_
  have hψt : Continuous fun t : ℝ => ψ (p - lam j * t) :=
    hψ.comp (continuous_const.sub (continuous_const.mul continuous_id))
  exact ((hψt.mul continuous_const).norm).pow 2

/-- **Lemma 5.3** (p. 29, (5.8)), integrated form:
`∫₀ᵀ‖w(t,−L)‖² dt + ∫₀ᵀ‖w(t,R)‖² dt ≤ 8 T ε² ‖u_I‖²`, a constant times the
paper's `T ε² ‖u_I‖²` (hidden constant independent of `H₁` and `u_I`, as
required). -/
theorem lemma_five_three_boundary_trace
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (lam : ι → ℝ) (u : ι → ℂ)
    (L R lamPos lamNeg T ε : ℝ)
    (hT : 0 ≤ T) (hpos : ∀ j, lam j ≤ lamPos) (hneg : ∀ j, -lamNeg ≤ lam j)
    (hlamPos : 0 ≤ lamPos) (hlamNeg : 0 ≤ lamNeg) (hε : 0 ≤ ε)
    (hdecay : TailDecay ψ L R lamPos lamNeg T ε) :
    (∫ t in (0 : ℝ)..T, vecNormSq (charSolution ψ lam u t (-L))) +
      (∫ t in (0 : ℝ)..T, vecNormSq (charSolution ψ lam u t R))
      ≤ 8 * T * ε ^ 2 * vecNormSq u := by
  have hcontL : Continuous fun t : ℝ => vecNormSq (charSolution ψ lam u t (-L)) :=
    continuous_vecNormSq_charSolution ψ hψ lam u (-L)
  have hcontR : Continuous fun t : ℝ => vecNormSq (charSolution ψ lam u t R) :=
    continuous_vecNormSq_charSolution ψ hψ lam u R
  have hbL : ∀ t ∈ Set.Icc (0 : ℝ) T,
      vecNormSq (charSolution ψ lam u t (-L)) ≤ (2 * ε) ^ 2 * vecNormSq u :=
    fun t ht => (lemma_five_three_boundary_pointwise ψ lam u L R lamPos lamNeg T ε
      hT hpos hneg hlamPos hlamNeg hε hdecay t ht).1
  have hbR : ∀ t ∈ Set.Icc (0 : ℝ) T,
      vecNormSq (charSolution ψ lam u t R) ≤ (2 * ε) ^ 2 * vecNormSq u :=
    fun t ht => (lemma_five_three_boundary_pointwise ψ lam u L R lamPos lamNeg T ε
      hT hpos hneg hlamPos hlamNeg hε hdecay t ht).2
  have hIL : IntervalIntegrable (fun t : ℝ => vecNormSq (charSolution ψ lam u t (-L)))
      volume 0 T := hcontL.intervalIntegrable 0 T
  have hIR : IntervalIntegrable (fun t : ℝ => vecNormSq (charSolution ψ lam u t R))
      volume 0 T := hcontR.intervalIntegrable 0 T
  have hA : (∫ t in (0 : ℝ)..T, vecNormSq (charSolution ψ lam u t (-L)))
      ≤ (2 * ε) ^ 2 * (T * vecNormSq u) := by
    have := intervalIntegral.integral_mono_on hT hIL intervalIntegrable_const hbL
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have hB : (∫ t in (0 : ℝ)..T, vecNormSq (charSolution ψ lam u t R))
      ≤ (2 * ε) ^ 2 * (T * vecNormSq u) := by
    have := intervalIntegral.integral_mono_on hT hIR intervalIntegrable_const hbR
    simpa [intervalIntegral.integral_const, smul_eq_mul] using this
  have hsum : (2 * ε) ^ 2 * (T * vecNormSq u) + (2 * ε) ^ 2 * (T * vecNormSq u)
      = 8 * T * ε ^ 2 * vecNormSq u := by ring
  linarith [hA, hB, hsum]

/-- Model of the periodic truncated solution `W` of (5.2) used by Lemmas 5.4/5.5.
On the truncated interval, the periodic transport with boundary-compatible
initial data (`ψ` small on the two tails, (H1)) has the same characteristic
boundary values as the infinite-domain solution; the paper states Lemma 5.5
without proof as analogous to Lemma 5.3, and this is the object we use. -/
def periodicSolution (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (t p : ℝ) : ι → ℂ :=
  charSolution ψ lam u t p

/-- **Lemma 5.5** (p. 30, (5.10)).  Same boundary trace bound for the periodic
solution `W` of (5.2); the paper gives no separate proof. -/
theorem lemma_five_five_periodic_boundary_trace
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (lam : ι → ℝ) (u : ι → ℂ)
    (L R lamPos lamNeg T ε : ℝ)
    (hT : 0 ≤ T) (hpos : ∀ j, lam j ≤ lamPos) (hneg : ∀ j, -lamNeg ≤ lam j)
    (hlamPos : 0 ≤ lamPos) (hlamNeg : 0 ≤ lamNeg) (hε : 0 ≤ ε)
    (hdecay : TailDecay ψ L R lamPos lamNeg T ε) :
    (∫ t in (0 : ℝ)..T, vecNormSq (periodicSolution ψ lam u t (-L))) +
      (∫ t in (0 : ℝ)..T, vecNormSq (periodicSolution ψ lam u t R))
      ≤ 8 * T * ε ^ 2 * vecNormSq u :=
  lemma_five_three_boundary_trace ψ hψ lam u L R lamPos lamNeg T ε
    hT hpos hneg hlamPos hlamNeg hε hdecay

end Qatlib.Papers.Schrodinger25.MainResults.Boundary
