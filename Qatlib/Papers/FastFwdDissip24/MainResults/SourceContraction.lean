/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FastFwdDissip24.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FastFwdDissip24 — Lemma 5 (contraction of the time-ordered exponential)

Source: arXiv:2410.13189, Lemma 5, p. 8, Eq. (12) and Eq. (13).

* Eq. (12): `‖T exp(∫_{t0}^{t1} A(s) ds)‖ ≤ exp(-η (t1 - t0))` for
  `A(t) + A(t)† ⪯ -2η`.
* Eq. (13): for any state `|v⟩`, `‖T exp(∫_{t0}^{t1} A) |v⟩‖ ≥
  exp(-(t1 - t0) max_t ‖A(t)‖)`.

Proof route (paper Appendix A, reproduced from the Dyson-series definition):
1. write `A = C - η • 1` with `C + C† ⪰ 0`; the scalar shift commutes out of the
   time-ordered exponential, giving `T exp(∫A) = exp(-η(t1-t0)) • T exp(∫C)`;
2. the PSD-contraction theorem
   `QuantumAlgorithm.Papers.QLinearODE17.TaylorAnalysis.ordered_evolution_psd_contraction`
   bounds `‖T exp(∫C)‖ ≤ 1`;
3. the unit lower bound follows by inverting the propagator and using the
   Dyson-series factorial majorant `‖propagator‖ ≤ exp(M |t1 - t0|)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.FastFwdDissip24.MainResults

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.PureStateMath.BornBridge

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Dyson-series factorial majorant: a continuous generator bounded by `M` on
the interval `[s,t]` gives `‖orderedEvolution B s t‖ ≤ exp(M |t - s|)`.
This is the `n`-th-term estimate `‖term_n‖ ≤ (M|t-s|)^n / n!` summed up
(arXiv:2410.13189, Appendix A, used in the proof of Lemma 5). -/
theorem norm_orderedEvolution_le_exp (B : ℝ → Matrix I I ℂ) (hB : Continuous B)
    {s t M : ℝ} (hM : 0 ≤ M) (hbound : ∀ u ∈ Set.uIcc s t, ‖B u‖ ≤ M) :
    ‖orderedEvolution B s t‖ ≤ Real.exp (M * |t - s|) := by
  have hsum : Summable (fun n => orderedDysonTerm B s n t) :=
    orderedDysonTerm_summable B hB s t
  have hnorm : Summable (fun n => ‖orderedDysonTerm B s n t‖) := hsum.norm
  have hfac : Summable (fun n : ℕ => (M * |t - s|) ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial _
  calc
    ‖orderedEvolution B s t‖ = ‖∑' n, orderedDysonTerm B s n t‖ := rfl
    _ ≤ ∑' n, ‖orderedDysonTerm B s n t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, (M * |t - s|) ^ n / (n.factorial : ℝ) :=
      hnorm.tsum_le_tsum
        (fun n => orderedDysonTerm_norm_le B hB s t M hM hbound n) hfac
    _ = Real.exp (M * |t - s|) := by
      rw [Real.exp_eq_exp_ℝ]
      exact (congrFun NormedSpace.exp_eq_tsum_div (M * |t - s|)).symm

/-- Scalar shift of the time-ordered exponential: shifting the generator of
`orderedEvolution` by `γ • 1` multiplies the propagator by `exp(-γ (t - s))`.
(arXiv:2410.13189, Appendix A: `T exp(∫(C - η)) = exp(-η(t1-t0)) T exp(∫C)`.) -/
theorem orderedEvolution_add_smul_one (C : ℝ → Matrix I I ℂ) (hC : Continuous C)
    (γ s t : ℝ) :
    orderedEvolution (fun u => C u + γ • (1 : Matrix I I ℂ)) s t =
      Real.exp (-γ * (t - s)) • orderedEvolution C s t := by
  have hA : Continuous (fun u => C u + γ • (1 : Matrix I I ℂ)) :=
    hC.add continuous_const
  have hshiftAlg : ∀ (X V : Matrix I I ℂ) (e γ : ℝ),
      e • (-(X * V)) + (-γ * e) • V =
        -((X + γ • (1 : Matrix I I ℂ)) * (e • V)) := by
    intro X V e γ
    rw [add_mul, Matrix.smul_mul, one_mul, Matrix.mul_smul, smul_smul, smul_neg,
      show -γ * e = -(γ * e) by ring, neg_smul]
    abel
  have hdRHS : ∀ u, HasDerivAt
      (fun v => Real.exp (-γ * (v - s)) • orderedEvolution C s v)
      (-((C u + γ • (1 : Matrix I I ℂ)) *
          (Real.exp (-γ * (u - s)) • orderedEvolution C s u))) u := by
    intro u
    have hscale : HasDerivAt (fun v : ℝ => Real.exp (-γ * (v - s)))
        (-γ * Real.exp (-γ * (u - s))) u := by
      have h1 : HasDerivAt (fun v : ℝ => -γ * (v - s)) (-γ) u := by
        simpa using ((hasDerivAt_id u).sub_const s).const_mul (-γ)
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1.exp
    have hscalar : HasDerivAt
        (fun v : ℝ => Real.exp (-γ * (v - s)) • (1 : Matrix I I ℂ))
        ((-γ * Real.exp (-γ * (u - s))) • (1 : Matrix I I ℂ)) u :=
      hscale.smul_const (1 : Matrix I I ℂ)
    have hV := orderedEvolution_hasDerivAt C hC s u
    have hmul := hscalar.mul hV
    have hfun : (fun v => Real.exp (-γ * (v - s)) • orderedEvolution C s v) =
        (fun v => (Real.exp (-γ * (v - s)) • (1 : Matrix I I ℂ)) *
          orderedEvolution C s v) := by
      funext v
      rw [Matrix.smul_mul, one_mul]
    rw [hfun]
    have hv : (-γ * Real.exp (-γ * (u - s))) • (1 : Matrix I I ℂ) *
          orderedEvolution C s u +
          (Real.exp (-γ * (u - s)) • (1 : Matrix I I ℂ)) *
            (-(C u * orderedEvolution C s u)) =
        -((C u + γ • (1 : Matrix I I ℂ)) *
          (Real.exp (-γ * (u - s)) • orderedEvolution C s u)) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, one_mul, one_mul]
      simpa only [add_comm] using
        hshiftAlg (C u) (orderedEvolution C s u) (Real.exp (-γ * (u - s))) γ
    convert! hmul using 1 <;> simp only [hv]
  have heq := ordered_matrix_ode_unique (fun u => C u + γ • (1 : Matrix I I ℂ)) hA
    (orderedEvolution (fun u => C u + γ • (1 : Matrix I I ℂ)) s)
    (fun v => Real.exp (-γ * (v - s)) • orderedEvolution C s v)
    s (by simp [orderedEvolution_self])
    (fun u => orderedEvolution_hasDerivAt _ hA s u) hdRHS
  exact congrFun heq t

/-- **Lemma 5, Part 1** `(arXiv:2410.13189, Lemma 5, Eq. (12), p. 8)`.
For a continuous dissipative generator `A(t) + A(t)† ⪯ -2η` and `0 ≤ t₀ ≤ t₁`,
the time-ordered exponential contracts:
`‖ T e^{∫_{t₀}^{t₁} A} ‖ ≤ e^{-η (t₁ - t₀)}`.

Proof route (paper Appendix A): write `-A = C + η • 1` with `C = -(A + η • 1)`,
so `C + C† ⪰ 0`; the scalar shift of `orderedEvolution` factors out as
`e^{-η(t₁-t₀)}`, and the PSD contraction `ordered_evolution_psd_contraction`
bounds `‖orderedEvolution C t₀ t₁‖ ≤ 1`. -/
theorem lemma5_part1 (A : ℝ → Matrix I I ℂ) (hA : Continuous A) {η : ℝ}
    (hdiss : Dissipative A η) {t0 t1 : ℝ} (h01 : t0 ≤ t1) :
    ‖paperPropagator A t0 t1‖ ≤ Real.exp (-η * (t1 - t0)) := by
  have hC : Continuous (fun u => -(A u + η • (1 : Matrix I I ℂ))) :=
    (hA.add continuous_const).neg
  have hgen : (fun u => (-(A u + η • (1 : Matrix I I ℂ))) + η • (1 : Matrix I I ℂ)) =
      (fun u => -A u) := by
    funext u
    have h : -(A u + η • (1 : Matrix I I ℂ)) =
        -A u + -(η • (1 : Matrix I I ℂ)) := neg_add _ _
    rw [h, add_assoc]
    simp
  have hshift := orderedEvolution_add_smul_one
    (fun u => -(A u + η • (1 : Matrix I I ℂ))) hC η t0 t1
  have hcontr := ordered_evolution_psd_contraction I
    (fun u => -(A u + η • (1 : Matrix I I ℂ))) hC (fun u => hdiss u) t0 t1 h01
  rw [paperPropagator, ← hgen, hshift]
  calc ‖Real.exp (-η * (t1 - t0)) •
        orderedEvolution (fun u => -(A u + η • (1 : Matrix I I ℂ))) t0 t1‖
      ≤ ‖Real.exp (-η * (t1 - t0))‖ *
          ‖orderedEvolution (fun u => -(A u + η • (1 : Matrix I I ℂ))) t0 t1‖ :=
        norm_smul_le _ _
    _ ≤ Real.exp (-η * (t1 - t0)) * 1 := by
        have hpos : (0 : ℝ) ≤ Real.exp (-η * (t1 - t0)) := le_of_lt (Real.exp_pos _)
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
        gcongr
    _ = Real.exp (-η * (t1 - t0)) := mul_one _

/-- **Lemma 5, Part 2** `(arXiv:2410.13189, Lemma 5, Eq. (13), p. 8)`.
For a continuous generator bounded by `M` on `[t₀,t₁]`, the time-ordered
exponential is bounded below on every vector:
`e^{-(t₁-t₀) M} ‖v‖ ≤ ‖ T e^{∫_{t₀}^{t₁} A} v ‖`.
For a unit quantum state this is the paper's `≥ e^{-(t₁-t₀) max_t ‖A(t)‖}`.

Proof route: `T e^{∫A}` is invertible with inverse `T e^{-∫A}` (the cocycle
relation), and the Dyson factorial majorant bounds the inverse norm by
`e^{M(t₁-t₀)}`; multiplying the trivial factorisation `v = (Te^{∫A})^{-1}(Te^{∫A})v`
by `e^{-M(t₁-t₀)}` gives the claim. -/
theorem lemma5_part2 (A : ℝ → Matrix I I ℂ) (hA : Continuous A)
    {t0 t1 M : ℝ} (hM : 0 ≤ M) (h01 : t0 ≤ t1)
    (hbound : ∀ u ∈ Set.uIcc t0 t1, ‖A u‖ ≤ M) (v : I → ℂ) :
    Real.exp (-(M * (t1 - t0))) * ‖toEuclidean_fromVec v‖ ≤
      ‖toEuclidean_fromVec (paperPropagator A t0 t1 *ᵥ v)‖ := by
  have hBt : Continuous (fun u => -A u) := hA.neg
  have hbnd : ∀ u ∈ Set.uIcc t0 t1, ‖(-A u : Matrix I I ℂ)‖ ≤ M := by
    intro u hu
    simpa using hbound u hu
  have habs : |t1 - t0| = t1 - t0 := abs_of_nonneg (sub_nonneg.mpr h01)
  have hback : ‖orderedEvolution (fun u => -A u) t1 t0‖ ≤ Real.exp (M * |t1 - t0|) :=
    (abs_sub_comm t0 t1) ▸
      norm_orderedEvolution_le_exp (fun u => -A u) hBt hM (by
        intro u hu
        rw [Set.uIcc_comm] at hu
        exact hbnd u hu)
  have hcoc :
      orderedEvolution (fun u => -A u) t1 t0 * orderedEvolution (fun u => -A u) t0 t1 = 1 := by
    have := orderedEvolution_cocycle (fun u => -A u) hBt t0 t1 t0
    simpa using this
  have hmv := Matrix.l2_opNorm_mulVec (orderedEvolution (fun u => -A u) t1 t0)
    (toEuclidean_fromVec (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v))
  have hid : orderedEvolution (fun u => -A u) t1 t0 *ᵥ
      (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hcoc, Matrix.one_mulVec]
  have hupper : ‖toEuclidean_fromVec v‖ ≤ Real.exp (M * |t1 - t0|) *
      ‖toEuclidean_fromVec (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v)‖ := by
    calc ‖toEuclidean_fromVec v‖
        = ‖toEuclidean_fromVec (orderedEvolution (fun u => -A u) t1 t0 *ᵥ
            (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v))‖ := by rw [hid]
      _ ≤ ‖orderedEvolution (fun u => -A u) t1 t0‖ *
            ‖toEuclidean_fromVec (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v)‖ := hmv
      _ ≤ Real.exp (M * |t1 - t0|) *
            ‖toEuclidean_fromVec (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v)‖ := by
            gcongr
  calc Real.exp (-(M * (t1 - t0))) * ‖toEuclidean_fromVec v‖
      ≤ Real.exp (-(M * (t1 - t0))) * (Real.exp (M * |t1 - t0|) *
          ‖toEuclidean_fromVec (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v)‖) := by
        gcongr
    _ = ‖toEuclidean_fromVec (orderedEvolution (fun u => -A u) t0 t1 *ᵥ v)‖ := by
        rw [← mul_assoc, ← Real.exp_add,
          show -(M * (t1 - t0)) + M * |t1 - t0| = 0 by rw [habs]; ring]
        simp
    _ = ‖toEuclidean_fromVec (paperPropagator A t0 t1 *ᵥ v)‖ := by
        rw [paperPropagator]

end Qatlib.Papers.FastFwdDissip24.MainResults
