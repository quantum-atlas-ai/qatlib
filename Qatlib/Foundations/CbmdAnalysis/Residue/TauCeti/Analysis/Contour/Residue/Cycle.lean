/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.PolarPart.Decomposition
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.Number.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.PerWindow.HigherOrder

/-!
# Residue theorem for null-homologous contours

Integrates finite polar-part decompositions along closed piecewise C1 curves. The analytic
remainder vanishes under the null-homology hypothesis, yielding
`classicalResidueTheorem_nullHomologous` with winding-number weights.

The result supplies a scalar contour-integration foundation for the methods of [WangEtAl2026].

## Main statements

* `intervalIntegral_deriv_smul_polarPart`: The integral of one polar part along a closed
  piecewise C1 curve avoiding its pole is `2πi` times its winding number and residue.
* `classicalResidueTheorem_nullHomologous`: The classical residue theorem for a closed piecewise
  C1 curve null homologous in an open set, with finitely many possible meromorphic singularities
  avoided by the curve.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

namespace PolarPartDecomposition

variable {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}

/-- The integral of one polar part along a closed piecewise C1 curve avoiding its pole is `2πi`
times its winding number and residue. -/
theorem intervalIntegral_deriv_smul_polarPart (decomp : PolarPartDecomposition f S U) (s : S)
    {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (h_ne : ∀ t ∈ uIcc a b, γ t ≠ (s : ℂ)) :
    ∫ t in a..b, deriv γ t • decomp.polarPart s (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s * residue f s := by
  classical
  have hcont : ContinuousOn γ (uIcc a b) := hγ.continuousOn
  have hderiv : IntervalIntegrable (fun t => deriv γ t) volume a b := hγ.intervalIntegrable_deriv
  have hne' : ∀ t ∈ uIcc a b, γ t - (s : ℂ) ≠ 0 := fun t ht => sub_ne_zero.mpr (h_ne t ht)
  have hindex : ∫ t in a..b, (γ t - (s : ℂ))⁻¹ * deriv γ t
      = 2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s := by
    rw [windingNumber_eq_integral_of_avoidance hcont h_ne
        (intervalIntegrable_inv_sub_mul_deriv hcont h_ne hderiv), ← mul_assoc,
      mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]
  have hterm : ∀ k : Fin (decomp.order s), IntervalIntegrable
      (fun t => decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t) volume a b :=
    fun k => hderiv.continuousOn_mul (continuousOn_const.div
      ((hcont.sub continuousOn_const).pow _) fun t ht => pow_ne_zero _ (hne' t ht))
  have hsplit : ∫ t in a..b, deriv γ t • decomp.polarPart s (γ t)
      = ∑ k : Fin (decomp.order s),
          ∫ t in a..b, decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t := by
    rw [← intervalIntegral.integral_finsetSum fun k _ => hterm k]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [smul_eq_mul, mul_comm, decomp.polarPart_eq s (γ t), Finset.sum_mul]
  have hval : ∀ k : Fin (decomp.order s),
      (∫ t in a..b, decomp.coeff s k / (γ t - (s : ℂ)) ^ (k.val + 1) * deriv γ t)
        = if k.val = 0 then
            decomp.coeff s k * (2 * (Real.pi : ℂ) * Complex.I * windingNumber γ a b s)
          else 0 := by
    intro k
    rcases Nat.eq_zero_or_pos k.val with hk0 | hk_pos
    · rw [if_pos hk0, ← hindex, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hk0]
      ring
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hk_pos)]
      exact integral_pow_inv_mul_deriv_eq_zero_of_closed (by omega) _ hγ hclosed h_ne
  rw [hsplit, Finset.sum_congr rfl fun k _ => hval k, decomp.sum_ite_coeff_eq_residue_mul s]
  ring

/-- Splits the integral of a function with a polar-part decomposition into the analytic
remainder integral and the winding-weighted sum of residues. -/
theorem intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum
    (decomp : PolarPartDecomposition f S U) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = (∫ t in a..b, deriv γ t • decomp.analyticRemainder (γ t))
        + 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  classical
  have hcont : ContinuousOn γ (uIcc a b) := hγ.continuousOn
  have hderiv : IntervalIntegrable (fun t => deriv γ t) volume a b := hγ.intervalIntegrable_deriv
  have hne : ∀ s : S, ∀ t ∈ uIcc a b, γ t ≠ (s : ℂ) := fun s t ht h_eq =>
    hoff t ht (h_eq ▸ Finset.mem_coe.mpr s.2)
  have hpol_cont : ∀ s : S, ContinuousOn (fun t => decomp.polarPart s (γ t)) (uIcc a b) :=
    fun s => ContinuousOn.congr
      (continuousOn_finsetSum Finset.univ fun k _ => continuousOn_const.div
        ((hcont.sub continuousOn_const).pow (k.val + 1))
        fun t ht => pow_ne_zero _ (sub_ne_zero.mpr (hne s t ht)))
      fun t _ => decomp.polarPart_eq s (γ t)
  have hrem_int : IntervalIntegrable
      (fun t => deriv γ t • decomp.analyticRemainder (γ t)) volume a b :=
    hderiv.smul_continuousOn
      (decomp.analyticRemainder_differentiableOn.continuousOn.comp hcont hγU)
  have hpol_int : ∀ s ∈ S.attach, IntervalIntegrable
      (fun t => deriv γ t • decomp.polarPart s (γ t)) volume a b :=
    fun s _ => hderiv.smul_continuousOn (hpol_cont s)
  have hsum_int : IntervalIntegrable
      (fun t => ∑ s ∈ S.attach, deriv γ t • decomp.polarPart s (γ t)) volume a b := by
    have h := IntervalIntegrable.sum S.attach hpol_int
    rwa [Finset.sum_fn] at h
  have hf_eq : EqOn (fun t => deriv γ t • f (γ t))
      (fun t => deriv γ t • decomp.analyticRemainder (γ t)
        + ∑ s ∈ S.attach, deriv γ t • decomp.polarPart s (γ t)) (uIcc a b) := fun t ht => by
    simp only
    rw [decomp.f_eq (γ t) ⟨hγU t ht, hoff t ht⟩, smul_add, Finset.smul_sum]
  rw [intervalIntegral.integral_congr hf_eq, intervalIntegral.integral_add hrem_int hsum_int,
    intervalIntegral.integral_finsetSum hpol_int,
    Finset.sum_congr rfl fun s _ =>
      decomp.intervalIntegral_deriv_smul_polarPart s hγ hclosed (hne s),
    Finset.mul_sum, ← Finset.sum_attach S
      fun s => 2 * (Real.pi : ℂ) * Complex.I * (windingNumber γ a b s * residue f s)]
  exact congrArg _ (Finset.sum_congr rfl fun s _ => by ring)

/-- For a closed piecewise C1 curve null homologous in an open set, a polar-part decomposition
gives the residue formula with winding-number weights. -/
theorem intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue
    (decomp : PolarPartDecomposition f S U) (hU : IsOpen U) {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : IsPiecewiseC1On γ a b) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  rw [decomp.intervalIntegral_deriv_smul_eq_analyticRemainder_add_sum hγ hγU hclosed hoff,
    decomp.intervalIntegral_deriv_smul_analyticRemainder_eq_zero hU hγ hγU hclosed hnull, zero_add]

end PolarPartDecomposition

/-- The classical residue theorem for a closed piecewise C1 curve null homologous in an open
set, with finitely many possible meromorphic singularities avoided by the curve. -/
theorem classicalResidueTheorem_nullHomologous {f : ℂ → ℂ} {S : Finset ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s) {γ : ℝ → ℂ} {a b : ℝ} (hγ : IsPiecewiseC1On γ a b)
    (hγU : ∀ t ∈ uIcc a b, γ t ∈ U) (hclosed : γ a = γ b)
    (hoff : ∀ t ∈ uIcc a b, γ t ∉ (↑S : Set ℂ)) (hnull : IsNullHomologous γ a b U) :
    ∫ t in a..b, deriv γ t • f (γ t)
      = 2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, windingNumber γ a b s * residue f s := by
  classical

  obtain ⟨T, hTS, hfT, hmeroT, hsum⟩ : ∃ T : Finset ℂ, (∀ s ∈ T, s ∈ S) ∧
      DifferentiableOn ℂ f (U \ (↑T : Set ℂ)) ∧ (∀ s ∈ T, MeromorphicAt f s) ∧
      (∑ s ∈ S, windingNumber γ a b s * residue f s)
        = ∑ s ∈ T, windingNumber γ a b s * residue f s :=
    ⟨S.filter (· ∈ U), fun _ hs => (Finset.mem_filter.mp hs).1,
      hf.mono fun z hz => ⟨hz.1, fun hzS =>
        hz.2 (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hzS, hz.1⟩))⟩,
      fun s hs => hmero s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2,
      (Finset.sum_filter_of_ne fun s _ hs => not_not.mp fun hsU =>
        hs (by rw [isNullHomologous_iff.mp hnull s hsU, zero_mul])).symm⟩
  rw [hsum]
  exact PolarPartDecomposition.intervalIntegral_deriv_smul_eq_sum_windingNumber_mul_residue
    (.ofMeromorphic hU hfT hmeroT) hU hγ hγU hclosed
    (fun t ht h => hoff t ht (Finset.mem_coe.mpr (hTS _ (Finset.mem_coe.mp h)))) hnull

end TauCeti.Contour

end

end Qatlib.Foundations.CbmdAnalysis.Residue
