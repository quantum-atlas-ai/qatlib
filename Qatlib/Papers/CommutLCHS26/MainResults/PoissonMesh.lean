/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.StripContour
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Poisson summation and mesh error

This module derives vector-valued Poisson summation and infinite-mesh quadrature estimates.
Exponential Fourier decay gives geometric error bounds, and strip analyticity supplies the decay
needed for the quadrature analysis of [AftabAnTrivisa2026].

The final strip estimate replaces normal convergence assumptions with a sufficient real-axis
power-decay condition.

## Main statements

* `poisson`: Poisson summation for vector-valued functions.
* `strip_mesh_error_of_rpow_decay`: the strip quadrature estimate corresponding to Lemma 4.13.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.PoissonMesh

open Complex Set Filter MeasureTheory TopologicalSpace
open ContinuousMap
open Asymptotics
open scoped Topology FourierTransform BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A continuous complex linear functional commutes with the Fourier transform of an integrable
function. -/
theorem fourier_scalarize (f : ℝ → E) (hf : Integrable f) (L : E →L[ℂ] ℂ) (ξ : ℝ) :
    𝓕 (fun x => L (f x)) ξ = L (𝓕 f ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hi : Integrable (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * ξ) * I) • f x) := by
    apply hf.bdd_smul 1
    · fun_prop
    · exact Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [map_smul] using L.integral_comp_comm hi

omit [NormedSpace ℂ E] in

/-- Normal convergence of integer translates on every compact set implies summability of the
integer samples. -/
theorem summable_samples (f : C(ℝ, E))
    (hn : ∀ K : Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)) :
    Summable (fun n : ℤ => f (n : ℝ)) := by
  simpa using (hasSum_apply (summable_of_locally_summable_norm hn).hasSum 0).summable

/-- The Poisson summation identity holds for a continuous integrable vector-valued function
whose integer translates converge normally on compact sets and whose Fourier samples are
absolutely summable. -/
theorem poisson (f : C(ℝ, E)) (hf : Integrable (f : ℝ → E))
    (hn : ∀ K : Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖))
    (hF : Summable (fun n : ℤ => ‖𝓕 (f : ℝ → E) n‖)) :
    (∑' n : ℤ, f (n : ℝ)) = ∑' n : ℤ, 𝓕 (f : ℝ → E) n := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  obtain ⟨L, _, hL⟩ := exists_dual_vector'' ℂ
    ((∑' n : ℤ, f (n : ℝ)) - ∑' n : ℤ, 𝓕 (f : ℝ → E) n)
  let g : C(ℝ, ℂ) := ⟨fun x => L (f x), L.continuous.comp f.continuous⟩
  have hg : ∀ K : Compacts ℝ,
      Summable (fun n : ℤ => ‖(g.comp (ContinuousMap.addRight n)).restrict K‖) := by
    intro K
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) ((hn K).mul_left ‖L‖)
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (ContinuousMap.norm_coe_le_norm ((f.comp (ContinuousMap.addRight n)).restrict K) x)
      (norm_nonneg _))
  have hFg : Summable (fun n : ℤ => 𝓕 (g : ℝ → ℂ) n) := by
    have hh := (L.hasSum hF.of_norm.hasSum).summable
    simpa only [g, ContinuousMap.coe_mk, fourier_scalarize _ hf L] using hh
  have hp := Real.tsum_eq_tsum_fourier hg hFg 0
  have heq : L (∑' n : ℤ, f (n : ℝ)) = L (∑' n : ℤ, 𝓕 (f : ℝ → E) n) := by
    rw [L.map_tsum (summable_samples f hn), L.map_tsum hF.of_norm]
    simpa only [g, zero_add, ContinuousMap.coe_mk, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, fourier_scalarize _ hf L,
      AddCircle.coe_zero, fourier_eval_zero, mul_one] using hp
  have hz : L ((∑' n : ℤ, f (n : ℝ)) - ∑' n : ℤ, 𝓕 (f : ℝ → E) n) = 0 := by
    rw [map_sub, heq, sub_self]
  rw [hL] at hz
  exact Complex.ofReal_eq_zero.mp hz

/-- For positive `a`, the geometric half-lattice mass is summable and equals `M / (exp a - 1)`. -/
theorem geometric_half_mass (a M : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => Real.exp (-a) ^ (n + 1) * M) ∧
      (∑' n : ℕ, Real.exp (-a) ^ (n + 1) * M) = M / (Real.exp a - 1) := by
  have hr : |Real.exp (-a)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hs := (summable_geometric_of_abs_lt_one hr).mul_right (Real.exp (-a) * M)
  constructor
  · simpa only [pow_succ, mul_assoc] using hs
  · simp_rw [pow_succ, mul_assoc]
    rw [tsum_mul_right, tsum_geometric_of_abs_lt_one hr, Real.exp_neg]
    have hex : Real.exp a - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr ha))
    field_simp

omit [NormedSpace ℂ E] [CompleteSpace E] in

/-- Exponential decay on the integer lattice bounds both positive and negative samples by the
same geometric sequence. -/
private theorem half_bounds (F : ℝ → E) (a M : ℝ)
    (hF : ∀ n : ℤ, ‖F (n : ℝ)‖ ≤ Real.exp (-a * |(n : ℝ)|) * M) (n : ℕ) :
    ‖F ((n : ℤ) + 1 : ℤ)‖ ≤ Real.exp (-a) ^ (n + 1) * M ∧
      ‖F (-((n : ℤ) + 1) : ℤ)‖ ≤ Real.exp (-a) ^ (n + 1) * M := by
  constructor
  · convert hF ((n : ℤ) + 1) using 1
    rw [Int.cast_add, Int.cast_natCast, Int.cast_one, abs_of_nonneg (by positivity)]
    rw [← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  · convert hF (-((n : ℤ) + 1)) using 1
    rw [Int.cast_neg, abs_neg, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity), ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring

omit [NormedSpace ℂ E] [CompleteSpace E] in

/-- Exponential decay on the integer lattice implies absolute summability of its samples. -/
theorem summable_fourier_lattice (F : ℝ → E) (a M : ℝ) (ha : 0 < a)
    (hF : ∀ n : ℤ, ‖F (n : ℝ)‖ ≤ Real.exp (-a * |(n : ℝ)|) * M) :
    Summable (fun n : ℤ => ‖F (n : ℝ)‖) := by
  have hs := (geometric_half_mass a M ha).1
  have hp := Summable.of_nonneg_of_le (fun n : ℕ => norm_nonneg (F ((n : ℤ) + 1 : ℤ)))
    (fun n => (half_bounds F a M hF n).1) hs
  have hm := Summable.of_nonneg_of_le (fun n : ℕ => norm_nonneg (F (-((n : ℤ) + 1) : ℤ)))
    (fun n => (half_bounds F a M hF n).2) hs
  exact Summable.of_add_one_of_neg_add_one hp hm

/-- Under Poisson summation hypotheses, exponential decay of Fourier samples bounds the
unit-mesh quadrature error by `2M / (exp a - 1)`. -/
theorem unit_mesh_error (f : C(ℝ, E)) (hf : Integrable (f : ℝ → E))
    (hn : ∀ K : Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖))
    (a M : ℝ) (ha : 0 < a)
    (hF : ∀ n : ℤ, ‖𝓕 (f : ℝ → E) n‖ ≤ Real.exp (-a * |(n : ℝ)|) * M) :
    ‖(∫ x : ℝ, f x) - ∑' n : ℤ, f (n : ℝ)‖ ≤ 2 * M / (Real.exp a - 1) := by
  have hs := (geometric_half_mass a M ha).1
  have hp := Summable.of_nonneg_of_le (fun n : ℕ => norm_nonneg (𝓕 (f : ℝ → E) ((n : ℤ) + 1 : ℤ)))
    (fun n => (half_bounds (𝓕 (f : ℝ → E)) a M hF n).1) hs
  have hm := Summable.of_nonneg_of_le (fun n : ℕ => norm_nonneg (𝓕 (f : ℝ → E) (-((n : ℤ) + 1) : ℤ)))
    (fun n => (half_bounds (𝓕 (f : ℝ → E)) a M hF n).2) hs
  have hsum := summable_fourier_lattice (𝓕 (f : ℝ → E)) a M ha hF
  have hzero : 𝓕 (f : ℝ → E) 0 = ∫ x : ℝ, f x := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp
  have hid : (∫ x : ℝ, f x) - (∑' n : ℤ, f (n : ℝ)) =
      -((∑' n : ℕ, 𝓕 (f : ℝ → E) ((n : ℤ) + 1 : ℤ)) +
        ∑' n : ℕ, 𝓕 (f : ℝ → E) (-((n : ℤ) + 1) : ℤ)) := by
    rw [poisson f hf hn hsum, tsum_of_add_one_of_neg_add_one
      (f := fun n : ℤ => 𝓕 (f : ℝ → E) n) hp.of_norm hm.of_norm,
      Int.cast_zero, hzero]
    abel
  rw [hid, norm_neg]
  calc
    _ ≤ ‖∑' n : ℕ, 𝓕 (f : ℝ → E) ((n : ℤ) + 1 : ℤ)‖ +
        ‖∑' n : ℕ, 𝓕 (f : ℝ → E) (-((n : ℤ) + 1) : ℤ)‖ := norm_add_le _ _
    _ ≤ (∑' n : ℕ, ‖𝓕 (f : ℝ → E) ((n : ℤ) + 1 : ℤ)‖) +
        ∑' n : ℕ, ‖𝓕 (f : ℝ → E) (-((n : ℤ) + 1) : ℤ)‖ :=
      add_le_add (norm_tsum_le_tsum_norm hp) (norm_tsum_le_tsum_norm hm)
    _ ≤ (∑' n : ℕ, Real.exp (-a) ^ (n + 1) * M) +
        ∑' n : ℕ, Real.exp (-a) ^ (n + 1) * M := add_le_add
      (hp.tsum_le_tsum (fun n => (half_bounds (𝓕 (f : ℝ → E)) a M hF n).1) hs)
      (hm.tsum_le_tsum (fun n => (half_bounds (𝓕 (f : ℝ → E)) a M hF n).2) hs)
    _ = _ := by rw [(geometric_half_mass a M ha).2]; ring

omit [CompleteSpace E] in

/-- The Fourier transform of the dilation `x ↦ f (h x)` is the inverse-scaled transform
evaluated at `ξ / h` for positive `h`. -/
theorem fourier_dilate (f : ℝ → E) (h ξ : ℝ) (hh : 0 < h) :
    𝓕 (fun x => f (h * x)) ξ = h⁻¹ • 𝓕 f (ξ / h) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  have hp : (fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * ξ) * I) • f (h * x)) =
      (fun x : ℝ => (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * (ξ / h)) * I) • f y)
        (h * x)) := by
    funext x
    congr 1
    congr 2
    field_simp
  rw [hp]
  simpa only [abs_of_pos (inv_pos.mpr hh)] using Measure.integral_comp_mul_left
    (fun y : ℝ => Complex.exp (↑(-2 * Real.pi * y * (ξ / h)) * I) • f y) h

/-- Exponential bounds on Fourier samples at frequencies `n / h` give mesh error at most `2M /
(exp a - 1)` under the stated convergence hypotheses. -/
theorem mesh_error (f : C(ℝ, E)) (hf : Integrable (f : ℝ → E))
    (h a M : ℝ) (hh : 0 < h) (ha : 0 < a)
    (hn : ∀ K : Compacts ℝ, Summable (fun n : ℤ =>
      ‖((f.comp ⟨fun x : ℝ => h * x, by fun_prop⟩).comp (ContinuousMap.addRight n)).restrict K‖))
    (hF : ∀ n : ℤ, ‖𝓕 (f : ℝ → E) ((n : ℝ) / h)‖ ≤
      Real.exp (-a * |(n : ℝ)|) * M) :
    ‖(∫ x : ℝ, f x) - h • (∑' n : ℤ, f (h * (n : ℝ)))‖ ≤
      2 * M / (Real.exp a - 1) := by
  let g : C(ℝ, E) := f.comp ⟨fun x : ℝ => h * x, by fun_prop⟩
  have hg : Integrable (g : ℝ → E) := (integrable_comp_mul_left_iff _ hh.ne').mpr hf
  have hFg (n : ℤ) : ‖𝓕 (g : ℝ → E) n‖ ≤ Real.exp (-a * |(n : ℝ)|) * (M / h) := by
    change ‖𝓕 (fun x : ℝ => f (h * x)) n‖ ≤ _
    rw [fourier_dilate _ h _ hh, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    calc
      _ ≤ h⁻¹ * (Real.exp (-a * |(n : ℝ)|) * M) :=
        mul_le_mul_of_nonneg_left (hF n) (inv_nonneg.mpr hh.le)
      _ = _ := by ring
  have hu := unit_mesh_error g hg hn a (M / h) ha hFg
  have hid : (∫ x : ℝ, f x) - h • (∑' n : ℤ, f (h * (n : ℝ))) =
      h • ((∫ x : ℝ, g x) - ∑' n : ℤ, g (n : ℝ)) := by
    rw [smul_sub]
    change (∫ x : ℝ, f x) - h • (∑' n : ℤ, f (h * (n : ℝ))) =
      h • (∫ x : ℝ, f (h * x)) - h • (∑' n : ℤ, f (h * (n : ℝ)))
    rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr hh), smul_smul,
      mul_inv_cancel₀ hh.ne', one_smul]
  rw [hid, norm_smul, Real.norm_of_nonneg hh.le]
  calc
    _ ≤ h * (2 * (M / h) / (Real.exp a - 1)) := mul_le_mul_of_nonneg_left hu hh.le
    _ = _ := by field_simp

/-- A holomorphic function on a strip with uniform decay, bounded horizontal integrals, and
normal convergence of mesh translates has quadrature error at most `2M / (exp (2πρ / h) -
1)`. -/
theorem strip_mesh_error (f : ℂ → E) (ρ M h : ℝ) (hρ : 0 < ρ) (hh : 0 < h)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hd : StripContour.UniformDecay f (-ρ) ρ)
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M)
    (hn : ∀ K : Compacts ℝ, Summable (fun n : ℤ =>
      ⨆ x : K, ‖f ((h * ((x : ℝ) + (n : ℝ)) : ℝ) : ℂ)‖)) :
    ‖(∫ x : ℝ, f (x : ℂ)) - h • (∑' n : ℤ, f ((h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 * M / (Real.exp (2 * Real.pi * ρ / h) - 1) := by
  let g : C(ℝ, E) := ⟨fun x : ℝ => f (x : ℂ), by
    apply hf.continuousOn.comp_continuous
    · fun_prop
    · intro x; simp only [ofReal_im, mem_setOf_eq]; constructor <;> linarith⟩
  apply mesh_error g (by simpa using! hi 0 ⟨by linarith, hρ⟩) h (2 * Real.pi * ρ / h) M hh
    (by positivity)
  · intro K
    convert hn K using 1
    funext n
    rw [ContinuousMap.norm_eq_iSup_norm]
    rfl
  · intro n
    have hb := StripContour.norm_fourier_le f ρ M ((n : ℝ) / h) hρ hf hd hi hm
    simp only [g, ContinuousMap.coe_mk, abs_div, abs_of_pos hh] at hb ⊢
    convert hb using 1
    congr 2
    ring

omit [NormedSpace ℂ E] [CompleteSpace E] in

/-- Decay of order `|x|^(-b)` with `b > 1` implies normal convergence of integer translates on
every compact set. -/
theorem normal_convergence_of_rpow_decay (f : C(ℝ, E)) (b : ℝ) (hb : 1 < b)
    (hf : (f : ℝ → E) =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-b))) :
    ∀ K : Compacts ℝ,
      Summable (fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖) := by
  intro K
  exact summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact f (zero_lt_one.trans hb) hf K).comp_tendsto
      Int.tendsto_coe_cofinite)

/-- With real-axis decay of order `|x|^(-b)` for `b > 1`, strip analyticity and the stated
horizontal integral bounds give mesh error at most `2M / (exp (2πρ / h) - 1)`; see [Aftab et
al., Lemma 4.13][AftabAnTrivisa2026]. -/
theorem strip_mesh_error_of_rpow_decay (f : ℂ → E) (ρ M h b : ℝ) (hρ : 0 < ρ)
    (hh : 0 < h) (hb : 1 < b)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hd : StripContour.UniformDecay f (-ρ) ρ)
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M)
    (hp : (fun x : ℝ => f ((h * x : ℝ) : ℂ)) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-b))) :
    ‖(∫ x : ℝ, f (x : ℂ)) - h • (∑' n : ℤ, f ((h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 * M / (Real.exp (2 * Real.pi * ρ / h) - 1) := by
  apply strip_mesh_error f ρ M h hρ hh hf hd hi hm
  let g : C(ℝ, E) := ⟨fun x : ℝ => f ((h * x : ℝ) : ℂ), by
    apply hf.continuousOn.comp_continuous
    · fun_prop
    · intro x; simp only [ofReal_im, mem_setOf_eq]; constructor <;> linarith⟩
  intro K
  convert normal_convergence_of_rpow_decay g b hb hp K using 1
  funext n
  rw [ContinuousMap.norm_eq_iSup_norm]
  rfl

end Qatlib.Papers.CommutLCHS26.MainResults.PoissonMesh
