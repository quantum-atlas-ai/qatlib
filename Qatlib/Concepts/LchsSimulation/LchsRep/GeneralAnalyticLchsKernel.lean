/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.LchsRep.GeneralKernelContour
import Qatlib.Concepts.LchsSimulation.Kernel.NearExponentialLchsKernel
import Qatlib.Concepts.LchsSimulation.TimeLchs

/-!
# Analytic-kernel reproduction and LCHS specialization

The theorem `general_kernel_entire_reproducing` gives a Banach-space reproduction formula for
entire functions bounded on the right half-plane. The module also exhibits an incomplete-space
obstruction, proves arbitrary power decay of `highKernelF`, and derives its dissipative matrix
evolution representation. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `general_kernel_entire_reproducing`: For an entire Banach-space-valued function bounded by one
  on the right half-plane and a lower-half-plane analytic kernel with positive-order decay, the
  integrable weighted boundary integral equals the kernel mass times `F 1`.
* `general_kernel_reproducing_incomplete_obstruction`: In an incomplete complex normed space
  containing the stated nonzero vector of norm at most one, there exist a decaying kernel and a
  bounded entire function satisfying the listed hypotheses for which the reproduction identity
  fails.
* `principal_power_kernel_lchs_representation`: For `0 < β < 1`, the principal-power kernel
  represents the forward dissipative ordered evolution as an entrywise integrable weighted
  integral of the unitary family under the stated continuity and positivity hypotheses.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.TimeLchs
open Qatlib.Concepts.LchsSimulation.Kernel
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.LchsSimulation.LchsRep

open MeasureTheory Matrix
open scoped Classical BigOperators
open scoped ComplexOrder Matrix.Norms.L2Operator
set_option warningAsError false

/-- For nonnegative `x` and positive `α`, `β`, and `c`, the product `x^α * exp (-x^β * c)` is at
most `(α / (β * c))^(α / β)`. -/
private theorem real_power_exp_bound (x α β c : ℝ) (hx : 0 ≤ x)
    (hα : 0 < α) (hβ : 0 < β) (hc : 0 < c) :
    x ^ α * Real.exp (-(x ^ β) * c) ≤ (α / (β * c)) ^ (α / β) := by
  by_cases hx0 : x = 0
  · rw [hx0, Real.zero_rpow hα.ne', zero_mul]
    exact Real.rpow_nonneg (by positivity) _
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  let a := α / (β * c)
  have ha : 0 < a := div_pos hα (mul_pos hβ hc)
  have hn : 0 < α / β := div_pos hα hβ
  have hy : 0 < x ^ β / a := div_pos (Real.rpow_pos_of_pos hxpos β) ha
  have hl := Real.log_le_sub_one_of_pos hy
  have hid : Real.log x * α - x ^ β * c =
      (α / β) * (Real.log (x ^ β / a) - x ^ β / a) + Real.log a * (α / β) := by
    rw [Real.log_div (Real.rpow_pos_of_pos hxpos β).ne' ha.ne', Real.log_rpow hxpos]
    dsimp [a]
    field_simp
    ring
  rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add, Real.rpow_def_of_pos ha]
  apply Real.exp_le_exp.mpr
  rw [show Real.log x * α + -(x ^ β) * c = Real.log x * α - x ^ β * c by ring, hid]
  nlinarith

/-- For `0 < β < 1` and any positive power `α`, the weighted norm `‖z‖^α * ‖highKernelF β z‖`
has the stated uniform bound on the closed lower half-plane. -/
theorem highKernelF_power_decay :
    ∀ β α : ℝ, 0 < β → β < 1 → 0 < α →
      ∀ z : ℂ, z.im ≤ 0 →
        ‖z‖ ^ α * ‖highKernelF β z‖ ≤
          (α / (β * Real.cos (β * Real.pi / 2))) ^ (α / β) / highKernelC β := by
  intro β α hβ hβ1 hα z hz
  have hc := highKernel_cos_pos β hβ hβ1
  have hshift : ‖z‖ ≤ ‖1 + Complex.I * z‖ := by
    have hs1 := Complex.sq_norm z
    have hs2 := Complex.sq_norm (1 + Complex.I * z)
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add] at hs1 hs2
    nlinarith [norm_nonneg z, norm_nonneg (1 + Complex.I * z)]
  have hp := Real.rpow_le_rpow (norm_nonneg z) hshift hβ.le
  have he : Real.exp (-(‖1 + Complex.I * z‖ ^ β) * Real.cos (β * Real.pi / 2)) ≤
      Real.exp (-(‖z‖ ^ β) * Real.cos (β * Real.pi / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ ‖z‖ ^ α * (Real.exp (-(‖1 + Complex.I * z‖ ^ β) *
        Real.cos (β * Real.pi / 2)) / highKernelC β) :=
      mul_le_mul_of_nonneg_left (highKernelF_norm_le β hβ hβ1 z hz)
        (Real.rpow_nonneg (norm_nonneg z) α)
    _ ≤ ‖z‖ ^ α * (Real.exp (-(‖z‖ ^ β) * Real.cos (β * Real.pi / 2)) / highKernelC β) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he (highKernelC_pos β).le)
        (Real.rpow_nonneg (norm_nonneg z) α)
    _ = (‖z‖ ^ α * Real.exp (-(‖z‖ ^ β) * Real.cos (β * Real.pi / 2))) / highKernelC β := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (real_power_exp_bound ‖z‖ α β _ (norm_nonneg z) hα hβ hc) (highKernelC_pos β).le

/-- For an entire Banach-space-valued function bounded by one on the right half-plane and a
lower-half-plane analytic kernel with positive-order decay, the integrable weighted boundary
integral equals the kernel mass times `F 1`. -/
theorem general_kernel_entire_reproducing
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ→ℂ) (F : ℂ→E)
    (hf : DifferentiableOn ℂ f {z : ℂ|z.im≤0})
    (hdecay : ∃ α C : ℝ,0<α ∧ 0≤C ∧ ∀ z : ℂ,z.im≤0→‖z‖^α*‖f z‖≤C)
    (hF : Differentiable ℂ F) (hbound : ∀ z : ℂ,0≤z.re→‖F z‖≤1)
    (hi : Integrable (fun k : ℝ=>(f (k:ℂ)/(1-Complex.I*(k:ℂ))) • F ((k:ℂ)*Complex.I))) :
    (∫ k : ℝ,(f (k:ℂ)/(1-Complex.I*(k:ℂ))) • F ((k:ℂ)*Complex.I))=
      (∫ k : ℝ,f (k:ℂ)/(1-Complex.I*(k:ℂ))) • F 1 := by
  obtain ⟨α,C,hα,hC,hdecay⟩ := hdecay
  have hw := power_kernel_weight_integrable f α C hα hC hf hdecay
  have hs := power_kernel_lower_cauchy_integral f α C hα hC hf hdecay hw
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro l
  let H := fun z : ℂ=>f z*l (F (Complex.I*z))
  have hd : DifferentiableOn ℂ H {z : ℂ|z.im≤0} :=
    hf.mul (l.differentiable.comp (hF.comp (differentiable_id.const_mul Complex.I))).differentiableOn
  have hH : ∀ z : ℂ,z.im≤0→‖z‖^α*‖H z‖≤C*‖l‖ := by
    intro z hz
    have hn : ‖l (F (Complex.I*z))‖≤‖l‖ :=
      (l.le_opNorm _).trans (mul_le_of_le_one_right (norm_nonneg _) (hbound _ (by simpa [Complex.mul_re] using! neg_nonneg.mpr hz)))
    dsimp only [H]
    rw [norm_mul]
    calc _≤‖z‖^α*(‖f z‖*‖l‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) (Real.rpow_nonneg (norm_nonneg _) _)
         _=(‖z‖^α*‖f z‖)*‖l‖ := by ring
         _≤C*‖l‖ := mul_le_mul_of_nonneg_right (hdecay z hz) (norm_nonneg _)
  have he (k : ℝ) : l ((f (k:ℂ)/(1-Complex.I*(k:ℂ))) • F ((k:ℂ)*Complex.I))=
      H (k:ℂ)/(1-Complex.I*(k:ℂ)) := by
    simp only [map_smul,smul_eq_mul,H,mul_comm Complex.I (k:ℂ)]
    ring
  have hHi : Integrable (fun k : ℝ=>H (k:ℂ)/(1-Complex.I*(k:ℂ))) := by
    simpa only [he] using! l.integrable_comp hi
  have hscalar :=
      power_kernel_lower_cauchy_integral H α (C*‖l‖) hα (mul_nonneg hC (norm_nonneg _)) hd hH hHi
  rw [← l.integral_comp_comm hi,map_smul]
  simp_rw [he]
  rw [hscalar,hs]
  simp only [H,smul_eq_mul, mul_neg,Complex.I_mul_I,neg_neg,mul_assoc]

/-- In an incomplete complex normed space containing the stated nonzero vector of norm at most
one, there exist a decaying kernel and a bounded entire function satisfying the listed
hypotheses for which the reproduction identity fails. -/
theorem general_kernel_reproducing_incomplete_obstruction
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hE : ¬ CompleteSpace E) (v : E) (hv : ‖v‖ ≤ 1) (hv0 : v ≠ 0) :
    ∃ (f : ℂ → ℂ) (F : ℂ → E),
      DifferentiableOn ℂ f {z : ℂ | z.im ≤ 0} ∧
      (∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧ ∀ z : ℂ, z.im ≤ 0 → ‖z‖ ^ α * ‖f z‖ ≤ C) ∧
      Differentiable ℂ F ∧
      (∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ 1) ∧
      Integrable (fun k : ℝ =>
        (f (k : ℂ) / (1 - Complex.I * (k : ℂ))) • F ((k : ℂ) * Complex.I)) ∧
      (∫ k : ℝ, (f (k : ℂ) / (1 - Complex.I * (k : ℂ))) • F ((k : ℂ) * Complex.I)) ≠
        (∫ k : ℝ, f (k : ℂ) / (1 - Complex.I * (k : ℂ))) • F 1 := by
  have hβ : (0 : ℝ) < 1 / 2 := by norm_num
  have hβ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hn := near_exponential_kernel_analytic_normalization (1 / 2) hβ hβ1
  refine ⟨highKernelF (1 / 2), fun _ => v, ?_, ?_, differentiable_const v,
    fun _ _ => hv, ?_, ?_⟩
  · intro z hz
    exact (highKernelF_analyticAt _ z hz).differentiableAt.differentiableWithinAt
  · refine ⟨1, (1 / ((1 / 2) * Real.cos ((1 / 2) * Real.pi / 2))) ^ ((1 : ℝ) / (1 / 2)) /
        highKernelC (1 / 2), by norm_num, ?_, ?_⟩
    · have hc := highKernelC_pos (1 / 2)
      have hcos := highKernel_cos_pos (1 / 2) hβ hβ1
      positivity
    · exact highKernelF_power_decay (1 / 2) 1 hβ hβ1 (by norm_num)
  · exact hn.2.2.1.smul_const v
  · change (∫ k : ℝ, highKernelG (1 / 2) k • v) ≠
      (∫ k : ℝ, highKernelG (1 / 2) k) • v
    have hz : (∫ k : ℝ, highKernelG (1 / 2) k • v) = 0 := by
      simp [MeasureTheory.integral, hE]
    rw [hz, hn.2.2.2, one_smul]
    exact Ne.symm hv0

/-- The norm of each matrix entry is at most the matrix operator norm. -/
private theorem kernel_entry_norm_le {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i j : I) : ‖A i j‖ ≤ ‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j)
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk, mul_one] at hn
  have hi :=
      PiLp.norm_apply_le (toEuclidean_fromVec (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j)) i
  have he : (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i = A i j := by
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]
  change ‖(A *ᵥ Qatlib.Foundations.PureStateMath.Ket j) i‖ ≤ ‖toEuclidean_fromVec
      (A *ᵥ Qatlib.Foundations.PureStateMath.Ket j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- For `0 < β < 1`, the principal-power kernel represents the forward dissipative ordered
evolution as an entrywise integrable weighted integral of the unitary family under the
stated continuity and positivity hypotheses. -/
theorem principal_power_kernel_lchs_representation :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (β : ℝ) (L H : ℝ → Matrix I I ℂ)
    (s t : ℝ),
    0 < β → β < 1 →
    Continuous L → Continuous H →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) →
    s ≤ t →
      (∀ i j : I, Integrable (fun k : ℝ => highKernelG β k *
          (orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t) i j)) ∧
      (∫ k : ℝ, highKernelG β k •
          orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t) =
        orderedEvolution (fun u => L u + Complex.I • H u) s t := by
  intro I _ _ β L H s t hβ hβ1 hL hH hPSD hHerm hst
  let F := fun z : ℂ => orderedEvolution (fun u => z • L u + Complex.I • H u) s t
  let U := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u + k • L u)) s t
  have hF := time_dependent_lchs_entire_parameter I L H s t hL hH hPSD hHerm hst
  have hb (k : ℝ) : F ((k : ℂ) * Complex.I) = U k := by
    dsimp [F, U]
    congr 1
    funext u
    rw [smul_add, ← Complex.coe_smul, smul_smul, mul_comm]
    exact add_comm _ _
  have hUc : Continuous U := by
    have h := hF.1.continuous.comp
      (Complex.continuous_ofReal.mul (continuous_const (y := Complex.I)))
    change Continuous (fun k : ℝ => F ((k : ℂ) * Complex.I)) at h
    simpa only [hb] using! h
  have hUu (k : ℝ) : U k ∈ unitaryGroup I ℂ :=
    ordered_evolution_hermitian_unitary I (fun u => H u + k • L u)
      (hH.add (hL.const_smul k))
      (fun u => (hHerm u).add ((hPSD u).isHermitian.smul (R := ℝ) (IsSelfAdjoint.all k))) s t
  have hi := highKernel_unitary_integrable I β U hβ hβ1 hUc hUu
  refine ⟨hi.1, ?_⟩
  have hFone : F 1 = orderedEvolution (fun u => L u + Complex.I • H u) s t := by
    simp [F]
  rw [← hFone]
  change (∫ k : ℝ, highKernelG β k • U k) = F 1
  ext i j
  let e : Matrix I I ℂ →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := by intro A B; rfl
      map_smul' := by intro c A; rfl }
  have he (A : Matrix I I ℂ) : e A = A i j := rfl
  let f := fun z : ℂ => highKernelF β z * F (Complex.I * z) i j
  have hdF : Differentiable ℂ (fun z : ℂ => F (Complex.I * z) i j) := by
    simpa only [Function.comp_def, he] using!
      e.differentiable.comp (hF.1.comp (differentiable_id.const_mul Complex.I))
  have hfd : DifferentiableOn ℂ f {z : ℂ | z.im ≤ 0} := by
    intro z hz
    exact ((highKernelF_analyticAt β z hz).differentiableAt.differentiableWithinAt).mul
      (hdF z).differentiableWithinAt
  have hfbound : ∀ z : ℂ, z.im ≤ 0 →
      ‖f z‖ ≤ (1 / highKernelC β) *
        Real.exp (-Real.cos (β * Real.pi / 2) * ‖1 + Complex.I * z‖ ^ β) := by
    intro z hz
    have hn : ‖F (Complex.I * z) i j‖ ≤ 1 :=
      (kernel_entry_norm_le _ i j).trans (hF.2 _ (by simpa [Complex.mul_re] using! neg_nonneg.mpr hz))
    calc
      _ ≤ ‖highKernelF β z‖ := by
        dsimp only [f]
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) hn
      _ ≤ _ := by simpa only [div_eq_mul_inv, one_mul, neg_mul, mul_neg, mul_comm, mul_left_comm,
        mul_assoc] using! highKernelF_norm_le β hβ hβ1 z hz
  have hweight (k : ℝ) : f (k : ℂ) / (1 - Complex.I * (k : ℂ)) =
      highKernelG β k * U k i j := by
    dsimp only [f, highKernelG]
    have hphase : Complex.I * (k : ℂ) = (k : ℂ) * Complex.I := mul_comm _ _
    rw [hphase, hb]
    simp only [div_eq_mul_inv]
    ring
  have hfi : Integrable (fun k : ℝ => f (k : ℂ) / (1 - Complex.I * (k : ℂ))) := by
    simpa only [hweight] using! hi.1 i j
  have hscalar := highKernel_lower_cauchy_integral f β (Real.cos (β * Real.pi / 2))
    (1 / highKernelC β) hβ (highKernel_cos_pos β hβ hβ1)
    (by have hC := highKernelC_pos β; positivity) hfd hfbound hfi
  simp only [hweight] at hscalar
  have hpole : (2 * Real.pi : ℂ) * f (-Complex.I) = F 1 i j := by
    dsimp only [f]
    rw [show Complex.I * (-Complex.I) = 1 by simp [Complex.I_mul_I], ← mul_assoc,
      highKernelF_pole_value, one_mul]
  rw [hpole] at hscalar
  have hm := e.integral_comp_comm hi.2
  simp only [map_smul, smul_eq_mul] at hm
  exact hm.symm.trans hscalar

end Qatlib.Concepts.LchsSimulation.LchsRep
