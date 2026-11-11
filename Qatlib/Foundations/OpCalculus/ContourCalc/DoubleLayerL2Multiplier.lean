/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NormNum


/-! Actual bounded multiplication on scalar L2, with pointwise semantics for
all powers of the same operator. For the polygon dilation, the input weight
is conjugate(p(panel)/Mc), and the contraction is the multiplier's adjoint. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open MeasureTheory ContinuousLinearMap Filter
open scoped ENNReal InnerProduct
variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- Construction for scalar B in the double layer l2 multiplier model. -/
private def scalarB : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := lsmul ℂ ℂ

/-- Construction for multiplication in the double layer l2 multiplier model. -/
def multiplication (g : C(X,ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  scalarB.holderL μ ⊤ 2 2 (ContinuousMap.toLp ⊤ μ ℂ g)

/-- The identity or estimate `multiplication_ae` holds with the displayed separation, geometry and norm hypotheses. -/
theorem multiplication_ae (g : C(X,ℂ)) (f : Lp ℂ 2 μ) :
    multiplication μ g f=ᵐ[μ] fun x => g x • f x := by
  change scalarB.holder 2 (ContinuousMap.toLp ⊤ μ ℂ g) f=ᵐ[μ] _
  filter_upwards [scalarB.coeFn_holder (r := 2) (ContinuousMap.toLp ⊤ μ ℂ g) f,
    ContinuousMap.coeFn_toLp (p := ⊤) (μ := μ) (𝕜 := ℂ) g] with x hx hg
  simpa only [scalarB,lsmul_apply,hg] using hx

/-- The identity or estimate `multiplication_contraction` holds with the displayed separation, geometry and norm hypotheses. -/
theorem multiplication_contraction (g : C(X,ℂ)) (hg : ∀ x,‖g x‖≤1) : ‖multiplication μ g‖≤1 := by
  let v := ContinuousMap.toLp ⊤ μ ℂ g
  have hv : ‖v‖≤1 := by
    have hb : ∀ᵐ x ∂μ,‖v x‖≤1 := by
      filter_upwards [ContinuousMap.coeFn_toLp (p := ⊤) (μ := μ) (𝕜 := ℂ) g] with x hx
      change ‖(ContinuousMap.toLp ⊤ μ ℂ g) x‖≤1
      simpa only [hx] using hg x
    simpa using (Lp.norm_le_of_ae_bound (p := ⊤) (f := v) (by norm_num : (0 : ℝ)≤1) hb)
  have hB : ‖scalarB‖≤1 := opNorm_lsmul_le
  apply opNorm_le_bound _ (by norm_num)
  intro f
  have hh := scalarB.norm_holder_apply_apply_le (r := 2) v f
  have hc : ‖scalarB‖*‖v‖≤1 := by
    calc
      _ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right hB (norm_nonneg _)
      _ ≤ 1 := by simpa only [one_mul] using hv
  exact hh.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg f))

/-- The identity or estimate `multiplication_pow_ae` holds with the displayed separation, geometry and norm hypotheses. -/
theorem multiplication_pow_ae (g : C(X,ℂ)) (n : ℕ) (f : Lp ℂ 2 μ) :
    ((multiplication μ g)^n) f=ᵐ[μ] fun x => (g x)^n • f x := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun x => by simp)
  | succ n ih =>
    rw [pow_succ',ContinuousLinearMap.mul_apply]
    filter_upwards [multiplication_ae μ g (((multiplication μ g)^n) f),ih] with x hx hi
    rw [hx,hi,smul_smul,pow_succ']

/-- Construction for dilation Contraction in the double layer l2 multiplier model. -/
def dilationContraction (g : C(X,ℂ)) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := (multiplication μ g)†

/-- The identity or estimate `dilationContraction_norm` holds with the displayed separation, geometry and norm hypotheses. -/
theorem dilationContraction_norm (g : C(X,ℂ)) (hg : ∀ x,‖g x‖≤1) : ‖dilationContraction μ g‖≤1 := by
  simpa only [dilationContraction,adjoint.norm_map] using multiplication_contraction μ g hg

/-- The identity or estimate `dilationContraction_adjoint_pow_ae` holds with the displayed separation, geometry and norm hypotheses. -/
theorem dilationContraction_adjoint_pow_ae (g : C(X,ℂ)) (n : ℕ) (f : Lp ℂ 2 μ) :
    (((dilationContraction μ g)†)^n) f=ᵐ[μ] fun x => (g x)^n • f x := by
  simpa only [dilationContraction,adjoint_adjoint] using multiplication_pow_ae μ g n f

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2

namespace Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
open MeasureTheory ContinuousLinearMap Filter
open scoped ENNReal InnerProduct
variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
  (μ : Measure X) [IsFiniteMeasure μ]

/-- The identity or estimate `multiplication_one` holds with the displayed separation, geometry and norm hypotheses. -/
theorem multiplication_one : multiplication μ (1 : C(X,ℂ))=1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [multiplication_ae μ (1 : C(X,ℂ)) f] with x hx
  simpa using hx

/-- The identity or estimate `multiplication_pow` holds with the displayed separation, geometry and norm hypotheses. -/
theorem multiplication_pow (g : C(X,ℂ)) (n : ℕ) : (multiplication μ g)^n=multiplication μ (g^n) := by
  ext1 f
  apply Lp.ext
  filter_upwards [multiplication_pow_ae μ g n f,multiplication_ae μ (g^n) f] with x hx hy
  rw [hx,hy]
  rfl

end Qatlib.Foundations.OpCalculus.ContourCalc.DoubleLayer.L2
