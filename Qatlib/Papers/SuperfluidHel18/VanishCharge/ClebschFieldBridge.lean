/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschAlgebra
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
public import Mathlib.Analysis.BoxIntegral.Integrability

/-!
# Clebsch helicity of actual twice differentiable potentials

[Kedia2018SuperfluidHelicity], Sections II–IV,
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
This module bridges the Cartesian jet identities of
`Qatlib.Papers.SuperfluidHel18.VanishCharge.ClebschAlgebra` to actual scalar fields
`φ, α, β : (Fin 3 → ℝ) → ℝ`. The partial derivatives of a `C²` field form a gradient jet
and a symmetric Hessian jet, so the public identities apply verbatim: the helicity density
of the Clebsch velocity `∇φ + α ∇β` against the vorticity `∇α × ∇β` is the divergence of
the flux `φ • (∇α × ∇β)`.

The local-to-integral step is the divergence theorem of
`Mathlib.Analysis.BoxIntegral.DivergenceTheorem` on a closed rectangular box: the integral
of the helicity density equals the signed flux of `φ • (∇α × ∇β)` through the six faces.
This is a statement about smooth single-valued potentials on a box; it derives neither the
Gross–Pitaevskii dynamics, nor decay conditions at infinity, nor the singular vortex-core
geometry of the paper, where helicity concentrates on vortex lines.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.VanishCharge

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open MeasureTheory
open scoped BigOperators

/-! ### Actual Cartesian jets of a scalar field -/

/-- The `i`-th Cartesian basis vector of `Fin 3 → ℝ`. -/
def stdBasis (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1

/-- The zeroth component of the Cartesian cross product. -/
theorem cross3_apply_zero (u w : Fin 3 → ℝ) : cross3 u w 0 = u 1 * w 2 - u 2 * w 1 := rfl

/-- The first component of the Cartesian cross product. -/
theorem cross3_apply_one (u w : Fin 3 → ℝ) : cross3 u w 1 = u 2 * w 0 - u 0 * w 2 := rfl

/-- The second component of the Cartesian cross product. -/
theorem cross3_apply_two (u w : Fin 3 → ℝ) : cross3 u w 2 = u 0 * w 1 - u 1 * w 0 := rfl

/-- The partial derivative of a scalar field along the `i`-th coordinate direction. -/
noncomputable def dPart (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → ℝ :=
  fun x => fderiv ℝ f x (stdBasis i)

/-- The Cartesian gradient jet of a scalar field at a point. -/
noncomputable def gradJet (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => dPart j f x

/-- The Hessian jet of a scalar field at a point; the first index is the outer
differentiation direction. -/
noncomputable def hessJet (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => fderiv ℝ (dPart j f) x (stdBasis i)

/-- A partial derivative is the evaluation of the total derivative on a basis vector. -/
theorem hasFDerivAt_dPart (i : Fin 3) {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    HasFDerivAt (dPart i f)
      ((ContinuousLinearMap.apply ℝ ℝ (stdBasis i)).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
  (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ ℝ (stdBasis i))).comp x
    hf.hasFDerivAt

/-- The derivative of a partial derivative evaluated on a vector. -/
theorem fderiv_dPart_apply (i : Fin 3) {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v : Fin 3 → ℝ) :
    fderiv ℝ (dPart i f) x v = fderiv ℝ (fderiv ℝ f) x v (stdBasis i) := by
  rw [(hasFDerivAt_dPart i hf).fderiv]
  simp

/-- The Hessian jet entries are iterated directional derivatives along basis vectors. -/
theorem hessJet_eq_second (i j : Fin 3) {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    hessJet f x i j = fderiv ℝ (fderiv ℝ f) x (stdBasis i) (stdBasis j) := by
  rw [hessJet, fderiv_dPart_apply j hf]

/-- The second derivative evaluated on a vector and a basis vector, expanded over the
Cartesian basis. -/
theorem second_apply_eq_sum {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (v : Fin 3 → ℝ) (j : Fin 3) :
    fderiv ℝ (fderiv ℝ f) x v (stdBasis j) = ∑ i, v i * hessJet f x i j := by
  have hv : v = ∑ i, v i • stdBasis i := by
    ext k
    simp only [stdBasis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_lhs => rw [hv]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, stdBasis,
    hessJet_eq_second _ _ hf]

/-- A `C²` field has a differentiable derivative. -/
theorem differentiableAt_fderiv_of_contDiffAt {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (fderiv ℝ f) x :=
  ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

/-- At a `C²` point, the Hessian jet is symmetric, which is the hypothesis under which the
public Clebsch identities hold. -/
theorem hessJet_symmetric {f : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ} (hf : ContDiffAt ℝ 2 f x) :
    SymmetricJet (hessJet f x) := by
  intro i j
  have hfd := differentiableAt_fderiv_of_contDiffAt hf
  rw [hessJet_eq_second i j hfd, hessJet_eq_second j i hfd]
  exact hf.isSymmSndFDerivAt (by simp) (stdBasis i) (stdBasis j)

/-! ### The vorticity of an actual Clebsch pair -/

/-- The product rule for two partial derivatives, phrased with Hessian jets. -/
theorem fderiv_dPart_mul_apply (k l : Fin 3) {f g : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (hg : DifferentiableAt ℝ (fderiv ℝ g) x)
    (v : Fin 3 → ℝ) :
    fderiv ℝ (dPart k f * dPart l g) x v =
      dPart k f x * ∑ i, v i * hessJet g x i l + dPart l g x * ∑ i, v i * hessJet f x i k := by
  have h := ((hasFDerivAt_dPart k hf).mul (hasFDerivAt_dPart l hg)).fderiv
  rw [h]
  simp only [add_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [second_apply_eq_sum hg, second_apply_eq_sum hf]

/-- The Jacobian row of the `j`-th component of `∇α × ∇β`, as a continuous linear map. -/
noncomputable def crossGradRowDeriv (α β : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) (j : Fin 3) :
    (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ∑ i, vorticityJacobian (gradJet α x) (gradJet β x) (hessJet α x) (hessJet β x) i j •
    (ContinuousLinearMap.proj i)

/-- A row of the vorticity derivative acts by contraction with the displacement. -/
theorem crossGradRowDeriv_apply (α β : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) (j : Fin 3)
    (v : Fin 3 → ℝ) :
    crossGradRowDeriv α β x j v =
      ∑ i, v i * vorticityJacobian (gradJet α x) (gradJet β x) (hessJet α x) (hessJet β x) i j := by
  simp [crossGradRowDeriv, mul_comm]

/-- Each component of the vorticity `∇α × ∇β` of two `C²` potentials is differentiable,
with the public vorticity Jacobian as its derivative. -/
theorem hasFDerivAt_crossGrad (α β : (Fin 3 → ℝ) → ℝ) {x : Fin 3 → ℝ} (j : Fin 3)
    (hα : ContDiffAt ℝ 2 α x) (hβ : ContDiffAt ℝ 2 β x) :
    HasFDerivAt (fun y => cross3 (gradJet α y) (gradJet β y) j)
      (crossGradRowDeriv α β x j) x := by
  have hdα := differentiableAt_fderiv_of_contDiffAt hα
  have hdβ := differentiableAt_fderiv_of_contDiffAt hβ
  have key : ∀ k l m n : Fin 3,
      HasFDerivAt (fun y => dPart k α y * dPart l β y - dPart m α y * dPart n β y)
        ((dPart k α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis l)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart l β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis k)).comp
            (fderiv ℝ (fderiv ℝ α) x))) -
        (dPart m α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis n)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart n β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis m)).comp
            (fderiv ℝ (fderiv ℝ α) x)))) x :=
    fun k l m n => ((hasFDerivAt_dPart k hdα).mul (hasFDerivAt_dPart l hdβ)).sub
      ((hasFDerivAt_dPart m hdα).mul (hasFDerivAt_dPart n hdβ))
  have clm0 : ((dPart 1 α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 2)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart 2 β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 1)).comp
            (fderiv ℝ (fderiv ℝ α) x))) -
        (dPart 2 α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 1)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart 1 β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 2)).comp
            (fderiv ℝ (fderiv ℝ α) x)))) =
        crossGradRowDeriv α β x 0 := by
    ext v
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply]
    rw [second_apply_eq_sum hdβ, second_apply_eq_sum hdα, second_apply_eq_sum hdβ,
      second_apply_eq_sum hdα, crossGradRowDeriv_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    simp only [vorticityJacobian, cross3_apply_zero, gradJet]
    exact Finset.sum_congr rfl fun i _ => by ring
  have clm1 : ((dPart 2 α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 0)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart 0 β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 2)).comp
            (fderiv ℝ (fderiv ℝ α) x))) -
        (dPart 0 α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 2)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart 2 β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 0)).comp
            (fderiv ℝ (fderiv ℝ α) x)))) =
        crossGradRowDeriv α β x 1 := by
    ext v
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply]
    rw [second_apply_eq_sum hdβ, second_apply_eq_sum hdα, second_apply_eq_sum hdβ,
      second_apply_eq_sum hdα, crossGradRowDeriv_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    simp only [vorticityJacobian, cross3_apply_one, gradJet]
    exact Finset.sum_congr rfl fun i _ => by ring
  have clm2 : ((dPart 0 α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 1)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart 1 β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 0)).comp
            (fderiv ℝ (fderiv ℝ α) x))) -
        (dPart 1 α x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 0)).comp
            (fderiv ℝ (fderiv ℝ β) x)) +
          dPart 0 β x • ((ContinuousLinearMap.apply ℝ ℝ (stdBasis 1)).comp
            (fderiv ℝ (fderiv ℝ α) x)))) =
        crossGradRowDeriv α β x 2 := by
    ext v
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply]
    rw [second_apply_eq_sum hdβ, second_apply_eq_sum hdα, second_apply_eq_sum hdβ,
      second_apply_eq_sum hdα, crossGradRowDeriv_apply]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    simp only [vorticityJacobian, cross3_apply_two, gradJet]
    exact Finset.sum_congr rfl fun i _ => by ring
  fin_cases j
  · exact HasFDerivAt.congr_fderiv (key 1 2 2 1) clm0
  · exact HasFDerivAt.congr_fderiv (key 2 0 0 2) clm1
  · exact HasFDerivAt.congr_fderiv (key 0 1 1 0) clm2

/-! ### The boundary flux and the pointwise divergence identity -/

/-- The boundary flux `φ • (∇α × ∇β)` of the actual Clebsch potentials. -/
noncomputable def clebschFlux (φ α β : (Fin 3 → ℝ) → ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun x j => φ x * cross3 (gradJet α x) (gradJet β x) j

/-- The total derivative of the boundary flux. -/
noncomputable def clebschFluxDeriv (φ α β : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun j =>
    φ x • crossGradRowDeriv α β x j + cross3 (gradJet α x) (gradJet β x) j • fderiv ℝ φ x)

/-- The helicity density of the actual Clebsch velocity `∇φ + α ∇β` against `∇α × ∇β`. -/
noncomputable def clebschHelicityDensity (φ α β : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  dot3 (clebschVelocity (α x) (gradJet φ x) (gradJet β x))
    (cross3 (gradJet α x) (gradJet β x))

/-- The boundary flux of `C²` potentials is differentiable, with the expected derivative. -/
theorem hasFDerivAt_clebschFlux {φ α β : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hα : ContDiffAt ℝ 2 α x) (hβ : ContDiffAt ℝ 2 β x) :
    HasFDerivAt (clebschFlux φ α β) (clebschFluxDeriv φ α β x) x :=
  hasFDerivAt_pi.2 fun j => hφ.hasFDerivAt.mul (hasFDerivAt_crossGrad α β j hα hβ)

/-- Pointwise identity for actual fields: the divergence of the boundary flux equals the
helicity density of the Clebsch velocity. This is the field-level version of
`Qatlib.Papers.SuperfluidHel18.VanishCharge.helicity_is_divergence`, now for actual `C²`
potentials rather than abstract jets. -/
theorem clebschFluxDeriv_trace {φ α β : (Fin 3 → ℝ) → ℝ} {x : Fin 3 → ℝ}
    (hα : ContDiffAt ℝ 2 α x) (hβ : ContDiffAt ℝ 2 β x) :
    ∑ i, clebschFluxDeriv φ α β x (stdBasis i) i = clebschHelicityDensity φ α β x := by
  simp only [clebschHelicityDensity]
  rw [helicity_is_divergence (φ x) (α x) (gradJet φ x) (gradJet α x) (gradJet β x)
    (hessJet α x) (hessJet β x) (hessJet_symmetric hα) (hessJet_symmetric hβ)]
  have hsingle : ∀ i : Fin 3,
      ∑ k, stdBasis i k *
          vorticityJacobian (gradJet α x) (gradJet β x) (hessJet α x) (hessJet β x) k i =
        vorticityJacobian (gradJet α x) (gradJet β x) (hessJet α x) (hessJet β x) i i := by
    intro i
    simp only [stdBasis, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  simp only [clebschFluxDeriv, ContinuousLinearMap.pi_apply, add_apply, smul_apply,
    smul_eq_mul, crossGradRowDeriv_apply]
  simp only [hsingle]
  simp only [divergenceJet, Fin.sum_univ_three, helicityFluxJacobian, gradJet, dPart]
  ring


/-! ### The box divergence theorem for the Clebsch flux -/

/-- The partial derivative of a `C¹` field is continuous. -/
theorem continuous_dPart (j : Fin 3) {f : (Fin 3 → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (dPart j f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The helicity density of `C¹`/`C²` Clebsch potentials is continuous. -/
theorem continuous_clebschHelicityDensity {φ α β : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β) :
    Continuous (fun x => clebschHelicityDensity φ α β x) := by
  have hca : Continuous α := hα.continuous
  have hdφ0 : Continuous (dPart 0 φ) := continuous_dPart 0 hφ
  have hdφ1 : Continuous (dPart 1 φ) := continuous_dPart 1 hφ
  have hdφ2 : Continuous (dPart 2 φ) := continuous_dPart 2 hφ
  have hdα0 : Continuous (dPart 0 α) := continuous_dPart 0 (hα.of_le (by norm_num))
  have hdα1 : Continuous (dPart 1 α) := continuous_dPart 1 (hα.of_le (by norm_num))
  have hdα2 : Continuous (dPart 2 α) := continuous_dPart 2 (hα.of_le (by norm_num))
  have hdβ0 : Continuous (dPart 0 β) := continuous_dPart 0 (hβ.of_le (by norm_num))
  have hdβ1 : Continuous (dPart 1 β) := continuous_dPart 1 (hβ.of_le (by norm_num))
  have hdβ2 : Continuous (dPart 2 β) := continuous_dPart 2 (hβ.of_le (by norm_num))
  simp only [clebschHelicityDensity, clebschVelocity, dot3, cross3_apply_zero,
    cross3_apply_one, cross3_apply_two, gradJet]
  fun_prop

/-- The boundary flux of `C¹`/`C²` Clebsch potentials is continuous. -/
theorem continuous_clebschFlux {φ α β : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β) :
    Continuous (clebschFlux φ α β) := by
  have hd : Differentiable ℝ (clebschFlux φ α β) := fun x =>
    (hasFDerivAt_clebschFlux (hφ.contDiffAt.differentiableAt (by norm_num)) hα.contDiffAt
      hβ.contDiffAt).differentiableAt
  exact hd.continuous

open BoxIntegral BoxIntegral.IntegrationParams in
/-- Divergence theorem over a box, `GP` integral form: the Henstock–Kurzweil-type integral
of the Clebsch helicity density of `C²` potentials over a closed rectangular box equals the
signed sum of the flux `φ • (∇α × ∇β)` through the six faces. -/
theorem hasIntegral_GP_clebschFlux_divergence (φ α β : (Fin 3 → ℝ) → ℝ)
    (I : Box (Fin 3))
    (hφ : ∀ x, DifferentiableAt ℝ φ x)
    (hα : ∀ x, ContDiffAt ℝ 2 α x) (hβ : ∀ x, ContDiffAt ℝ 2 β x) :
    HasIntegral I GP (fun x => clebschHelicityDensity φ α β x) BoxAdditiveMap.volume
      (∑ i : Fin 3, (integral (I.face i) GP
          (fun y => clebschFlux φ α β (i.insertNth (I.upper i) y) i)
          BoxAdditiveMap.volume -
        integral (I.face i) GP
          (fun y => clebschFlux φ α β (i.insertNth (I.lower i) y) i)
          BoxAdditiveMap.volume)) := by
  have h := hasIntegral_GP_divergence_of_forall_hasDerivWithinAt I (clebschFlux φ α β)
    (fun x => clebschFluxDeriv φ α β x) ∅ (by simp)
    (fun x hx => by simp at hx)
    (fun x hx =>
      (hasFDerivAt_clebschFlux (hφ x) (hα x) (hβ x)).hasFDerivWithinAt)
  convert h using 3
  rename_i x
  exact (clebschFluxDeriv_trace (hα x) (hβ x)).symm

open BoxIntegral BoxIntegral.IntegrationParams in
set_option maxHeartbeats 800000 in
/-- Integral form of the Clebsch helicity identity: over a rectangular box, the Lebesgue
integral of the helicity density `u · ω` of the Clebsch velocity equals the signed boundary
flux of `φ • (∇α × ∇β)` through the six faces. This is the rigorous local-to-integral step
for smooth single-valued potentials; boundary decay, the vortex singular set and the
Gross–Pitaevskii dynamics are not addressed. -/
theorem integral_clebschHelicityDensity_eq_faceFlux (φ α β : (Fin 3 → ℝ) → ℝ)
    (I : Box (Fin 3))
    (hφ : ContDiff ℝ 1 φ) (hα : ContDiff ℝ 2 α) (hβ : ContDiff ℝ 2 β) :
    ∫ x in (I : Set (Fin 3 → ℝ)), clebschHelicityDensity φ α β x =
      ∑ i : Fin 3, ((∫ y in (I.face i : Set (Fin 2 → ℝ)),
            clebschFlux φ α β (i.insertNth (I.upper i) y) i)
          - ∫ y in (I.face i : Set (Fin 2 → ℝ)),
            clebschFlux φ α β (i.insertNth (I.lower i) y) i) := by
  have hGP0 := hasIntegral_GP_clebschFlux_divergence φ α β I
    (fun x => hφ.contDiffAt.differentiableAt (by norm_num)) (fun x => hα.contDiffAt)
    (fun x => hβ.contDiffAt)
  have hGP : HasIntegral I GP (fun x => clebschHelicityDensity φ α β x)
      ((volume : Measure (Fin 3 → ℝ)).toBoxAdditive.toSMul)
      (∑ i : Fin 3, (integral (I.face i) GP
          (fun y => clebschFlux φ α β (i.insertNth (I.upper i) y) i)
          ((volume : Measure (Fin 2 → ℝ)).toBoxAdditive.toSMul) -
        integral (I.face i) GP
          (fun y => clebschFlux φ α β (i.insertNth (I.lower i) y) i)
          ((volume : Measure (Fin 2 → ℝ)).toBoxAdditive.toSMul))) := hGP0
  have hcf : Continuous (clebschFlux φ α β) := continuous_clebschFlux hφ hα hβ
  have hD : HasIntegral I GP (fun x => clebschHelicityDensity φ α β x)
      ((volume : Measure (Fin 3 → ℝ)).toBoxAdditive.toSMul)
      (∫ x in (I : Set (Fin 3 → ℝ)), clebschHelicityDensity φ α β x) :=
    (continuous_clebschHelicityDensity hφ hα hβ).continuousOn.hasBoxIntegral
      (volume : Measure (Fin 3 → ℝ)) GP
  refine Eq.trans (hD.unique hGP) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcfi : ContinuousOn (fun z => clebschFlux φ α β z i) (Box.Icc I) :=
    ((continuous_apply i).comp hcf).continuousOn
  have hface : ∀ b ∈ Set.Icc (I.lower i) (I.upper i),
      HasIntegral (I.face i) GP
        (fun y => clebschFlux φ α β (i.insertNth b y) i)
        ((volume : Measure (Fin 2 → ℝ)).toBoxAdditive.toSMul)
        (∫ y in (I.face i : Set (Fin 2 → ℝ)),
          clebschFlux φ α β (i.insertNth b y) i) := fun b hb =>
    ((hcfi.comp (continuousOn_const.finInsertNth i continuousOn_id)
        (I.mapsTo_insertNth_face_Icc hb))).hasBoxIntegral
      (volume : Measure (Fin 2 → ℝ)) GP
  rw [(hface (I.upper i) (Set.right_mem_Icc.2 (I.lower_le_upper i))).integral_eq,
    (hface (I.lower i) (Set.left_mem_Icc.2 (I.lower_le_upper i))).integral_eq]

end Qatlib.Papers.SuperfluidHel18.VanishCharge
