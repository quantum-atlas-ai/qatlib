/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LaplaceEigen24.MainResults.SourceModel
import Qatlib.Concepts.LchsSimulation.LchsRep.GeneralKernelContour

/-!
# LaplaceEigen24 — the Laplace-transform LCHS representation (Theorem 4)

Fixed source: arXiv:2411.04010, Theorem 4, printed p.10–11, Eq. (27), proved on
p.11 and in Appendix (Section 3.1).

The printed statement (verbatim scope): let `A = L + iH` with `L ⪰ 0`
positive semidefinite and `H` Hermitian; let `f` be in the Hardy space
`H¹(ℂ₋)` with boundary trace on `ℝ`, continuous up to the closure of the lower
half-plane, and normalized by `∫_ℝ f(k)/(1-ik) dk = 1`; let `g ∈ L¹(ℝ₊)`.
Then

`h(A) = ∫₀^∞ ∫_ℝ f(k) g(t)/(1-ik) · e^{-it(kL+H)} dk dt`   (27)

where `h` is the Laplace transform of `g`.

Formalization notes (deviations, in the style of the Frozen
`Qatlib.Papers.LinDynamics23.LchsRep.GeneralAnalyticKernelLchs`
contract): the analyticity premise is recorded as `DifferentiableOn ℂ f
{z | z.im ≤ 0}` (the contour-rectangle hypothesis actually used); `f ∈ H¹(ℂ₋)`
is recorded through the printed decay condition `‖z‖^α‖f z‖ ≤ C` on the lower
half-plane, which makes the boundary trace `f(k)/(1-ik)` absolutely integrable
(`power_kernel_weight_integrable`); the matrix exponential is the actual
Banach-algebra exponential of `Matrix I I ℂ`.

The proof follows the printed route: for each fixed `t ≥ 0`, Theorem 3 applied
to the entire bounded function `z ↦ e^{-t(zL+iH)}` reproduces
`e^{-t(L+iH)}`; then integrate over `t`. The abstract Theorem 3 engine is the
Frozen `general_kernel_entire_reproducing`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LaplaceEigen24.MainResults

open Qatlib.Concepts.LchsSimulation.StaticLchs

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The LCHS integrand `exp (-i t • (kL + H))` agrees with the parametrized
entire function `z ↦ exp (-t • (zL + iH))` evaluated at `z = i k`.
Helper for the fixed-`t` reproduction step of Theorem 4. -/
theorem lchsKernelEvolution_eq_parametrized (L H : Matrix I I ℂ) (k t : ℝ) :
    lchsKernelEvolution L H k t =
      NormedSpace.exp ((-(t : ℂ)) • (((k : ℂ) * Complex.I) • L + Complex.I • H)) := by
  dsimp only [lchsKernelEvolution]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply]
  ring

/-- Fixed-time reproduction: the printed Theorem 3 (Frozen
`general_kernel_entire_reproducing`) applied to the bounded entire function
`z ↦ e^{-t(zL+iH)}` gives, for every `t ≥ 0`,
`∫_ℝ f(k)/(1-ik) · e^{-it(kL+H)} dk = e^{-t(L+iH)}`.
This is the fixed-`t` identity used in the proof of Theorem 4, Eq. (27). -/
theorem lchs_kernel_representation_fixed_time
    (f : ℂ → ℂ) (L H : Matrix I I ℂ)
    (hL : L.PosSemidef) (hH : H.IsHermitian)
    (hf : DifferentiableOn ℂ f {z : ℂ | z.im ≤ 0})
    (hdecay : ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ z : ℂ, z.im ≤ 0 → ‖z‖ ^ α * ‖f z‖ ≤ C)
    (hnorm : (∫ k : ℝ, laplaceKernel f k) = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ k : ℝ, laplaceKernel f k • lchsKernelEvolution L H k t) =
      cartesianEvolution L H t := by
  obtain ⟨α, C, hα, hC, hd⟩ := hdecay
  have hw : Integrable (laplaceKernel f) :=
    Qatlib.Concepts.LchsSimulation.LchsRep.power_kernel_weight_integrable
      f α C hα hC hf hd
  have hwc : Continuous (laplaceKernel f) :=
    Qatlib.Concepts.LchsSimulation.LchsRep.power_kernel_weight_continuous f hf
  let F : ℂ → Matrix I I ℂ :=
    fun z => NormedSpace.exp ((-(t : ℂ)) • (z • L + Complex.I • H))
  have hdF : Differentiable ℂ F := by
    intro z
    apply (NormedSpace.exp_analytic (𝕂 := ℂ) _).differentiableAt.comp z
    have ha : DifferentiableAt ℂ (fun z : ℂ => z • L + Complex.I • H) z := by fun_prop
    exact ha.const_smul (-(t : ℂ))
  have hbF (z : ℂ) (hz : 0 ≤ z.re) : ‖F z‖ ≤ 1 := by
    have he : F z = NormedSpace.exp ((-t : ℝ) • (z • L + Complex.I • H)) := by
      dsimp only [F]
      rw [← Complex.ofReal_neg, Complex.coe_smul]
    rw [he]
    exact Qatlib.Concepts.LchsSimulation.StaticLchs.static_lchs_halfplane_exponential_contraction
      L H hL hH z hz t ht
  have hbound (k : ℝ) : F ((k : ℂ) * Complex.I) = lchsKernelEvolution L H k t :=
    (lchsKernelEvolution_eq_parametrized L H k t).symm
  have hUc : Continuous (fun k : ℝ => lchsKernelEvolution L H k t) := by
    have h := hdF.continuous.comp
      (Complex.continuous_ofReal.mul (continuous_const (y := Complex.I)))
    change Continuous (fun k : ℝ => F ((k : ℂ) * Complex.I)) at h
    simpa only [hbound] using h
  have hint : Integrable
      (fun k : ℝ => laplaceKernel f k • lchsKernelEvolution L H k t) := by
    apply hw.norm.mono' (hwc.smul hUc).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun k => by
      change ‖laplaceKernel f k • lchsKernelEvolution L H k t‖ ≤ ‖laplaceKernel f k‖
      rw [norm_smul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      rw [← hbound]
      exact hbF ((k : ℂ) * Complex.I) (by simp))
  have he := Qatlib.Concepts.LchsSimulation.LchsRep.general_kernel_entire_reproducing
    f F hf ⟨α, C, hα, hC, hd⟩ hdF hbF (by simpa only [laplaceKernel, hbound] using! hint)
  have hFone : F 1 = cartesianEvolution L H t := by
    simp only [F, cartesianEvolution, cartesianMatrix, one_smul]
  have hnorm' : (∫ k : ℝ, f (k : ℂ) / (1 - Complex.I * (k : ℂ))) = 1 := by
    simpa only [laplaceKernel] using hnorm
  simpa only [laplaceKernel, hbound, hFone, hnorm', one_smul] using! he

/-- Theorem 4 of arXiv:2411.04010 (printed p.10–11, Eq. (27)): the Laplace
transform `h(A) = ∫₀^∞ g(t) e^{-tA} dt` of a matrix `A = L + iH` with `L ⪰ 0`
equals the LCHS double integral of the truncated Hardy-kernel weight
`f(k)/(1-ik)` against `g(t) e^{-it(kL+H)}`.

The printed proof: apply Theorem 3 with `F_t(z) = e^{-t(zL+iH)}` (entire,
`‖F_t‖ ≤ 1` on the closed right half-plane by dissipativity) for each `t ≥ 0`,
use the normalization `∫_ℝ f(k)/(1-ik) dk = 1`, then exchange the `k`- and
`t`-integrals.  Here the `t`-integral is the printed iterated integral; no
Fubini interchange is needed because the inner identity holds pointwise, the
paper's `g ∈ L¹(ℝ₊)` only guaranteeing that the outer integral converges.
The query/gate counts of the algorithm are not asserted at this layer. -/
theorem laplace_transform_lchs_representation
    (f : ℂ → ℂ) (g : ℝ → ℂ) (L H : Matrix I I ℂ)
    (hL : L.PosSemidef) (hH : H.IsHermitian)
    (hf : DifferentiableOn ℂ f {z : ℂ | z.im ≤ 0})
    (hdecay : ∃ α C : ℝ, 0 < α ∧ 0 ≤ C ∧
      ∀ z : ℂ, z.im ≤ 0 → ‖z‖ ^ α * ‖f z‖ ≤ C)
    (hnorm : (∫ k : ℝ, laplaceKernel f k) = 1)
    (hg : IntegrableOn g (Set.Ioi (0 : ℝ))) :
    matrixLaplace g (cartesianMatrix L H) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ k : ℝ,
        (g t * laplaceKernel f k) • lchsKernelEvolution L H k t := by
  rw [matrixLaplace]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  show g t • NormedSpace.exp ((-(t : ℂ)) • cartesianMatrix L H) =
    ∫ k : ℝ, (g t * laplaceKernel f k) • lchsKernelEvolution L H k t
  have ht0 : 0 ≤ t := le_of_lt ht
  have hfix := lchs_kernel_representation_fixed_time f L H hL hH hf hdecay hnorm t ht0
  have hsm : (∫ k : ℝ, (g t * laplaceKernel f k) • lchsKernelEvolution L H k t)
      = g t • ∫ k : ℝ, laplaceKernel f k • lchsKernelEvolution L H k t := by
    have h1 : (fun k : ℝ => (g t * laplaceKernel f k) • lchsKernelEvolution L H k t)
        = fun k : ℝ => g t • (laplaceKernel f k • lchsKernelEvolution L H k t) := by
      funext k
      rw [smul_smul]
    rw [h1, integral_smul]
  rw [hsm, hfix]
  simp only [cartesianEvolution]

end Qatlib.Papers.LaplaceEigen24.MainResults
