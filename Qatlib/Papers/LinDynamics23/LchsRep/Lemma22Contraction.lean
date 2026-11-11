/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeLchs
import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

/-!
# Lemma 22: dissipative contraction of the non-unitary propagator

Lemma 22 of arXiv:2312.03916v2 (p. 30, Eq. (168)) states that for the
decomposition `A(t) = L(t) + i H(t)` of Eqs. (3)-(4) with `L(s) ⪰ 0` on
`0 ≤ s ≤ t`, the time-ordered propagator satisfies
`‖𝒯 e^{-∫_0^t A(s) ds}‖ ≤ 1`.  The follow-up remark in the same paragraph
specialises this to the homogeneous system `b ≡ 0`, where the norm of the
solution `u(t)` is therefore non-increasing.

Both statements are proved here from the frozen Dyson-series contraction
`ordered_evolution_psd_contraction`; no unitary or boundedness hypothesis on
`A` is assumed beyond the positivity of `L`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Qatlib.Papers.LinDynamics23.LchsRep

open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexOrder

/-- **Lemma 22**, Eq. (168): the propagator `𝒯 e^{-∫_s^t (L + iH)}` of the
decomposition `A = L + iH` is a contraction whenever `L` is positive
semidefinite along the interval and `H` is Hermitian. -/
theorem lemma22_dissipative_contraction :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (s t : ℝ),
      Continuous L → Continuous H → (∀ u, (L u).PosSemidef) →
      (∀ u, (H u).IsHermitian) → s ≤ t →
      ‖orderedEvolution (fun u => L u + Complex.I • H u) s t‖ ≤ 1 := by
  intro I _ _ L H s t hL hH hPSD hHerm hst
  have hgen : Continuous (fun u => L u + Complex.I • H u) :=
    hL.add (hH.const_smul Complex.I)
  refine ordered_evolution_psd_contraction I (fun u => L u + Complex.I • H u) hgen ?_ s t hst
  intro u
  have he : L u + Complex.I • H u + (L u + Complex.I • H u)ᴴ = L u + L u := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      (hPSD u).isHermitian.eq, (hHerm u).eq]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Complex.star_def, Complex.conj_I]
    ring
  rw [he]
  exact (hPSD u).add (hPSD u)

/-- The homogeneous consequence recorded after Lemma 22: with `b ≡ 0` the LCHS
solution `u(t) = 𝒯 e^{-∫_0^t A} u₀` has non-increasing norm in forward time. -/
theorem lemma22_homogeneous_solution_norm_nonincreasing :
    ∀ {I : Type} [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
      (u₀ : EuclideanSpace ℂ I) (t : ℝ), Continuous L → Continuous H →
      (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → 0 ≤ t →
      ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)
        (orderedEvolution (fun u => L u + Complex.I • H u) 0 t)) u₀‖ ≤ ‖u₀‖ := by
  intro I _ _ L H u₀ t hL hH hPSD hHerm ht
  have hcon := lemma22_dissipative_contraction I L H 0 t hL hH hPSD hHerm ht
  have hclm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)
      (orderedEvolution (fun u => L u + Complex.I • H u) 0 t)‖ ≤ 1 := hcon
  calc ‖(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)
          (orderedEvolution (fun u => L u + Complex.I • H u) 0 t)) u₀‖
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := I)
          (orderedEvolution (fun u => L u + Complex.I • H u) 0 t)‖ * ‖u₀‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u₀‖ := by
        exact mul_le_mul_of_nonneg_right hclm (norm_nonneg u₀)
    _ = ‖u₀‖ := one_mul _

end Qatlib.Papers.LinDynamics23.LchsRep
