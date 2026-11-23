/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.GroverInterp.GroverInterpolationQuan
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

@[expose] public section

/-!
# Euclidean form of the Claim 5 resolvent estimates

Fixed source: [Ambainis2007ElementDistinctness], Claim 5
(quant-ph/0311001v9, p. 15).  This module transports the proved
imaginary-resolvent bounds from coordinate sums to the complex
`EuclideanSpace` used by ordinary state-vector consumers.  In particular,
the residual bound accompanies the start-component decomposition
`imaginaryResolvent = coefficient • start + residual`, measured in the
Euclidean norm. The paper's two normalized eigenvector expansions with
the end direction are outside the scope of these estimates.

## Main statements

* `claim5_euclidean_resolvent_bound`: a uniform constant `6` outside all
  quantifiers gives `‖imaginaryResolvent‖ ≤ 6 / ε`, together with the
  source's Euclidean residual estimate at a secular root.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Papers.QWalkAmbainis03.GroverInterp.EuclideanClaim5

open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib.Foundations.PureStateMath.BornBridge
open Matrix

/-- The Claim 5 estimates in complex Euclidean space.  The domain is required
to be nonempty, and the uniform constant `6` is fixed before all parameters.
The final bound controls the Euclidean residual after projecting the imaginary
part of the resolvent onto `start`. The secular root from Claim 4 and the
real unitary spectral model are hypotheses. -/
theorem claim5_euclidean_resolvent_bound :
    ∃ uniformConstant : ℝ, 0 < uniformConstant ∧
      ∀ (m : ℕ) [Nonempty (Fin m)] (ε α β : ℝ),
        0 < ε → ε ≤ 1 → 0 < α → α ≤ ε ^ 2 / 200 →
        β ∈ Set.Icc (ε * α / Real.sqrt (2 * Real.pi)) ((13 / 5 : ℝ) * α) →
        ∀ (U : Matrix (Fin m) (Fin m) ℂ) (start good : Fin m → ℂ),
          star U * U = 1 →
          (∀ i j, (U i j).im = 0) →
          (∀ i, (start i).im = 0) →
          (∀ i, (good i).im = 0) →
          (∑ i, ‖start i‖ ^ 2) = 1 →
          (∑ i, ‖good i‖ ^ 2) = 1 →
          (∑ i, star (good i) * start i) = (α : ℂ) →
          U *ᵥ start = start →
          (∀ (ν : ℂ) (v : Fin m → ℂ), U *ᵥ v = ν • v →
            (∑ i, star (v i) * start i) = 0 → v ≠ 0 →
            ∃ θ : ℝ, ε ≤ θ ∧ θ ≤ 2 * Real.pi - ε ∧ θ ≠ Real.pi ∧
              ν = Complex.exp (Complex.I * θ)) →
          groverSecularScalar m U good β = 0 →
            let y := (U - Complex.exp (Complex.I * β) •
              (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good)
            let coefficient := α * Real.sin β / (2 * (1 - Real.cos β))
            let imaginaryResolvent : EuclideanSpace ℂ (Fin m) :=
              toEuclidean_fromVec (fun i => ((y i).im : ℂ))
            let euclideanStart : EuclideanSpace ℂ (Fin m) :=
              toEuclidean_fromVec start
            let residual : EuclideanSpace ℂ (Fin m) :=
              toEuclidean_fromVec
                (fun i => ((y i).im : ℂ) - (coefficient : ℂ) * start i)
            imaginaryResolvent = coefficient • euclideanStart + residual ∧
              0 < coefficient ∧
              ‖imaginaryResolvent‖ ≤ uniformConstant / ε ∧
              ‖residual‖ ≤ 2 * β / ε * coefficient := by
  refine ⟨6, by norm_num, fun m [Nonempty (Fin m)] ε α β
      hε hε1 hα hsmall hβbounds U start good hu hU hsr hgr hsn hgn
      hoverlap hstart hphase hroot => ?_⟩
  set y : Fin m → ℂ := (U - Complex.exp (Complex.I * β) •
    (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ *ᵥ (U *ᵥ good) with hy
  set coefficient : ℝ := α * Real.sin β / (2 * (1 - Real.cos β)) with hcoefficientDef
  obtain ⟨hcoefficient, himaginary, hresidual⟩ :=
    grover_small_overlap_normalization_bounds m ε α β hε hε1 hα hsmall hβbounds
      U start good hu hU hsr hgr hsn hgn hoverlap hstart hphase hroot
  refine ⟨?_, hcoefficient, ?_, ?_⟩
  · ext i
    simp [toEuclidean_fromVec]
  · have hsq := norm_toEuclidean_fromVec_sq
      (fun i => ((y i).im : ℂ))
    rw [hy] at hsq
    have hnorm : ‖toEuclidean_fromVec (fun i => ((y i).im : ℂ))‖ ^ 2 ≤ 36 / ε ^ 2 := by
      rw [hsq]
      exact himaginary
    have hbound : 36 / ε ^ 2 = (6 / ε) ^ 2 := by
      field_simp
      ring
    rw [hbound] at hnorm
    refine le_of_sq_le_sq hnorm ?_
    exact le_of_lt (div_pos (show (0 : ℝ) < 6 by norm_num) hε)
  · have hsq := norm_toEuclidean_fromVec_sq
      (fun i => ((y i).im : ℂ) - (coefficient : ℂ) * start i)
    rw [hy, hcoefficientDef] at hsq
    have hnonneg : 0 ≤ 2 * β / ε * coefficient := by
      have hβ : 0 < β := lt_of_lt_of_le (by positivity) hβbounds.1
      positivity
    have hnorm : ‖toEuclidean_fromVec
        (fun i => ((y i).im : ℂ) - (coefficient : ℂ) * start i)‖ ^ 2 ≤
        (2 * β / ε * coefficient) ^ 2 := by
      rw [hy, hcoefficientDef, hsq]
      exact hresidual
    exact le_of_sq_le_sq hnorm hnonneg

end Qatlib.Papers.QWalkAmbainis03.GroverInterp.EuclideanClaim5
