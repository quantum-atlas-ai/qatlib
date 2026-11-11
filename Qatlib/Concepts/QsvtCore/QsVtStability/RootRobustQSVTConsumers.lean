/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.SquareRootQSVTRobustness
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Compiled QSVT with square-root encoding errors

This module transports real polynomial singular transforms through approximate block encodings
and the clean phase compiler. The error is `4 * d * √(ε / α)`, as in the square-root robustness
setting of [GilyenSuLowWiebe2019], and the compiler retains exact instruction counts.

For odd degree bounds, the same construction gives output-norm and normalized-state bounds
whenever the error is smaller than the ideal output norm.

## Main statements

* `source_cpp_encoded_corner_root_error_of_response`: Bound the error for an already specified
  real response list.
* `source_cpp_encoded_corner_root_error`: Synthesize a length-controlled approximate encoding.
* `source_cpp_root_error_actual_conditional_output`: Bound outputs of the compiled odd word.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QsvtCore.QsVtStability
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open scoped Matrix.Norms.L2Operator

/-- A given real response list yields the parity-appropriate compiled block encoding with error
`4 * d * √(ε / α)` and exact instruction counts under the polynomial and contraction
assumptions. -/
theorem source_cpp_encoded_corner_root_error_of_response :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (α ε : ℝ) (p : Polynomial ℝ) (d : ℕ)
      (Φ : List ℝ),
      BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 → Φ.length = d →
      (∀ x : ℝ, ((sourcePhaseResponse Φ).eval (x : ℂ)).re = p.eval x) →
      p.degree ≤ (d : WithBot ℕ) → HasRealParity d p →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
      cppCounts (cppCompile (sourceRealFamily Φ)) = (d,2*(d/2),2*((d+1)/2),d) ∧
        (d % 2 = 1 → BlockEncoding
          (oddSingularTransform ((α⁻¹ : ℝ) • A) (fun x => ((p.eval x : ℝ) : ℂ)))
          (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
          (sourceAverageClean L) (sourceAverageClean R) 1 (4*d*Real.sqrt (ε/α))) ∧
        (d % 2 = 0 → BlockEncoding
          (rightSingularTransform ((α⁻¹ : ℝ) • A) (fun x => ((p.eval x : ℝ) : ℂ)))
          (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
          (sourceAverageClean R) (sourceAverageClean R) 1 (4*d*Real.sqrt (ε/α))) := by
  intro H I O _ _ _ _ _ _ A U L R α ε p d Φ h hA hlen hre hp hpar hb
  obtain ⟨hodd,heven,hcounts⟩ := source_cpp_real_singular_transform_of_response
    H I O (compress L U R) U L R p Φ (decodedBlock_projectedEncoding h) hre
  rw [hlen] at hodd heven hcounts
  have hrob := real_singular_polynomial_root_robustness I O ((α⁻¹:ℝ)•A) (compress L U R)
    p d hA (decodedBlock_norm_le_one h) hp hpar hb
  have hη : 0 ≤ 4*(d:ℝ)*Real.sqrt (ε/α) := by positivity
  have hscale : 4*(d:ℝ)*Real.sqrt ‖(α⁻¹:ℝ)•A-compress L U R‖ ≤
      4*(d:ℝ)*Real.sqrt (ε/α) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (encodedBlock_normalized_error h)) (by positivity)
  refine ⟨hcounts,?_,?_⟩
  · intro ho
    simpa only [zero_add] using!
        (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (hodd ho)).perturb hη ((hrob.1 ho).trans hscale)
  · intro he
    simpa only [zero_add] using!
        (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (heven he)).perturb hη ((hrob.2 he).trans hscale)

/-- A bounded real polynomial with positive degree bound and matching parity has a compiled
block encoding with error `4 * d * √(ε / α)` and exact instruction counts
[GilyenSuLowWiebe2019]. -/
theorem source_cpp_encoded_corner_root_error :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (α ε : ℝ) (p : Polynomial ℝ) (d : ℕ),
      BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 → 0 < d →
      p.degree ≤ (d : WithBot ℕ) → HasRealParity d p →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
      ∃ Φ : List ℝ, Φ.length = d ∧
        cppCounts (cppCompile (sourceRealFamily Φ)) = (d,2*(d/2),2*((d+1)/2),d) ∧
        (d % 2 = 1 → BlockEncoding
          (oddSingularTransform ((α⁻¹ : ℝ) • A) (fun x => ((p.eval x : ℝ) : ℂ)))
          (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
          (sourceAverageClean L) (sourceAverageClean R) 1 (4*d*Real.sqrt (ε/α))) ∧
        (d % 2 = 0 → BlockEncoding
          (rightSingularTransform ((α⁻¹ : ℝ) • A) (fun x => ((p.eval x : ℝ) : ℂ)))
          (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
          (sourceAverageClean R) (sourceAverageClean R) 1 (4*d*Real.sqrt (ε/α))) := by
  intro H I O _ _ _ _ _ _ A U L R α ε p d h hA hd hp hpar hb
  obtain ⟨Φ,hlen,hre⟩ := source_length_real_phase_existence p d hd hp hpar hb
  exact ⟨Φ,hlen,source_cpp_encoded_corner_root_error_of_response
    H I O A U L R α ε p d Φ h hA hlen hre hp hpar hb⟩

/-- For an odd degree bound, a compiled polynomial word has output squared norm at least `(τ -
η) ^ 2` and normalized error at most `2 * η / τ` whenever `η = 4 * d * √(ε / α) < τ`
[GilyenSuLowWiebe2019]. -/
theorem source_cpp_root_error_actual_conditional_output :
    ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ) (α ε : ℝ) (p : Polynomial ℝ) (d : ℕ),
      BlockEncoding A U L R α ε → ‖(α⁻¹ : ℝ) • A‖ ≤ 1 → d % 2 = 1 →
      p.degree ≤ (d : WithBot ℕ) → HasRealParity d p →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) →
      ∃ Φ : List ℝ, Φ.length = d ∧
        ∀ ψ : QState I, Normalized ψ →
        let F := oddSingularTransform ((α⁻¹ : ℝ) • A) (fun x => ((p.eval x : ℝ) : ℂ))
        let y := compress (sourceAverageClean L)
          (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
          (sourceAverageClean R) *ᵥ ψ
        let v := F *ᵥ ψ
        let τ := ‖toEuclidean_fromVec v‖
        let η := 4*d*Real.sqrt (ε/α)
        η < τ →
        (τ-η)^2 ≤ ‖toEuclidean_fromVec y‖^2 ∧
        ‖toEuclidean_fromVec
          (((‖toEuclidean_fromVec y‖⁻¹ : ℝ) : ℂ) • y - ((τ⁻¹ : ℝ) : ℂ) • v)‖ ≤ 2*η/τ := by
  intro H I O _ _ _ _ _ _ A U L R α ε p d h hA hodd hp hpar hb
  obtain ⟨Φ,hlen,_,henc,_⟩ := source_cpp_encoded_corner_root_error H I O A U L R α ε p d
    h hA (by omega) hp hpar hb
  refine ⟨Φ,hlen,?_⟩
  intro ψ hψ F y v τ η hgap
  have hclose : ‖toEuclidean_fromVec y-toEuclidean_fromVec v‖ ≤ η := by
    rw [norm_sub_rev]
    simpa only [stateVector,postselectionVector,one_smul] using!
        Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error
        (henc hodd) hψ
  have hlower : τ-η ≤ ‖toEuclidean_fromVec y‖ := by
    have hh : ‖toEuclidean_fromVec v‖-‖toEuclidean_fromVec y‖ ≤ η :=
      (norm_sub_norm_le (toEuclidean_fromVec v) (toEuclidean_fromVec y)).trans
        (by simpa only [norm_sub_rev] using! hclose)
    dsimp only [τ]
    linarith
  have hnorm := (normalize_error_of_gap hclose hgap).2
  constructor
  · exact pow_le_pow_left₀ (sub_nonneg.mpr hgap.le) hlower 2
  · simpa only [NormedSpace.normalize,toEuclidean_fromVec,WithLp.toLp_sub,
      WithLp.toLp_smul,Complex.real_smul] using! hnorm

end Qatlib.Concepts.QsvtCore.QsVtStability
