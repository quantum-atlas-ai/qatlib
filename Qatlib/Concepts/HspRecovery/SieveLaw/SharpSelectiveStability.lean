/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.SieveLaw.MixedSelectivePerturbation
import Qatlib.Concepts.HspRecovery.SieveLaw.NormalizedBranchDistance

/-!
# Sharp stability of selective quantum operations

For equal-trace positive inputs, this module controls a selected instrument output and its mass
jointly, including arbitrary finite reference systems. The proofs use positive and negative
parts of Hermitian matrices in the trace-norm framework of [Watrous2018].

`sharp_selective_joint_stability` bounds normalized output distance by the input distance
divided by the larger selected mass. A gap formulation also guarantees positivity of the
perturbed output mass.

## Main statements

* `selective_joint_mass_budget`: a combined trace-norm and output-mass error bound.
* `sharp_selective_joint_stability`: normalized stability with the larger output mass.
* `sharp_selective_joint_stability_of_gap`: positivity and stability from a mass gap.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.HspRecovery.SieveLaw

open Matrix
open scoped ComplexOrder

/-- The positive part of a Hermitian matrix is positive semidefinite. -/
private theorem positive_split_pos {I : Type} [Fintype I] [DecidableEq I]
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (le_max_right (hX.eigenvalues i) 0)

/-- The negative part in the positive-minus-negative decomposition of a Hermitian matrix is
positive semidefinite. -/
private theorem positive_split_neg {I : Type} [Fintype I] [DecidableEq I]
    {X : Matrix I I ℂ} (hX : X.IsHermitian) :
    (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (le_max_right (-hX.eigenvalues i) 0)

/-- A positive trace-non-increasing map sends a Hermitian input of zero real trace to an output
whose trace norm plus absolute real trace is at most the input trace norm. -/
theorem positive_tni_trace_zero_budget
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hpos : ∀ A, A.PosSemidef → (T A).PosSemidef)
    (htni : ∀ A, A.PosSemidef → (Matrix.trace (T A)).re ≤ (Matrix.trace A).re)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (hzero : (Matrix.trace X).re = 0) :
    Matrix.traceNorm (T X) + |(Matrix.trace (T X)).re| ≤ Matrix.traceNorm X := by
  let P := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX
  let N := Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX
  have hp : P.PosSemidef := positive_split_pos hX
  have hn : N.PosSemidef := positive_split_neg hX
  have heq : P - N = X :=
      Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.sub_posPart_negPart hX
  have hnorm : Matrix.traceNorm X = (Matrix.trace P).re + (Matrix.trace N).re := by
    rw [Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.traceNorm_sub_posPart_negPart hX]
    change Matrix.traceNorm P + Matrix.traceNorm N = _
    rw [posSemidef_traceNorm_eq_re hp, posSemidef_traceNorm_eq_re hn]
  have hequal : (Matrix.trace P).re = (Matrix.trace N).re := by
    have hh := congrArg (fun A : Matrix I I ℂ => (Matrix.trace A).re) heq
    change (Matrix.trace (P - N)).re = (Matrix.trace X).re at hh
    rw [Matrix.trace_sub, Complex.sub_re, hzero] at hh
    linarith
  have hpout := hpos P hp
  have hnout := hpos N hn
  have hdiff : T X = T P - T N := by rw [← heq, map_sub]
  have htri : Matrix.traceNorm (T X) ≤
      (Matrix.trace (T P)).re + (Matrix.trace (T N)).re := by
    rw [hdiff]
    simpa only [← sub_eq_add_neg, Matrix.traceNorm_neg,
      posSemidef_traceNorm_eq_re hpout, posSemidef_traceNorm_eq_re hnout] using
      Matrix.traceNorm_add_le (T P) (-(T N))
  have hmass : (Matrix.trace (T X)).re =
      (Matrix.trace (T P)).re - (Matrix.trace (T N)).re := by
    rw [hdiff, Matrix.trace_sub, Complex.sub_re]
  have htp := htni P hp
  have htn := htni N hn
  rw [hmass, hnorm]
  rcases le_total (Matrix.trace (T N)).re (Matrix.trace (T P)).re with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    linarith

/-- For equal-trace positive inputs, selected reference-system outputs have trace-norm
difference plus absolute mass difference at most the input trace-norm difference. -/
theorem selective_joint_mass_budget
    {O : Type} [Fintype O] {D E R : ℕ} (J : Instrument O D E) (S : Finset O)
    (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
    (hequal : (Matrix.trace ρ).re = (Matrix.trace τ).re) :
    Matrix.traceNorm (tensorLeft (selectiveMap J S) ρ - tensorLeft (selectiveMap J S) τ)
      + |(Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
          - (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re|
      ≤ Matrix.traceNorm (ρ - τ) := by
  let T : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ →ₗ[ℂ]
      Matrix (Fin E × Fin R) (Fin E × Fin R) ℂ :=
    { toFun := tensorLeft (selectiveMap J S)
      map_add' := by
        intro A B
        ext x y
        exact congrArg (fun M : Operator E => M x.1 y.1)
          ((selectiveMap J S).map_add (fun i j => A (i, x.2) (j, y.2))
            (fun i j => B (i, x.2) (j, y.2)))
      map_smul' := by
        intro c A
        ext x y
        exact congrArg (fun M : Operator E => M x.1 y.1)
          ((selectiveMap J S).map_smul c (fun i j => A (i, x.2) (j, y.2))) }
  have hh := positive_tni_trace_zero_budget T
    (fun A hA => tensorLeft_posSemidef (selectiveMap_cp J S) hA)
    (fun A hA => selectiveMap_tensorLeft_tni J S hA)
    (ρ - τ) (hρ.isHermitian.sub hτ.isHermitian)
    (by rw [Matrix.trace_sub, Complex.sub_re, hequal, sub_self])
  change Matrix.traceNorm (tensorLeft (selectiveMap J S) (ρ - τ)) +
    |(Matrix.trace (tensorLeft (selectiveMap J S) (ρ - τ))).re| ≤
      Matrix.traceNorm (ρ - τ) at hh
  simpa only [tensorLeft_sub, Matrix.trace_sub, Complex.sub_re] using hh

/-- For equal-trace positive inputs, the selected output masses differ by at most half the input
trace-norm difference. -/
theorem selective_joint_mass_error
    {O : Type} [Fintype O] {D E R : ℕ} (J : Instrument O D E) (S : Finset O)
    (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ)
    (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
    (hequal : (Matrix.trace ρ).re = (Matrix.trace τ).re) :
    |(Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
        - (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re|
      ≤ Matrix.traceNorm (ρ - τ) / 2 := by
  have hb := selective_joint_mass_budget J S ρ τ hρ hτ hequal
  have hm : |(Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      - (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re| ≤
      Matrix.traceNorm (tensorLeft (selectiveMap J S) ρ - tensorLeft (selectiveMap J S) τ) := by
    rw [← Complex.sub_re, ← Matrix.trace_sub]
    exact (Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)
  linarith

/-- For equal-trace positive inputs and positive selected output masses, the normalized
selected-output distance is at most the input trace-norm difference divided by the larger
output mass, with a finite reference system included. -/
theorem sharp_selective_joint_stability :
    ∀ (O : Type) [Fintype O] (D E R : ℕ) (J : Instrument O D E) (S : Finset O)
      (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ),
      ρ.PosSemidef → τ.PosSemidef → (Matrix.trace ρ).re = (Matrix.trace τ).re →
      let A := tensorLeft (selectiveMap J S) ρ
      let B := tensorLeft (selectiveMap J S) τ
      0 < (Matrix.trace A).re → 0 < (Matrix.trace B).re →
      Matrix.traceNorm (normalizedPositiveBranch A - normalizedPositiveBranch B) ≤
        Matrix.traceNorm (ρ - τ) / max (Matrix.trace A).re (Matrix.trace B).re := by
  intro O _ D E R J S ρ τ hρ hτ hequal
  (try dsimp only)
  intro hp hq
  have hnorm := normalized_positive_branch_distance (Fin E × Fin R)
    (tensorLeft (selectiveMap J S) ρ) (tensorLeft (selectiveMap J S) τ)
    (tensorLeft_posSemidef (selectiveMap_cp J S) hρ)
    (tensorLeft_posSemidef (selectiveMap_cp J S) hτ) hp hq
  have hmax : 0 ≤ max (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re :=
    (le_of_lt hp).trans (le_max_left _ _)
  exact hnorm.trans (div_le_div_of_nonneg_right
    (selective_joint_mass_budget J S ρ τ hρ hτ hequal) hmax)

/-- For equal-trace positive inputs at distance at most `η ≥ 0`, a reference output mass greater
than `η/2` ensures positive mass for the other output and normalized distance at most `η`
divided by the reference mass. -/
theorem sharp_selective_joint_stability_of_gap
    {O : Type} [Fintype O] {D E R : ℕ} (J : Instrument O D E) (S : Finset O)
    (ρ τ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) (η : ℝ)
    (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef)
    (hequal : (Matrix.trace ρ).re = (Matrix.trace τ).re)
    (hη : 0 ≤ η) (hdiff : Matrix.traceNorm (ρ - τ) ≤ η)
    (hgap : η / 2 < (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re) :
    0 < (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re ∧
    Matrix.traceNorm (normalizedPositiveBranch (tensorLeft (selectiveMap J S) ρ)
      - normalizedPositiveBranch (tensorLeft (selectiveMap J S) τ)) ≤
      η / (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re := by
  have hm := selective_joint_mass_error J S ρ τ hρ hτ hequal
  have hp : 0 < (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re := by
    have hlow := (abs_le.mp hm).1
    linarith
  have hq : 0 < (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re := by
    linarith
  have hmax : 0 ≤ max (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re :=
    (le_of_lt hq).trans (le_max_right _ _)
  refine ⟨hp, (sharp_selective_joint_stability O D E R J S ρ τ hρ hτ hequal hp hq).trans ?_⟩
  exact (div_le_div_of_nonneg_right hdiff hmax).trans
    (div_le_div_of_nonneg_left hη hq (le_max_right _ _))

end Qatlib.Concepts.HspRecovery.SieveLaw
