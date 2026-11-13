/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualProjectors
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

/-!
# Eigenvector branches for alternating projectors

The branch recursion `branchState` tracks agreement and disagreement outcomes for a pair of
orthogonal projectors. Invariant eigenvector relations persist along both kinds of branch, so
`record_mass` factors the final mass into the initial mass and the Bernoulli product
`recordWeight`.

The mathematical background is developed in [MarriottWatrous2005].

## Main statements

* `same_invariant`: propagates the eigenvector relation through an agreement branch.
* `different_invariant`: propagates the relation through a disagreement branch.
* `record_mass`: computes the mass of an entire branch record.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped Classical BigOperators

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- The real part of a state vector's self-inner-product equals its total measurement mass. -/
theorem inner_self_re_mass (ψ : QState H) :
    (Inner ψ ψ).re = MeasureProb ψ Finset.univ := by
  rw [inner_self, ← Complex.ofReal_sum]
  simp only [Complex.ofReal_re, MeasureProb, BornProb]

omit [DecidableEq H] in

/-- Scaling the second argument of `Inner` by `c` scales the inner product by `c`. -/
theorem inner_smul_right (c : ℂ) (ψ φ : QState H) :
    Inner ψ (c • φ) = c * Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct_smul, smul_eq_mul]

omit [DecidableEq H] in

/-- If `R *ᵥ (S *ᵥ ψ) = p • ψ` and `S` is an orthogonal projector, then `S *ᵥ ψ` is fixed by `S`
and satisfies the corresponding eigenvector relation with the projectors exchanged. -/
theorem same_invariant (R S : Matrix H H ℂ) (hS : IsOrthogonalProjector S)
    (ψ : QState H) (p : ℝ) (heig : R *ᵥ (S *ᵥ ψ) = (p : ℂ) • ψ) :
    S *ᵥ (S *ᵥ ψ) = S *ᵥ ψ ∧
      S *ᵥ (R *ᵥ (S *ᵥ ψ)) = (p : ℂ) • (S *ᵥ ψ) := by
  constructor
  · rw [Matrix.mulVec_mulVec, hS.1]
  · rw [heig, Matrix.mulVec_smul]

/-- If `ψ` is fixed by `R` and satisfies the compressed eigenvector relation with `S`, the
vector `(1 - S) *ᵥ ψ` is fixed by `1 - S` and satisfies the complementary compressed
relation with eigenvalue `p`. -/
theorem different_invariant (R S : Matrix H H ℂ) (hS : IsOrthogonalProjector S)
    (ψ : QState H) (p : ℝ) (hfix : R *ᵥ ψ = ψ)
    (heig : R *ᵥ (S *ᵥ ψ) = (p : ℂ) • ψ) :
    (1 - S) *ᵥ ((1 - S) *ᵥ ψ) = (1 - S) *ᵥ ψ ∧
      (1 - S) *ᵥ ((1 - R) *ᵥ ((1 - S) *ᵥ ψ)) =
        (p : ℂ) • ((1 - S) *ᵥ ψ) := by
  have hT := isOrthogonalProjector_compl hS
  have hfixed : (1 - S) *ᵥ ((1 - S) *ᵥ ψ) = (1 - S) *ᵥ ψ := by
    rw [Matrix.mulVec_mulVec, hT.1]
  have hRφ : R *ᵥ ((1 - S) *ᵥ ψ) = (1 - (p : ℂ)) • ψ := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hfix, heig]
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨hfixed, ?_⟩
  have hnext : (1 - R) *ᵥ ((1 - S) *ᵥ ψ) =
      ((1 - S) *ᵥ ψ) - R *ᵥ ((1 - S) *ᵥ ψ) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  rw [hnext, Matrix.mulVec_sub, hfixed, hRφ,
    Matrix.mulVec_smul]
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- For orthogonal projectors and a vector fixed by `R` with compressed eigenvalue `p`, applying
`S` multiplies total mass by `p`. -/
theorem same_mass (R S : Matrix H H ℂ)
    (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (ψ : QState H) (p : ℝ) (hfix : R *ᵥ ψ = ψ)
    (heig : R *ᵥ (S *ᵥ ψ) = (p : ℂ) • ψ) :
    MeasureProb (S *ᵥ ψ) Finset.univ = p * MeasureProb ψ Finset.univ := by
  have hSs : Sᴴ = S := hS.2
  have hRs : Rᴴ = R := hR.2
  have hSS : Sᴴ * S = S := by rw [hSs, hS.1]
  have hproj : Inner (S *ᵥ ψ) (S *ᵥ ψ) = Inner ψ (S *ᵥ ψ) := by
    rw [inner_mulVec_left_rect, Matrix.mulVec_mulVec, hSS]
  have hcomp : Inner ψ (S *ᵥ ψ) = Inner ψ (R *ᵥ (S *ᵥ ψ)) := by
    calc
      _ = Inner (R *ᵥ ψ) (S *ᵥ ψ) := by rw [hfix]
      _ = _ := by rw [inner_mulVec_left_rect, hRs]
  have hinner : Inner (S *ᵥ ψ) (S *ᵥ ψ) = (p : ℂ) * Inner ψ ψ := by
    rw [hproj, hcomp, heig, inner_smul_right]
  have hre := congrArg Complex.re hinner
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, inner_self_re_mass] using hre

/-- For orthogonal projectors and a vector fixed by `R` with compressed eigenvalue `p`, applying
`1 - S` multiplies total mass by `1 - p`. -/
theorem different_mass (R S : Matrix H H ℂ)
    (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (ψ : QState H) (p : ℝ) (hfix : R *ᵥ ψ = ψ)
    (heig : R *ᵥ (S *ᵥ ψ) = (p : ℂ) • ψ) :
    MeasureProb ((1 - S) *ᵥ ψ) Finset.univ =
      (1 - p) * MeasureProb ψ Finset.univ := by
  have htotal := projectiveBranchMass_add hS ψ
  change MeasureProb ((1 - S) *ᵥ ψ) Finset.univ +
    MeasureProb (S *ᵥ ψ) Finset.univ = MeasureProb ψ Finset.univ at htotal
  rw [same_mass R S hR hS ψ p hfix heig] at htotal
  linarith

/-- The unnormalized state obtained recursively from agreement bits, exchanging the projectors
on a true bit and exchanging their complements on a false bit. -/
def branchState (R S : Matrix H H ℂ) : List Bool → QState H → QState H
  | [], ψ => ψ
  | true :: rest, ψ => branchState S R rest (S *ᵥ ψ)
  | false :: rest, ψ => branchState (1 - S) (1 - R) rest ((1 - S) *ᵥ ψ)

/-- The product of factors `p` for true record bits and `1 - p` for false record bits. -/
def recordWeight (p : ℝ) : List Bool → ℝ
  | [] => 1
  | b :: rest => (if b then p else 1 - p) * recordWeight p rest

/-- For a vector fixed by `R` with compressed eigenvalue `p`, the mass of a branch state is its
initial mass multiplied by `recordWeight p record`. -/
theorem record_mass (R S : Matrix H H ℂ)
    (hR : IsOrthogonalProjector R) (hS : IsOrthogonalProjector S)
    (ψ : QState H) (p : ℝ) (hfix : R *ᵥ ψ = ψ)
    (heig : R *ᵥ (S *ᵥ ψ) = (p : ℂ) • ψ) (record : List Bool) :
    MeasureProb (branchState R S record ψ) Finset.univ =
      recordWeight p record * MeasureProb ψ Finset.univ := by
  induction record generalizing R S ψ with
  | nil => simp [branchState, recordWeight]
  | cons b rest ih =>
      cases b with
      | true =>
          obtain ⟨hfix', heig'⟩ := same_invariant R S hS ψ p heig
          change MeasureProb (branchState S R rest (S *ᵥ ψ)) Finset.univ = _
          rw [ih S R hS hR (S *ᵥ ψ) hfix' heig', same_mass R S hR hS ψ p hfix heig]
          simp only [recordWeight, ite_true]
          ring
      | false =>
          obtain ⟨hfix', heig'⟩ := different_invariant R S hS ψ p hfix heig
          change MeasureProb (branchState (1 - S) (1 - R) rest ((1 - S) *ᵥ ψ))
            Finset.univ = _
          rw [ih (1 - S) (1 - R) (isOrthogonalProjector_compl hS)
            (isOrthogonalProjector_compl hR) ((1 - S) *ᵥ ψ) hfix' heig',
            different_mass R S hR hS ψ p hfix heig]
          simp only [recordWeight, Bool.false_eq_true, ite_false]
          ring

end Qatlib.Concepts.QueryComplexity.DegreeMethod
