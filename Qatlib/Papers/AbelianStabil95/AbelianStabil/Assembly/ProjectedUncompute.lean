/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CoherentCompute.ProjectedError.RestrictedUncompute
import Qatlib.Foundations.CoherentCompute.ProjectedError.ProjectionSuccess

/-!
# Projected coherent uncomputation

`projected_coherent_uncompute` bounds the operator error of compute–control–uncompute on a
finite family of input components. `projected_uncompute_of_unit_success` derives the same bound
from success probabilities on unit vectors in projected input subspaces, using an isometric
computation and contractive operators. The development follows [Kitaev1995].

## Main statements

* `projected_coherent_uncompute`: bounds the error by `2 * sqrt (card Ω * ε)`.
* `projected_uncompute_of_unit_success`: obtains the bound from subspace success estimates.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.Assembly

/-- Under the left-inverse, contraction, commutation, and component-error hypotheses,
compute–control–uncompute differs from the componentwise target by at most `2 * sqrt (card Ω
* ε)` in operator norm. -/
theorem projected_coherent_uncompute
    {E Ω Θ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ω]
    (U V T : E →L[ℂ] E) (P : Ω → E →L[ℂ] E) (Q : Θ → E →L[ℂ] E)
    (S : Θ → E →L[ℂ] E) (F : Ω → Θ) (ε : ℝ) (hε : 0 ≤ ε)
    (hVU : ∀ x, V (U x) = x)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hS : ∀ θ x, ‖S θ x‖ ≤ ‖x‖)
    (hcomm : ∀ θ x, S θ (U x) = U (S θ x))
    (hcontrolled : ∀ θ x, T (Q θ x) = S θ (Q θ x))
    (hpyth : ∀ x, ∑ i, ‖P i x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hcompute : ∀ i x,
      ‖U (P i x) - Q (F i) (U (P i x))‖ ^ 2 ≤ ε * ‖P i x‖ ^ 2) :
    ‖(V.comp (T.comp U)).comp (∑ i, P i) - ∑ i, (S (F i)).comp (P i)‖ ≤
      2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε) :=
  Qatlib.Foundations.CoherentCompute.ProjectedError.coherentUncomputeRestrictedBound U V T P Q S F ε hε hVU hV hT hS hcomm hcontrolled hpyth hcompute

/-- For an isometric computation with success at least `1 - ε` on each unit input in the
specified subspaces, the stated contraction and control hypotheses yield a projected
uncomputation error at most `2 * sqrt (card Ω * ε)`. This gives a subspace form of the
estimate underlying [Kitaev, 1995, Theorem 2][Kitaev1995]. -/
theorem projected_uncompute_of_unit_success
    {E Ω Θ : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Fintype Ω]
    (W : Ω → Submodule ℂ E) (K : Θ → Submodule ℂ E)
    [∀ i, (W i).HasOrthogonalProjection] [∀ θ, (K θ).HasOrthogonalProjection]
    (U : E →ₗᵢ[ℂ] E) (V T : E →L[ℂ] E) (S : Θ → E →L[ℂ] E)
    (F : Ω → Θ) (ε : ℝ) (hε : 0 ≤ ε)
    (hVU : ∀ x, V (U x) = x)
    (hV : ∀ x, ‖V x‖ ≤ ‖x‖) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hS : ∀ θ x, ‖S θ x‖ ≤ ‖x‖)
    (hcomm : ∀ θ x, S θ (U x) = U (S θ x))
    (hcontrolled : ∀ θ x, T ((K θ).starProjection x) = S θ ((K θ).starProjection x))
    (hpyth : ∀ x, ∑ i, ‖(W i).starProjection x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hsuccess : ∀ i x, x ∈ W i → ‖x‖ = 1 →
      1 - ε ≤ ‖(K (F i)).starProjection (U x)‖ ^ 2) :
    ‖(V.comp (T.comp U.toContinuousLinearMap)).comp (∑ i, (W i).starProjection) -
        ∑ i, (S (F i)).comp ((W i).starProjection)‖ ≤
      2 * Real.sqrt ((Fintype.card Ω : ℝ) * ε) := by
  apply projected_coherent_uncompute U.toContinuousLinearMap V T
    (fun i => (W i).starProjection) (fun θ => (K θ).starProjection) S F ε hε
    hVU hV hT hS hcomm hcontrolled hpyth
  intro i x
  exact Qatlib.Foundations.CoherentCompute.ProjectedError.successOnSubspace_to_wrongSquared
    (W i) (K (F i)) U ε (hsuccess i) ((W i).starProjection x)
    ((W i).starProjection_apply_mem x)

end Qatlib.Papers.AbelianStabil95.AbelianStabil.Assembly
