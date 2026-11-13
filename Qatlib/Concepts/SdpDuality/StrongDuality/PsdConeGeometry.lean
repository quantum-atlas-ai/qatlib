/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpDuality.StrongDuality.SdpDuality

/-!
# Finite PSD cone geometry and SDP duality

`finitePsdCone` is the real proper cone of finite Hermitian positive semidefinite matrices.
`finitePsdGeometry` packages its closedness, convexity, self-duality, real trace inner product,
and adjoint separation characterizations for closed linear images. Matrix positivity and trace
pairings are treated in [Bhatia1997].

`g1` combines this geometry over the real and complex scalars with a weakly infeasible corner
example. `g2` collects Slater strong duality, optimizer attainment, and compactness results,
together with a boundary example whose primal optimum is attained while its dual infimum is not;
see [Watrous2018] for SDP background.

## Main statements

* `finitePsdGeometry`: finite PSD cone geometry in every dimension.
* `g1`: geometric and corner-system conclusions.
* `g2`: duality, attainment, and boundary conclusions.

## References

* [Bhatia, 1997][Bhatia1997]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.DyadicFloor.FloorRounding
open Qatlib.Concepts.DyadicFloor.FloorRounding.Program

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpDuality.StrongDuality
open Matrix
open scoped InnerProductSpace ComplexOrder

/-- The proper cone of positive semidefinite Hermitian `D × D` matrices, viewed as a real cone. -/
def finitePsdCone (𝕜 : Type*) [RCLike 𝕜] (D : ℕ) :
    ProperCone ℝ (HermitianMat (Fin D) 𝕜) := ProperCone.positive ℝ _

/-- Packages closedness, convexity, self-duality, and the real trace inner product of finite PSD
cones, together with adjoint certificates for membership in their closed linear images. -/
def FinitePsdGeometry (𝕜 : Type*) [RCLike 𝕜] : Prop := ∀ D : ℕ,
  IsClosed (finitePsdCone 𝕜 D : Set (HermitianMat (Fin D) 𝕜)) ∧
  Convex ℝ (finitePsdCone 𝕜 D : Set (HermitianMat (Fin D) 𝕜)) ∧
  ProperCone.innerDual (finitePsdCone 𝕜 D : Set (HermitianMat (Fin D) 𝕜)) = finitePsdCone 𝕜 D ∧
  (∀ X Y : HermitianMat (Fin D) 𝕜,
    ⟪X,Y⟫_ℝ = RCLike.re (Matrix.trace (X.mat * Y.mat))) ∧
  (∀ (m : ℕ) (A : HermitianMat (Fin D) 𝕜 →L[ℝ] EuclideanSpace ℝ (Fin m))
      (b : EuclideanSpace ℝ (Fin m)),
    (b ∈ (finitePsdCone 𝕜 D).map A ↔
      ∀ y, 0 ≤ A.adjoint y → 0 ≤ ⟪b,y⟫_ℝ) ∧
    (b ∉ (finitePsdCone 𝕜 D).map A ↔
      ∃ y, 0 ≤ A.adjoint y ∧ ⟪b,y⟫_ℝ < 0))

/-- Finite PSD cones satisfy `FinitePsdGeometry`, including their trace inner product and
adjoint separation characterizations. -/
theorem finitePsdGeometry (𝕜 : Type*) [RCLike 𝕜] : FinitePsdGeometry 𝕜 := by
  intro D
  refine ⟨(finitePsdCone 𝕜 D).isClosed, (finitePsdCone 𝕜 D).convex, ?_, ?_, ?_⟩
  · ext X
    change (∀ ⦃Y : HermitianMat (Fin D) 𝕜⦄, 0 ≤ Y → 0 ≤ ⟪Y,X⟫_ℝ) ↔ 0 ≤ X
    simpa only [real_inner_comm] using! (HermitianMat.nonneg_iff_inner_nonneg X).symm
  · intro X Y
    have h := congrArg RCLike.re (HermitianMat.inner_eq_trace_mul (R := ℝ) X Y)
    simpa using! h.symm
  · intro m A b
    have hclosed : b ∈ (finitePsdCone 𝕜 D).map A ↔
        ∀ y, 0 ≤ A.adjoint y → 0 ≤ ⟪b,y⟫_ℝ := by
      have h := ProperCone.relative_hyperplane_separation
        (C := finitePsdCone 𝕜 D) (f := A) (b := b)
      constructor
      · intro hb y hy
        apply h.mp hb y
        intro X hX
        exact HermitianMat.inner_ge_zero hX hy
      · intro hb
        apply h.mpr
        intro y hy
        apply hb y
        apply (HermitianMat.nonneg_iff_inner_nonneg _).mpr
        intro X hX
        simpa only [real_inner_comm] using! hy hX
    refine ⟨hclosed, ?_⟩
    rw [hclosed]
    push Not
    rfl

/-- Combines real and complex PSD cone geometry with a two-dimensional corner system that is
infeasible, has positive perturbations, and satisfies the stated nonnegative-functional
coefficient condition. -/
theorem g1 : FinitePsdGeometry ℝ ∧ FinitePsdGeometry ℂ ∧
    (¬ ∃ X : HermitianMat (Fin 2) ℂ,
      0 ≤ X ∧ (X.mat 0 0).re = 0 ∧ (X.mat 0 1).re = 1) ∧
    (∀ ε : ℝ, 0 < ε → ∃ X : HermitianMat (Fin 2) ℂ,
      0 ≤ X ∧ (X.mat 0 0).re = ε ∧ (X.mat 0 1).re = 1) ∧
    (∀ a b : ℝ, (∀ X : HermitianMat (Fin 2) ℂ, 0 ≤ X →
      0 ≤ a * (X.mat 0 0).re + b * (X.mat 0 1).re) → 0 ≤ b) :=
  ⟨finitePsdGeometry ℝ, finitePsdGeometry ℂ, weak_corner_infeasible,
   weak_corner_approximate, weak_corner_no_strict_separator⟩

/-- Combines Slater strong duality and optimizer attainment, bounded feasible value sets, and
compact primal superlevels with a boundary example having an attained primal value zero and
an unattained dual infimum zero. -/
theorem g2 :
    (∀ (D m : ℕ) (P : Program (Fin D) (EuclideanSpace ℝ (Fin m))),
      P.PrimalSlater → (∃ y, P.DualFeasible y) →
        ∃ α : ℝ, IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
          ∃ y, P.DualFeasible y ∧ P.dualScore y = α) ∧
    (∀ (D m : ℕ) (P : Program (Fin D) (EuclideanSpace ℝ (Fin m))),
      P.DualSlater → (∃ X, P.PrimalFeasible X) →
        ∃ α : ℝ, IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
          ∃ X, P.PrimalFeasible X ∧ P.primalScore X = α) ∧
    (∀ (D m : ℕ) (P : Program (Fin D) (EuclideanSpace ℝ (Fin m))),
      P.PrimalSlater → P.DualSlater →
        ∃ (α : ℝ) (X : HermitianMat (Fin D) ℂ) (y : EuclideanSpace ℝ (Fin m)),
          P.PrimalFeasible X ∧ P.DualFeasible y ∧
          IsLUB P.primalValues α ∧ IsGLB P.dualValues α ∧
          P.primalScore X = α ∧ P.dualScore y = α) ∧
    (∀ (D m : ℕ) (P : Program (Fin D) (EuclideanSpace ℝ (Fin m)))
      (X : HermitianMat (Fin D) ℂ) (y : EuclideanSpace ℝ (Fin m)),
      P.PrimalFeasible X → P.DualFeasible y →
        P.primalValues.Nonempty ∧ BddAbove P.primalValues ∧
          P.dualValues.Nonempty ∧ BddBelow P.dualValues) ∧
    (∀ (D m : ℕ) (P : Program (Fin D) (EuclideanSpace ℝ (Fin m))),
      P.DualSlater → ∀ a : ℝ, IsCompact (P.primalSuperlevel a)) ∧
    (∃ X : HermitianMat (Fin 2) ℂ, boundaryPrimal X ∧ 2 * (X.mat 0 1).re = 0) ∧
    (∀ X : HermitianMat (Fin 2) ℂ, boundaryPrimal X → ¬ X.mat.PosDef) ∧
    (∀ X : HermitianMat (Fin 2) ℂ, boundaryPrimal X → 2 * (X.mat 0 1).re = 0) ∧
    (IsGLB {s : ℝ | ∃ t : ℝ, (boundaryDual s t).PosSemidef} 0 ∧
      ¬ ∃ t : ℝ, (boundaryDual 0 t).PosSemidef) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, boundary_primal_attained,
    boundary_primal_no_strict_feasibility, boundary_primal_value,
    boundary_dual_infimum_not_attained⟩
  · rintro D m P hs ⟨y, hy⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.primalSlater_strong_duality (P := P)) hs hy
  · rintro D m P hs ⟨X, hX⟩
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlater_strong_duality (P := P)) hs hX
  · intro D m P hp hd
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.bothSlater_optimizers (P := P)) hp hd
  · intro D m P X y hX hy
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.feasible_values_bounded (P := P)) hX hy
  · intro D m P hs a
    exact (Qatlib.Concepts.SdpDuality.StrongDuality.Program.dualSlater_compact_superlevel (P := P)) hs a

end Qatlib.Concepts.SdpDuality.StrongDuality
