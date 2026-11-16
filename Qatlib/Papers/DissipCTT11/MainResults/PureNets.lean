/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section


/-! # An actual finite net of normalized complex state vectors

This proves a quantitative upper cover in the Hilbert metric, including
the real dimension 2D. It is partial support for Lemma 9, not its lower
bound, its printed 5/(2 epsilon) constant, or a projective-state net.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.DissipCTT11.MainResults.PureNets

/-- D complex amplitudes have real dimension exactly 2D. -/
theorem realDim (D : ℕ) : Module.finrank ℝ (EuclideanSpace ℂ (Fin D)) = 2 * D := by
  rw [← Module.finrank_mul_finrank ℝ ℂ,Complex.finrank_real_complex,
    finrank_euclideanSpace,Fintype.card_fin]

/-- The actual complex unit sphere has a finite Hilbert-metric epsilon cover
with the explicit (1+4/epsilon)^(2D) cardinality budget. -/
theorem finiteCover (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (EuclideanSpace ℂ (Fin D)),
      (∀ y ∈ s, ‖y‖ = 1) ∧
      (∀ x : EuclideanSpace ℂ (Fin D), ‖x‖ = 1 → ∃ y ∈ s, dist x y ≤ ε) ∧
      (s.card : ℝ) ≤ (1 + 4 / ε) ^ (2 * D) := by
  have h := Qatlib.Foundations.MatrixGeometry.SphereNets.FiniteNet.sphere_quantitative_net
    (E := EuclideanSpace ℂ (Fin D)) ε hε
  have hr : (1 + ε / 4) / (ε / 4) = 1 + 4 / ε := by
    field_simp
    ring
  simpa only [realDim,hr] using h

end Qatlib.Papers.DissipCTT11.MainResults.PureNets
