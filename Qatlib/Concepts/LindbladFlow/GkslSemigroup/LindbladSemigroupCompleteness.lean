/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroup
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupDirichlet
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupEntropy
import Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupKmsMixing

/-!
# Assembled Lindblad semigroup and KMS identities

This module packages the finite-dimensional semigroup law, a second-order
short-time remainder, Kraus representations, trace preservation, and density
preservation for nonnegative times. It adds KMS-adjoint uniqueness, a
stationarity implication, and the stationary-state commutator expression for
the Heisenberg Dirichlet form.

The background is [Lindblad1976], [GoriniKossakowskiSudarshan1976], and
[Breuer & Petruccione, *The Theory of Open Quantum Systems*][BreuerPetruccione2007].
`Clause22Complete` specifies the exact package proved here.
-/
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.DirichletForm.KmsDirichlet

open Qatlib.Concepts.LindbladFlow.GkslSemigroup

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCompleteness
open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The generator norm bound `2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖^2`. -/
private noncomputable def lindbladGeneratorBound {D : ℕ} (G : GKSL D) : ℝ :=
  2 * ‖G.ham‖ + 2 * ∑ j, ‖G.jumps j‖ ^ 2

/-- The complex-linear map defined by the Kraus sum `∑ j, K j * ρ * (K j)ᴴ`. -/
private noncomputable def krausMap {D : ℕ} (K : Fin (D * D * D * D) → Operator D) :
    Operator D →ₗ[ℂ] Operator D where
  toFun ρ := ∑ j, K j * ρ * (K j)ᴴ
  map_add' := by
    intro ρ σ
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by
    intro c ρ
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]

/-- The conjunction of semigroup, first-order remainder, Kraus, trace, density-preservation,
growth, KMS-normal-form, and Choi-positivity properties. -/
def Clause22 : Prop :=
  (∀ (D : ℕ) (G : GKSL D),

    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ ρ : Operator D,
        lindbladSemigroup G (s + t) ρ = lindbladSemigroup G s (lindbladSemigroup G t ρ)) ∧

    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ ρ : Operator D,
        ‖lindbladSemigroup G t ρ - ρ - t • lindbladApply G ρ‖
          ≤ (lindbladGeneratorBound G) ^ 2 * Real.exp (lindbladGeneratorBound G)
              * t ^ 2 * ‖ρ‖) ∧

    (∀ t : ℝ, 0 ≤ t →
        ∃ K : Fin (D * D * D * D) → Operator D,
          (∀ ρ : Operator D, lindbladSemigroup G t ρ = ∑ j, K j * ρ * (K j)ᴴ) ∧
            HasKrausFamily (krausMap K) ∧
            (∀ ρ : Operator D, Matrix.trace (lindbladSemigroup G t ρ) = Matrix.trace ρ) ∧
            (∀ ρ : Operator D, IsDensityOperator ρ →
                IsDensityOperator (lindbladSemigroup G t ρ))) ∧

    (∀ t : ℝ, 0 ≤ t → ∀ ρ : Operator D,
        ‖lindbladSemigroup G t ρ‖
          ≤ Real.exp (lindbladGeneratorBound G * t) * ‖ρ‖) ∧

    (∀ ρ : Operator D, KMSNormalForm G ρ →
        IsStationary G ρ ∧ KmsSelfAdjoint ρ (lindbladMap G) ∧
          ∀ O : Operator D, kmsDirichlet ρ (lindbladMap G) O
            = kmsDirichlet ρ (kmsGeneratorFam ρ (G.jumps)) O)) ∧

  (∀ (D E : ℕ) (T : Operator D →ₗ[ℂ] Operator E),
      HasKrausFamily T ↔ (ChoiMatrix T).PosSemidef)

/-- Extends `Clause22` with the KMS-adjoint pairing and uniqueness properties, the
self-adjointness criterion, stationarity from Heisenberg KMS symmetry, and the stationary
Dirichlet trace identity. -/
def Clause22Complete : Prop :=
  Clause22 ∧
  (∀ (D E : ℕ) (ρ : Operator D), ρ.PosDef →
    ∀ (σ : Operator E) (T : Operator D →ₗ[ℂ] Operator E) (X : Operator D) (Y : Operator E),
    kmsInner ρ X (kmsAdjointMap ρ σ T Y) = kmsInner σ (T X) Y) ∧
  (∀ (D E : ℕ) (ρ : Operator D), ρ.PosDef →
    ∀ (σ : Operator E) (T : Operator D →ₗ[ℂ] Operator E)
      (A : Operator E →ₗ[ℂ] Operator D),
    (∀ X Y, kmsInner ρ X (A Y) = kmsInner σ (T X) Y) → A = kmsAdjointMap ρ σ T) ∧
  (∀ (D : ℕ) (ρ : Operator D), ρ.PosDef →
    ∀ T : Operator D →ₗ[ℂ] Operator D,
    KmsSelfAdjoint ρ T ↔ kmsAdjointMap ρ ρ T = T) ∧
  (∀ (D : ℕ) (G : GKSL D) (ρ : Operator D), ρ.PosSemidef →
    KmsSelfAdjoint ρ (gkslHeisenbergMap G) → IsStationary G ρ) ∧
  (∀ (D : ℕ) (G : GKSL D) (ρ : Operator D), ρ.IsHermitian →
    lindbladApply G ρ = 0 → ∀ X : Operator D,
    -(Matrix.trace (ρ * Xᴴ * gkslHeisenbergMap G X)).re =
      (1 / 2 : ℝ) * ∑ j,
        (Matrix.trace (ρ * (G.jumps j * X - X * G.jumps j)ᴴ *
          (G.jumps j * X - X * G.jumps j))).re)
end Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCompleteness

namespace Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCompleteness.LindbladSemigroup
open Matrix Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- Assemble the semigroup, channel, and KMS-adjoint properties of the given GKSL
generator; see [Lindblad, quantum dynamical semigroups][Lindblad1976]. -/
theorem clause1_complete : Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCompleteness.Clause22Complete := by
  exact ⟨Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore.g1,
    (fun D E ρ hρ σ T X Y => kmsAdjointMap_inner hρ σ T X Y),
    (fun D E ρ hρ σ T A hA => kmsAdjointMap_unique hρ σ T A hA),
    (fun D ρ hρ T => kmsSelfAdjoint_iff_kmsAdjointMap_eq hρ T),
    (fun D G ρ hρ hself => stationary_of_heisenberg_kmsSelfAdjoint G ρ hρ hself),
    (fun D G ρ hρ hzero X => gkslHeisenberg_dirichlet_trace G hρ hzero X)⟩
end Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCompleteness.LindbladSemigroup
