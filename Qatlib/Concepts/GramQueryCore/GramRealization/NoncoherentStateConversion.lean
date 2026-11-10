/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.FilteredCert

namespace Qatlib.Concepts.GramQueryCore.GramRealization
open Matrix
open scoped ComplexOrder BigOperators

def qStateTensor {H K : Type} (ψ : QState H) (φ : QState K) : QState (H × K) :=
  fun p => ψ p.1 * φ p.2

theorem normalized_qStateTensor {H K : Type} [Fintype H] [Fintype K]
    {ψ : QState H} {φ : QState K} (hψ : Normalized ψ) (hφ : Normalized φ) :
    Normalized (qStateTensor ψ φ) := by
  unfold Normalized qStateTensor at *
  simp only [Fintype.sum_prod_type, norm_mul, mul_pow]
  simp_rw [← Finset.mul_sum]
  rw [hφ]
  simp only [mul_one]
  exact hψ

theorem gramStateMatrix_qStateTensor {H K X : Type} [Fintype H] [Fintype K]
    (σ : X → QState H) (s : X → QState K) :
    gramStateMatrix (fun x => qStateTensor (σ x) (s x)) =
      gramStateMatrix σ ⊙ gramStateMatrix s := by
  classical
  ext x y
  change Inner (qStateTensor (σ x) (s x)) (qStateTensor (σ y) (s y)) =
    Inner (σ x) (σ y) * Inner (s x) (s y)
  rw [Qatlib.Foundations.PureStateMath.inner_apply,
      Qatlib.Foundations.PureStateMath.inner_apply, Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [qStateTensor, Fintype.sum_prod_type, map_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gramStateMatrix_posSemidef {H X : Type} [Fintype H] [Fintype X]
    (ρ : X → QState H) : (gramStateMatrix ρ).PosSemidef := by
  let V : Matrix H X ℂ := fun i x => ρ x i
  have hg : gramStateMatrix ρ = Vᴴ * V := by ext x y; rfl
  rw [hg]
  exact Matrix.posSemidef_conjTranspose_mul_self V

noncomputable def overlapPhase (z : ℂ) : ℂ := if z = 0 then 1 else (‖z‖ : ℂ) / z

theorem overlapPhase_mul (z : ℂ) : overlapPhase z * z = (‖z‖ : ℂ) := by
  classical
  by_cases hz : z = 0
  · simp [overlapPhase, hz]
  · simp only [overlapPhase, if_neg hz]
    exact div_mul_cancel₀ _ hz

theorem overlapPhase_norm (z : ℂ) : ‖overlapPhase z‖ = 1 := by
  classical
  by_cases hz : z = 0
  · simp [overlapPhase, hz]
  · simp [overlapPhase, hz, Complex.norm_real, norm_ne_zero_iff.mpr hz]

theorem normalized_phase {H : Type} [Fintype H] (ψ : QState H)
    (hψ : Normalized ψ) (a : ℂ) (ha : ‖a‖ = 1) :
    Normalized (fun i => a * ψ i) := by
  unfold Normalized at *
  simpa only [norm_mul, ha, one_mul] using hψ

theorem gramStateMatrix_phase {H X : Type} [Fintype H]
    (ψ : X → QState H) (a : X → ℂ) :
    gramStateMatrix (fun x i => a x * ψ x i) =
      fun x y => (starRingEnd ℂ) (a x) * a y * gramStateMatrix ψ x y := by
  classical
  ext x y
  change Inner (fun i => a x * ψ x i) (fun i => a y * ψ y i) =
    (starRingEnd ℂ) (a x) * a y * Inner (ψ x) (ψ y)
  rw [Qatlib.Foundations.PureStateMath.inner_apply,
      Qatlib.Foundations.PureStateMath.inner_apply]
  simp only [map_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem posSemidef_phase {X : Type} [Fintype X] [DecidableEq X]
    (S : Matrix X X ℂ) (hS : S.PosSemidef) (a : X → ℂ) :
    Matrix.PosSemidef (fun x y => (starRingEnd ℂ) (a x) * a y * S x y) := by
  have he : (fun x y => (starRingEnd ℂ) (a x) * a y * S x y) =
      (Matrix.diagonal a)ᴴ * S * Matrix.diagonal a := by
    ext x y
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
      starRingEnd_apply, Pi.star_apply]
    ring
  rw [he]
  exact hS.conjTranspose_mul_mul_same (Matrix.diagonal a)

end Qatlib.Concepts.GramQueryCore.GramRealization
