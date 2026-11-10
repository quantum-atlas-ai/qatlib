/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
import Qatlib.Foundations.PureStateMath.Tensor
import Mathlib.LinearAlgebra.UnitaryGroup
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QMechSim97.MainResults.ActualCollision
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.OneDimContinuum
open scoped Classical BigOperators

def collision (a b : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, b, a, 0; 0, a, b, 0; 0, 0, 0, 1]

def pairOccupation (i : Fin 4) : ℕ := if i = 0 then 0 else if i = 3 then 2 else 1

theorem collision_unitary (a b : ℂ) (hp : IsUnitaryPair a b) :
    collision a b ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have hbb : (starRingEnd ℂ) b * b = (Complex.normSq b : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self]
  have haa : (starRingEnd ℂ) a * a = (Complex.normSq a : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self]
  have hn : (Complex.normSq a : ℂ) + (Complex.normSq b : ℂ) = 1 := by
    exact_mod_cast hp.1
  have hab : (starRingEnd ℂ) a * b + (starRingEnd ℂ) b * a = 0 := by
    convert hp.2 using 1; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [collision, Matrix.mul_apply, Fin.sum_univ_succ, haa, hbb, hn,
      add_comm, hab]

theorem collision_off_sector (a b : ℂ) (i j : Fin 4)
    (h : pairOccupation i ≠ pairOccupation j) : collision a b i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [collision, pairOccupation]

theorem collision_single_particle (a b α β : ℂ) :
    (collision a b).mulVec ![0, α, β, 0] = ![0, b * α + a * β, a * α + b * β, 0] := by
  ext i
  fin_cases i <;> simp [collision, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def InNumberSector {W : Type} (outsideCount : W → ℕ) (n : ℕ)
    (ψ : Fin 4 × W → ℂ) : Prop :=
  ∀ z, pairOccupation z.1 + outsideCount z.2 ≠ n → ψ z = 0

def collisionWithSpectator {W : Type} [DecidableEq W] (a b : ℂ) :
    Matrix (Fin 4 × W) (Fin 4 × W) ℂ := TensorGate (collision a b) 1

theorem collisionWithSpectator_unitary {W : Type} [Fintype W] [DecidableEq W]
    (a b : ℂ) (hp : IsUnitaryPair a b) :
    collisionWithSpectator (W := W) a b ∈ Matrix.unitaryGroup (Fin 4 × W) ℂ :=
  tensorGate_unitary (collision_unitary a b hp) (Submonoid.one_mem _)

theorem collisionWithSpectator_apply {W : Type} [Fintype W] [DecidableEq W]
    (a b : ℂ) (ψ : QState (Fin 4 × W)) (i : Fin 4) (w : W) :
    ApplyGate (collisionWithSpectator a b) ψ (i, w) =
      ∑ j : Fin 4, collision a b i j * ψ (j, w) := by
  simp only [collisionWithSpectator, ApplyGate, TensorGate, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single w (fun v _ hv => ?_) (fun h => absurd (Finset.mem_univ w) h)]
  · rw [Matrix.one_apply_eq]
    ring
  · rw [Matrix.one_apply_ne (fun h => hv h.symm), mul_zero, zero_mul]

theorem collision_preserves_number_sector {W : Type} [Fintype W] [DecidableEq W]
    (a b : ℂ) (outsideCount : W → ℕ) (n : ℕ) (ψ : QState (Fin 4 × W))
    (hψ : InNumberSector outsideCount n ψ) :
    InNumberSector outsideCount n (ApplyGate (collisionWithSpectator a b) ψ) := by
  intro z hz
  obtain ⟨i, w⟩ := z
  rw [collisionWithSpectator_apply]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : pairOccupation i = pairOccupation j
  · have hj : pairOccupation j + outsideCount w ≠ n := by simpa [hij] using hz
    rw [hψ (j, w) hj, mul_zero]
  · rw [collision_off_sector a b i j hij, zero_mul]

end Qatlib.Papers.QMechSim97.MainResults.ActualCollision
