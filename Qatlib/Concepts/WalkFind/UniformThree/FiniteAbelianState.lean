/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.FiniteAbelian
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.WalkFind.UniformThree

open Matrix
open scoped ComplexConjugate Kronecker Classical

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem inner_fourier [DecidableEq G] (ψ φ : QState G) :
    Inner (fourier ψ) (fourier φ) = Inner ψ φ := by
  simp only [Qatlib.Foundations.PureStateMath.Inner, fourier]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    fourierMatrix_conjTranspose_mul, Matrix.vecMul_one]

theorem normalized_fourier_iff [DecidableEq G] (ψ : QState G) :
    Normalized (fourier ψ) ↔ Normalized ψ := by
  classical
  rw [normalized_iff_inner_self, inner_fourier, normalized_iff_inner_self]

theorem normalized_fourier [DecidableEq G] {ψ : QState G} (hψ : Normalized ψ) :
    Normalized (fourier ψ) := (normalized_fourier_iff ψ).2 hψ

theorem bornProb_fourier (ψ : QState G) (χ : AddChar G ℂ) :
    BornProb (fourier ψ) χ = ‖fourierScale G * ∑ x, conj (χ x) * ψ x‖ ^ 2 := by
  rw [BornProb, fourier_apply]

theorem normalized_fourierInv_iff [DecidableEq G] (φ : QState (AddChar G ℂ)) :
    Normalized (fourierInv φ) ↔ Normalized φ := by
  have h := normalized_fourier_iff (fourierInv φ)
  simpa only [fourier_fourierInv] using h.symm

theorem fourier_eq_sqrt_mul_average (ψ : QState G) (χ : AddChar G ℂ) :
    fourier ψ χ = (Real.sqrt (Fintype.card G) : ℂ) *
      ((Fintype.card G : ℂ)⁻¹ * ∑ x, conj (χ x) * ψ x) := by
  have hc : (Real.sqrt (Fintype.card G) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2
      (Nat.cast_pos.2 (Fintype.card_pos) : (0 : ℝ) < Fintype.card G)).ne'
  have h := fourierScale_mul_self (G := G)
  rw [fourier_apply, ← h, fourierScale]
  field_simp

theorem fourier_ket [DecidableEq G] (x : G) (χ : AddChar G ℂ) :
    fourier (Ket x) χ = fourierScale G * conj (χ x) := by
  simp [fourier_apply, Ket]

omit [AddCommGroup G] in

theorem norm_fourierScale_sq : ‖fourierScale G‖ ^ 2 = (Fintype.card G : ℝ)⁻¹ := by
  simp [fourierScale, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem bornProb_fourier_ket [DecidableEq G] (x : G) (χ : AddChar G ℂ) :
    BornProb (fourier (Ket x)) χ = 1 / (Fintype.card (AddChar G ℂ) : ℝ) := by
  simp [BornProb, fourier_ket, AddChar.norm_apply, norm_fourierScale_sq]

noncomputable def characterState (χ : AddChar G ℂ) : QState G :=
  fun x => fourierScale G * χ x

theorem fourier_characterState (η : AddChar G ℂ) :
    fourier (characterState η) = Ket η := by
  funext χ
  rw [fourier_apply]
  simp only [characterState]
  calc
    fourierScale G * (∑ x, conj (χ x) * (fourierScale G * η x)) =
        (fourierScale G * fourierScale G) * (∑ x, η x * conj (χ x)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = Ket η χ := by
      rw [sum_char_mul_conj]
      by_cases h : χ = η
      · subst χ
        simp [Ket, fourierScale_sq_mul_card]
      · simp [h, Ne.symm h, Ket]

theorem normalized_characterState [DecidableEq G] (χ : AddChar G ℂ) :
    Normalized (characterState χ) := by
  rw [← normalized_fourier_iff, fourier_characterState]
  exact normalized_ket χ

@[simp] theorem characterState_zero : characterState (0 : AddChar G ℂ) = Uniform G := by
  funext x
  simp [characterState, Uniform, fourierScale]

theorem fourier_uniform : fourier (Uniform G) = Ket (0 : AddChar G ℂ) := by
  rw [← characterState_zero, fourier_characterState]

theorem bornDistribution_fourier_apply [DecidableEq G] (ψ : QState G)
    (hψ : Normalized ψ) (χ : AddChar G ℂ) :
    bornDistribution (fourier ψ) (normalized_fourier hψ) χ =
      ENNReal.ofReal (‖fourierScale G * ∑ x, conj (χ x) * ψ x‖ ^ 2) := by
  rw [bornDistribution_apply, bornProb_fourier]

noncomputable def dualLabeling (G : Type*) [AddCommGroup G] [Fintype G] :
    G ≃ AddChar G ℂ := Fintype.equivOfCardEq (AddChar.card_eq (α := G)).symm

noncomputable def fourierGate (e : G ≃ AddChar G ℂ) : Matrix G G ℂ :=
  (fourierMatrix G).submatrix e id

theorem applyGate_fourierGate [DecidableEq G] (e : G ≃ AddChar G ℂ)
    (ψ : QState G) (x : G) :
    ApplyGate (fourierGate e) ψ x = fourier ψ (e x) := rfl

theorem fourierGate_unitary [DecidableEq G] (e : G ≃ AddChar G ℂ) :
    fourierGate e ∈ Matrix.unitaryGroup G ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  change (∑ z : G, star (fourierMatrix G (e z) x) * fourierMatrix G (e z) y) = _
  rw [e.sum_comp (fun χ => star (fourierMatrix G χ x) * fourierMatrix G χ y)]
  exact congrArg (fun A : Matrix G G ℂ => A x y) fourierMatrix_conjTranspose_mul

noncomputable def fourierCircuit (e : G ≃ AddChar G ℂ) : Circuit G :=
  [Step.gate (fourierGate e)]

theorem fourierCircuit_unitary [DecidableEq G] (e : G ≃ AddChar G ℂ) :
    IsUnitaryCircuit (fourierCircuit e) := by
  simp [fourierCircuit, fourierGate_unitary]

theorem fourierCircuit_resources (e : G ≃ AddChar G ℂ) :
    QueryCount (fourierCircuit e) = 0 ∧ GateCount (fourierCircuit e) = 1 ∧
      Size (fourierCircuit e) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

theorem run_fourierCircuit [DecidableEq G] (e : G ≃ AddChar G ℂ)
    (oracle : Matrix G G ℂ) (ψ : QState G) (χ : AddChar G ℂ) :
    Run oracle (fourierCircuit e) ψ (e.symm χ) = fourier ψ χ := by
  simp [fourierCircuit, applyGate_fourierGate]

theorem bornProb_run_fourierCircuit [DecidableEq G] (e : G ≃ AddChar G ℂ)
    (oracle : Matrix G G ℂ) (ψ : QState G) (χ : AddChar G ℂ) :
    BornProb (Run oracle (fourierCircuit e) ψ) (e.symm χ) = BornProb (fourier ψ) χ := by
  simp only [BornProb, run_fourierCircuit]

theorem measureProb_run_fourierCircuit [DecidableEq G] (e : G ≃ AddChar G ℂ)
    (oracle : Matrix G G ℂ) (ψ : QState G) (S : Finset (AddChar G ℂ)) :
    MeasureProb (Run oracle (fourierCircuit e) ψ) (S.map e.symm.toEmbedding) =
      MeasureProb (fourier ψ) S := by
  simp only [MeasureProb, Finset.sum_map, Equiv.toEmbedding_apply,
    bornProb_run_fourierCircuit]

section Product
variable {H : Type*} [AddCommGroup H] [Fintype H]

theorem fourier_tensorState (ψ : QState G) (φ : QState H) :
    (fourier (TensorState ψ φ)) ∘ prodDualEquiv = TensorState (fourier ψ) (fourier φ) := by
  funext ⟨χ, η⟩
  exact fourier_prod_apply ψ φ χ η

theorem fourierGate_prod (e : G ≃ AddChar G ℂ) (d : H ≃ AddChar H ℂ) :
    fourierGate ((Equiv.prodCongr e d).trans prodDualEquiv.toEquiv) =
      TensorGate (fourierGate e) (fourierGate d) := by
  ext ⟨x, y⟩ ⟨u, v⟩
  exact congrArg (fun A : Matrix (AddChar G ℂ × AddChar H ℂ) (G × H) ℂ =>
    A (e x, d y) (u, v)) fourierMatrix_prod

theorem bornProb_fourier_tensorState (ψ : QState G) (φ : QState H)
    (χ : AddChar G ℂ) (η : AddChar H ℂ) :
    BornProb (fourier (TensorState ψ φ)) (prodDualEquiv (χ, η)) =
      BornProb (fourier ψ) χ * BornProb (fourier φ) η := by
  have h := congrFun (fourier_tensorState ψ φ) (χ, η)
  change fourier (TensorState ψ φ) (prodDualEquiv (χ, η)) =
    fourier ψ χ * fourier φ η at h
  simp only [BornProb, h, norm_mul, mul_pow]

end Product

end Qatlib.Concepts.WalkFind.UniformThree
