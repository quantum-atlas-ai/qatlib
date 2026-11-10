/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity
import Qatlib.Concepts.MixedFidelity.FidelityMetric.SimultaneousDiagonalization
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.MixedFidelity.FidelityMetric
open Matrix
open scoped BigOperators MatrixOrder ComplexOrder

theorem isProbVector_of_unitary_diagonal {D : ℕ} {ρ : Operator D}
    (hρ : IsDensityOperator ρ) {U : Operator D}
    (hU : Uᴴ * U = 1) {p : Fin D → ℝ}
    (hp : U * ρ * Uᴴ = diagDensity p) : IsProbVector p := by
  have hpos : (diagDensity p).PosSemidef := by
    rw [← hp]
    exact hρ.1.mul_mul_conjTranspose_same U
  refine ⟨?_, ?_⟩
  · intro i
    have h := (Complex.nonneg_iff.mp (hpos.diag_nonneg (i := i))).1
    simpa [diagDensity] using h
  · have ht : (diagDensity p).trace = 1 := by
      rw [← hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU,
        Matrix.one_mul, hρ.2]
    have hr := congrArg Complex.re ht
    simpa [diagDensity, Matrix.trace] using hr

theorem commutesToClassical_of_density {D : ℕ} {ρ σ : Operator D}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    CommutesToClassical ρ σ := by
  intro hcomm
  let C : Bool → Operator D := fun b => if b then σ else ρ
  have hHerm : ∀ b, (C b).IsHermitian := by
    intro b
    cases b <;> simp only [C, Bool.false_eq_true, ↓reduceIte] <;>
      first | exact hρ.1.1 | exact hσ.1.1
  have hComm : ∀ a b, C a * C b = C b * C a := by
    intro a b
    cases a <;> cases b <;> simp only [C, Bool.false_eq_true, ↓reduceIte]
    · exact hcomm
    · exact hcomm.symm
  obtain ⟨U, d, hUr, hUl, hd⟩ :=
    exists_simultaneous_unitary_diagonalization C hHerm hComm
  have hdiag (b : Bool) : Uᴴ * C b * (Uᴴ)ᴴ = diagDensity (d b) := by
    rw [hd b, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUl, Matrix.one_mul, Matrix.mul_one]
    rfl
  have hρd : Uᴴ * ρ * (Uᴴ)ᴴ = diagDensity (d false) := by
    simpa only [C, Bool.false_eq_true, ↓reduceIte] using hdiag false
  have hσd : Uᴴ * σ * (Uᴴ)ᴴ = diagDensity (d true) := by
    simpa only [C, ↓reduceIte] using hdiag true
  have hV : (Uᴴ)ᴴ * Uᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hUr
  refine ⟨Uᴴ, d false, d true, ?_,
    isProbVector_of_unitary_diagonal hρ hV hρd,
    isProbVector_of_unitary_diagonal hσ hV hσd, hρd, hσd⟩
  apply Matrix.mem_unitaryGroup_iff.mpr
  change Uᴴ * (Uᴴ)ᴴ = 1
  simpa only [Matrix.conjTranspose_conjTranspose] using hUl

private noncomputable def completeFrootG {I : Type} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

theorem clause1_complete :
  (∀ (D : ℕ) (ρ σ : Operator D), IsDensityOperator ρ → IsDensityOperator σ →
    (completeFrootG ρ σ = Froot ρ σ) ∧
    (0 ≤ Froot ρ σ ∧ Froot ρ σ ≤ 1 ∧
      0 ≤ traceDistance ρ σ ∧ traceDistance ρ σ ≤ 1) ∧
    (Froot ρ σ = Froot σ ρ) ∧
    (Froot ρ σ = 1 ↔ ρ = σ) ∧
    (∀ ψ φ : QState (Fin D), Normalized ψ → Normalized φ →
      Froot (outerProduct ψ) (outerProduct φ) = ‖Qatlib.Foundations.PureStateMath.Inner ψ φ‖) ∧
    (∀ (p q : Fin D → ℝ), IsProbVector p → IsProbVector q →
      Froot (diagDensity p) (diagDensity q) = ∑ i, Real.sqrt (p i * q i)) ∧
    (CommutesToClassical ρ σ → ρ * σ = σ * ρ →
      ∀ (p q : Fin D → ℝ), IsProbVector p → IsProbVector q →
        ∀ U : Matrix (Fin D) (Fin D) ℂ, U ∈ Matrix.unitaryGroup (Fin D) ℂ →
          U * ρ * Uᴴ = diagDensity p → U * σ * Uᴴ = diagDensity q →
          Froot ρ σ = ∑ i, Real.sqrt (p i * q i)) ∧
    (∀ U : Matrix (Fin D) (Fin D) ℂ, U ∈ Matrix.unitaryGroup (Fin D) ℂ →
      Froot (U * ρ * Uᴴ) (U * σ * Uᴴ) = Froot ρ σ ∧
      traceDistance (U * ρ * Uᴴ) (U * σ * Uᴴ) = traceDistance ρ σ) ∧
    (∀ (E : ℕ) (τ ω : Operator E), IsDensityOperator τ → IsDensityOperator ω →
      completeFrootG (TensorGate ρ τ) (TensorGate σ ω) =
        completeFrootG ρ σ * completeFrootG τ ω)) ∧
  (∀ (D : ℕ) (ρ σ : Operator D), IsDensityOperator ρ → IsDensityOperator σ →
    ρ * σ = σ * ρ → CommutesToClassical ρ σ) := by
  refine ⟨?_, ?_⟩
  · exact g1
  · intro D ρ σ hρ hσ _
    exact commutesToClassical_of_density hρ hσ

end Qatlib.Concepts.MixedFidelity.FidelityMetric
