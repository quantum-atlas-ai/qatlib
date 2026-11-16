/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.ClauseModel
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Preserved explicit QAOA state and conditional expectation bridges
The archived phase sign and clause functional have not been identified with
the paper objective. Normalization is an explicit hypothesis of the bridges.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOABddOcc14.MainResults
open scoped BigOperators
open Qatlib.Papers.QAOABddOcc14.MainResults
open Matrix

/-- `Z_a`: the diagonal `σ_z` on bit `a`, with eigenvalue `±1` on a basis state. -/
def Zop {n : ℕ} (a : Fin n) : Matrix (Basis n) (Basis n) ℂ :=
  Matrix.diagonal (fun z => (bitSign z a : ℂ))

/-- `X_a`: the `σ_x` on bit `a`; it flips bit `a`. -/
def Xop {n : ℕ} (a : Fin n) : Matrix (Basis n) (Basis n) ℂ :=
  fun z w => if w = Function.update z a (!z a) then (1 : ℂ) else 0

/-- The objective operator `C = (1/2) Σ_{a<b<c} d_abc Z_a Z_b Z_c` of paper (6). -/
def Cmat {n : ℕ} (I : E3Instance n) : Matrix (Basis n) (Basis n) ℂ :=
  (1 / 2 : ℂ) • ∑ p : Triple n,
    (I.d p : ℂ) • (Zop p.first * Zop p.second * Zop p.third)

/-- The mixer `B = X_1 + ⋯ + X_n` of paper (2). -/
def Bmat (n : ℕ) : Matrix (Basis n) (Basis n) ℂ := ∑ a : Fin n, Xop a

/-- The uniform start-state amplitude `2^{-n/2}` of paper (3). -/
def plusAmp (n : ℕ) : ℂ := ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ)

/-- The phase stage `e^{-iγC}` evaluated on a basis state: `C` is diagonal (1). -/
def phaseAmp {n : ℕ} (I : E3Instance n) (γ : ℝ) (z : Basis n) : ℂ :=
  Complex.exp (-(Complex.I * (γ : ℂ)) * (I.objectiveValue z : ℂ))

/-- The mixer `e^{-iβB} = ⊗_a e^{-iβX_a}` evaluated in the computational basis.
Single-qubit entry: `cos β` on the diagonal and `−i sin β` off the diagonal. -/
def mixAmp {n : ℕ} (β : ℝ) (z w : Basis n) : ℂ :=
  ∏ a : Fin n, if z a = w a then (Real.cos β : ℂ) else -(Complex.I * (Real.sin β : ℂ))

/-- The level-1 state `|γ,β⟩ = e^{-iβB} e^{-iγC} |s⟩` of paper (4), written as
the explicit superposition over the computational basis. -/
def qaoaAmp {n : ℕ} (I : E3Instance n) (γ β : ℝ) (z : Basis n) : ℂ :=
  ∑ w : Basis n, mixAmp β z w * phaseAmp I γ w * plusAmp n

/-- The measurement weight `|⟨z|γ,β⟩|²`. -/
def measWeight {n : ℕ} (I : E3Instance n) (γ β : ℝ) (z : Basis n) : ℝ :=
  Complex.normSq (qaoaAmp I γ β z)

/-- The archived expectation for the state with phase `exp(-i gamma C)`.
The positive-advantage calculation in the source uses the sign-adjusted state. -/
def qaoaExp {n : ℕ} (I : E3Instance n) (γ β : ℝ) : ℝ :=
  ∑ z : Basis n, measWeight I γ β z * I.objectiveValue z

/-- A finite weighted average is at most the maximum when the weights sum to one. -/
theorem exists_ge_weighted_average {ι : Type*} [Fintype ι] [Nonempty ι]
    (w C : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ∃ i, C i ≥ ∑ i, w i * C i := by
  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι) C (by simp)
  refine ⟨i₀, ?_⟩
  have hle : ∑ i, w i * C i ≤ ∑ i, w i * C i₀ := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hmax i (Finset.mem_univ i)) (hw i)
  have heq : ∑ i, w i * C i₀ = C i₀ := by
    rw [← Finset.sum_mul, hsum, one_mul]
  linarith

/-- Every computational-basis measurement weight is nonnegative. `|v|² ≥ 0`. -/
theorem measWeight_nonneg {n : ℕ} (I : E3Instance n) (γ β : ℝ) (z : Basis n) :
    0 ≤ measWeight I γ β z := Complex.normSq_nonneg _

/-- **Expected satisfied equations** = `m/2` plus the objective expectation
(paper §II p. 4: "The expected number of satisfied equations is `m/2` plus (7)"). -/
theorem expected_satisfied_eq {n : ℕ} (I : E3Instance n) (γ β : ℝ)
    (hsum : ∑ z : Basis n, measWeight I γ β z = 1) :
    ∑ z : Basis n, measWeight I γ β z * (I.satisfiedCount z : ℝ) =
      (I.numEquations : ℝ) / 2 + qaoaExp I γ β := by
  have hstep : ∀ z : Basis n,
      measWeight I γ β z * (I.satisfiedCount z : ℝ) =
        measWeight I γ β z * I.objectiveValue z + measWeight I γ β z * ((I.numEquations : ℝ) / 2) := by
    intro z
    rw [I.objectiveValue_eq z]; ring
  calc
    ∑ z : Basis n, measWeight I γ β z * (I.satisfiedCount z : ℝ)
        = ∑ z : Basis n, (measWeight I γ β z * I.objectiveValue z +
            measWeight I γ β z * ((I.numEquations : ℝ) / 2)) :=
          Finset.sum_congr rfl (fun z _ => hstep z)
    _ = qaoaExp I γ β + (∑ z : Basis n, measWeight I γ β z) * ((I.numEquations : ℝ) / 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]; rfl
    _ = (I.numEquations : ℝ) / 2 + qaoaExp I γ β := by rw [hsum, one_mul]; ring

/-- A normalized expectation lower bound gives existence of a good basis string.
This finite support argument does not establish a repeated-sampling success probability. -/
theorem exists_string_of_expectation {n : ℕ} (I : E3Instance n) (γ β : ℝ)
    (hsum : ∑ z : Basis n, measWeight I γ β z = 1) (δ : ℝ)
    (hδ : qaoaExp I γ β ≥ δ) :
    ∃ z : Basis n, (I.satisfiedCount z : ℝ) ≥ (I.numEquations : ℝ) / 2 + δ := by
  have hbridge := expected_satisfied_eq I γ β hsum
  have hgood : ∑ z : Basis n, measWeight I γ β z * (I.satisfiedCount z : ℝ) ≥
      (I.numEquations : ℝ) / 2 + δ := by
    rw [hbridge]; linarith
  have : Nonempty (Basis n) := ⟨fun _ => false⟩
  obtain ⟨z, hz⟩ := exists_ge_weighted_average (measWeight I γ β) (fun z => (I.satisfiedCount z : ℝ))
    (measWeight_nonneg I γ β) hsum
  exact ⟨z, le_trans hgood hz⟩

end Qatlib.Papers.QAOABddOcc14.MainResults
