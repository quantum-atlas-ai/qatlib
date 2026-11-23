/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOAScaling23.LABSDefs
public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

/-!
# The LABS phase operator

Equations (4)–(5) of arXiv:2308.02342v2 use each four- and two-qubit
Pauli Z product as a diagonal Hamiltonian term. Index the terms from zero
and use the standard spin eigenvalues to obtain the finite matrix.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QAOAScaling23.LABSDefs

namespace Qatlib.Papers.QAOAScaling23.QuantumPrep

/-- The zero-based four-body domain is precisely the three printed sum ranges. -/
theorem four_body_index_bounds (N i t k : ℕ) :
    (0 < t ∧ t < k ∧ i + k + t < N) ↔
      i + 1 ≤ N - 3 ∧ 1 ≤ t ∧ t ≤ (N - (i + 1) - 1) / 2 ∧
        t + 1 ≤ k ∧ k ≤ N - (i + 1) - t := by
  omega

/-- The zero-based two-body domain is precisely the two printed sum ranges. -/
theorem two_body_index_bounds (N i k : ℕ) :
    (0 < k ∧ i + 2 * k < N) ↔
      i + 1 ≤ N - 2 ∧ 1 ≤ k ∧ k ≤ (N - (i + 1)) / 2 := by
  omega

/-- The product of the four computational-basis eigenvalues in Eq. (4). -/
def fourBodySpin {N : ℕ} (s : Fin N → Bool) (i t k : Fin N) : ℝ :=
  if h : 0 < t.val ∧ t.val < k.val ∧ i.val + k.val + t.val < N then
    spin (s i) * spin (s ⟨i.val + t.val, by omega⟩) *
      spin (s ⟨i.val + k.val, by omega⟩) * spin (s ⟨i.val + k.val + t.val, h.2.2⟩)
  else 0

/-- The product of the two computational-basis eigenvalues in Eq. (4). -/
def twoBodySpin {N : ℕ} (s : Fin N → Bool) (i k : Fin N) : ℝ :=
  if h : 0 < k.val ∧ i.val + 2 * k.val < N then
    spin (s i) * spin (s ⟨i.val + 2 * k.val, h.2⟩)
  else 0

/-- The printed LABS Hamiltonian's energy on a computational-basis string. -/
def printedEnergy {N : ℕ} (s : Fin N → Bool) : ℝ :=
  2 * (∑ i : Fin N, ∑ t : Fin N, ∑ k : Fin N, fourBodySpin s i t k) +
    ∑ i : Fin N, ∑ k : Fin N, twoBodySpin s i k

/-- The diagonal LABS Hamiltonian matrix specified by Eq. (4). -/
def labsHamiltonian (N : ℕ) : Matrix (Fin N → Bool) (Fin N → Bool) ℂ :=
  Matrix.diagonal (fun s => (printedEnergy s : ℂ))

/-- The phase operator in Eq. (5), defined as the exponential of that Hamiltonian. -/
def labsPhaseOperator (N : ℕ) (γ : ℝ) : Matrix (Fin N → Bool) (Fin N → Bool) ℂ :=
  NormedSpace.exp ((-(γ : ℂ) * Complex.I) • labsHamiltonian N)

/-- The matrix exponential is diagonal with the printed energy phases as entries. -/
theorem labsPhaseOperator_diagonal (N : ℕ) (γ : ℝ) :
    labsPhaseOperator N γ =
      Matrix.diagonal (fun s => Complex.exp ((-γ * printedEnergy s : ℝ) * Complex.I)) := by
  rw [labsPhaseOperator, labsHamiltonian, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext s
  simp only [Pi.exp_def, Pi.smul_apply, smul_eq_mul, ← Complex.exp_eq_exp_ℂ]
  push_cast
  congr 1
  ring

/-- The phase operator multiplies every basis vector by the expected energy phase. -/
theorem labsPhaseOperator_ket {N : ℕ} (γ : ℝ) (s : Fin N → Bool) :
    labsPhaseOperator N γ *ᵥ Ket s =
      Complex.exp ((-γ * printedEnergy s : ℝ) * Complex.I) • Ket s := by
  rw [labsPhaseOperator_diagonal]
  funext x
  rw [Matrix.mulVec_diagonal]
  by_cases h : x = s
  · subst x
    rfl
  · simp [Ket, h]

/-- Every real phase angle yields a unitary LABS evolution. -/
theorem labsPhaseOperator_unitary (N : ℕ) (γ : ℝ) :
    labsPhaseOperator N γ ∈ Matrix.unitaryGroup (Fin N → Bool) ℂ := by
  rw [labsPhaseOperator_diagonal]
  apply diagonal_mem_unitaryGroup
  intro s
  simp [Complex.norm_exp, Complex.mul_re]

/-- At three sites the printed scalar is exactly the first/last spin product. -/
theorem printedEnergy_three (s : Fin 3 → Bool) : printedEnergy s = printed_core s := by
  norm_num [printedEnergy, fourBodySpin, twoBodySpin, printed_core, Fin.sum_univ_succ]

/-- At three sites the true squared sidelobe energy retains its constant and scale. -/
theorem trueEnergy_three (s : Fin 3 → Bool) : energy s = 3 + 2 * printedEnergy s := by
  rw [printedEnergy_three, energy_three]

end Qatlib.Papers.QAOAScaling23.QuantumPrep
