/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hamiltonians and solution probabilities for adiabatic bounds

Defines spectral blocks, Walsh characters, computational and Hadamard basis Hamiltonians, and
their linear interpolation `genHamiltonian`. It also specifies coordinatewise Schrödinger
evolution, uniform initialization, the solution probability, and the dimension of a block
complement. See [IoannouMosca2008].

## Main statements

* `solutionProb_initialUniform`: Uniform initialization gives the fraction of configurations in
  the solution set.
* `SchrodingerIVP`: The coordinatewise Schrödinger equation on the time interval.
* `eigenspaceComplementDim`: The real cardinality of the complement of a spectral block.

## References

* [Ioannou and Mosca, 2008][IoannouMosca2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

/-- The number `2 ^ n` of Boolean register configurations. -/
def numConfigs (n : ℕ) : ℕ := 2 ^ n

/-- The number of configurations equals the cardinality of `Reg n`. -/
theorem numConfigs_eq_card_reg (n : ℕ) : numConfigs n = Fintype.card (Reg n) := by
  rw [numConfigs, card_reg]

variable {n : ℕ}

/-- The finite fiber of the spectral block index `qIdx` at `k`. -/
def qBlock {q : ℕ} (qIdx : Reg n → Fin (q + 1)) (k : Fin (q + 1)) : Finset (Reg n) :=
  Finset.univ.filter fun z => qIdx z = k

/-- The finite fiber of the computational block index `pIdx` at `j`. -/
def pBlock {p : ℕ} (pIdx : Reg n → Fin (p + 1)) (j : Fin (p + 1)) : Finset (Reg n) :=
  Finset.univ.filter fun z => pIdx z = j

/-- The configurations in the zeroth computational block. -/
def solutionSet {p : ℕ} (pIdx : Reg n → Fin (p + 1)) : Finset (Reg n) :=
  pBlock pIdx 0

/-- The Boolean Walsh character obtained by multiplying the signs associated with `z` and the
bitwise difference of `x` and `y`. -/
def walshChar (z x y : Reg n) : ℂ :=
  ∏ i, (if z i && (x i ^^ y i) then (-1 : ℂ) else 1)

/-- The matrix obtained by conjugating the diagonal energies `F (qIdx z)` by the register
Hadamard matrix. -/
def hadamardHamiltonian {q : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) : Matrix (Reg n) (Reg n) ℂ :=
  HadamardN n * Matrix.diagonal (fun z => (F (qIdx z) : ℂ)) * (HadamardN n)ᴴ

/-- The diagonal matrix with computational basis energies `E (pIdx z)`. -/
def computationalHamiltonian {p : ℕ} (E : Fin (p + 1) → ℝ)
    (pIdx : Reg n → Fin (p + 1)) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun z => (E (pIdx z) : ℂ))

/-- The affine interpolation `(1 - s) • H0 + s • H1` of two Hamiltonian matrices. -/
def genHamiltonian (s : ℝ) (H0 H1 : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  (1 - s) • H0 + s • H1

/-- The sum of computational basis Born probabilities over `solutionSet pIdx`. -/
def solutionProb {p : ℕ} (pIdx : Reg n → Fin (p + 1)) (ψ : QState (Reg n)) : ℝ :=
  ∑ w ∈ solutionSet pIdx, BornProb ψ w

/-- The uniform state on the Boolean register. -/
def initialUniform (n : ℕ) : QState (Reg n) := Uniform (Reg n)

/-- The coordinatewise Schrödinger equation with derivative `-i H(t) ψ(t)` for every time in
`Set.Icc 0 T`. -/
def SchrodingerIVP (H : ℝ → Matrix (Reg n) (Reg n) ℂ)
    (ψ : ℝ → QState (Reg n)) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ x,
    HasDerivAt (fun s => ψ s x) (-(Complex.I) * (H t).mulVec (ψ t) x) t

/-- The condition that the state at time zero is `initialUniform n`. -/
def InitialUniform (ψ : ℝ → QState (Reg n)) : Prop :=
  ψ 0 = initialUniform n

/-- The solution probability of the uniform state is the solution-set cardinality divided by `2
^ n` [IoannouMosca2008]. -/
theorem solutionProb_initialUniform {p : ℕ} (pIdx : Reg n → Fin (p + 1)) :
    solutionProb pIdx (initialUniform n) =
      ((solutionSet pIdx).card : ℝ) / (((2 : ℕ) ^ n : ℝ)) := by
  have hN : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := by positivity
  have h1 : ‖((Real.sqrt (Fintype.card (Reg n)) : ℂ))⁻¹‖ =
      (Real.sqrt (Fintype.card (Reg n)))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  simp [solutionProb, initialUniform, BornProb, Uniform, h1, inv_pow,
    Real.sq_sqrt hN.le, card_reg, div_eq_mul_inv]

/-- The condition that block `K` has cardinality at least that of every other spectral block. -/
def LargestBlock {q : ℕ} (qIdx : Reg n → Fin (q + 1)) (K : Fin (q + 1)) : Prop :=
  ∀ k, (qBlock qIdx k).card ≤ (qBlock qIdx K).card

/-- The register cardinality minus the cardinality of spectral block `K`, regarded as a real
number. -/
def eigenspaceComplementDim {q : ℕ} (qIdx : Reg n → Fin (q + 1))
    (K : Fin (q + 1)) : ℝ :=
  ((2 : ℕ) ^ n : ℝ) - ((qBlock qIdx K).card : ℝ)

end Qatlib.Papers.AdiabLimit07.MainResults
