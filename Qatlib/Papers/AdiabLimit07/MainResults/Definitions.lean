/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

def numConfigs (n : ℕ) : ℕ := 2 ^ n

theorem numConfigs_eq_card_reg (n : ℕ) : numConfigs n = Fintype.card (Reg n) := by
  rw [numConfigs, card_reg]

variable {n : ℕ}

def qBlock {q : ℕ} (qIdx : Reg n → Fin (q + 1)) (k : Fin (q + 1)) : Finset (Reg n) :=
  Finset.univ.filter fun z => qIdx z = k

def pBlock {p : ℕ} (pIdx : Reg n → Fin (p + 1)) (j : Fin (p + 1)) : Finset (Reg n) :=
  Finset.univ.filter fun z => pIdx z = j

def solutionSet {p : ℕ} (pIdx : Reg n → Fin (p + 1)) : Finset (Reg n) :=
  pBlock pIdx 0

def walshChar (z x y : Reg n) : ℂ :=
  ∏ i, (if z i && (x i ^^ y i) then (-1 : ℂ) else 1)

def hadamardHamiltonian {q : ℕ} (F : Fin (q + 1) → ℝ)
    (qIdx : Reg n → Fin (q + 1)) : Matrix (Reg n) (Reg n) ℂ :=
  HadamardN n * Matrix.diagonal (fun z => (F (qIdx z) : ℂ)) * (HadamardN n)ᴴ

def computationalHamiltonian {p : ℕ} (E : Fin (p + 1) → ℝ)
    (pIdx : Reg n → Fin (p + 1)) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal (fun z => (E (pIdx z) : ℂ))

def genHamiltonian (s : ℝ) (H0 H1 : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  (1 - s) • H0 + s • H1

def solutionProb {p : ℕ} (pIdx : Reg n → Fin (p + 1)) (ψ : QState (Reg n)) : ℝ :=
  ∑ w ∈ solutionSet pIdx, BornProb ψ w

def initialUniform (n : ℕ) : QState (Reg n) := Uniform (Reg n)

def SchrodingerIVP (H : ℝ → Matrix (Reg n) (Reg n) ℂ)
    (ψ : ℝ → QState (Reg n)) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ x,
    HasDerivAt (fun s => ψ s x) (-(Complex.I) * (H t).mulVec (ψ t) x) t

def InitialUniform (ψ : ℝ → QState (Reg n)) : Prop :=
  ψ 0 = initialUniform n

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

def LargestBlock {q : ℕ} (qIdx : Reg n → Fin (q + 1)) (K : Fin (q + 1)) : Prop :=
  ∀ k, (qBlock qIdx k).card ≤ (qBlock qIdx K).card

def eigenspaceComplementDim {q : ℕ} (qIdx : Reg n → Fin (q + 1))
    (K : Fin (q + 1)) : ℝ :=
  ((2 : ℕ) ^ n : ℝ) - ((qBlock qIdx K).card : ℝ)

end Qatlib.Papers.AdiabLimit07.MainResults
