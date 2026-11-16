/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.Qubitization19.MainResults

/-- Lemma 11's printed positive shifts give the stated two-dimensional phased iterate. -/
theorem lemma11_phased_iterate
    (lam φ : ℝ) (_h1 : -1 ≤ lam) (_h2 : lam ≤ 1) :
    let Z : ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
      fun c => Matrix.diagonal ![(Complex.exp (-Complex.I * c)), (-1 : ℂ)]
    let W : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(lam : ℂ), -((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ);
        ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ), (lam : ℂ)]
    let Wφ : Matrix (Fin 2) (Fin 2) ℂ :=
      !![(lam : ℂ), -Complex.I * Complex.exp (-Complex.I * (φ : ℂ)) *
          ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ);
        -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) *
          ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ), (lam : ℂ)]
    Wφ = Z ((φ : ℂ) + Real.pi / 2) * W * Z (-((φ : ℂ) + Real.pi / 2)) := by
  dsimp only
  have he1 : Complex.exp (-Complex.I * ((φ : ℂ) + Real.pi / 2)) =
      -Complex.I * Complex.exp (-Complex.I * (φ : ℂ)) := by
    rw [show -Complex.I * ((φ : ℂ) + Real.pi / 2) =
      -(Real.pi : ℂ) / 2 * Complex.I + -Complex.I * (φ : ℂ) by ring,
      Complex.exp_add, Complex.exp_neg_pi_div_two_mul_I]
  have he2 : Complex.exp (-Complex.I * (-((φ : ℂ) + Real.pi / 2))) =
      Complex.I * Complex.exp (Complex.I * (φ : ℂ)) := by
    rw [show -Complex.I * (-((φ : ℂ) + Real.pi / 2)) =
      (Real.pi : ℂ) / 2 * Complex.I + Complex.I * (φ : ℂ) by ring,
      Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  have he3 : Complex.exp (-Complex.I * (φ : ℂ)) *
      Complex.exp (Complex.I * (φ : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  · change (lam : ℂ) =
      Complex.exp (-Complex.I * ((φ : ℂ) + Real.pi / 2)) * (lam : ℂ) *
        Complex.exp (-Complex.I * (-((φ : ℂ) + Real.pi / 2)))
    rw [he1, he2]
    calc
      (lam : ℂ) = (lam : ℂ) *
          (Complex.exp (-Complex.I * (φ : ℂ)) * Complex.exp (Complex.I * (φ : ℂ))) := by
            rw [he3, mul_one]
      _ = _ := by ring_nf; simp [Complex.I_sq]
  · change -Complex.I * Complex.exp (-Complex.I * (φ : ℂ)) *
      ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) =
        Complex.exp (-Complex.I * ((φ : ℂ) + Real.pi / 2)) *
          (-((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ)) * -1
    rw [he1]
    ring
  · change -Complex.I * Complex.exp (Complex.I * (φ : ℂ)) *
      ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) =
        (-1 : ℂ) * ((Real.sqrt (1 - lam ^ 2) : ℝ) : ℂ) *
          Complex.exp (-Complex.I * (-((φ : ℂ) + Real.pi / 2)))
    rw [he2]
    ring
  · change (lam : ℂ) = (-1 : ℂ) * (lam : ℂ) * -1
    ring


end Qatlib.Papers.Qubitization19.MainResults
