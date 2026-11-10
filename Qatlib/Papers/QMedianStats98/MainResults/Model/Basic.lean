/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

set_option autoImplicit false

namespace Qatlib.Papers.QMedianStats98.MainResults.Model

open MvPolynomial

def weight {n : ℕ} (X : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => X i = true)).card

def partialSymmetric (n ℓ ℓ' : ℕ) (X : Fin n → Bool) : Option Bool :=
  if weight X = ℓ then some true
  else if weight X = ℓ' then some false
  else none

noncomputable def evalBool {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (X : Fin n → Bool) : ℝ :=
  p.eval (fun i => if X i then (1 : ℝ) else 0)

noncomputable def ApproximatesWithin {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (ℓ ℓ' : ℕ) (c : ℝ) : Prop :=
  (∀ X : Fin n → Bool, evalBool p X ∈ Set.Icc (-c) (1 + c)) ∧
  (∀ X : Fin n → Bool, weight X = ℓ → |evalBool p X - 1| ≤ c) ∧
  (∀ X : Fin n → Bool, weight X = ℓ' → |evalBool p X| ≤ c)

def deltaL (ℓ ℓ' : ℕ) : ℝ := (Nat.dist ℓ ℓ' : ℝ)

noncomputable def mSelect (n ℓ ℓ' : ℕ) : ℝ :=
  if |(n : ℝ) / 2 - (ℓ : ℝ)| ≥ |(n : ℝ) / 2 - (ℓ' : ℝ)| then (ℓ : ℝ) else (ℓ' : ℝ)

noncomputable def lowerBound (n ℓ ℓ' : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / deltaL ℓ ℓ') +
    Real.sqrt (mSelect n ℓ ℓ' * ((n : ℝ) - mSelect n ℓ ℓ')) / deltaL ℓ ℓ'

def BigOmega (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * g n ≤ f n

def BigO (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n ≤ c * g n

end Qatlib.Papers.QMedianStats98.MainResults.Model
