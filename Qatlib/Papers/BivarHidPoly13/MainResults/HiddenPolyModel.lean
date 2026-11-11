/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option backward.isDefEq.respectTransparency false

/-!
# BivariateHiddenPoly13 — shared source model (MainResults)

Fixed source: arXiv:1305.1543v2 (9 Oct 2013), "Polynomial time quantum algorithms
for certain bivariate hidden polynomial problems" (Decker, Høyer, Ivanyos, Santha).
This module fixes the paper's standing notation:

* a hidden univariate polynomial with **zero constant term**,
  `f(x) = Σ_{s=1}^{D} ν_s x^s` (Section 1, p.2), encoded by `hiddenPoly`;
* its **level-set superposition** `Σ_{x∈F} |w + f(x)⟩|x⟩` (Eq. (1), p.2), whose
  amplitude pattern is `x ↦ w + f x`, encoded by `levelSetAmplitude`.

The results here are the *identifiability* kernel shared by Theorems 1 and 3:
the level-set data determine the hidden coefficients because the polynomial has
degree `< |F|` and zero constant term.  They do **not** model the quantum circuit
(QFT, measurements, Las Vegas δ-search); that is recorded in the per-claim
modules as the modeled residue.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset

namespace Qatlib.Papers.BivarHidPoly13.MainResults

variable {F : Type*} [Field F]

/-- Section 1, p.2: `f(x) = Σ_{s=1}^{D} ν_s x^s`, the hidden polynomial with
zero constant term; `ν : Fin D → F` records `ν_s` at index `s-1`. -/
def hiddenPoly (D : ℕ) (ν : Fin D → F) (x : F) : F :=
  ∑ i : Fin D, ν i * x ^ (i.val + 1)

/-- The polynomial form of `hiddenPoly` in `F[X]`. -/
def hiddenPolyPoly (D : ℕ) (ν : Fin D → F) : F[X] :=
  ∑ i : Fin D, C (ν i) * X ^ (i.val + 1)

/-- The amplitude pattern of the level-set superposition of Eq. (1):
`Σ_{x∈F} |w + f(x)⟩|x⟩` has the amplitude `w + f x` in the base register for
each `x` in the second register; up to normalisation the state is this function. -/
def levelSetAmplitude (f : F → F) (w : F) : F → F := fun x => w + f x

/-- The hidden polynomial vanishes at zero because all its monomials have
positive exponent (the zero constant term of the source). -/
@[simp] theorem hiddenPoly_zero (D : ℕ) (ν : Fin D → F) : hiddenPoly D ν 0 = 0 := by
  simp [hiddenPoly]

/-- Evaluating the polynomial form `hiddenPolyPoly` recovers the function
`hiddenPoly`. -/
@[simp] theorem hiddenPolyPoly_eval (D : ℕ) (ν : Fin D → F) (x : F) :
    (hiddenPolyPoly D ν).eval x = hiddenPoly D ν x := by
  simp [hiddenPolyPoly, hiddenPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]

/-- The `m`-th coefficient of `hiddenPolyPoly` is the sum of the `ν i` whose
monomial `X^{i+1}` has exponent `m`. -/
theorem coeff_hiddenPolyPoly (D : ℕ) (ν : Fin D → F) (m : ℕ) :
    (hiddenPolyPoly D ν).coeff m =
      ∑ i : Fin D, if i.val + 1 = m then ν i else 0 := by
  have hterm : ∀ i : Fin D,
      (C (ν i) * X ^ (i.val + 1) : F[X]).coeff m =
        if i.val + 1 = m then ν i else 0 := by
    intro i
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases h : i.val + 1 = m
    · simp [h]
    · have h' : m ≠ i.val + 1 := fun hh => h hh.symm
      simp [h, h']
  unfold hiddenPolyPoly
  rw [finsetSum_coeff]
  simp only [hterm]

/-- The coefficient of `X^{i+1}` in `hiddenPolyPoly` is `ν i`. -/
theorem coeff_hiddenPolyPoly_self (D : ℕ) (ν : Fin D → F) (i : Fin D) :
    (hiddenPolyPoly D ν).coeff (i.val + 1) = ν i := by
  rw [coeff_hiddenPolyPoly]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have hb' : b.val ≠ i.val := fun h => hb (Fin.ext h)
    have hne : b.val + 1 ≠ i.val + 1 := by omega
    rw [if_neg hne]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- `hiddenPolyPoly` has degree at most `D` (the top monomial is `X^D`). -/
theorem natDegree_hiddenPolyPoly_le (D : ℕ) (ν : Fin D → F) :
    (hiddenPolyPoly D ν).natDegree ≤ D := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_hiddenPolyPoly]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hne : i.val + 1 ≠ m := by have := i.isLt; omega
  simp [hne]

/-- **Identifiability of the hidden coefficients from the level-set data.**
If two zero-constant-term degree-`≤ D` polynomials produce the same level-set
superposition amplitude pattern `x ↦ w + f(x)` (possibly for different shifts
`w, w'`), then their coefficient vectors coincide.  Uses `D < |F|` so a nonzero
polynomial of degree `≤ D` cannot vanish on all of `F`.

This is the mathematical content of "the input states determine the hidden
coefficients" (Theorem 1, p.2–3); the quantum extraction of the coefficients is
modeled separately in `SourceTheorem1`. -/
theorem hiddenPoly_determined_by_levelSetAmplitude [Fintype F] [DecidableEq F]
    (D : ℕ) (hD : D < Fintype.card F) {ν ν' : Fin D → F} {w w' : F}
    (h : ∀ x, levelSetAmplitude (hiddenPoly D ν) w x
            = levelSetAmplitude (hiddenPoly D ν') w' x) :
    ν = ν' := by
  have hz := h 0
  simp only [levelSetAmplitude, hiddenPoly_zero, add_zero] at hz
  have hf : ∀ x, hiddenPoly D ν x = hiddenPoly D ν' x := by
    intro x
    have hx := h x
    simp only [levelSetAmplitude] at hx
    rw [hz] at hx
    exact add_left_cancel hx
  have hpoly : hiddenPolyPoly D ν = hiddenPolyPoly D ν' := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (Function.injective_id)
      (fun x => ?_) ?_
    · simpa only [hiddenPolyPoly_eval, id_eq] using hf x
    · have h1 := natDegree_hiddenPolyPoly_le D ν
      have h2 := natDegree_hiddenPolyPoly_le D ν'
      omega
  funext i
  have hcoeff := congrArg (fun p : F[X] => p.coeff (i.val + 1)) hpoly
  simpa only [coeff_hiddenPolyPoly_self] using hcoeff

/-- **Recovery map from one level-set superposition.**  From the amplitude
pattern `s = x ↦ w + f(x)` of a level-set superposition of a zero-constant-term
degree-`≤ D` polynomial, this map returns the coefficient vector.  It is defined
by choosing a witness `ν` with `s = x ↦ s(0) + f_ν(x)`; the shift `s 0 = w` is
recovered from the value at `0` because `f(0) = 0`. -/
def recoverFromLevelSet [Fintype F] [DecidableEq F] (D : ℕ) (s : F → F) : Fin D → F :=
  if h : ∃ ν : Fin D → F, s = levelSetAmplitude (hiddenPoly D ν) (s 0) then
    Classical.choose h
  else 0

/-- **The recovery map is correct on every promised instance.**  In the paper's
language: given a level-set superposition `Σ_x |w + f(x)⟩|x⟩` of the hidden
polynomial, the recovery returns exactly `ν_1, …, ν_D`.

Fixed arXiv:1305.1543v2, Theorem 1, p.2–3 (Eq. (1)). -/
theorem recoverFromLevelSet_spec [Fintype F] [DecidableEq F]
    (D : ℕ) (hD : D < Fintype.card F) (ν : Fin D → F) (w : F) :
    recoverFromLevelSet D (levelSetAmplitude (hiddenPoly D ν) w) = ν := by
  have h0 : levelSetAmplitude (hiddenPoly D ν) w 0 = w := by
    simp [levelSetAmplitude]
  have hex : ∃ ν' : Fin D → F,
      levelSetAmplitude (hiddenPoly D ν) w =
        levelSetAmplitude (hiddenPoly D ν') (levelSetAmplitude (hiddenPoly D ν) w 0) := by
    refine ⟨ν, ?_⟩
    rw [h0]
  unfold recoverFromLevelSet
  rw [dif_pos hex]
  have hchoose :
      levelSetAmplitude (hiddenPoly D ν) w =
        levelSetAmplitude (hiddenPoly D (Classical.choose hex))
          (levelSetAmplitude (hiddenPoly D ν) w 0) :=
    Classical.choose_spec hex
  have huniq := hiddenPoly_determined_by_levelSetAmplitude (F := F) D hD
    (fun x => congrFun hchoose x)
  exact huniq.symm

end Qatlib.Papers.BivarHidPoly13.MainResults
