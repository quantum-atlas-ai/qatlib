/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BivarHidPoly13.MainResults.HiddenPolyModel
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination

set_option backward.isDefEq.respectTransparency false

/-!
# BivarHidPoly13 — Theorem 2 (c002)

Fixed source: arXiv:1305.1543v2 (9 Oct 2013), Theorem 2, p.2–3; proof in
Section 3, p.15–16.

Theorem 2 (p.2–3). *Let `D` and `D'` be constants and let `g(y) = Σ_{s=0}^{D'}
μ_s y^s` be a fixed polynomial.  Furthermore, let `f(x) = Σ_{s=1}^{D} ν_s x^s`
be a polynomial of degree `D` with unknown coefficients `ν_s`.  Then, given a
quantum oracle that maps `|y⟩|x⟩|0⟩` to `|y⟩|x⟩|E(g(y) − f(x))⟩`, the unknown
coefficients `ν_1, …, ν_D` can be determined in polynomial time.*

The proof (Section 3) does three things:

1. the level-set counts satisfy `M_F(w) = Σ_{x∈F} m_g(f(x) + w)` (p.15),
   `M_F(w) = #{(x,y): g(y) − f(x) = w}`, `m_g(z) = #{y : g(y) = z}`;
2. the state `|Ψ_w⟩` obtained after the map `U_g` has constant overlap with the
   level-set superposition `|Λ_w⟩` of `u − f(x)`, so Theorem 1 still succeeds
   with `O(1)` states (p.16);
3. **verification by `D + 1` oracle points**: if a guess `f₀` satisfies
   `f(x_i) = f₀(x_i) + c` at `D + 1` distinct points `x_1,…,x_{D+1}`, then
   `f(x) = f₀(x) + c` for *every* `x`, because `f` has degree `≤ D`
   (p.16, lines "From this, f(x) = f₀(x) + w' − w follows for every x because
   f has degree at most D").

Formalized here: the count identity `theorem2_levelSetCount_identity` (1) and
the verification uniqueness `theorem2_guessVerification_correct` (3), together
with `theorem2_verification_determines`, which turns the `D + 1` verified
points into equality of the coefficient vectors (using the fixed zero constant
term).

Modeled residue (not discharged): the `U_g` amplitude analysis (Berlekamp root
finding, `m_g` bounds, overlap `≥ √(M_F(w)/(D'|F|))`), the repetition/constant
success probability, and the oracle/query cost of the final test; these need the
gate-level and amplitude layers.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset

namespace Qatlib.Papers.BivarHidPoly13.MainResults

section Counts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Section 3, p.15: `M_F(w) = #{(x,y) ∈ F² : g(y) − f(x) = w}`. -/
def levelSetCount (f g : F → F) (w : F) : ℕ :=
  Fintype.card {p : F × F // g p.2 - f p.1 = w}

/-- Section 3, p.15: `m_g(z) = #{y ∈ F : g(y) = z}`. -/
def fibreCount (g : F → F) (z : F) : ℕ :=
  Fintype.card {y : F // g y = z}

/-- Splitting the level set of `F(x,y) = g(y) − f(x)` by the value of `x`: the
pairs `(x,y)` with `g(y) − f(x) = w` are, for each `x`, the `y` with
`g(y) = f(x) + w`. -/
def levelSetEquiv (f g : F → F) (w : F) :
    {p : F × F // g p.2 - f p.1 = w} ≃ Σ x : F, {y : F // g y = f x + w} where
  toFun p := ⟨p.1.1, ⟨p.1.2, by linear_combination p.2⟩⟩
  invFun s := ⟨(s.1, s.2.1), by linear_combination s.2.2⟩
  left_inv p := by rfl
  right_inv s := by rfl

/-- Section 3, p.15: `M_F(w) = Σ_{x∈F} m_g(f(x) + w)` (the display on p.15,
just above "for every `w ∈ F`"). -/
theorem theorem2_levelSetCount_identity (f g : F → F) (w : F) :
    levelSetCount f g w = ∑ x : F, fibreCount g (f x + w) := by
  unfold levelSetCount fibreCount
  calc
    Fintype.card {p : F × F // g p.2 - f p.1 = w}
        = Fintype.card (Σ x : F, {y : F // g y = f x + w}) :=
          Fintype.card_congr (levelSetEquiv f g w)
    _ = ∑ x : F, Fintype.card {y : F // g y = f x + w} := Fintype.card_sigma

end Counts

section Verification

variable {F : Type*} [Field F]

/-- **Theorem 2, guess-verification uniqueness** (p.16, end of Section 3): if a
candidate `f₀` agrees with `f` up to an additive constant `c` at `D + 1`
distinct points and both have degree at most `D`, then `f = f₀ + C c` as
polynomials.  This is the fact that justifies accepting a guess after testing
`D + 1` oracle points. -/
theorem theorem2_guessVerification_correct
    (f f₀ : F[X]) (D : ℕ) (c : F)
    (hf : f.natDegree ≤ D) (hf₀ : f₀.natDegree ≤ D)
    (x : Fin (D + 1) → F) (hx : Function.Injective x)
    (heval : ∀ i, f.eval (x i) = f₀.eval (x i) + c) :
    f = f₀ + C c := by
  have hsub : (f - f₀).natDegree ≤ D :=
    le_trans (Polynomial.natDegree_sub_le f f₀) (max_le hf hf₀)
  have hpdeg : (f - f₀ - C c).natDegree ≤ D :=
    le_trans (Polynomial.natDegree_sub_le (f - f₀) (C c))
      (max_le hsub (by rw [Polynomial.natDegree_C]; exact Nat.zero_le D))
  have hp : f - f₀ - C c = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (f - f₀ - C c) (ι := Fin (D + 1)) hx ?_ ?_
    · intro i
      rw [Polynomial.eval_sub, Polynomial.eval_sub, Polynomial.eval_C]
      have := heval i
      linear_combination this
    · simpa using hpdeg.trans_lt (Nat.lt_succ_self D)
  rw [← sub_eq_zero]
  linear_combination hp

/-- **Theorem 2, coefficient determination from the verified points.**  If the
degree-`≤ D` hidden polynomial `f_ν` and a candidate `f_{ν'}` agree at `D + 1`
distinct points up to a constant, then their coefficient vectors coincide
(the fixed zero constant term forces the shift to be `0`).  This is the
"determines the unknown coefficients" content of Theorem 2 at the level of the
`D + 1` verified oracle points.

Fixed arXiv:1305.1543v2, Theorem 2, p.2–3; proof p.16. -/
theorem theorem2_verification_determines (D : ℕ)
    {ν ν' : Fin D → F} (c : F)
    (x : Fin (D + 1) → F) (hx : Function.Injective x)
    (h : ∀ i, hiddenPoly D ν (x i) = hiddenPoly D ν' (x i) + c) :
    ν = ν' := by
  have hpoly := theorem2_guessVerification_correct
    (f := hiddenPolyPoly D ν) (f₀ := hiddenPolyPoly D ν') D c
    (natDegree_hiddenPolyPoly_le D ν) (natDegree_hiddenPolyPoly_le D ν')
    x hx (fun i => by simpa only [hiddenPolyPoly_eval] using h i)
  have hz := congrArg (fun p : F[X] => p.eval 0) hpoly
  simp only [Polynomial.eval_add, hiddenPolyPoly_eval, hiddenPoly_zero,
    Polynomial.eval_C, zero_add] at hz
  have hc : c = 0 := hz.symm
  subst hc
  have hp : hiddenPolyPoly D ν = hiddenPolyPoly D ν' := by
    simpa using hpoly
  funext i
  have hcoeff := congrArg (fun p : F[X] => p.coeff (i.val + 1)) hp
  simpa only [coeff_hiddenPolyPoly_self] using hcoeff

end Verification

end Qatlib.Papers.BivarHidPoly13.MainResults
