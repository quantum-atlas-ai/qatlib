/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SoftDecoder24.MainResults.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Characters of `(F_q)^n` — Proposition 2

Chailloux–Tillich, *Quantum advantage from soft decoders*, fixed arXiv:2411.12553v2
(9 March 2026), **Proposition 2, p.10**:

1. (Group homomorphism) `χ_y(x + x') = χ_y(x) · χ_y(x')`;
2. (Symmetry) `χ_y(x) = χ_x(y)`;
3. (Orthogonality) `Σ_y χ_y(x) \overline{χ_y(x')} = qⁿ δ_{x,x'}`.

The paper works over the finite field `F_q`; the character identities only use the additive
group of `ZMod q` and the multiplicativity of the character, so they are stated for an
arbitrary modulus `q ≠ 0` (a harmless generalisation; for prime `q` this is exactly `F_q`).
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Finset

namespace Qatlib.Papers.SoftDecoder24.MainResults.Characters

open Qatlib.Papers.SoftDecoder24.MainResults.Basic

variable {q : ℕ} [NeZero q]

/-- The standard additive character takes unit-circle values, so its conjugate is its
inverse: `star (stdAddChar t) = stdAddChar (-t)` (used for the orthogonality relation of
Proposition 2(3), p.10). -/
lemma stdAddChar_star (t : ZMod q) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply]
  have h : ZMod.toCircle (-t) = (ZMod.toCircle t)⁻¹ := AddChar.map_neg_eq_inv _ _
  rw [h, Complex.star_def, ← Circle.coe_inv_eq_conj]

/-- `conj (χ_y(x)) = χ_y(-x)`. -/
lemma char_conj (y x : ZMod q) : star (char y x) = char y (-x) := by
  unfold char
  rw [stdAddChar_star]
  congr 1
  ring

/-- Proposition 2(1), p.10, one-coordinate form: `χ_y(x + x') = χ_y(x) χ_y(x')`. -/
lemma char_add (y x x' : ZMod q) : char y (x + x') = char y x * char y x' := by
  unfold char
  rw [add_mul, AddChar.map_add_eq_mul]

/-- Proposition 2(2), p.10, one-coordinate form: `χ_y(x) = χ_x(y)`. -/
lemma char_symm (x y : ZMod q) : char y x = char x y := by
  unfold char
  rw [mul_comm]

/-- Character/anti-character product: `χ_y(x) \overline{χ_y(x')} = χ_y(x - x')`. -/
lemma char_mul_star (y x x' : ZMod q) :
    char y x * star (char y x') = char y (x - x') := by
  rw [char_conj, ← char_add, sub_eq_add_neg]

/-- The character sum `Σ_{y ∈ Z_q} ω^{t y}` vanishes unless `t = 0`, where it is `q`
(this is the one-coordinate orthogonality underlying Proposition 2(3), p.10). -/
lemma sum_stdAddChar_mul (t : ZMod q) :
    ∑ y : ZMod q, ZMod.stdAddChar (t * y) = if t = 0 then (q : ℂ) else 0 := by
  by_cases h : t = 0
  · subst h
    rw [if_pos rfl]
    have h0 : (∑ y : ZMod q, ZMod.stdAddChar ((0 : ZMod q) * y))
        = ∑ _y : ZMod q, (1 : ℂ) := by
      exact Finset.sum_congr rfl (fun y _ => by simp)
    rw [h0]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · rw [if_neg h]
    have hne : (AddChar.mulShift ZMod.stdAddChar t : AddChar (ZMod q) ℂ) ≠ 1 :=
      ZMod.isPrimitive_stdAddChar q h
    have heq : (fun y : ZMod q => ZMod.stdAddChar (t * y))
        = fun y => AddChar.mulShift ZMod.stdAddChar t y := rfl
    rw [heq]
    exact AddChar.sum_eq_zero_of_ne_one hne

/-- Proposition 2(3), p.10, one-coordinate form:
`Σ_y χ_y(x) \overline{χ_y(x')} = q δ_{x,x'}`. -/
lemma sum_char_mul_star (x x' : ZMod q) :
    ∑ y : ZMod q, char y x * star (char y x') = if x = x' then (q : ℂ) else 0 := by
  simp only [char_mul_star]
  have heq : (fun y : ZMod q => char y (x - x'))
      = fun y => ZMod.stdAddChar ((x - x') * y) := rfl
  rw [heq, sum_stdAddChar_mul]
  by_cases hx : x = x'
  · subst hx
    simp
  · have hsub : x - x' ≠ 0 := sub_ne_zero.mpr hx
    rw [if_neg hx, if_neg hsub]

/-- Vector form of the character/anti-character product. -/
lemma vchar_mul_star {n : ℕ} (y x x' : Fin n → ZMod q) :
    vchar y x * star (vchar y x') = ∏ i, char (y i) (x i - x' i) := by
  unfold vchar
  rw [star_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => char_mul_star (y i) (x i) (x' i))

/-- Proposition 2(3), p.10, vector form:
`Σ_y χ_y(x) \overline{χ_y(x')} = qⁿ δ_{x,x'}`. -/
lemma sum_vchar_mul_star {n : ℕ} (x x' : Fin n → ZMod q) :
    ∑ y : Fin n → ZMod q, vchar y x * star (vchar y x')
      = if x = x' then ((q : ℂ) ^ n) else 0 := by
  simp only [vchar_mul_star]
  rw [← Fintype.prod_sum (fun i (a : ZMod q) => char a (x i - x' i))]
  have hfac : ∀ i, ∑ a : ZMod q, char a (x i - x' i)
      = if x i = x' i then (q : ℂ) else 0 := by
    intro i
    have heq : (fun a : ZMod q => char a (x i - x' i))
        = fun a => ZMod.stdAddChar ((x i - x' i) * a) := rfl
    rw [heq, sum_stdAddChar_mul]
    by_cases h : x i = x' i
    · rw [h]
      simp
    · have hsub : x i - x' i ≠ 0 := sub_ne_zero.mpr h
      rw [if_neg h, if_neg hsub]
  simp only [hfac]
  by_cases hx : x = x'
  · subst hx
    rw [if_pos rfl]
    simp [Finset.prod_const]
  · rw [if_neg hx]
    have hex : ∃ i, x i ≠ x' i := by
      by_contra hc
      push_neg at hc
      exact hx (funext hc)
    obtain ⟨i, hi⟩ := hex
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]

/-- **Proposition 2(1), p.10** (group homomorphism for `(F_q)^n`):
`χ_y(x + x') = χ_y(x) · χ_y(x')`. -/
theorem source_proposition2_hom {n : ℕ} (y x x' : Fin n → ZMod q) :
    vchar y (x + x') = vchar y x * vchar y x' := by
  unfold vchar
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun i _ => char_add (y i) (x i) (x' i))

/-- **Proposition 2(2), p.10** (symmetry for `(F_q)^n`): `χ_y(x) = χ_x(y)`. -/
theorem source_proposition2_symm {n : ℕ} (x y : Fin n → ZMod q) :
    vchar y x = vchar x y := by
  unfold vchar
  exact Finset.prod_congr rfl (fun i _ => char_symm (x i) (y i))

/-- **Proposition 2(3), p.10** (orthogonality of characters for `(F_q)^n`):
`Σ_y χ_y(x) \overline{χ_y(x')} = qⁿ δ_{x,x'}`. -/
theorem source_proposition2_orthogonal {n : ℕ} (x x' : Fin n → ZMod q) :
    ∑ y : Fin n → ZMod q, vchar y x * star (vchar y x')
      = if x = x' then ((q : ℂ) ^ n) else 0 :=
  sum_vchar_mul_star x x'

end Qatlib.Papers.SoftDecoder24.MainResults.Characters
