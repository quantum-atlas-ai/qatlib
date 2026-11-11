/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.GeneralTrotterOrderConsumers
import Qatlib.Concepts.TrotterFormula.SuzukiFourth.SuzukiFourthOrderConsumers
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recursive even-order Suzuki generators

This module constructs the symmetric five-block Suzuki recursion and proves its scale bounds,
exact uncompressed length, mass estimate, and coefficient matching through degree `2 * (k + 1)`.
The recursion is based on [Suzuki1990].

A formal power-series argument tracks the first unmatched coefficient under scaling and
multiplication, cancels it with the Suzuki scale relation, and uses symmetry to obtain the next
even order. The generator recursion also preserves anti-Hermiticity.

## Main statements

* `recursiveSuzukiGenerators`: the symmetric base word and five-block recursive generator lists.
* `recursive_suzuki_length_and_mass`: length `2 * hs.length * 5^k` and mass at most `3^k` times
  the input mass.
* `recursive_suzuki_all_even_order_coefficients`: matching exponential coefficients through
  degree `2 * (k + 1)`.

## References

* [Suzuki, 1990][Suzuki1990]
* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The real Suzuki recursion coefficient `(4 - 4 ^ (1 / (2 * k + 3)))⁻¹`. -/
noncomputable def recursiveSuzukiScale (k : ℕ) : ℝ :=
  (4 - (4 : ℝ) ^ (1 / (2 * k + 3 : ℝ)))⁻¹

/-- The symmetric half-scaled base generator list and its five-block recursion with scale
factors `u, u, 1 - 4u, u, u`. -/
noncomputable def recursiveSuzukiGenerators {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) : ℕ → List (Matrix I I ℂ)
  | 0 => hs.map (fun X => (1/2 : ℝ) • X) ++ hs.reverse.map (fun X => (1/2 : ℝ) • X)
  | k+1 =>
    let xs := recursiveSuzukiGenerators hs k
    let u := recursiveSuzukiScale k
    let a := xs.map (fun X => u • X)
    let b := xs.map (fun X => (1-4*u) • X)
    a ++ a ++ b ++ a ++ a

/-- Every recursive Suzuki scale lies strictly between `1/4` and `1/2`. -/
theorem recursiveSuzukiScale_bounds (k : ℕ) :
    1/4 < recursiveSuzukiScale k ∧ recursiveSuzukiScale k < 1/2 := by
  let c := (4 : ℝ) ^ (1 / (2 * k + 3 : ℝ))
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have he : 1 / (2 * k + 3 : ℝ) ≤ 1/3 := by
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    nlinarith
  have hc_le : c ≤ (4 : ℝ) ^ (1/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have hd0 : 0 ≤ (4 : ℝ) ^ (1/3 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hd3 : ((4 : ℝ) ^ (1/3 : ℝ))^3 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hd2 : (4 : ℝ) ^ (1/3 : ℝ) < 2 := by
    by_contra h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (not_lt.mp h) 3
    rw [hd3] at hp
    norm_num at hp
  have hc2 : c < 2 := hc_le.trans_lt hd2
  have hden : 0 < 4 - c := by linarith
  change 1/4 < (4-c)⁻¹ ∧ (4-c)⁻¹ < 1/2
  rw [← one_div, lt_div_iff₀ hden, div_lt_iff₀ hden]
  constructor <;> linarith

/-- The generator mass of a concatenation is the sum of the two generator masses. -/
private theorem recursiveSuzuki_mass_append {I : Type} [Fintype I] [DecidableEq I]
    (xs ys : List (Matrix I I ℂ)) :
    suzukiMass (xs ++ ys) = suzukiMass xs + suzukiMass ys := by
  simp [suzukiMass, List.map_append, List.sum_append]

/-- Scaling every generator by a real number `a` multiplies the generator mass by `|a|`. -/
private theorem recursiveSuzuki_mass_scale {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (a : ℝ) :
    suzukiMass (xs.map (fun X => a • X)) = |a| * suzukiMass xs := by
  induction xs with
  | nil => simp [suzukiMass]
  | cons X xs ih =>
    simpa [suzukiMass, norm_smul, Real.norm_eq_abs, mul_add] using! ih

/-- At recursion level `k`, the generator list has length `2 * hs.length * 5^k` and mass at most
`3^k * suzukiMass hs`; these estimates support the error analysis of
[ChildsEtAl2021Trotter]. -/
theorem recursive_suzuki_length_and_mass :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (hs : List (Matrix I I ℂ)) (k : ℕ),
      (recursiveSuzukiGenerators hs k).length = 2*hs.length*5^k ∧
      suzukiMass (recursiveSuzukiGenerators hs k) ≤ (3 : ℝ)^k*suzukiMass hs := by
  intro I _ _ hs k
  induction k with
  | zero =>
    constructor
    · simp [recursiveSuzukiGenerators]; omega
    · simp only [recursiveSuzukiGenerators, recursiveSuzuki_mass_append,
        recursiveSuzuki_mass_scale, pow_zero, one_mul]
      have hrev : suzukiMass hs.reverse = suzukiMass hs := by
        simp [suzukiMass, List.map_reverse, List.sum_reverse]
      rw [hrev]
      norm_num
      linarith
  | succ k ih =>
    obtain ⟨huq, huh⟩ := recursiveSuzukiScale_bounds k
    have hu : 0 < recursiveSuzukiScale k := by linarith
    have hv : 1-4*recursiveSuzukiScale k < 0 := by linarith
    have hm : 0 ≤ suzukiMass (recursiveSuzukiGenerators hs k) :=
      general_trotter_mass_nonneg _
    constructor
    · simp only [recursiveSuzukiGenerators, List.length_append, List.length_map,
        ih.1, pow_succ]
      ring
    · simp only [recursiveSuzukiGenerators, recursiveSuzuki_mass_append,
        recursiveSuzuki_mass_scale, abs_of_pos hu, abs_of_neg hv]
      calc
        _ = (8*recursiveSuzukiScale k-1)*suzukiMass (recursiveSuzukiGenerators hs k) := by ring
        _ ≤ 3*suzukiMass (recursiveSuzukiGenerators hs k) :=
          mul_le_mul_of_nonneg_right (by linarith) hm
        _ ≤ 3*((3 : ℝ)^k*suzukiMass hs) := mul_le_mul_of_nonneg_left ih.2 (by norm_num)
        _ = (3 : ℝ)^(k+1)*suzukiMass hs := by rw [pow_succ]; ring

/-- The Suzuki coefficient satisfies the odd-order cancellation identity `4 * u ^ (2 * k + 3) +
(1 - 4 * u) ^ (2 * k + 3) = 0`. -/
theorem recursiveSuzukiScale_order_condition (k : ℕ) :
    4 * recursiveSuzukiScale k ^ (2*k+3) +
      (1-4*recursiveSuzukiScale k) ^ (2*k+3) = 0 := by
  let c := (4 : ℝ) ^ (1 / (2*k+3 : ℝ))
  have hc : c^(2*k+3) = 4 := by
    dsimp [c]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    have he : (1/(2*k+3 : ℝ))*((2*k+3 : ℕ) : ℝ) = 1 := by
      push_cast
      field_simp
    rw [he, Real.rpow_one]
  have hden : 4-c ≠ 0 := by
    have hu := (recursiveSuzukiScale_bounds k).1
    intro h
    have hz : recursiveSuzukiScale k = 0 := by
      change (4-c)⁻¹ = 0
      rw [h, _root_.inv_zero]
    rw [hz] at hu
    norm_num at hu
  have hi : (4-c)*recursiveSuzukiScale k = 1 := mul_inv_cancel₀ hden
  have hv : 1-4*recursiveSuzukiScale k = -c*recursiveSuzukiScale k := by
    nlinarith [hi]
  have ho : Odd (2*k+3) := ⟨k+1, by omega⟩
  rw [hv, mul_pow, ho.neg_pow, hc]
  ring

/-- Every recursive Suzuki generator list is equal to its reversal. -/
theorem recursiveSuzukiGenerators_reverse {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) :
    (recursiveSuzukiGenerators hs k).reverse = recursiveSuzukiGenerators hs k := by
  induction k with
  | zero => simp [recursiveSuzukiGenerators, List.reverse_append, ← List.map_reverse]
  | succ k ih =>
    simp [recursiveSuzukiGenerators, List.reverse_append, ← List.map_reverse, ih, List.append_assoc]

/-- If every input generator is anti-Hermitian, every recursively constructed Suzuki generator
is anti-Hermitian. -/
theorem recursiveSuzukiGenerators_antiHermitian {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) (k : ℕ) (hhs : ∀ X ∈ hs, Xᴴ = -X) :
    ∀ X ∈ recursiveSuzukiGenerators hs k, Xᴴ = -X := by
  have scale : ∀ (xs : List (Matrix I I ℂ)) (a : ℝ),
      (∀ X ∈ xs, Xᴴ = -X) → ∀ Y ∈ xs.map (fun X => a • X), Yᴴ = -Y := by
    intro xs a hxs Y hY
    obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hY
    change star (a • X) = -(a • X)
    simp only [star_smul, star_trivial, Matrix.star_eq_conjTranspose, hxs X hX,
      smul_neg]
  induction k with
  | zero =>
    intro X hX
    rcases List.mem_append.mp hX with hX | hX
    · exact scale hs (1/2) hhs X hX
    · exact scale hs.reverse (1/2) (by simpa using! hhs) X hX
  | succ k ih =>
    intro X hX
    simp only [recursiveSuzukiGenerators, List.mem_append] at hX
    rcases hX with (((hX | hX) | hX) | hX) | hX
    all_goals first
      | exact scale _ (recursiveSuzukiScale k) ih X hX
      | exact scale _ (1-4*recursiveSuzukiScale k) ih X hX

namespace RecursiveSuzukiProof
variable {A : Type} [Ring A] [Algebra ℝ A]

/-- The formal exponential series with coefficient `(a^n / n!) • H^n` at degree `n`. -/
private def e (H : A) (a : ℝ) : PowerSeries A :=
  PowerSeries.mk fun n => (a^n/(n.factorial : ℝ)) • H^n

/-- The factorial-weighted convolution of the powers of `a` and `b` at degree `n` equals `(a +
b)^n / n!`. -/
private theorem scalar_conv (a b : ℝ) (n : ℕ) :
    (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (a ^ kl.1 / (kl.1.factorial : ℝ)) * (b ^ kl.2 / (kl.2.factorial : ℝ))) =
      (a+b)^n/(n.factorial : ℝ) := by
  rw [(Commute.all a b).add_pow' n, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro kl hk
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hk, ← Nat.cast_smul_eq_nsmul ℝ,
      Nat.cast_add_choose]
  rw [smul_eq_mul]
  field_simp [Nat.factorial_ne_zero]

/-- Formal exponential series with the same generator multiply by adding their real scale
parameters. -/
private theorem e_mul (H : A) (a b : ℝ) : e H a * e H b = e H (a+b) := by
  apply PowerSeries.ext
  intro n
  simp only [e, PowerSeries.coeff_mul, PowerSeries.coeff_mk]
  calc
    _ = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((a^kl.1/(kl.1.factorial : ℝ))*(b^kl.2/(kl.2.factorial : ℝ))) • H^n := by
      apply Finset.sum_congr rfl
      intro kl hk
      rw [smul_mul_smul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hk]
    _ = _ := by rw [← Finset.sum_smul, scalar_conv]

/-- The ring homomorphism multiplying the degree-`n` coefficient of a formal power series by
`a^n`. -/
private def rescale (a : ℝ) : PowerSeries A →+* PowerSeries A where
  toFun f := PowerSeries.mk fun n => a^n • PowerSeries.coeff n f
  map_zero' := by apply PowerSeries.ext; intro n; simp
  map_one' := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with hn
    · subst n; simp
    · simp
  map_add' f g := by apply PowerSeries.ext; intro n; simp [smul_add]
  map_mul' f g := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro kl hk
    rw [smul_mul_smul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hk]

/-- The degree-`n` coefficient of a rescaled series is `a^n` times its original coefficient. -/
private theorem coeff_rescale (f : PowerSeries A) (a : ℝ) (n : ℕ) :
    PowerSeries.coeff n (rescale a f) = a^n • PowerSeries.coeff n f := by
  simp [rescale]

omit [Algebra ℝ A] in

/-- For two series with constant coefficient one, the degree-`n + 1` product coefficient splits
into the interior convolution and the two endpoint coefficients. -/
private theorem coeff_prod_top (f g : PowerSeries A) (n : ℕ)
    (hf : PowerSeries.coeff 0 f = 1) (hg : PowerSeries.coeff 0 g = 1) :
    PowerSeries.coeff (n+1) (f*g) =
      (∑ j ∈ Finset.range n,
        PowerSeries.coeff (j+1) f * PowerSeries.coeff (n+1-(j+1)) g) +
      PowerSeries.coeff (n+1) g + PowerSeries.coeff (n+1) f := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_succ']
  simp [hf, hg]

omit [Algebra ℝ A] in

/-- For pairs of series with constant coefficient one and matching coefficients through degree
`n`, the degree-`n + 1` product defect is the sum of the two individual defects. -/
private theorem product_defect (f g F G : PowerSeries A) (n : ℕ)
    (hf0 : PowerSeries.coeff 0 f = 1) (hg0 : PowerSeries.coeff 0 g = 1)
    (hF0 : PowerSeries.coeff 0 F = 1) (hG0 : PowerSeries.coeff 0 G = 1)
    (hf : ∀ j ≤ n, PowerSeries.coeff j f = PowerSeries.coeff j F)
    (hg : ∀ j ≤ n, PowerSeries.coeff j g = PowerSeries.coeff j G) :
    PowerSeries.coeff (n+1) (f*g) - PowerSeries.coeff (n+1) (F*G) =
      (PowerSeries.coeff (n+1) f-PowerSeries.coeff (n+1) F) +
      (PowerSeries.coeff (n+1) g-PowerSeries.coeff (n+1) G) := by
  rw [coeff_prod_top f g n hf0 hg0, coeff_prod_top F G n hF0 hG0]
  have hs : (∑ j ∈ Finset.range n,
      PowerSeries.coeff (j+1) f * PowerSeries.coeff (n+1-(j+1)) g) =
      ∑ j ∈ Finset.range n,
        PowerSeries.coeff (j+1) F * PowerSeries.coeff (n+1-(j+1)) G := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    rw [hf (j+1) (by omega), hg (n+1-(j+1)) (by omega)]
  rw [hs]
  abel

/-- The constant coefficient of a formal exponential series is one. -/
@[simp] private theorem e_coeff_zero (H : A) (a : ℝ) : PowerSeries.coeff 0 (e H a) = 1 := by
  simp [e]

/-- The formal exponential series with scale parameter zero is the unit series. -/
@[simp] private theorem e_zero (H : A) : e H 0 = 1 := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [e, PowerSeries.coeff_one]

/-- Rescaling a formal exponential by `a` multiplies its scale parameter by `a`. -/
private theorem rescale_e (H : A) (a b : ℝ) : rescale a (e H b) = e H (a*b) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_rescale, e, PowerSeries.coeff_mk, smul_smul, mul_pow]
  congr 1
  ring

/-- Series matching exponential series with the same generator through degree `p` have a product
matching the exponential at the sum of their scale parameters through that degree. -/
private theorem matches_mul (f g : PowerSeries A) (H : A) (p : ℕ) (a b : ℝ)
    (hf : ∀ n ≤ p, PowerSeries.coeff n f = PowerSeries.coeff n (e H a))
    (hg : ∀ n ≤ p, PowerSeries.coeff n g = PowerSeries.coeff n (e H b)) :
    ∀ n ≤ p, PowerSeries.coeff n (f*g) = PowerSeries.coeff n (e H (a+b)) := by
  intro n hn
  rw [← e_mul, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro kl hk
  have hkl := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
  rw [hf kl.1 (by omega), hg kl.2 (by omega)]

/-- When two exponential-matching series have degree-`p + 1` defects `d • D` and `t • D`, their
product retains the lower matches and has defect `(d + t) • D`. -/
private theorem jet_mul (f g : PowerSeries A) (H D : A) (p : ℕ) (a b d t : ℝ)
    (hf : ∀ n ≤ p, PowerSeries.coeff n f = PowerSeries.coeff n (e H a))
    (hg : ∀ n ≤ p, PowerSeries.coeff n g = PowerSeries.coeff n (e H b))
    (hfd : PowerSeries.coeff (p+1) f-PowerSeries.coeff (p+1) (e H a) = d • D)
    (hgd : PowerSeries.coeff (p+1) g-PowerSeries.coeff (p+1) (e H b) = t • D) :
    (∀ n ≤ p, PowerSeries.coeff n (f*g) = PowerSeries.coeff n (e H (a+b))) ∧
    PowerSeries.coeff (p+1) (f*g)-PowerSeries.coeff (p+1) (e H (a+b)) = (d+t) • D := by
  refine ⟨matches_mul f g H p a b hf hg, ?_⟩
  have hf0 : PowerSeries.coeff 0 f = 1 := (hf 0 (by omega)).trans (e_coeff_zero H a)
  have hg0 : PowerSeries.coeff 0 g = 1 := (hg 0 (by omega)).trans (e_coeff_zero H b)
  have hd := product_defect f g (e H a) (e H b) p hf0 hg0
    (e_coeff_zero H a) (e_coeff_zero H b) hf hg
  rw [e_mul, hfd, hgd, ← add_smul] at hd
  exact hd

/-- Two series with constant coefficient one, the stated reversal identities, and matching
coefficients through degree `p` also match at degree `p + 1` when that degree is even. -/
private theorem symmetry_even_coefficient (f F : PowerSeries A) (p : ℕ)
    (hp : Even (p+1)) (hf0 : PowerSeries.coeff 0 f = 1)
    (hF0 : PowerSeries.coeff 0 F = 1)
    (hfi : rescale (-1) f * f = 1) (hFi : rescale (-1) F * F = 1)
    (hf : ∀ n ≤ p, PowerSeries.coeff n f = PowerSeries.coeff n F) :
    PowerSeries.coeff (p+1) f = PowerSeries.coeff (p+1) F := by
  have hr0 : PowerSeries.coeff 0 (rescale (-1) f) = 1 := by
    rw [coeff_rescale, pow_zero, one_smul, hf0]
  have hR0 : PowerSeries.coeff 0 (rescale (-1) F) = 1 := by
    rw [coeff_rescale, pow_zero, one_smul, hF0]
  have hrf : ∀ n ≤ p, PowerSeries.coeff n (rescale (-1) f) =
      PowerSeries.coeff n (rescale (-1) F) := by
    intro n hn
    rw [coeff_rescale, coeff_rescale, hf n hn]
  have hd := product_defect (rescale (-1) f) f (rescale (-1) F) F p
    hr0 hf0 hR0 hF0 hrf hf
  rw [hfi, hFi, sub_self, coeff_rescale, coeff_rescale, hp.neg_one_pow, one_smul] at hd
  have htwo : (2 : ℝ) • (PowerSeries.coeff (p+1) f-PowerSeries.coeff (p+1) F) = 0 := by
    rw [two_smul]
    simpa only [one_smul] using! hd.symm
  exact sub_eq_zero.mp ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
/-- The list-order product of the formal exponential series of the generators at unit scale. -/
private def word (xs : List A) : PowerSeries A := (xs.map (fun X => e X 1)).prod

/-- The formal exponential word of the empty generator list is one. -/
@[simp] private theorem word_nil : word ([] : List A) = 1 := by simp [word]

/-- The formal word of `X :: xs` is the formal exponential of `X` multiplied by the word of
`xs`. -/
@[simp] private theorem word_cons (X : A) (xs : List A) : word (X::xs) = e X 1 * word xs := by
  simp [word]

/-- The formal word of a concatenation is the product of the formal words of its two parts. -/
@[simp] private theorem word_append (xs ys : List A) : word (xs++ys) = word xs * word ys := by
  simp [word, List.prod_append]

/-- The formal exponential of a scaled generator at unit parameter equals the corresponding
rescaling of its unit-parameter exponential. -/
private theorem e_scale (H : A) (a : ℝ) : e (a • H) 1 = rescale a (e H 1) := by
  apply PowerSeries.ext
  intro n
  simp only [e, coeff_rescale, PowerSeries.coeff_mk, smul_pow, smul_smul, one_pow]
  congr 1
  ring

/-- Scaling every generator in a formal word equals rescaling the resulting power series. -/
private theorem word_scale (xs : List A) (a : ℝ) :
    word (xs.map (fun X => a • X)) = rescale a (word xs) := by
  induction xs with
  | nil => simp
  | cons X xs ih => simp [ih, e_scale, map_mul]

/-- The formal exponential of `-H` is a left inverse of the formal exponential of `H` at unit
scale. -/
private theorem e_neg_mul (H : A) : e (-H) 1 * e H 1 = 1 := by
  rw [← neg_one_smul ℝ H, e_scale, rescale_e, neg_one_mul, e_mul]
  simp

/-- The formal word of the reversed, negated generator list is a left inverse of the original
formal word. -/
private theorem word_inverse (xs : List A) :
    word (xs.reverse.map (fun X => -X)) * word xs = 1 := by
  induction xs with
  | nil => simp
  | cons X xs ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      word_append, word_cons, word_nil, mul_one]
    calc
      _ = word (xs.reverse.map (fun Y => -Y)) * (e (-X) 1 * e X 1) * word xs := by
        noncomm_ring
      _ = 1 := by rw [e_neg_mul]; simpa using! ih

/-- For a generator list equal to its reversal, rescaling its formal word by `-1` gives a left
inverse of the word. -/
private theorem word_symmetry (xs : List A) (hs : xs.reverse = xs) :
    rescale (-1) (word xs) * word xs = 1 := by
  have h := word_inverse xs
  rw [hs] at h
  have hm : xs.map (fun X => -X) = xs.map (fun X => (-1 : ℝ) • X) := by
    apply List.map_congr_left
    intro X _
    exact (neg_one_smul ℝ X).symm
  rw [hm, word_scale] at h
  exact h

/-- Rescaling a unit-parameter formal exponential by `-1` gives its left inverse. -/
private theorem e_symmetry (H : A) : rescale (-1) (e H 1) * e H 1 = 1 := by
  rw [rescale_e, neg_one_mul, e_mul]
  simp

/-- Rescaling a series that matches the exponential through degree `p` preserves the scaled
matches and multiplies the degree-`p + 1` defect by `a ^ (p + 1)`. -/
private theorem scale_jet (f : PowerSeries A) (H : A) (p : ℕ) (a : ℝ)
    (hf : ∀ n ≤ p, PowerSeries.coeff n f = PowerSeries.coeff n (e H 1)) :
    (∀ n ≤ p, PowerSeries.coeff n (rescale a f) = PowerSeries.coeff n (e H a)) ∧
    PowerSeries.coeff (p+1) (rescale a f) - PowerSeries.coeff (p+1) (e H a) =
      a^(p+1) • (PowerSeries.coeff (p+1) f-PowerSeries.coeff (p+1) (e H 1)) := by
  have ha : e H a = rescale a (e H 1) := by rw [rescale_e, mul_one]
  rw [ha]
  constructor
  · intro n hn
    rw [coeff_rescale, coeff_rescale, hf n hn]
  · rw [coeff_rescale, coeff_rescale, smul_sub]

/-- If `4u + v = 1` and `4u^(p+1) + v^(p+1) = 0`, the five-block rescaled product of a series
matching through degree `p` matches the unit exponential through degree `p + 1`. -/
private theorem five_jet (f : PowerSeries A) (H : A) (p : ℕ) (u v : ℝ)
    (hf : ∀ n ≤ p, PowerSeries.coeff n f = PowerSeries.coeff n (e H 1))
    (huv : 4*u+v=1) (hc : 4*u^(p+1)+v^(p+1)=0) :
    ∀ n ≤ p+1,
      PowerSeries.coeff n (rescale u f * rescale u f * rescale v f * rescale u f * rescale u f) =
      PowerSeries.coeff n (e H 1) := by
  let D := PowerSeries.coeff (p+1) f - PowerSeries.coeff (p+1) (e H 1)
  obtain ⟨hu, hud⟩ := scale_jet f H p u hf
  obtain ⟨hv, hvd⟩ := scale_jet f H p v hf
  obtain ⟨h2, h2d⟩ := jet_mul _ _ H D p u u (u^(p+1)) (u^(p+1)) hu hu hud hud
  obtain ⟨h3, h3d⟩ := jet_mul _ _ H D p (u+u) v (u^(p+1)+u^(p+1)) (v^(p+1)) h2 hv h2d hvd
  obtain ⟨h4, h4d⟩ := jet_mul _ _ H D p (u+u+v) u
    (u^(p+1)+u^(p+1)+v^(p+1)) (u^(p+1)) h3 hu h3d hud
  obtain ⟨h5, h5d⟩ := jet_mul _ _ H D p (u+u+v+u) u
    (u^(p+1)+u^(p+1)+v^(p+1)+u^(p+1)) (u^(p+1)) h4 hu h4d hud
  have he : u+u+v+u+u = 1 := by linarith
  have hd : u^(p+1)+u^(p+1)+v^(p+1)+u^(p+1)+u^(p+1) = 0 := by linarith
  rw [he] at h5 h5d
  rw [hd, zero_smul] at h5d
  intro n hn
  rcases Nat.eq_or_lt_of_le hn with rfl | hn
  · exact sub_eq_zero.mp h5d
  · exact h5 n (by omega)

end RecursiveSuzukiProof

open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki.RecursiveSuzukiProof

/-- The degree-`n` coefficient of the formal exponential word is `suzukiSeries xs n`. -/
private theorem recursiveSuzuki_coeff_word {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (n : ℕ) :
    PowerSeries.coeff n (word xs) = suzukiSeries xs n := by
  induction xs generalizing n with
  | nil => cases n <;> simp [word_nil, suzukiSeries, PowerSeries.coeff_one]
  | cons X xs ih =>
    simp only [word_cons, PowerSeries.coeff_mul, e, PowerSeries.coeff_mk,
      one_pow, one_div, suzukiSeries, ih]

/-- The degree-one Suzuki series coefficient is the sum of the generators. -/
private theorem recursiveSuzuki_first {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) : suzukiSeries xs 1 = xs.sum := by
  induction xs with
  | nil => rfl
  | cons X xs ih => simp [ih, List.sum_cons, add_comm]

/-- Summing a list of generators scaled by `a` gives `a` times the original sum. -/
private theorem recursiveSuzuki_sum_scale {I : Type} [Fintype I] [DecidableEq I]
    (xs : List (Matrix I I ℂ)) (a : ℝ) :
    (xs.map (fun X => a • X)).sum = a • xs.sum := by
  induction xs with
  | nil => simp
  | cons X xs ih => simp [ih, smul_add]

/-- The level-zero symmetric half-scaled generator list has the same sum as the original list. -/
private theorem recursiveSuzuki_base_sum {I : Type} [Fintype I] [DecidableEq I]
    (hs : List (Matrix I I ℂ)) : (recursiveSuzukiGenerators hs 0).sum = hs.sum := by
  simp only [recursiveSuzukiGenerators, List.sum_append, recursiveSuzuki_sum_scale,
    List.sum_reverse, ← add_smul]
  norm_num

/-- The level-`k` Suzuki generator list matches the exponential of `hs.sum` through every degree
`n ≤ 2 * (k + 1)`, for the recursion of [Suzuki1990] used in the framework of
[ChildsEtAl2021Trotter]. -/
theorem recursive_suzuki_all_even_order_coefficients :
    ∀ (I : Type) [Fintype I] [DecidableEq I]
      (hs : List (Matrix I I ℂ)) (k n : ℕ), n ≤ 2*(k+1) →
      suzukiSeries (recursiveSuzukiGenerators hs k) n =
        ((n.factorial : ℝ)⁻¹) • hs.sum^n := by
  intro I _ _ hs k
  suffices h : ∀ n ≤ 2*(k+1),
      PowerSeries.coeff n (word (recursiveSuzukiGenerators hs k)) =
      PowerSeries.coeff n (e hs.sum 1) by
    intro n hn
    simpa only [recursiveSuzuki_coeff_word, e, PowerSeries.coeff_mk, one_pow,
      one_div] using! h n hn
  induction k with
  | zero =>
    have hlow : ∀ n ≤ 1,
        PowerSeries.coeff n (word (recursiveSuzukiGenerators hs 0)) =
        PowerSeries.coeff n (e hs.sum 1) := by
      intro n hn
      interval_cases n
      · simp [recursiveSuzuki_coeff_word]
      · simp [recursiveSuzuki_coeff_word, recursiveSuzuki_first,
          recursiveSuzuki_base_sum, e]
    have htwo := symmetry_even_coefficient
      (word (recursiveSuzukiGenerators hs 0)) (e hs.sum 1) 1 (by decide)
      (by simp [recursiveSuzuki_coeff_word]) (e_coeff_zero _ _)
      (word_symmetry _ (recursiveSuzukiGenerators_reverse hs 0)) (e_symmetry _) hlow
    intro n hn
    by_cases hn1 : n ≤ 1
    · exact hlow n hn1
    · have hn2 : n = 2 := by omega
      subst n
      exact htwo
  | succ k ih =>
    let p := 2*(k+1)
    let u := recursiveSuzukiScale k
    let v := 1-4*u
    have hc : 4*u^(p+1)+v^(p+1) = 0 := by
      have he : p+1 = 2*k+3 := by dsimp [p]; omega
      rw [he]
      exact recursiveSuzukiScale_order_condition k
    have hup : 4*u+v=1 := by dsimp [v]; ring
    have hlow := five_jet (word (recursiveSuzukiGenerators hs k)) hs.sum p u v ih hup hc
    have hw : word (recursiveSuzukiGenerators hs (k+1)) =
        rescale u (word (recursiveSuzukiGenerators hs k)) *
        rescale u (word (recursiveSuzukiGenerators hs k)) *
        rescale v (word (recursiveSuzukiGenerators hs k)) *
        rescale u (word (recursiveSuzukiGenerators hs k)) *
        rescale u (word (recursiveSuzukiGenerators hs k)) := by
      simp only [recursiveSuzukiGenerators, word_append, word_scale, u, v]
    rw [← hw] at hlow
    have hnext := symmetry_even_coefficient
      (word (recursiveSuzukiGenerators hs (k+1))) (e hs.sum 1) (p+1)
      (by dsimp [p]; exact ⟨k+2, by omega⟩)
      (by simp [recursiveSuzuki_coeff_word]) (e_coeff_zero _ _)
      (word_symmetry _ (recursiveSuzukiGenerators_reverse hs (k+1)))
      (e_symmetry _) hlow
    intro n hn
    by_cases hnp : n ≤ p+1
    · exact hlow n hnp
    · have he : n = (p+1)+1 := by dsimp [p] at *; omega
      subst n
      exact hnext

end Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
