/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Foundations.DyadicHorner.HornerError.DyadicHornerDefs

/-!
# Error and operation bounds for dyadic Horner evaluation

This module bounds the rounding error and operation counts of the integer evaluator `run`
against `exactValue`. For inputs satisfying `|x| ≤ 2^b`, `g1` gives an error of at most one
dyadic unit per coefficient, and `g2` adds coefficient quantization error.

The theorem `g3` bounds both the final integer output and the recorded peak magnitude when the
coefficients have a common magnitude bound. These are finite-precision arithmetic estimates
within the computational setting of [KitaevShenVyalyi2002].

## Main statements

* `g1`: For `|x| ≤ 2^b`, all three operation counts equal the coefficient count and the
  normalized rounding error is at most `cs.length / 2^b`.
* `g2`: With normalized input of absolute value at most one and coefficient errors bounded by
  nonnegative `δ`, the total normalized evaluation error is at most `cs.length * (2⁻ᵇ + δ)`.
* `g3`: If `|x| ≤ 2^b` and each coefficient has absolute value at most `C`, the output magnitude
  is at most `cs.length * C` and the recorded peak is at most `2^b * cs.length * C`.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

namespace Qatlib.Foundations.DyadicHorner.HornerError
open scoped BigOperators
set_option autoImplicit false

/-- Integer division by a positive denominator differs from the real quotient by at most one. -/
private theorem floor_error (n d : ℤ) (hd : 0 < d) :
    |((n / d : ℤ) : ℝ) - (n : ℝ) / (d : ℝ)| ≤ 1 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hr0 : (0 : ℝ) ≤ (n % d : ℤ) := by
    exact_mod_cast Int.emod_nonneg n (ne_of_gt hd)
  have hr1 : ((n % d : ℤ) : ℝ) ≤ d := by
    exact_mod_cast (Int.emod_lt_of_pos n hd).le
  have he : ((n % d : ℤ) : ℝ) + ((n / d : ℤ) : ℝ) * (d : ℝ) = n := by
    exact_mod_cast Int.emod_add_ediv_mul n d
  have hv : (n : ℝ) / (d : ℝ) = ((n / d : ℤ) : ℝ) + ((n % d : ℤ) : ℝ) / d := by
    apply (div_eq_iff (ne_of_gt hdR)).mpr
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hdR)]
    linarith only [he]
  have h0 : (0 : ℝ) ≤ ((n % d : ℤ) : ℝ) / d := div_nonneg hr0 hdR.le
  have h1 : ((n % d : ℤ) : ℝ) / d ≤ 1 := (div_le_one hdR).mpr hr1
  rw [hv]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- If `|x| ≤ 2^b`, the normalized input `x / 2^b` has absolute value at most one. -/
private theorem input_contraction (b : ℕ) (x : ℤ) (hx : |x| ≤ (2 ^ b : ℤ)) :
    |(x : ℝ) / (2 ^ b : ℝ)| ≤ 1 := by
  have hxR : |(x : ℝ)| ≤ (2 ^ b : ℝ) := by exact_mod_cast hx
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ b)]
  exact (div_le_one (by positivity)).mpr hxR

/-- One dyadic multiplication and integer division incurs normalized error at most `2⁻ᵇ`. -/
private theorem round_step_error (b : ℕ) (x v : ℤ) :
    |(((x * v / (2 ^ b : ℤ) : ℤ) : ℝ) / (2 ^ b : ℝ)) -
      (x : ℝ) / (2 ^ b : ℝ) * ((v : ℝ) / (2 ^ b : ℝ))| ≤
      1 / (2 ^ b : ℝ) := by
  have h := floor_error (x * v) (2 ^ b) (by positivity)
  have he : (((x * v / (2 ^ b : ℤ) : ℤ) : ℝ) / (2 ^ b : ℝ)) -
      (x : ℝ) / (2 ^ b : ℝ) * ((v : ℝ) / (2 ^ b : ℝ)) =
      (((x * v / (2 ^ b : ℤ) : ℤ) : ℝ) - ((x * v : ℤ) : ℝ) / ((2 ^ b : ℤ) : ℝ)) /
        (2 ^ b : ℝ) := by push_cast; ring
  rw [he, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ b)]
  exact div_le_div_of_nonneg_right (by simpa only [Int.cast_pow, Int.cast_ofNat] using h)
    (by positivity)

/-- The Horner evaluator performs one addition, multiplication, and division for each
coefficient. -/
private theorem counters (b : ℕ) (x : ℤ) (cs : List ℤ) :
    (run b x cs).additions = cs.length ∧
    (run b x cs).multiplications = cs.length ∧
    (run b x cs).divisions = cs.length := by
  induction cs with
  | nil => simp [run]
  | cons c cs ih => simp [run, ih.1, ih.2.1, ih.2.2]

/-- For `|x| ≤ 2^b`, the normalized output of `run` differs from `exactValue` by at most
`cs.length / 2^b`. -/
private theorem rounding_error (b : ℕ) (x : ℤ) (cs : List ℤ)
    (hx : |x| ≤ (2 ^ b : ℤ)) :
    |((run b x cs).value : ℝ) / (2 ^ b : ℝ) - exactValue b x cs| ≤
      (cs.length : ℝ) / (2 ^ b : ℝ) := by
  induction cs with
  | nil => simp [run, exactValue, realValue]
  | cons c cs ih =>
    have hs := round_step_error b x (run b x cs).value
    have hxR := input_contraction b x hx
    have ht : |(x : ℝ) / (2 ^ b : ℝ) *
        (((run b x cs).value : ℝ) / (2 ^ b : ℝ) - exactValue b x cs)| ≤
        (cs.length : ℝ) / (2 ^ b : ℝ) := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hxR (abs_nonneg _)).trans (by simpa using ih)
    have he : ((run b x (c :: cs)).value : ℝ) / (2 ^ b : ℝ) -
        exactValue b x (c :: cs) =
        (((x * (run b x cs).value / (2 ^ b : ℤ) : ℤ) : ℝ) / (2 ^ b : ℝ) -
          (x : ℝ) / (2 ^ b : ℝ) * (((run b x cs).value : ℝ) / (2 ^ b : ℝ))) +
        (x : ℝ) / (2 ^ b : ℝ) *
          (((run b x cs).value : ℝ) / (2 ^ b : ℝ) - exactValue b x cs) := by
      simp [run, exactValue, realValue]
      ring
    rw [he]
    calc
      _ ≤ _ := abs_add_le _ _
      _ ≤ 1 / (2 ^ b : ℝ) + (cs.length : ℝ) / (2 ^ b : ℝ) := add_le_add hs ht
      _ = ((c :: cs).length : ℝ) / (2 ^ b : ℝ) := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

/-- For `|x| ≤ 2^b`, all three operation counts equal the coefficient count and the normalized
rounding error is at most `cs.length / 2^b`. -/
theorem g1 :
    ∀ (b : ℕ) (x : ℤ) (cs : List ℤ), |x| ≤ (2^b:ℤ) →
      (run b x cs).additions = cs.length ∧
      (run b x cs).multiplications = cs.length ∧
      (run b x cs).divisions = cs.length ∧
      |((run b x cs).value:ℝ)/(2^b:ℝ) - exactValue b x cs| ≤
        (cs.length:ℝ)/(2^b:ℝ) := by
  intro b x cs hx
  exact ⟨(counters b x cs).1, (counters b x cs).2.1,
    (counters b x cs).2.2, rounding_error b x cs hx⟩

/-- If the normalized input has absolute value at most one and corresponding coefficients differ
by at most nonnegative `δ`, their exact Horner values differ by at most `cs.length * δ`. -/
private theorem coefficient_error (b : ℕ) (x : ℤ) (δ : ℝ)
    (hx : |x| ≤ (2^b:ℤ)) (_hδ : 0 ≤ δ) (cs : List ℤ) (a : List ℝ)
    (hlen : cs.length = a.length)
    (ha : ∀ i : Fin cs.length,
      |((cs[i.val]'i.isLt):ℝ)/(2^b:ℝ) - (a[i.val]'(by omega))| ≤ δ) :
    |exactValue b x cs - realValue a ((x:ℝ)/(2^b:ℝ))| ≤ (cs.length:ℝ)*δ := by
  induction cs generalizing a with
  | nil =>
    cases a with
    | nil => simp [exactValue, realValue]
    | cons d a => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons c cs ih =>
    cases a with
    | nil => simp at hlen
    | cons d a =>
      have hlen' : cs.length = a.length := by simpa using hlen
      have hh : |(c:ℝ)/(2^b:ℝ) - d| ≤ δ := by
        simpa using ha ⟨0, by simp⟩
      have ha' : ∀ i : Fin cs.length,
          |((cs[i.val]'i.isLt):ℝ)/(2^b:ℝ) - (a[i.val]'(by omega))| ≤ δ := by
        intro i
        simpa using ha ⟨i.val+1, by simp⟩
      have ht := ih a hlen' ha'
      have hm : |(x:ℝ)/(2^b:ℝ) * (exactValue b x cs - realValue a ((x:ℝ)/(2^b:ℝ)))| ≤
          (cs.length:ℝ)*δ := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right (input_contraction b x hx) (abs_nonneg _)).trans
          (by simpa using ht)
      have he : exactValue b x (c::cs) - realValue (d::a) ((x:ℝ)/(2^b:ℝ)) =
          ((c:ℝ)/(2^b:ℝ) - d) +
          (x:ℝ)/(2^b:ℝ)*(exactValue b x cs - realValue a ((x:ℝ)/(2^b:ℝ))) := by
        simp [exactValue, realValue]
        ring
      rw [he]
      calc
        _ ≤ _ := abs_add_le _ _
        _ ≤ δ + (cs.length:ℝ)*δ := add_le_add hh hm
        _ = ((c::cs).length:ℝ)*δ := by simp; ring

/-- With normalized input of absolute value at most one and coefficient errors bounded by
nonnegative `δ`, the total normalized evaluation error is at most `cs.length * (2⁻ᵇ + δ)`. -/
theorem g2 :
    ∀ (b : ℕ) (x : ℤ) (cs : List ℤ) (a : List ℝ) (δ : ℝ),
      |x| ≤ (2^b:ℤ) → 0 ≤ δ → ∀ (hlen : cs.length = a.length),
      (∀ i : Fin cs.length,
        |((cs[i.val]'i.isLt):ℝ)/(2^b:ℝ) - (a[i.val]'(by omega))| ≤ δ) →
      |((run b x cs).value:ℝ)/(2^b:ℝ) - realValue a ((x:ℝ)/(2^b:ℝ))| ≤
        (cs.length:ℝ)*((2^b:ℝ)⁻¹ + δ) := by
  intro b x cs a δ hx hδ hlen ha
  calc
    _ ≤ |((run b x cs).value:ℝ)/(2^b:ℝ) - exactValue b x cs| +
        |exactValue b x cs - realValue a ((x:ℝ)/(2^b:ℝ))| := abs_sub_le _ _ _
    _ ≤ (cs.length:ℝ)/(2^b:ℝ) + (cs.length:ℝ)*δ :=
      add_le_add (rounding_error b x cs hx) (coefficient_error b x δ hx hδ cs a hlen ha)
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- For `|x| ≤ 2^b`, multiplying an integer by `x` and dividing by `2^b` does not increase its
absolute value. -/
private theorem quotient_contracts (b : ℕ) (x v : ℤ) (hx : |x| ≤ (2^b:ℤ)) :
    (x*v/(2^b:ℤ)).natAbs ≤ v.natAbs := by
  have hd : (0:ℤ) < 2^b := by positivity
  have hn : |x*v| ≤ (2^b:ℤ)*(v.natAbs:ℤ) := by
    rw [abs_mul, Int.natCast_natAbs]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg v)
  have hlo : -(v.natAbs:ℤ) ≤ x*v/(2^b:ℤ) :=
    Int.le_ediv_of_mul_le hd (by nlinarith [(abs_le.mp hn).1])
  have hhi : x*v/(2^b:ℤ) ≤ (v.natAbs:ℤ) :=
    Int.ediv_le_of_le_mul hd (by nlinarith [(abs_le.mp hn).2])
  have h := abs_le.mpr ⟨hlo,hhi⟩
  rw [← Int.natCast_natAbs] at h
  exact_mod_cast h

/-- If `|x| ≤ 2^b` and each coefficient has absolute value at most `C`, the output magnitude is
at most `cs.length * C` and the recorded peak is at most `2^b * cs.length * C`. -/
theorem g3 :
    ∀ (b C : ℕ) (x : ℤ) (cs : List ℤ),
      |x| ≤ (2^b:ℤ) → (∀ c ∈ cs, c.natAbs ≤ C) →
      (run b x cs).value.natAbs ≤ cs.length*C ∧
      (run b x cs).peakAbs ≤ (2^b)*cs.length*C := by
  intro b C x cs hx hc
  have hscale : 1 ≤ (2^b:ℕ) := one_le_pow₀ (by norm_num)
  have hxN : x.natAbs ≤ 2^b := by
    have h : (x.natAbs:ℤ) ≤ (2^b:ℤ) := by simpa only [Int.natCast_natAbs] using hx
    exact_mod_cast h
  revert hc
  induction cs with
  | nil => intro hc; simp [run]
  | cons c cs ih =>
    intro hc
    have hc0 : c.natAbs ≤ C := hc c (by simp)
    have hct : ∀ d ∈ cs, d.natAbs ≤ C := fun d hd => hc d (by simp [hd])
    obtain ⟨hv,hp⟩ := ih hct
    have hq := (quotient_contracts b x (run b x cs).value hx).trans hv
    have hval : (c + x*(run b x cs).value/(2^b:ℤ)).natAbs ≤ (cs.length+1)*C := by
      exact (Int.natAbs_add_le _ _).trans (by nlinarith)
    have hmul : (x*(run b x cs).value).natAbs ≤ (2^b)*cs.length*C := by
      rw [Int.natAbs_mul]
      have h := Nat.mul_le_mul hxN hv
      simpa only [Nat.mul_assoc] using h
    have hnew : (cs.length+1)*C ≤ (2^b)*(cs.length+1)*C := by
      nlinarith [Nat.mul_le_mul_right ((cs.length+1)*C) hscale]
    have hold : (2^b)*cs.length*C ≤ (2^b)*(cs.length+1)*C := by
      exact Nat.mul_le_mul_right C (Nat.mul_le_mul_left (2^b) (by omega))
    constructor
    · simpa only [run, List.length_cons] using hval
    · change max (run b x cs).peakAbs
        (max c.natAbs (max (x*(run b x cs).value).natAbs
          (c+x*(run b x cs).value/(2^b:ℤ)).natAbs)) ≤ (2^b)*(cs.length+1)*C
      exact max_le (hp.trans hold)
        (max_le (hc0.trans (by nlinarith)) (max_le (hmul.trans hold) (hval.trans hnew)))

end Qatlib.Foundations.DyadicHorner.HornerError
