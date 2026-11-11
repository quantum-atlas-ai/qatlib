/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.ErrorStream.DistinctFourierNoise

/-!
# Conditional noise inclusion laws and Fourier moments

`conditionalNoiseMean` averages over the size-`L` subsets of a finite set `C`. Exact single-site
and distinct-pair inclusion factors determine the Fourier mean and second moment for this
sampling without replacement.

For noise restricted to the complement of a signal set,
`conditional_signal_noise_mixed_second_moment` computes both the noise moment and the full union
moment, retaining the signal-noise cross term.

The error-stream setting is developed in [Cornwell2014].

## Main statements

* `conditional_noise_exact_inclusion`: fixed-cardinality inclusion probabilities.
* `conditionalNoiseMean_add`: additivity of the conditional mean.
* `conditional_signal_noise_mixed_second_moment`: exact noise and mixed Fourier moments.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QuditTeleport.TeleportCore

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.AmpTransform.ErrorStream
open scoped Classical BigOperators

/-- The uniform real-valued mean over subsets of `C` of cardinality `L`, using the inverse
cardinality of that family as normalization. -/
def conditionalNoiseMean {X : Type} [DecidableEq X] (C : Finset X) (L : ℕ)
    (f : Finset X → ℝ) : ℝ :=
  ((C.powersetCard L).card : ℝ)⁻¹ * ∑ S ∈ C.powersetCard L, f S

/-- A size-`L` subset of the complement of `A` is disjoint from `A`, and its union with `A` has
cardinality `A.card + L`. -/
theorem conditional_noise_record {X : Type} [Fintype X] [DecidableEq X]
    (A S : Finset X) (L : ℕ) (hS : S ∈ (Finset.univ \ A).powersetCard L) :
    Disjoint A S ∧ (A ∪ S).card = A.card+L := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
  have hdis : Disjoint A S := Finset.disjoint_left.mpr fun x hx hs =>
    (Finset.mem_sdiff.mp (hsub hs)).2 hx
  exact ⟨hdis, by rw [Finset.card_union_of_disjoint hdis, hcard]⟩

/-- The sum of real indicators over a finite set equals the cardinality of the filtered set. -/
private theorem conditional_sum_indicator {X : Type} [DecidableEq X]
    (T : Finset X) (p : X → Prop) [DecidablePred p] :
    (∑ x ∈ T, if p x then (1 : ℝ) else 0) = ((T.filter p).card : ℝ) := by
  rw [← Finset.sum_filter]
  simp

/-- The binomial coefficient identity `n * choose (n - 1) (l - 1) = choose n l * l` for positive
`n` and `l`. -/
private theorem conditional_choose_one (n l : ℕ) (hn : 0 < n) (hl : 0 < l) :
    n * ((n-1).choose (l-1)) = (n.choose l) * l := by
  have h := Nat.add_one_mul_choose_eq (n-1) (l-1)
  simpa only [Nat.sub_add_cancel hn, Nat.sub_add_cancel hl] using! h

/-- The two-element binomial coefficient identity relating `choose (n - 2) (l - 2)` to `choose n
l * l * (l - 1)` when `n` and `l` are at least two. -/
private theorem conditional_choose_two (n l : ℕ) (hn : 2 ≤ n) (hl : 2 ≤ l) :
    n*(n-1)*((n-2).choose (l-2)) = (n.choose l)*l*(l-1) := by
  have h1 := conditional_choose_one n l (by omega) (by omega)
  have h2 := conditional_choose_one (n-1) (l-1) (by omega) (by omega)
  simp only [Nat.sub_sub, show (1 : ℕ)+1 = 2 from rfl] at h2
  calc
    _ = n*((n-1)*((n-2).choose (l-2))) := by ring
    _ = n*(((n-1).choose (l-1))*(l-1)) := by rw [h2]
    _ = (n*((n-1).choose (l-1)))*(l-1) := by ring
    _ = _ := by rw [h1]

/-- In the uniform size-`L` subsets of `C`, a specified element of `C` is included with mean
indicator `L / C.card`. -/
private theorem conditional_single_inclusion {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (hL : L ≤ C.card) (x : X) (hx : x ∈ C) :
    conditionalNoiseMean C L (fun S => if x ∈ S then 1 else 0) = (L : ℝ)/C.card := by
  by_cases hl : L = 0
  · subst L; simp [conditionalNoiseMean, Finset.powersetCard_zero]
  have hlp : 0 < L := Nat.pos_of_ne_zero hl
  have hcp : 0 < C.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hc := Finset.card_filter_powersetCard_subset ({x} : Finset X) C L
    (Finset.singleton_subset_iff.mpr hx) (by simpa using! hlp)
  simp only [Finset.singleton_subset_iff, Finset.card_singleton] at hc
  rw [conditionalNoiseMean, conditional_sum_indicator, hc, Finset.card_powersetCard]
  have hb : (C.card.choose L : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hL).ne'
  have hn : (C.card : ℝ) ≠ 0 := by exact_mod_cast hcp.ne'
  have hh : (C.card : ℝ)*((C.card-1).choose (L-1) : ℝ) =
      (C.card.choose L : ℝ)*(L : ℝ) := by
    exact_mod_cast conditional_choose_one C.card L hcp hlp
  apply (eq_div_iff hn).mpr
  calc
    _ = (C.card.choose L : ℝ)⁻¹*((C.card : ℝ)*((C.card-1).choose (L-1) : ℝ)) := by ring
    _ = (C.card.choose L : ℝ)⁻¹*((C.card.choose L : ℝ)*(L : ℝ)) := by rw [hh]
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul]

/-- Two distinct specified elements of `C` have joint mean inclusion indicator `L * (L - 1) /
(C.card * (C.card - 1))` for a feasible size `L`. -/
private theorem conditional_pair_inclusion {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (hL : L ≤ C.card) (x y : X)
    (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    conditionalNoiseMean C L (fun S => if x ∈ S ∧ y ∈ S then 1 else 0) =
      (L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1)) := by
  have hsub : ({x,y} : Finset X) ⊆ C := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using! And.intro hx hy
  have hn2 : 2 ≤ C.card := by simpa [Finset.card_pair hxy] using! Finset.card_le_card hsub
  by_cases hl : 2 ≤ L
  · have hc := Finset.card_filter_powersetCard_subset ({x,y} : Finset X) C L
      hsub (by simpa [hxy] using! hl)
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.card_pair hxy] at hc
    rw [conditionalNoiseMean, conditional_sum_indicator, hc, Finset.card_powersetCard]
    have hb : (C.card.choose L : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hL).ne'
    have hn : (C.card : ℝ) ≠ 0 := by exact_mod_cast (show C.card ≠ 0 by omega)
    have hn1 : (C.card : ℝ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show C.card ≠ 1 by omega))
    have hh : (C.card : ℝ)*((C.card-1 : ℕ) : ℝ)*((C.card-2).choose (L-2) : ℝ) =
        (C.card.choose L : ℝ)*(L : ℝ)*((L-1 : ℕ) : ℝ) := by
      exact_mod_cast conditional_choose_two C.card L hn2 hl
    rw [Nat.cast_sub (by omega : 1 ≤ C.card), Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one] at hh
    apply (eq_div_iff (mul_ne_zero hn hn1)).mpr
    calc
      _ = (C.card.choose L : ℝ)⁻¹*((C.card : ℝ)*(C.card-1)*((C.card-2).choose (L-2) : ℝ)) := by ring
      _ = (C.card.choose L : ℝ)⁻¹*((C.card.choose L : ℝ)*(L : ℝ)*(L-1)) := by rw [hh]
      _ = _ := by rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hb, one_mul]
  · have he : ∀ S ∈ C.powersetCard L, ¬(x ∈ S ∧ y ∈ S) := by
      intro S hS hm
      have hs := (Finset.mem_powersetCard.mp hS).2
      have hsubS : ({x,y} : Finset X) ⊆ S := by
        simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using! hm
      have hh := Finset.card_le_card hsubS
      rw [Finset.card_pair hxy, hs] at hh
      omega
    have hm : conditionalNoiseMean C L (fun S => if x ∈ S ∧ y ∈ S then 1 else 0) = 0 := by
      unfold conditionalNoiseMean
      rw [Finset.sum_eq_zero (fun S hS => if_neg (he S hS))]
      simp
    rw [hm]
    have hl01 : L = 0 ∨ L = 1 := by omega
    rcases hl01 with rfl | rfl <;> simp

/-- For a feasible fixed-cardinality family, identify its binomial cardinality and the exact
single-site and distinct-pair inclusion means used in the error-stream moment calculation of
[Cornwell2014]. -/
theorem conditional_noise_exact_inclusion :
    ∀ (X : Type) [Fintype X] [DecidableEq X] (C : Finset X) (L : ℕ), L ≤ C.card →
      let T := C.powersetCard L
      let avg := fun f : Finset X → ℝ => (T.card : ℝ)⁻¹ * ∑ S ∈ T, f S
      T.card = C.card.choose L ∧
      (∀ x ∈ C, avg (fun S => if x ∈ S then 1 else 0) = (L : ℝ)/C.card) ∧
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        avg (fun S => if x ∈ S ∧ y ∈ S then 1 else 0) =
          (L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1))) := by
  intro X _ _ C L hL
  exact ⟨Finset.card_powersetCard L C, conditional_single_inclusion C L hL,
    fun x hx y hy hxy => conditional_pair_inclusion C L hL x y hx hy hxy⟩

/-- The uniform complex-valued mean over subsets of `C` of cardinality `L`. -/
private def conditionalComplexMean {X : Type} [DecidableEq X] (C : Finset X) (L : ℕ)
    (f : Finset X → ℂ) : ℂ :=
  ((C.powersetCard L).card : ℂ)⁻¹ * ∑ S ∈ C.powersetCard L, f S

/-- Functions agreeing on all size-`L` subsets of `C` have equal conditional complex means. -/
private theorem conditionalComplexMean_congr {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (f g : Finset X → ℂ)
    (h : ∀ S ∈ C.powersetCard L, f S = g S) :
    conditionalComplexMean C L f = conditionalComplexMean C L g := by
  unfold conditionalComplexMean
  rw [Finset.sum_congr rfl h]

/-- Conditional complex averaging commutes with a finite sum. -/
private theorem conditionalComplexMean_sum {X J : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (D : Finset J) (f : J → Finset X → ℂ) :
    conditionalComplexMean C L (fun S => ∑ x ∈ D, f x S) =
      ∑ x ∈ D, conditionalComplexMean C L (f x) := by
  unfold conditionalComplexMean
  rw [Finset.sum_comm, Finset.mul_sum]

/-- A constant complex factor can be pulled out of the conditional mean. -/
private theorem conditionalComplexMean_mul_left {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (c : ℂ) (f : Finset X → ℂ) :
    conditionalComplexMean C L (fun S => c*f S) = c*conditionalComplexMean C L f := by
  simp [conditionalComplexMean, ← Finset.mul_sum, mul_left_comm]

/-- Conditional complex averaging commutes with complex conjugation. -/
private theorem conditionalComplexMean_star {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (f : Finset X → ℂ) :
    conditionalComplexMean C L (fun S => star (f S)) = star (conditionalComplexMean C L f) := by
  simp [conditionalComplexMean, star_sum, star_mul, mul_comm]

/-- Express the Fourier sum of `S ⊆ C` as a sum over `C` weighted by membership indicators of
`S`. -/
private theorem conditional_fourier_expand {N : ℕ} [NeZero N]
    (C S : Finset (ZMod N)) (y : ZMod N) (hS : S ⊆ C) :
    distinctNoiseFourier S y = ∑ x ∈ C, ZMod.stdAddChar (x*y)*(if x ∈ S then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  unfold distinctNoiseFourier
  calc
    _ = ∑ x ∈ S, (if x ∈ S then ZMod.stdAddChar (x*y) else 0) := by
      exact Finset.sum_congr rfl fun x hx => (if_pos hx).symm
    _ = _ := Finset.sum_subset hS (by intros; simp_all)

/-- For a feasible layer in a set of size at least two, compute the conditional Fourier mean and
second moment from the one-site and two-site inclusion factors. -/
private theorem conditional_fourier_moments (N L : ℕ) [NeZero N]
    (C : Finset (ZMod N)) (y : ZMod N) (hC : 2 ≤ C.card) (hL : L ≤ C.card) :
    conditionalComplexMean C L (fun S => distinctNoiseFourier S y) =
      ((L : ℂ)/C.card)*distinctNoiseFourier C y ∧
    conditionalComplexMean C L (fun S => distinctNoiseFourier S y*star (distinctNoiseFourier S y)) =
      L + ((L : ℂ)*(L-1)/((C.card : ℂ)*(C.card-1)))*
        (distinctNoiseFourier C y*star (distinctNoiseFourier C y)-C.card) := by
  let χ := fun x : ZMod N => ZMod.stdAddChar (x*y)
  let p : ℂ := (L : ℂ)/C.card
  let q : ℂ := (L : ℂ)*(L-1)/((C.card : ℂ)*(C.card-1))
  obtain ⟨_, hi, hij⟩ := conditional_noise_exact_inclusion (ZMod N) C L hL
  have hp (x : ZMod N) (hx : x ∈ C) :
      conditionalComplexMean C L (fun S => if x ∈ S then 1 else 0) = p := by
    have hh := congrArg Complex.ofReal (hi x hx)
    simpa [conditionalComplexMean, conditionalNoiseMean, p] using! hh
  have hpq (x w : ZMod N) (hx : x ∈ C) (hw : w ∈ C) :
      conditionalComplexMean C L (fun S => if x ∈ S ∧ w ∈ S then 1 else 0) =
        if x=w then p else q := by
    by_cases he : x=w
    · subst w; simpa only [and_self, ite_true] using! hp x hx
    · rw [if_neg he]
      have hh := congrArg Complex.ofReal (hij x hx w hw he)
      simpa [conditionalComplexMean, conditionalNoiseMean, q] using! hh
  have hu (x : ZMod N) : χ x*star (χ x) = 1 := by
    dsimp only [χ]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_stdAddChar]
    norm_num
  have hex (S : Finset (ZMod N)) (hS : S ∈ C.powersetCard L) :
      distinctNoiseFourier S y = ∑ x ∈ C, χ x*(if x ∈ S then 1 else 0) :=
    conditional_fourier_expand C S y (Finset.mem_powersetCard.mp hS).1
  have hsq (S : Finset (ZMod N)) (hS : S ∈ C.powersetCard L) :
      distinctNoiseFourier S y*star (distinctNoiseFourier S y) =
        ∑ x ∈ C, ∑ w ∈ C, (χ x*star (χ w))*(if x ∈ S ∧ w ∈ S then 1 else 0) := by
    rw [hex S hS, star_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro w _
    by_cases hx : x ∈ S <;> by_cases hw : w ∈ S <;> simp [hx, hw]
  constructor
  · rw [conditionalComplexMean_congr C L _ _ hex, conditionalComplexMean_sum]
    simp_rw [conditionalComplexMean_mul_left]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (χ x * ·) (hp x hx))]
    rw [← Finset.sum_mul, mul_comm]
    rfl
  · rw [conditionalComplexMean_congr C L _ _ hsq, conditionalComplexMean_sum]
    simp_rw [conditionalComplexMean_sum, conditionalComplexMean_mul_left]
    have hrow (x : ZMod N) (hx : x ∈ C) :
        (∑ w ∈ C, (χ x*star (χ w))*conditionalComplexMean C L
          (fun S => if x ∈ S ∧ w ∈ S then 1 else 0)) =
          q*χ x*star (distinctNoiseFourier C y)+(p-q) := by
      have he (w : ZMod N) (hw : w ∈ C) :
          (χ x*star (χ w))*conditionalComplexMean C L
            (fun S => if x ∈ S ∧ w ∈ S then 1 else 0) =
          q*χ x*star (χ w)+(if w=x then (p-q)*(χ x*star (χ w)) else 0) := by
        rw [hpq x w hx hw]
        by_cases hh : w=x
        · subst w; simp only [ite_true]; ring
        · simp only [if_neg hh, if_neg (Ne.symm hh), add_zero]; ring
      rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', hx, ite_true, hu, mul_one]
      rw [distinctNoiseFourier, star_sum]
    rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    have he : (∑ x ∈ C, q*χ x*star (distinctNoiseFourier C y)) =
        q*distinctNoiseFourier C y*star (distinctNoiseFourier C y) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]; rfl
    rw [he]
    have hn : (C.card : ℂ) ≠ 0 := by exact_mod_cast (show C.card ≠ 0 by omega)
    have hnp : (C.card : ℂ)*p = L := by dsimp [p]; field_simp
    calc
      _ = (C.card : ℂ)*p+q*(distinctNoiseFourier C y*star (distinctNoiseFourier C y)-C.card) := by ring
      _ = _ := by rw [hnp]

/-- The real part of a conditional complex mean equals the conditional real mean of the real
parts. -/
private theorem conditionalComplexMean_re {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (f : Finset X → ℂ) :
    (conditionalComplexMean C L f).re = conditionalNoiseMean C L (fun S => (f S).re) := by
  unfold conditionalComplexMean conditionalNoiseMean
  rw [show ((C.powersetCard L).card : ℂ)⁻¹ = (((C.powersetCard L).card : ℝ)⁻¹ : ℂ) by simp]
  simp [Complex.mul_re]

/-- Conditional real averaging is additive. -/
@[simp] theorem conditionalNoiseMean_add {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (f g : Finset X → ℝ) :
    conditionalNoiseMean C L (fun S => f S+g S) =
      conditionalNoiseMean C L f + conditionalNoiseMean C L g := by
  simp [conditionalNoiseMean, Finset.sum_add_distrib, mul_add]

/-- A constant real factor can be pulled out of the conditional mean. -/
@[simp] theorem conditionalNoiseMean_mul_left {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (c : ℝ) (f : Finset X → ℝ) :
    conditionalNoiseMean C L (fun S => c*f S) = c*conditionalNoiseMean C L f := by
  simp [conditionalNoiseMean, ← Finset.mul_sum, mul_left_comm]

/-- The conditional mean of a constant equals that constant when the fixed-cardinality layer is
feasible. -/
theorem conditionalNoiseMean_const {X : Type} [DecidableEq X]
    (C : Finset X) (L : ℕ) (hL : L ≤ C.card) (c : ℝ) :
    conditionalNoiseMean C L (fun _ => c) = c := by
  have hb : (C.card.choose L : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hL).ne'
  simp [conditionalNoiseMean, hb]

/-- For fixed-cardinality noise on a signal complement of size at least two, compute the noise
Fourier second moment and the mixed signal-plus-noise second moment, including their cross
term; see [Cornwell, Section 3.4.4][Cornwell2014]. -/
theorem conditional_signal_noise_mixed_second_moment :
    ∀ (N L : ℕ) [NeZero N] (A : Finset (ZMod N)) (y : ZMod N),
      let C := Finset.univ \ A
      2 ≤ C.card → L ≤ C.card →
      let T := C.powersetCard L
      let avg := fun f : Finset (ZMod N) → ℝ => (T.card : ℝ)⁻¹ * ∑ S ∈ T, f S
      let a := distinctNoiseFourier A y
      let c := distinctNoiseFourier C y
      let p₂ := (L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1))
      avg (fun S => ‖distinctNoiseFourier S y‖^2) =
        L+p₂*(‖c‖^2-C.card) ∧
      avg (fun S => ‖distinctNoiseFourier (A ∪ S) y‖^2) =
        ‖a‖^2+2*(L : ℝ)/C.card*(a*star c).re+L+p₂*(‖c‖^2-C.card) := by
  intro N L _ A y C hC hL
  (try dsimp only)
  obtain ⟨hm, hs⟩ := conditional_fourier_moments N L C y hC hL
  have hsecond : conditionalNoiseMean C L (fun S => ‖distinctNoiseFourier S y‖^2) =
      L+((L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1)))*
        (‖distinctNoiseFourier C y‖^2-C.card) := by
    have hh := congrArg Complex.re hs
    rw [conditionalComplexMean_re] at hh
    have hq : (L : ℂ)*(L-1)/((C.card : ℂ)*(C.card-1)) =
        Complex.ofReal ((L : ℝ)*(L-1)/((C.card : ℝ)*(C.card-1))) := by push_cast; rfl
    rw [hq] at hh
    simpa only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im, Complex.sub_im,
      mul_zero, zero_mul, sub_zero] using hh
  have hcross : conditionalNoiseMean C L
      (fun S => (distinctNoiseFourier A y*star (distinctNoiseFourier S y)).re) =
      ((L : ℝ)/C.card)*(distinctNoiseFourier A y*star (distinctNoiseFourier C y)).re := by
    rw [← conditionalComplexMean_re, conditionalComplexMean_mul_left,
      conditionalComplexMean_star, hm]
    have hp : ((L : ℂ)/C.card) = Complex.ofReal ((L : ℝ)/C.card) := by simp
    rw [hp, star_mul]
    simp [Complex.mul_re]
    ring
  refine ⟨hsecond, ?_⟩
  have hunion (S : Finset (ZMod N)) (hS : S ∈ C.powersetCard L) :
      distinctNoiseFourier (A ∪ S) y = distinctNoiseFourier A y+distinctNoiseFourier S y := by
    exact Finset.sum_union (conditional_noise_record A S L hS).1
  have he : conditionalNoiseMean C L (fun S => ‖distinctNoiseFourier (A ∪ S) y‖^2) =
      conditionalNoiseMean C L (fun S => ‖distinctNoiseFourier A y‖^2+
        2*(distinctNoiseFourier A y*star (distinctNoiseFourier S y)).re+
        ‖distinctNoiseFourier S y‖^2) := by
    unfold conditionalNoiseMean
    congr 1
    apply Finset.sum_congr rfl
    intro S hS
    (try dsimp only)
    rw [hunion S hS, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp only [Complex.star_def, Complex.normSq_eq_norm_sq]
    ring
  change conditionalNoiseMean C L _ = _
  rw [he, conditionalNoiseMean_add, conditionalNoiseMean_add,
    conditionalNoiseMean_const C L hL, conditionalNoiseMean_mul_left, hcross, hsecond]
  ring

end Qatlib.Concepts.AmpTransform.ErrorStream
