/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring
public import Qatlib.Papers.UniversalWalk12.MainResults.Model.SourceModel

@[expose] public section

/-!
# Exact Fourier selection for the correlated two-particle lattice

The variables conjugate to the particle positions are (x+y)/2 and x-y. The first frequency
can be a half integer, so orthogonality must integrate the second frequency first. This file
proves the integer selection rule from the elementary integral of the complex exponential.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

open Qatlib.Papers.UniversalWalk12.MainResults.Model

/-- A real-frequency character in the angular coordinate. -/
def character (frequency angle : ℝ) : ℂ :=
  Complex.exp (Complex.I * (frequency : ℂ) * (angle : ℂ))

/-- The normalized integral over one angular period. -/
def average (f : ℝ → ℂ) : ℂ :=
  (1 / (2 * Real.pi : ℝ) : ℂ) * ∫ angle in -Real.pi..Real.pi, f angle

/-- Continuous angular characters are integrable over every bounded interval. -/
theorem character_integrable (frequency a b : ℝ) :
    IntervalIntegrable (character frequency) volume a b := by
  apply Continuous.intervalIntegrable
  unfold character
  fun_prop

/-- Integer characters have equal values at the two endpoints of the period. -/
theorem character_endpoints (n : ℤ) : character n Real.pi = character n (-Real.pi) := by
  unfold character
  have heq : Complex.I * ((n : ℝ) : ℂ) * (Real.pi : ℂ) =
      Complex.I * ((n : ℝ) : ℂ) * ((-Real.pi : ℝ) : ℂ) +
        (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Averaging an integer-frequency character selects exactly the zero frequency. -/
theorem average_integer (n : ℤ) : average (character n) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [average, character, intervalIntegral.integral_const,
      Complex.real_smul]
    field_simp
    ring
  · have hc : Complex.I * ((n : ℝ) : ℂ) ≠ 0 := by
      exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
    unfold average character
    rw [integral_exp_mul_complex hc]
    have he := character_endpoints n
    unfold character at he
    rw [he, sub_self, zero_div, mul_zero, ite_eq_right hn]

/-- Multiplication adds character frequencies. -/
theorem character_mul (a b angle : ℝ) :
    character a angle * character b angle = character (a + b) angle := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Conjugating an angular character reverses its real frequency. -/
theorem character_conj (a angle : ℝ) : star (character a angle) = character (-a) angle := by
  unfold character
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

/-- A constant factor can be extracted from the normalized Fourier integral. -/
theorem average_const_mul (c : ℂ) (f : ℝ → ℂ) :
    average (fun angle => c * f angle) = c * average f := by
  unfold average
  rw [intervalIntegral.integral_const_mul]
  ring

/-- The two-dimensional average uses the relative coordinate before the center coordinate. -/
def average₂ (f : ℝ → ℝ → ℂ) : ℂ :=
  average fun angle₁ => average fun angle₂ => f angle₁ angle₂

/-- The Fourier character associated with the two integer particle positions. -/
def latticeChar (x y : ℤ) (angle₁ angle₂ : ℝ) : ℂ :=
  character (((x + y : ℤ) : ℝ) / 2) angle₁ * character ((x - y : ℤ) : ℝ) angle₂

/-- The relative-frequency integral vanishes unless the two particle separations coincide. -/
theorem lattice_inner_average (x y u v : ℤ) (angle₁ : ℝ) :
    average (fun angle₂ => latticeChar x y angle₁ angle₂ *
      star (latticeChar u v angle₁ angle₂)) =
    (character (((x + y : ℤ) : ℝ) / 2) angle₁ *
      star (character (((u + v : ℤ) : ℝ) / 2) angle₁)) *
      if x - y = u - v then 1 else 0 := by
  have hpoint (angle₂ : ℝ) : latticeChar x y angle₁ angle₂ *
      star (latticeChar u v angle₁ angle₂) =
      (character (((x + y : ℤ) : ℝ) / 2) angle₁ *
        star (character (((u + v : ℤ) : ℝ) / 2) angle₁)) *
      character (((x - y - (u - v) : ℤ) : ℝ)) angle₂ := by
    unfold latticeChar
    rw [star_mul, character_conj]
    have hh := character_mul (((x - y : ℤ) : ℝ)) (-((u - v : ℤ) : ℝ)) angle₂
    push_cast at hh ⊢
    rw [show (x : ℝ) - (y : ℝ) - ((u : ℝ) - (v : ℝ)) =
      (x : ℝ) - (y : ℝ) + -((u : ℝ) - (v : ℝ)) by ring]
    rw [← hh]
    ring
  simp_rw [hpoint]
  rw [average_const_mul, average_integer]
  simp [sub_eq_zero]

/-- The correlated half-integer Fourier lattice is orthonormal on the angular square. -/
theorem lattice_orthogonal (x y u v : ℤ) :
    average₂ (fun angle₁ angle₂ => latticeChar x y angle₁ angle₂ *
      star (latticeChar u v angle₁ angle₂)) = if x = u ∧ y = v then 1 else 0 := by
  unfold average₂
  simp_rw [lattice_inner_average]
  by_cases hsep : x - y = u - v
  · simp only [hsep, ite_true, mul_one]
    have hpoint (angle₁ : ℝ) :
        character (((x + y : ℤ) : ℝ) / 2) angle₁ *
          star (character (((u + v : ℤ) : ℝ) / 2) angle₁) =
        character ((y - v : ℤ) : ℝ) angle₁ := by
      rw [character_conj, character_mul]
      congr 1
      push_cast
      have hh : (x : ℝ) - (y : ℝ) = (u : ℝ) - (v : ℝ) := by exact_mod_cast hsep
      linarith
    simp_rw [hpoint]
    rw [average_integer]
    have heq : y - v = 0 ↔ x = u ∧ y = v := by omega
    simp only [heq]
  · simp [hsep, average]
    omega


/-- Fourier averaging commutes with a finite sum of integrable functions. -/
theorem average_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume (-Real.pi) Real.pi) :
    average (fun angle => ∑ i ∈ s, f i angle) = ∑ i ∈ s, average (f i) := by
  unfold average
  rw [intervalIntegral.integral_finsetSum hf, Finset.mul_sum]

/-- Iterated Fourier averaging commutes with a finite sum when both integrations exist. -/
theorem average₂_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℂ)
    (hinner : ∀ i ∈ s, ∀ angle₁, IntervalIntegrable (f i angle₁) volume (-Real.pi) Real.pi)
    (houter : ∀ i ∈ s, IntervalIntegrable (fun angle₁ => average (f i angle₁))
      volume (-Real.pi) Real.pi) :
    average₂ (fun angle₁ angle₂ => ∑ i ∈ s, f i angle₁ angle₂) =
      ∑ i ∈ s, average₂ (f i) := by
  unfold average₂
  simp_rw [average_sum s (fun i => f i _) (fun i hi => hinner i hi _)]
  rw [average_sum s _ houter]

/-- A scalar coefficient factors out of both Fourier averages. -/
theorem average₂_const_mul (c : ℂ) (f : ℝ → ℝ → ℂ) :
    average₂ (fun angle₁ angle₂ => c * f angle₁ angle₂) = c * average₂ f := by
  unfold average₂
  simp_rw [average_const_mul]

/-- A finite position-space amplitude has a concrete Fourier polynomial. -/
def synthesis (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (angle₁ angle₂ : ℝ) : ℂ :=
  ∑ v ∈ s, c v * latticeChar v.1 v.2 angle₁ angle₂

/-- The integrand for a coefficient of the finite Fourier polynomial. -/
def coeffTerm (c : ℂ) (x y u v : ℤ) (angle₁ angle₂ : ℝ) : ℂ :=
  c * (latticeChar x y angle₁ angle₂ * star (latticeChar u v angle₁ angle₂))

/-- Each coefficient integrand is integrable in the relative angular variable. -/
theorem coeffTerm_inner (c : ℂ) (x y u v : ℤ) (angle₁ : ℝ) :
    IntervalIntegrable (coeffTerm c x y u v angle₁) volume (-Real.pi) Real.pi := by
  apply Continuous.intervalIntegrable
  unfold coeffTerm latticeChar character
  fun_prop

/-- Integrating the relative angle leaves a continuous function of the center angle. -/
theorem coeffTerm_outer (c : ℂ) (x y u v : ℤ) :
    IntervalIntegrable (fun angle₁ => average (coeffTerm c x y u v angle₁))
      volume (-Real.pi) Real.pi := by
  unfold coeffTerm
  simp_rw [average_const_mul, lattice_inner_average]
  apply Continuous.intervalIntegrable
  unfold character
  fun_prop

/-- Averaging a coefficient term selects its exact integer position. -/
theorem coeffTerm_average (c : ℂ) (x y u v : ℤ) :
    average₂ (coeffTerm c x y u v) = c * if x = u ∧ y = v then 1 else 0 := by
  unfold coeffTerm
  rw [average₂_const_mul, lattice_orthogonal]

/-- Fourier inversion for arbitrary finite position-space data on the correlated lattice. -/
theorem synthesis_inversion (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (u v : ℤ) :
    average₂ (fun angle₁ angle₂ =>
      synthesis s c angle₁ angle₂ * star (latticeChar u v angle₁ angle₂)) =
      if (u, v) ∈ s then c (u, v) else 0 := by
  classical
  have hpoint (angle₁ angle₂ : ℝ) :
      synthesis s c angle₁ angle₂ * star (latticeChar u v angle₁ angle₂) =
      ∑ z ∈ s, coeffTerm (c z) z.1 z.2 u v angle₁ angle₂ := by
    unfold synthesis coeffTerm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _hz
    ring
  simp_rw [hpoint]
  rw [average₂_sum s (fun z angle₁ angle₂ => coeffTerm (c z) z.1 z.2 u v angle₁ angle₂)
    (fun z _hz angle₁ => coeffTerm_inner _ _ _ _ _ angle₁)
    (fun z _hz => coeffTerm_outer _ _ _ _ _)]
  simp_rw [coeffTerm_average]
  have hterm (z : ℤ × ℤ) :
      c z * (if z.1 = u ∧ z.2 = v then 1 else 0) =
      if z = (u, v) then c (u, v) else 0 := by
    by_cases hz : z = (u, v)
    · subst z
      simp
    · have hh : ¬(z.1 = u ∧ z.2 = v) := by
        rintro ⟨h1, h2⟩
        exact hz (Prod.ext h1 h2)
      simp [hz, hh]
  simp_rw [hterm]
  simp

/-- The normalized angular average equals the source's iterated Lebesgue integral. -/
theorem average₂_integral (f : ℝ → ℝ → ℂ) :
    average₂ f =
      ∫ angle₁ in Icc (-Real.pi) Real.pi,
        ∫ angle₂ in Icc (-Real.pi) Real.pi,
          ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) * f angle₁ angle₂ := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  unfold average₂ average
  simp_rw [intervalIntegral.integral_of_le hpi, ← integral_Icc_eq_integral_Ioc]
  simp_rw [integral_const_mul]
  have hc : (1 / (2 * Real.pi : ℝ) : ℂ) * (1 / (2 * Real.pi : ℝ) : ℂ) =
      ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← mul_assoc, hc]


/-- The two finite position windows defining the incoming two-particle packet. -/
def packetSupport (M L : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1))) ×ˢ
    (Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)))

/-- The correlated lattice character agrees with the two phases in the source kernel. -/
theorem latticeChar_source (x y : ℤ) (angle₁ angle₂ : ℝ) :
    latticeChar x y angle₁ angle₂ =
      Complex.exp (Complex.I * (angle₁ : ℂ) * ((x + y : ℤ) : ℂ) / 2) *
      Complex.exp (Complex.I * (angle₂ : ℂ) * ((x - y : ℤ) : ℂ)) := by
  unfold latticeChar character
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The paper's A kernel is the actual Fourier polynomial of its finite position packet. -/
theorem kernel_synthesis (M L : ℕ) (angle₁ angle₂ : ℝ) :
    synthesis (packetSupport M L) (fun _ => ((1 / (L : ℝ) : ℝ) : ℂ)) angle₁ angle₂ =
      AmpA M L angle₁ angle₂ := by
  unfold synthesis packetSupport AmpA
  rw [Finset.sum_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [latticeChar_source]

/-- Exact inversion selects the source packet's two finite position windows. -/
theorem kernel_inversion (M L : ℕ) (u v : ℤ) :
    average₂ (fun angle₁ angle₂ =>
      AmpA M L angle₁ angle₂ * star (latticeChar u v angle₁ angle₂)) =
      if (u, v) ∈ packetSupport M L then ((1 / (L : ℝ) : ℝ) : ℂ) else 0 := by
  simp_rw [← kernel_synthesis]
  exact synthesis_inversion _ _ _ _

/-- The source's inverse phases are the conjugate character of the selected positions. -/
theorem inverse_phases (x y : ℤ) (angle₁ angle₂ : ℝ) :
    star (latticeChar x y angle₁ angle₂) =
      Complex.exp (-Complex.I * (angle₁ : ℂ) * ((((x + y : ℤ) : ℝ) / 2 : ℝ) : ℂ)) *
      Complex.exp (-(2 : ℂ) * Complex.I * (angle₂ : ℂ) *
        ((((x - y : ℤ) : ℝ) / 2 : ℝ) : ℂ)) := by
  rw [latticeChar, star_mul, character_conj, character_conj]
  unfold character
  rw [mul_comm]
  congr 1 <;> congr 1 <;> push_cast <;> ring

/-- The double integral in Lemma 6 is the exact inverse Fourier selector for integer positions. -/
theorem lemmaSix_select (M L : ℕ) (x y : ℤ) :
    lemmaSixIntegral M L (((x + y : ℤ) : ℝ) / 2) (((x - y : ℤ) : ℝ) / 2) =
      if (x, y) ∈ packetSupport M L then ((1 / (L : ℝ) : ℝ) : ℂ) else 0 := by
  have hkernel := kernel_inversion M L x y
  rw [average₂_integral] at hkernel
  rw [← hkernel]
  unfold lemmaSixIntegral setIntegral
  congr 1
  funext angle₁
  congr 1
  funext angle₂
  rw [inverse_phases]
  ring

/-- Floor translations of the positions reproduce precisely the source's moving rectangle F. -/
theorem lemmaSix_window (M L : ℕ) (t : ℝ) (x y : ℤ) :
    lemmaSixIntegral M L
        (-(⌊t⌋ : ℝ) + (⌊t / Real.sqrt 2⌋ : ℝ) + (((x + y : ℤ) : ℝ)) / 2)
        (-(⌊t⌋ : ℝ) - (⌊t / Real.sqrt 2⌋ : ℝ) + (((x - y : ℤ) : ℝ)) / 2) =
      ((twoF M L t x y : ℝ) : ℂ) / (L : ℂ) := by
  have h := lemmaSix_select M L (x - 2 * ⌊t⌋) (y + 2 * ⌊t / Real.sqrt 2⌋)
  have hsum : (((x - 2 * ⌊t⌋ + (y + 2 * ⌊t / Real.sqrt 2⌋) : ℤ) : ℝ) / 2) =
      -(⌊t⌋ : ℝ) + (⌊t / Real.sqrt 2⌋ : ℝ) + (((x + y : ℤ) : ℝ)) / 2 := by
    push_cast
    ring
  have hdiff : (((x - 2 * ⌊t⌋ - (y + 2 * ⌊t / Real.sqrt 2⌋) : ℤ) : ℝ) / 2) =
      -(⌊t⌋ : ℝ) - (⌊t / Real.sqrt 2⌋ : ℝ) + (((x - y : ℤ) : ℝ)) / 2 := by
    push_cast
    ring
  rw [hsum, hdiff] at h
  simpa [packetSupport, twoF, apply_ite, ite_div] using h


/-- Pairing a finite Fourier polynomial with itself gives its exact coefficient energy. -/
theorem synthesis_energy (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    average₂ (fun angle₁ angle₂ =>
      synthesis s c angle₁ angle₂ * star (synthesis s c angle₁ angle₂)) =
      ∑ z ∈ s, c z * star (c z) := by
  classical
  let f := fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
    coeffTerm (c p.1 * star (c p.2)) p.1.1 p.1.2 p.2.1 p.2.2
  have hpoint (angle₁ angle₂ : ℝ) :
      synthesis s c angle₁ angle₂ * star (synthesis s c angle₁ angle₂) =
      ∑ p ∈ s ×ˢ s, f p angle₁ angle₂ := by
    unfold synthesis f coeffTerm
    rw [star_sum, Finset.sum_mul, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro z _hz
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _hw
    rw [star_mul]
    ring
  simp_rw [hpoint]
  rw [average₂_sum (s ×ˢ s) f
    (fun p _hp angle₁ => coeffTerm_inner _ _ _ _ _ angle₁)
    (fun p _hp => coeffTerm_outer _ _ _ _ _)]
  simp only [f, coeffTerm_average]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro z hz
  have hterm (w : ℤ × ℤ) :
      (c z * star (c w)) * (if z.1 = w.1 ∧ z.2 = w.2 then 1 else 0) =
      if w = z then c z * star (c z) else 0 := by
    by_cases hw : w = z
    · subst w
      simp
    · have hh : ¬(z.1 = w.1 ∧ z.2 = w.2) := by
        rintro ⟨h1, h2⟩
        exact hw (Prod.ext h1.symm h2.symm)
      simp [hw, hh]
  simp_rw [hterm]
  simp [hz]

/-- The complex product with its conjugate is the squared norm embedded in the complex field. -/
theorem mul_star_norm (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  exact_mod_cast Complex.mul_conj' z

/-- Parseval's identity for the exact finite-packet Fourier transform. -/
theorem synthesis_parseval (s : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) :
    average₂ (fun angle₁ angle₂ =>
      ((‖synthesis s c angle₁ angle₂‖ ^ 2 : ℝ) : ℂ)) =
      ∑ z ∈ s, ((‖c z‖ ^ 2 : ℝ) : ℂ) := by
  simpa only [mul_star_norm] using synthesis_energy s c

/-- The two-particle position rectangle contains exactly L squared positions. -/
theorem packetSupport_card (M L : ℕ) : (packetSupport M L).card = L * L := by
  unfold packetSupport
  rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
  have h1 : -((M : ℤ) + 1) + 1 - -((M : ℤ) + (L : ℤ)) = (L : ℤ) := by ring
  have h2 : (M : ℤ) + (L : ℤ) + 1 - ((M : ℤ) + 1) = (L : ℤ) := by ring
  rw [h1, h2, Int.toNat_natCast]

/-- The source kernel is normalized because it is the Fourier transform of L squared entries 1/L. -/
theorem kernel_parseval (M L : ℕ) (hL : 0 < L) :
    average₂ (fun angle₁ angle₂ => ((‖AmpA M L angle₁ angle₂‖ ^ 2 : ℝ) : ℂ)) = 1 := by
  simp_rw [← kernel_synthesis]
  rw [synthesis_parseval]
  simp only [Finset.sum_const, nsmul_eq_mul, packetSupport_card, Nat.cast_mul,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  push_cast
  field_simp

/-- The exact normalization conclusion of Lemma 5 in the source's real-integral convention. -/
theorem kernel_normalized (M L : ℕ) (hL : 0 < L) :
    setIntegralR (Icc (-Real.pi) Real.pi) (fun angle₁ =>
      setIntegralR (Icc (-Real.pi) Real.pi) (fun angle₂ =>
        (1 / (4 * Real.pi ^ 2)) * ‖AmpA M L angle₁ angle₂‖ ^ 2)) = 1 := by
  have h := kernel_parseval M L hL
  rw [average₂_integral] at h
  unfold setIntegralR
  apply Complex.ofReal_injective
  push_cast
  simpa only [← Complex.ofReal_mul, integral_complex_ofReal] using h

end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
