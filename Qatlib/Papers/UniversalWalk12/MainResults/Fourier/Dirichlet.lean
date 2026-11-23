/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Qatlib.Papers.UniversalWalk12.MainResults.Fourier.KernelBounds

@[expose] public section

/-!
# One-dimensional finite-packet spectral mass

The Dirichlet sum is the exact finite sum of unit angular characters. Its energy density has
unit normalized mass and its off-origin decay is obtained from the geometric sum and Jordan
inequality. These are the one-dimensional factors of the physical two-particle packet kernel.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

/-- The exact character polynomial of a length-L position packet. -/
def dirichletSum (L : ℕ) (angle : ℝ) : ℂ :=
  ∑ n ∈ Finset.range L, character (n : ℝ) angle

/-- The one-particle normalized energy density of its character polynomial. -/
def dirichletEnergy (L : ℕ) (angle : ℝ) : ℝ := ‖dirichletSum L angle‖ ^ 2 / (L : ℝ)

/-- Integer-frequency orthogonality in the angular average. -/
theorem natural_orthogonal (n m : ℕ) :
    average (fun angle => character (n : ℝ) angle * star (character (m : ℝ) angle)) =
      if n = m then 1 else 0 := by
  have hp (angle : ℝ) : character (n : ℝ) angle * star (character (m : ℝ) angle) =
      character (((n : ℤ) - (m : ℤ) : ℤ) : ℝ) angle := by
    rw [character_conj, character_mul]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [average_integer]
  simp [sub_eq_zero]

/-- Parseval's formula gives exactly L units of unnormalized finite-packet energy. -/
theorem dirichlet_parseval (L : ℕ) :
    average (fun angle => ((‖dirichletSum L angle‖ ^ 2 : ℝ) : ℂ)) = (L : ℂ) := by
  have hp (angle : ℝ) : ((‖dirichletSum L angle‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ Finset.range L, ∑ m ∈ Finset.range L,
        character (n : ℝ) angle * star (character (m : ℝ) angle) := by
    rw [← mul_star_norm, dirichletSum, star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [Finset.mul_sum]
  simp_rw [hp]
  rw [average_sum (Finset.range L)
    (fun n angle => ∑ m ∈ Finset.range L,
      character (n : ℝ) angle * star (character (m : ℝ) angle))
    (fun _n _hn => Continuous.intervalIntegrable (by unfold character; fun_prop) _ _)]
  have hi (n : ℕ) : average (fun angle => ∑ m ∈ Finset.range L,
      character (n : ℝ) angle * star (character (m : ℝ) angle)) =
      ∑ m ∈ Finset.range L, if n = m then (1 : ℂ) else 0 := by
    rw [average_sum (Finset.range L)
      (fun m angle => character (n : ℝ) angle * star (character (m : ℝ) angle))
      (fun _m _hm => Continuous.intervalIntegrable (by unfold character; fun_prop) _ _)]
    simp_rw [natural_orthogonal]
  simp_rw [hi]
  simp
  rw [Finset.filter_eq_self.mpr (fun _ hn => Finset.mem_range.mp hn), Finset.card_range]

/-- The normalized finite-packet energy has exact unit angular mass. -/
theorem dirichlet_normalized (L : ℕ) (hL : 0 < L) :
    average (fun angle => ((dirichletEnergy L angle : ℝ) : ℂ)) = 1 := by
  have hp (angle : ℝ) : ((dirichletEnergy L angle : ℝ) : ℂ) =
      ((1 / (L : ℝ) : ℝ) : ℂ) * ((‖dirichletSum L angle‖ ^ 2 : ℝ) : ℂ) := by
    unfold dirichletEnergy
    push_cast
    ring
  simp_rw [hp]
  rw [average_const_mul, dirichlet_parseval]
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  push_cast
  field_simp

/-- The finite character polynomial is bounded pointwise by its actual number of terms. -/
theorem dirichlet_norm (L : ℕ) (angle : ℝ) : ‖dirichletSum L angle‖ ≤ (L : ℝ) := by
  calc
    ‖dirichletSum L angle‖ ≤ ∑ n ∈ Finset.range L, ‖character (n : ℝ) angle‖ := norm_sum_le _ _
    _ = _ := by simp [character_norm]

/-- The packet energy is nonnegative and bounded by L uniformly over angular position. -/
theorem dirichlet_energy_bounds (L : ℕ) (angle : ℝ) :
    0 ≤ dirichletEnergy L angle ∧ dirichletEnergy L angle ≤ (L : ℝ) := by
  constructor
  · unfold dirichletEnergy
    positivity
  · by_cases hL : L = 0
    · subst L
      simp [dirichletEnergy]
    · have hLc : 0 < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hL
      unfold dirichletEnergy
      apply (div_le_iff₀ hLc).mpr
      have hh := dirichlet_norm L angle
      nlinarith [norm_nonneg (dirichletSum L angle)]

/-- The exact packet energy is a continuous angular function. -/
theorem dirichlet_continuous (L : ℕ) : Continuous (dirichletEnergy L) := by
  unfold dirichletEnergy dirichletSum character
  fun_prop

/-- The interval character sum of length L agrees with the finite-packet polynomial. -/
theorem dirichlet_angular (L : ℕ) (angle : ℝ) :
    dirichletSum L angle = angularSum 0 ((L : ℤ) - 1) angle := by
  unfold dirichletSum
  simp_rw [character_nat]
  rw [angularSum_geometric]
  simp [character]

/-- On the positive half-period, finite-packet energy has the explicit inverse-square tail envelope. -/
theorem dirichlet_decay (L : ℕ) (hL : 0 < L) (angle : ℝ)
    (hangle : 0 < angle) (hpi : angle ≤ Real.pi) :
    dirichletEnergy L angle ≤ Real.pi ^ 2 / ((L : ℝ) * angle ^ 2) := by
  have hh := angularSum_nonresonant 0 ((L : ℤ) - 1) angle (angle / 2) (by positivity)
    (by rw [abs_of_pos (by positivity : 0 < angle / 2)])
    (by rw [abs_of_pos (by positivity : 0 < angle / 2)]; linarith)
  rw [← dirichlet_angular] at hh
  have hn : ‖dirichletSum L angle‖ ≤ Real.pi / angle := by
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hh
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ Real.pi / angle)).mpr hn
  unfold dirichletEnergy
  calc
    _ ≤ (Real.pi / angle) ^ 2 / (L : ℝ) := div_le_div_of_nonneg_right hsq (by positivity)
    _ = _ := by field_simp


/-- The energy retained outside a symmetric angular window. -/
def dirichletTail (L : ℕ) (δ angle : ℝ) : ℝ :=
  if δ < |angle| then dirichletEnergy L angle else 0

/-- Reversing the angular coordinate conjugates the actual finite-packet polynomial. -/
theorem dirichlet_conjugate (L : ℕ) (angle : ℝ) :
    dirichletSum L (-angle) = star (dirichletSum L angle) := by
  unfold dirichletSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [character_conj]
  unfold character
  congr 1
  push_cast
  ring

/-- The physical finite-packet energy is even in the angular coordinate. -/
theorem dirichlet_even (L : ℕ) (angle : ℝ) :
    dirichletEnergy L (-angle) = dirichletEnergy L angle := by
  unfold dirichletEnergy
  rw [dirichlet_conjugate, norm_star]

/-- The off-window packet energy retains the same even symmetry. -/
theorem dirichletTail_even (L : ℕ) (δ angle : ℝ) :
    dirichletTail L δ (-angle) = dirichletTail L δ angle := by
  simp only [dirichletTail, abs_neg, dirichlet_even]

/-- The actual off-window energy is integrable on every finite angular interval. -/
theorem dirichletTail_integrable (L : ℕ) (δ a b : ℝ) :
    IntervalIntegrable (dirichletTail L δ) MeasureTheory.volume a b := by
  have hf := (dirichlet_continuous L).intervalIntegrable (μ := MeasureTheory.volume) a b
  have hs : MeasurableSet {angle : ℝ | δ < |angle|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have heq : dirichletTail L δ = {angle : ℝ | δ < |angle|}.indicator (dirichletEnergy L) := by
    funext angle
    rfl
  rw [heq]
  exact ⟨hf.1.indicator hs, hf.2.indicator hs⟩

/-- The inverse-square envelope has its exact elementary integral away from zero. -/
theorem integral_inverse_square (δ : ℝ) (hδ : 0 < δ) (hδpi : δ ≤ Real.pi) :
    (∫ angle in δ..Real.pi, (1 : ℝ) / angle ^ 2) = 1 / δ - 1 / Real.pi := by
  have hzero : (0 : ℝ) ∉ Set.uIcc δ Real.pi := by
    rw [Set.uIcc_of_le hδpi]
    intro h
    exact (not_le_of_gt hδ) h.1
  have hh := integral_zpow (a := δ) (b := Real.pi) (n := (-2 : ℤ))
    (Or.inr ⟨by norm_num, hzero⟩)
  norm_num [zpow_neg, one_div] at hh
  simpa only [one_div, div_neg, div_one, neg_sub] using hh

/-- The positive off-window finite-packet energy has the explicit one-sided tail mass. -/
theorem dirichlet_positive_tail (L : ℕ) (hL : 0 < L) (δ : ℝ)
    (hδ : 0 < δ) (hδpi : δ ≤ Real.pi) :
    (∫ angle in δ..Real.pi, dirichletEnergy L angle) ≤
      Real.pi ^ 2 / ((L : ℝ) * δ) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc δ Real.pi := by
    rw [Set.uIcc_of_le hδpi]
    intro h
    exact (not_le_of_gt hδ) h.1
  have hinv : IntervalIntegrable (fun angle : ℝ => 1 / angle ^ 2)
      MeasureTheory.volume δ Real.pi := by
    simpa [zpow_neg, one_div] using
      intervalIntegral.intervalIntegrable_zpow (n := (-2 : ℤ)) (Or.inr hzero)
  have henv : IntervalIntegrable
      (fun angle : ℝ => Real.pi ^ 2 / ((L : ℝ) * angle ^ 2))
      MeasureTheory.volume δ Real.pi := by
    simpa only [div_mul_eq_div_div, mul_one_div] using
      hinv.const_mul (Real.pi ^ 2 / (L : ℝ))
  have hi := intervalIntegral.integral_mono_on hδpi
    ((dirichlet_continuous L).intervalIntegrable δ Real.pi) henv
    (fun angle hangle => dirichlet_decay L hL angle (lt_of_lt_of_le hδ hangle.1) hangle.2)
  have heq :
      (∫ angle in δ..Real.pi, Real.pi ^ 2 / ((L : ℝ) * angle ^ 2)) =
        (Real.pi ^ 2 / (L : ℝ)) * (1 / δ - 1 / Real.pi) := by
    have hp (angle : ℝ) : Real.pi ^ 2 / ((L : ℝ) * angle ^ 2) =
        (Real.pi ^ 2 / (L : ℝ)) * (1 / angle ^ 2) := by ring
    simp_rw [hp]
    rw [intervalIntegral.integral_const_mul, integral_inverse_square δ hδ hδpi]
  rw [heq] at hi
  apply hi.trans
  have hpos : 0 ≤ Real.pi ^ 2 / (L : ℝ) / Real.pi := by positivity
  have hmain : (Real.pi ^ 2 / (L : ℝ)) * (1 / δ - 1 / Real.pi) =
      Real.pi ^ 2 / ((L : ℝ) * δ) - Real.pi ^ 2 / (L : ℝ) / Real.pi := by ring
  rw [hmain]
  linarith

/-- Evenness identifies the full off-window mass with twice its positive half. -/
theorem dirichletTail_integral (L : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hδpi : δ ≤ Real.pi) :
    (∫ angle in -Real.pi..Real.pi, dirichletTail L δ angle) =
      2 * ∫ angle in δ..Real.pi, dirichletEnergy L angle := by
  have hneg : (∫ angle in -Real.pi..0, dirichletTail L δ angle) =
      ∫ angle in 0..Real.pi, dirichletTail L δ angle := by
    have hh := intervalIntegral.integral_comp_neg (f := dirichletTail L δ)
      (a := 0) (b := Real.pi)
    simp_rw [dirichletTail_even] at hh
    simpa only [neg_zero] using hh.symm
  have hinside : (∫ angle in 0..δ, dirichletTail L δ angle) = 0 := by
    have hh : (∫ angle in 0..δ, dirichletTail L δ angle) = ∫ _angle in 0..δ, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_uIoo
      intro angle hangle
      rw [Set.uIoo_of_le hδ] at hangle
      simp [dirichletTail, abs_of_pos hangle.1, not_lt_of_ge hangle.2.le]
    rw [hh]
    simp
  have houtside : (∫ angle in δ..Real.pi, dirichletTail L δ angle) =
      ∫ angle in δ..Real.pi, dirichletEnergy L angle := by
    apply intervalIntegral.integral_congr_uIoo
    intro angle hangle
    rw [Set.uIoo_of_le hδpi] at hangle
    simp [dirichletTail, abs_of_pos (lt_of_le_of_lt hδ hangle.1), hangle.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (dirichletTail_integrable L δ (-Real.pi) 0) (dirichletTail_integrable L δ 0 Real.pi),
    hneg]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (dirichletTail_integrable L δ 0 δ) (dirichletTail_integrable L δ δ Real.pi),
    hinside, zero_add, houtside]
  ring

/-- The normalized one-particle angular tail has the source's inverse-length concentration rate. -/
theorem dirichlet_tail_mass (L : ℕ) (hL : 0 < L) (δ : ℝ)
    (hδ : 0 < δ) (hδpi : δ ≤ Real.pi) :
    (1 / (2 * Real.pi)) * (∫ angle in -Real.pi..Real.pi, dirichletTail L δ angle) ≤
      Real.pi / ((L : ℝ) * δ) := by
  rw [dirichletTail_integral L δ hδ.le hδpi]
  have hh := dirichlet_positive_tail L hL δ hδ hδpi
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * (Real.pi ^ 2 / ((L : ℝ) * δ))) := by gcongr
    _ = _ := by field_simp

/-- A full real angular period carries exactly two pi units of packet energy. -/
theorem dirichlet_mass (L : ℕ) (hL : 0 < L) :
    (∫ angle in -Real.pi..Real.pi, dirichletEnergy L angle) = 2 * Real.pi := by
  have hh := dirichlet_normalized L hL
  unfold average at hh
  rw [intervalIntegral.integral_ofReal] at hh
  have hc : ((∫ angle in -Real.pi..Real.pi, dirichletEnergy L angle : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast at hh ⊢
    field_simp at hh
    exact hh
  exact_mod_cast hc

/-- Integer angular characters, and hence their finite-packet energy, have period two pi. -/
theorem dirichlet_periodic (L : ℕ) :
    Function.Periodic (dirichletEnergy L) (2 * Real.pi) := by
  have hp (n : ℕ) (angle : ℝ) :
      character (n : ℝ) (angle + 2 * Real.pi) = character (n : ℝ) angle := by
    unfold character
    have heq : Complex.I * ((n : ℝ) : ℂ) * ((angle + 2 * Real.pi : ℝ) : ℂ) =
        Complex.I * ((n : ℝ) : ℂ) * (angle : ℂ) +
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [heq, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  intro angle
  simp only [dirichletEnergy, dirichletSum, hp]

end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
