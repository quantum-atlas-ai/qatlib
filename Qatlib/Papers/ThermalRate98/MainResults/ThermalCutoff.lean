/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.PhysicalRateFormula

/-!
# Weighted thermal cutoff bounds

This module bounds the high-energy contribution to the finite spectral correlation sum in
[LidarWang1999]. With positive inverse temperature, nonnegative energies, and uniform bounds on
energy gaps and overlaps, each tail summand is controlled by an exponential cutoff factor times
the squared gap and overlap bounds.

`weighted_tail_bound` includes the number of index pairs, and `weighted_cutoff_epsilon` gives a
sufficient logarithmic cutoff for a prescribed error. Further identities describe tail
multiplicity, strict positivity of Boltzmann tails, and the decomposition into active and tail
contributions.

## Main statements

* `eq16Summand_norm_tail_le`: bounds an individual summand with at least one energy above the
  cutoff.
* `weighted_tail_bound`: bounds the sum of tail norms including the dimension factor.
* `weighted_cutoff_epsilon`: gives a sufficient cutoff for a positive error tolerance.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The pairwise thermal weight `exp (-β * (E n + E m) / 2)`. -/
def boltzmannPair (β : ℝ) (E : I → ℝ) (n m : I) : ℝ :=
  Real.exp (-(β * (E n + E m)) / 2)

/-- The spectral correlation summand consisting of a thermal factor, an oscillatory phase, a
squared energy gap, and a squared overlap norm. -/
def eq16Summand (β t ħ : ℝ) (E : I → ℝ) (S : I → I → ℂ) (n m : I) : ℂ :=
  Complex.exp (-(β * (E n + E m)) / 2) *
    Complex.exp (Complex.I * ((E m - E n) * t / ħ)) *
    (((E n - E m : ℝ) : ℂ) ^ 2) * (Complex.normSq (S n m) : ℂ)

/-- The norm of a spectral correlation summand is its real thermal weight times the squared
energy gap and squared overlap norm. -/
theorem eq16Summand_norm (β t ħ : ℝ) (E : I → ℝ) (S : I → I → ℂ) (n m : I) :
    ‖eq16Summand β t ħ E S n m‖ =
      Real.exp (-(β * (E n + E m)) / 2) * (E n - E m) ^ 2 * ‖S n m‖ ^ 2 := by
  unfold eq16Summand
  rw [norm_mul, norm_mul, norm_mul]
  have hthermal :
      ‖Complex.exp (-(β * (E n + E m)) / 2)‖ =
        Real.exp (-(β * (E n + E m)) / 2) := by
    rw [Complex.norm_exp]
    simp
  have hphase : ‖Complex.exp (Complex.I * ((E m - E n) * t / ħ))‖ = 1 := by
    rw [show Complex.I * ((E m - E n) * t / ħ) =
        ((((E m - E n) * t / ħ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hgap : ‖(((E n - E m : ℝ) : ℂ) ^ 2)‖ = (E n - E m) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hov : ‖(Complex.normSq (S n m) : ℂ)‖ = ‖S n m‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq]
  rw [hthermal, hphase, hgap, hov]
  ring

/-- The pairwise thermal weight is symmetric in its two indices. -/
theorem boltzmannPair_comm (β : ℝ) (E : I → ℝ) (n m : I) :
    boltzmannPair β E n m = boltzmannPair β E m n := by
  unfold boltzmannPair
  rw [add_comm]

/-- For positive inverse temperature and nonnegative energies, a pair whose first energy is at
least `E_c` has thermal weight at most `exp (-β * E_c / 2)`. -/
theorem boltzmannPair_tail_le (β E_c : ℝ) (hβ : 0 < β) (E : I → ℝ)
    (hE0 : ∀ k, 0 ≤ E k) (n m : I) (hn : E_c ≤ E n) :
    boltzmannPair β E n m ≤ Real.exp (-(β * E_c) / 2) := by
  unfold boltzmannPair
  apply Real.exp_le_exp.2
  have hm : 0 ≤ E m := hE0 m
  nlinarith

/-- The finite set of indices with energy at least the cutoff `E_c`. -/
def energyTail (E : I → ℝ) (E_c : ℝ) : Finset I := by
  classical
  exact Finset.univ.filter (fun k => E_c ≤ E k)

/-- The finite set of index pairs having at least one energy at or above the cutoff `E_c`. -/
def tailPairs (E : I → ℝ) (E_c : ℝ) : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun p => E_c ≤ E p.1 ∨ E_c ≤ E p.2)

/-- For positive inverse temperature and nonnegative energies, a summand with at least one
energy at or above the cutoff is bounded in norm by the cutoff exponential times the squared
uniform gap and overlap bounds. See [LidarWang1999]. -/
theorem eq16Summand_norm_tail_le (β t ħ E_c gap ov : ℝ) (hβ : 0 < β)
    (E : I → ℝ) (hE0 : ∀ k, 0 ≤ E k) (S : I → I → ℂ)
    (hgap : ∀ n m, |E n - E m| ≤ gap) (hov : ∀ n m, ‖S n m‖ ≤ ov)
    (n m : I) (h : E_c ≤ E n ∨ E_c ≤ E m) :
    ‖eq16Summand β t ħ E S n m‖ ≤ Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
  rw [eq16Summand_norm]
  have hb : boltzmannPair β E n m ≤ Real.exp (-(β * E_c) / 2) := by
    rcases h with h | h
    · exact boltzmannPair_tail_le β E_c hβ E hE0 n m h
    · rw [boltzmannPair_comm]
      exact boltzmannPair_tail_le β E_c hβ E hE0 m n h
  have hb0 : 0 ≤ boltzmannPair β E n m := by
    unfold boltzmannPair; positivity
  have hgap0 : 0 ≤ gap := le_trans (abs_nonneg _) (hgap n m)
  have hov0 : 0 ≤ ov := le_trans (norm_nonneg _) (hov n m)
  have hsq : (E n - E m) ^ 2 ≤ gap ^ 2 := by
    have hg : |gap| = gap := abs_of_nonneg hgap0
    rw [sq_le_sq, hg]
    exact hgap n m
  have hovsq : ‖S n m‖ ^ 2 ≤ ov ^ 2 := by
    have hnn : 0 ≤ ‖S n m‖ := norm_nonneg _
    nlinarith [hov n m]
  calc boltzmannPair β E n m * (E n - E m) ^ 2 * ‖S n m‖ ^ 2
      ≤ Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
        apply mul_le_mul
        · exact mul_le_mul hb hsq (sq_nonneg _) (le_trans hb0 hb)
        · exact hovsq
        · positivity
        · apply mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- For positive inverse temperature, nonnegative energies, and uniform gap and overlap bounds,
the sum of tail summand norms is at most the squared dimension times the cutoff exponential
and the squared bounds. See [LidarWang1999]. -/
theorem weighted_tail_bound (β t ħ E_c gap ov : ℝ) (hβ : 0 < β)
    (E : I → ℝ) (hE0 : ∀ k, 0 ≤ E k) (S : I → I → ℂ)
    (hgap : ∀ n m, |E n - E m| ≤ gap) (hov : ∀ n m, ‖S n m‖ ≤ ov) :
    (∑ p ∈ tailPairs E E_c, ‖eq16Summand β t ħ E S p.1 p.2‖) ≤
      (Fintype.card I : ℝ) ^ 2 * Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
  classical
  have hconst : 0 ≤ Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
    apply mul_nonneg
    · exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    · exact sq_nonneg _
  have hmem : ∀ p : I × I, p ∈ tailPairs E E_c ↔ (E_c ≤ E p.1 ∨ E_c ≤ E p.2) := by
    intro p
    unfold tailPairs
    rw [Finset.mem_filter]
    simp
  calc (∑ p ∈ tailPairs E E_c, ‖eq16Summand β t ħ E S p.1 p.2‖)
      ≤ ∑ _p ∈ tailPairs E E_c, Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact eq16Summand_norm_tail_le β t ħ E_c gap ov hβ E hE0 S hgap hov p.1 p.2
          ((hmem p).mp hp)
    _ = (tailPairs E E_c).card * (Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card I : ℝ) ^ 2 * (Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2) := by
        have hcard : (tailPairs E E_c).card ≤ Fintype.card (I × I) :=
          Finset.card_le_univ _
        have hc : (Fintype.card (I × I) : ℝ) = (Fintype.card I : ℝ) ^ 2 := by
          rw [Fintype.card_prod, Nat.cast_mul, sq]
        have hcard' : ((tailPairs E E_c).card : ℝ) ≤ (Fintype.card I : ℝ) ^ 2 := by
          rw [← hc]; exact_mod_cast hcard
        exact mul_le_mul_of_nonneg_right hcard' hconst
    _ = (Fintype.card I : ℝ) ^ 2 * Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
        ring

/-- Under the positivity and uniform bound hypotheses, the stated logarithmic lower bound on
`E_c` makes the sum of tail summand norms at most positive `ε`. See [LidarWang1999]. -/
theorem weighted_cutoff_epsilon (β t ħ E_c gap ov ε : ℝ) (hβ : 0 < β) (hε : 0 < ε)
    (hgap0 : 0 < gap) (hov0 : 0 < ov) [Nonempty I]
    (E : I → ℝ) (hE0 : ∀ k, 0 ≤ E k) (S : I → I → ℂ)
    (hgap : ∀ n m, |E n - E m| ≤ gap) (hov : ∀ n m, ‖S n m‖ ≤ ov)
    (hlog : (2 / β) * Real.log
      ((Fintype.card I : ℝ) ^ 2 * gap ^ 2 * ov ^ 2 / ε) ≤ E_c) :
    (∑ p ∈ tailPairs E E_c, ‖eq16Summand β t ħ E S p.1 p.2‖) ≤ ε := by
  classical
  set A : ℝ := (Fintype.card I : ℝ) ^ 2 * gap ^ 2 * ov ^ 2 with hA
  have hN : 0 < (Fintype.card I : ℝ) := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ‹Nonempty I›
    exact_mod_cast this
  have hApos : 0 < A := by
    rw [hA]
    exact mul_pos (mul_pos (pow_pos hN 2) (pow_pos hgap0 2)) (pow_pos hov0 2)
  have htail := weighted_tail_bound β t ħ E_c gap ov hβ E hE0 S hgap hov
  refine le_trans htail ?_

  have hkey : Real.exp (-(β * E_c) / 2) ≤ ε / A := by
    rw [← Real.exp_log (div_pos hε hApos)]
    apply Real.exp_le_exp.2
    rw [Real.log_div hε.ne' hApos.ne']
    have hmul : Real.log (A / ε) ≤ β * E_c / 2 := by
      have hpos : 0 < β / 2 := by linarith
      calc Real.log (A / ε) = (β / 2) * (2 / β * Real.log (A / ε)) := by
            field_simp
        _ ≤ (β / 2) * E_c := mul_le_mul_of_nonneg_left hlog hpos.le
        _ = β * E_c / 2 := by ring
    have hsplit : Real.log (A / ε) = Real.log A - Real.log ε :=
      Real.log_div hApos.ne' hε.ne'
    rw [hsplit] at hmul
    linarith
  have hAle : A * Real.exp (-(β * E_c) / 2) ≤ A * (ε / A) :=
    mul_le_mul_of_nonneg_left hkey hApos.le
  have hright : A * (ε / A) = ε := by
    field_simp
  have hleft : A * Real.exp (-(β * E_c) / 2) =
      (Fintype.card I : ℝ) ^ 2 * Real.exp (-(β * E_c) / 2) * gap ^ 2 * ov ^ 2 := by
    rw [hA]; ring
  rw [hleft, hright] at hAle
  exact hAle

/-- The sum of `k` identical Boltzmann weights equals `k` times that weight. See
[LidarWang1999]. -/
theorem boltzmann_tail_multiplicity (k : ℕ) (β E₀ : ℝ) :
    (∑ _n : Fin k, Real.exp (-(β * E₀))) = (k : ℝ) * Real.exp (-(β * E₀)) := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- For positive inverse temperature and positive energy, the Boltzmann weight is strictly
between zero and one. -/
theorem boltzmann_tail_not_zero (β E₀ : ℝ) (hβ : 0 < β) (hE : 0 < E₀) :
    0 < Real.exp (-(β * E₀)) ∧ Real.exp (-(β * E₀)) < 1 := by
  constructor
  · exact Real.exp_pos _
  · rw [← Real.exp_zero, Real.exp_lt_exp]
    nlinarith

/-- In the two-level example, the tail over the true index equals `exp (-β * E₀ / 2)` and lies
strictly between zero and one for positive `β` and `E₀`. -/
theorem boltzmann_tail_example (β E₀ : ℝ) (hβ : 0 < β) (hE : 0 < E₀) :
    (∑ m ∈ Finset.univ.filter (fun b : Bool => b = true),
        Real.exp (-(β * ((if m then E₀ else 0) + (0 : ℝ))) / 2)) =
      Real.exp (-(β * E₀) / 2) ∧
    0 < Real.exp (-(β * E₀) / 2) ∧ Real.exp (-(β * E₀) / 2) < 1 := by
  have hset : (Finset.univ.filter (fun b : Bool => b = true)) = ({true} : Finset Bool) := by
    ext b; cases b <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hset, Finset.sum_singleton]; simp
  · exact Real.exp_pos _
  · rw [← Real.exp_zero, Real.exp_lt_exp]; nlinarith

/-- The sum over pairs outside the thermal tail plus the sum over tail pairs equals the sum over
all pairs. See [LidarWang1999]. -/
theorem tail_add_active (f : I × I → ℝ) (E : I → ℝ) (E_c : ℝ) :
    (∑ p ∈ (Finset.univ \ tailPairs E E_c), f p) +
      (∑ p ∈ tailPairs E E_c, f p) = ∑ p, f p := by
  classical
  simp

end Qatlib.Papers.ThermalRate98.MainResults
