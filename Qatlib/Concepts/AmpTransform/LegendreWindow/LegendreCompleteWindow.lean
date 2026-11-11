/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.LegendreWindow.LegendreFullBoundaryAmpl

/-!
# Complete boundary of the Legendre approximation window

This module defines `aqLegendreWindow` and proves that a rational in the closed window is a
continued-fraction convergent exactly when it avoids the exceptional integer half-tie. It also
constructs the correct rounded numerator for modular period recovery, completing the boundary
analysis relevant to the Fourier recovery method of [Cornwell2014].

## Main statements

* `aqNext_legendre_window_complete`: A rational in the closed Legendre window is a
  continued-fraction convergent or has denominator one with ξ exactly one half below it.
* `aqNext_residue_window_complete`: When P² ≤ N and the modular distance is at most ⌊P/2⌋, the
  rounded numerator divided by P reduces to a continued-fraction convergent of y/N whose
  denominator divides P.
* `clause25_accepted`: Combines `clause25_endpoint` with the exact characterization of
  closed-window convergents by exclusion of the integer half-tie. See [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.AmpTransform.LegendreWindow

/-- The closed Legendre approximation condition |ξ−q| ≤ 1/(2 · den(q)²). -/
def aqLegendreWindow (ξ : ℝ) (q : ℚ) : Prop :=
  |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2)

/-- The distance from P · y to the nearest multiple of N, computed as the smaller modular
residue distance. -/
def aqResidueDistance (N P y : ℕ) : ℕ :=
  min ((P * y) % N) (N - (P * y) % N)

/-- The integer quotient of P · y by N, rounded up exactly when the remainder exceeds its
complementary distance. -/
def aqResidueNumerator (N P y : ℕ) : ℕ :=
  (P * y) / N + if (P * y) % N ≤ N - (P * y) % N then 0 else 1

/-- The combined closed-window contract: convergent recovery up to the exceptional integer
half-tie, failure of the unconditional closed-window claim, and recovery using the rounded
modular numerator. -/
def clause25_endpoint : Prop :=
  (∀ (ξ : ℝ) (a : ℤ) (b : ℕ) (hb : 0 < b) (hc : Nat.Coprime b a.natAbs),
      |ξ - (a : ℝ) / (b : ℝ)| ≤ 1 / (2 * (b : ℝ) ^ 2) →
      (∃ n : ℕ, ((a : ℚ) / (b : ℚ)) = ξ.convergent n) ∨
        (b = 1 ∧ ξ = (a : ℝ) - 1 / 2))
  ∧ (∀ (ξ : ℝ) (q : ℚ), aqLegendreWindow ξ q →
      (∃ n : ℕ, q = ξ.convergent n) ∨
        (q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2))
  ∧ (¬ ∀ (ξ : ℝ) (q : ℚ), aqLegendreWindow ξ q → ∃ n : ℕ, q = ξ.convergent n)
  ∧ (∀ (N P y : ℕ) (hN : 0 < N) (hP : 0 < P) (hsize : P ^ 2 ≤ N),
      aqResidueDistance N P y ≤ P / 2 →
      ∃ a b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ b ∣ P ∧
        ((a : ℚ) / b = (aqResidueNumerator N P y : ℚ) / P) ∧
        ∃ n : ℕ, ((a : ℚ) / b) = ((y : ℝ) / N).convergent n)

/-- The claim that every rational in the closed Legendre window is a continued-fraction
convergent is false. -/
theorem aqNext_legendre_window_fails_at_tie :
    ¬ (∀ (ξ : ℝ) (q : ℚ), aqLegendreWindow ξ q → ∃ n : ℕ, q = ξ.convergent n) := by
  intro h
  obtain ⟨n, hn⟩ := h (1 / 2) 1 (by
    unfold aqLegendreWindow
    norm_num)
  cases n with
  | zero =>
    rw [Real.convergent_zero] at hn
    norm_num at hn
  | succ n =>
    rw [Real.convergent_succ] at hn
    norm_num [Int.fract] at hn
    have hi : (2 : ℝ).convergent n = 2 := Real.convergent_of_int (ξ := 2) n
    rw [hi] at hn
    norm_num at hn

/-- A reduced fraction a/b with b ≥ 2 in the closed Legendre window is a continued-fraction
convergent of ξ. -/
theorem aqNext_legendre_window_den_ge_two (ξ : ℝ) (a : ℤ) (b : ℕ) (hb : 2 ≤ b)
    (hc : Nat.Coprime b a.natAbs)
    (h : |ξ - (a : ℝ) / (b : ℝ)| ≤ 1 / (2 * (b : ℝ) ^ 2)) :
    ∃ n : ℕ, ((a : ℚ) / (b : ℚ)) = ξ.convergent n := by
  have hAss : Real.ContfracLegendre.Ass ξ a ((b : ℕ) : ℤ) := by
    refine ⟨Int.isCoprime_iff_nat_coprime.mpr (by simpa using hc.symm), ?_, ?_⟩
    · intro hb1
      omega
    · have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show (0 : ℕ) < b by omega)
      simp only [Int.cast_natCast]
      have hconv : |ξ - ↑a / ↑b| = |ξ - (a : ℝ) / (b : ℝ)| := by rfl
      rw [hconv]
      have hkey : (b : ℝ) * (2 * (b : ℝ) - 1) < 2 * (b : ℝ) ^ 2 := by
        nlinarith [hbR, hbpos]
      have hpos : (0 : ℝ) < (b : ℝ) * (2 * (b : ℝ) - 1) := by nlinarith [hbR, hbpos]
      refine lt_of_le_of_lt h ?_
      rw [← one_div]
      exact one_div_lt_one_div_of_lt hpos hkey
  obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent' (ξ := ξ) (v := b) (u := a) hAss
  refine ⟨n, ?_⟩
  have hq : ((a : ℤ) : ℚ) / ((b : ℕ) : ℚ) = (a : ℚ) / (b : ℚ) := by norm_num
  rw [hq] at hn
  exact hn

/-- An integer within distance 1/2 of ξ is a continued-fraction convergent unless ξ is exactly
one half below it. -/
theorem aqNext_legendre_integer_window (ξ : ℝ) (u : ℤ) (h : |ξ - (u : ℝ)| ≤ 1 / 2) :
    (∃ n : ℕ, (u : ℚ) = ξ.convergent n) ∨ ξ = (u : ℝ) - 1 / 2 := by
  by_cases htie : ξ = (u : ℝ) - 1 / 2
  · exact Or.inr htie
  · have hab := abs_le.mp h
    have hlo : (u : ℝ) - 1 / 2 < ξ := by
      have h1 : (u : ℝ) - 1 / 2 ≤ ξ := by linarith [hab.1]
      refine lt_of_le_of_ne h1 ?_
      intro hc
      apply htie
      linarith
    have hAss : Real.ContfracLegendre.Ass ξ u ((1 : ℕ) : ℤ) := by
      refine ⟨Int.isCoprime_iff_nat_coprime.mpr (Nat.coprime_one_right _), ?_, ?_⟩
      · intro hb1
        have : -(1 / 2) < ξ - ↑u := by linarith [hlo]
        exact this
      · simp only [Int.cast_natCast]
        norm_num
        linarith [h]
    obtain ⟨n, hn⟩ := Real.exists_rat_eq_convergent' (ξ := ξ) (v := 1) (u := u) hAss
    refine Or.inl ⟨n, ?_⟩
    have hq : ((u : ℤ) : ℚ) / ((1 : ℕ) : ℚ) = (u : ℚ) := by norm_num
    rw [hq] at hn
    exact hn

/-- A rational in the closed Legendre window is a continued-fraction convergent or has
denominator one with ξ exactly one half below it. -/
theorem aqNext_legendre_window_complete (ξ : ℝ) (q : ℚ) (h : aqLegendreWindow ξ q) :
    (∃ n : ℕ, q = ξ.convergent n) ∨
      (q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2) := by
  have hw : |ξ - (q : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) := h
  by_cases hd1 : q.den = 1
  · have hhalf : |ξ - (q : ℝ)| ≤ 1 / 2 := by
      rw [hd1] at hw
      norm_num at hw ⊢
      exact hw
    have hqd := q.num_div_den
    rw [hd1] at hqd
    norm_num at hqd
    have hq : (q.num : ℚ) = q := hqd
    have hu : (q : ℝ) = (q.num : ℝ) := by
      have h1 := congrArg (fun r : ℚ => (r : ℝ)) hq
      push_cast at h1
      rw [h1]
    have hhalf' : |ξ - (q.num : ℝ)| ≤ 1 / 2 := by rw [← hu]; exact hhalf
    rcases aqNext_legendre_integer_window ξ q.num hhalf' with ⟨⟨n, hn⟩⟩ | htie
    · refine Or.inl ⟨n, ?_⟩
      rw [← hq]
      exact hn
    · refine Or.inr ⟨hd1, ?_⟩
      rw [hu]
      exact htie
  · have hd2 : 2 ≤ q.den := by
      have h1 : q.den = 0 ∨ q.den = 1 ∨ 2 ≤ q.den := by omega
      rcases h1 with h | h | h
      · exact absurd h (Nat.ne_of_gt q.den_pos)
      · exact absurd h hd1
      · exact h
    refine Or.inl ?_
    have hq : q = (q.num : ℚ) / (q.den : ℚ) := by
      have h1 := q.num_div_den
      exact h1.symm
    have hcop : Nat.Coprime q.den q.num.natAbs :=
      (Int.natAbs_natCast q.den ▸ q.reduced).symm
    have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    have hden2 : (2 : ℝ) ≤ q.den := by exact_mod_cast hd2
    have hqd := q.num_div_den
    have hqR : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
      have h1 := congrArg (fun r : ℚ => (r : ℝ)) hqd
      push_cast at h1
      rw [h1]
    have hdist : |ξ - (q.num : ℝ) / (q.den : ℝ)| ≤ 1 / (2 * (q.den : ℝ) ^ 2) := by
      rw [hqR]
      exact hw
    obtain ⟨n, hn⟩ := aqNext_legendre_window_den_ge_two ξ q.num q.den hd2 hcop hdist
    refine ⟨n, ?_⟩
    rw [hq]
    exact hn

/-- When P² ≤ N and the modular distance is at most ⌊P/2⌋, the rounded numerator divided by P
reduces to a continued-fraction convergent of y/N whose denominator divides P. -/
theorem aqNext_residue_window_complete {N P y : ℕ} (hN : 0 < N) (hP : 0 < P)
    (hsize : P ^ 2 ≤ N)
    (hd : aqResidueDistance N P y ≤ P / 2) :
    ∃ a b : ℕ, 0 < b ∧ Nat.Coprime a b ∧ b ∣ P ∧
      ((a : ℚ) / b = (aqResidueNumerator N P y : ℚ) / P) ∧
      ∃ n : ℕ, ((a : ℚ) / b) = ((y : ℝ) / N).convergent n := by
  have hrlt : (P * y) % N < N := Nat.mod_lt _ hN

  let r : ℕ := (P * y) % N
  let t : ℕ := (P * y) / N
  have he : (P : ℝ) * y = (N : ℝ) * t + r := by
    have hn := Nat.div_add_mod (P * y) N
    exact_mod_cast hn.symm
  have hnum : aqResidueNumerator N P y = t + (if r ≤ N - r then 0 else 1) := by
    simp [aqResidueNumerator, r, t]
  have hdist : |(P : ℝ) * y - (N : ℝ) * aqResidueNumerator N P y| =
      (aqResidueDistance N P y : ℝ) := by
    by_cases hh : r ≤ N - r
    · rw [hnum, if_pos hh, add_zero]
      have hz : (P : ℝ) * y - (N : ℝ) * t = r := by linarith
      rw [hz, abs_of_nonneg (Nat.cast_nonneg _)]
      simp [aqResidueDistance, r, hh]
    · rw [hnum, if_neg hh, Nat.cast_add, Nat.cast_one]
      have hle : N - r ≤ r := by omega
      have hcastsub : ((N - r : ℕ) : ℝ) = (N : ℝ) - r := by
        exact_mod_cast (Nat.cast_sub (by omega : r ≤ N))
      have hz : (P : ℝ) * y - (N : ℝ) * ((t : ℝ) + 1) = (r : ℝ) - N := by
        nlinarith
      have hrR : (r : ℝ) ≤ N := by exact_mod_cast hrlt.le
      rw [hz, abs_of_nonpos (by linarith)]
      have hdist : (aqResidueDistance N P y : ℝ) = (N : ℝ) - r := by
        simp [aqResidueDistance, r, hle, hcastsub]
      rw [hdist]
      ring
  have hwin : |(P : ℝ) * y - (N : ℝ) * aqResidueNumerator N P y| ≤ (P : ℝ) / 2 := by
    rw [hdist]
    have hh : 2 * aqResidueDistance N P y ≤ P := by
      have h1 : 2 * aqResidueDistance N P y ≤ 2 * (P / 2) := by
        have := Nat.mul_le_mul_left 2 hd
        omega
      omega
    have hhR : 2 * ((aqResidueDistance N P y : ℕ) : ℝ) ≤ P := by exact_mod_cast hh
    linarith
  obtain ⟨hdiv, n, hn⟩ := Qatlib.Concepts.AmpTransform.LegendreWindow.legendre_correct_numerator
    N P y (aqResidueNumerator N P y) hN hP hsize hwin

  set q : ℚ := (aqResidueNumerator N P y : ℚ) / P with hq
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hnum' : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hcast : (q.num.natAbs : ℚ) = q.num := by
    have hh : (q.num.natAbs : ℤ) = q.num := by rw [Int.natCast_natAbs, abs_of_nonneg hnum']
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hh
  have heq : (q.num.natAbs : ℚ) / q.den = q := by rw [hcast, q.num_div_den]
  refine ⟨q.num.natAbs, q.den, q.den_pos, q.reduced, hdiv, ?_, n, ?_⟩
  · show (q.num.natAbs : ℚ) / q.den = (aqResidueNumerator N P y : ℚ) / P
    rw [heq, hq]
  · show (q.num.natAbs : ℚ) / q.den = ((y : ℝ) / N).convergent n
    rw [heq]
    exact hn

/-- Proves the combined closed-window and modular-numerator contract `clause25_endpoint`. -/
theorem clause25_endpoint_holds : clause25_endpoint := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ξ a b hb hc hwin
    by_cases hb1 : b = 1
    · have hhalf : |ξ - (a : ℝ)| ≤ 1 / 2 := by
        rw [hb1] at hwin
        norm_num at hwin ⊢
        exact hwin
      rcases aqNext_legendre_integer_window ξ a hhalf with ⟨⟨n, hn⟩⟩ | htie
      · refine Or.inl ⟨n, ?_⟩
        rw [hb1]
        simpa using hn
      · refine Or.inr ⟨hb1, ?_⟩
        exact htie
    · have hb2 : 2 ≤ b := by omega
      refine Or.inl ?_
      obtain ⟨n, hn⟩ := aqNext_legendre_window_den_ge_two ξ a b hb2 hc hwin
      exact ⟨n, hn⟩
  · intro ξ q h
    exact aqNext_legendre_window_complete ξ q h
  · exact aqNext_legendre_window_fails_at_tie
  · intro N P y hN hP hsize hd
    exact aqNext_residue_window_complete hN hP hsize hd

/-- No continued-fraction convergent of u−1/2 equals the integer u. -/
theorem aqNext_legendre_integer_tie_ne_convergent (u : ℤ) (n : ℕ) :
    (u : ℚ) ≠ ((u : ℝ) - 1 / 2).convergent n := by
  have hfloor : ⌊(u : ℝ) - 1 / 2⌋ = u - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  have hfract : Int.fract ((u : ℝ) - 1 / 2) = 1 / 2 := by
    unfold Int.fract
    rw [hfloor]
    push_cast
    ring
  cases n with
  | zero =>
    rw [Real.convergent_zero, hfloor]
    push_cast
    linarith
  | succ n =>
    rw [Real.convergent_succ, hfloor, hfract]
    have hinv : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    rw [hinv]
    have htwo : (2 : ℝ).convergent n = 2 := Real.convergent_of_int (ξ := 2) n
    rw [htwo]
    push_cast
    norm_num
    linarith

/-- Within the closed Legendre window, q is a continued-fraction convergent exactly when the
exceptional denominator-one half-tie does not occur. -/
theorem aqNext_legendre_window_convergent_iff (ξ : ℝ) (q : ℚ)
    (h : aqLegendreWindow ξ q) :
    (∃ n : ℕ, q = ξ.convergent n) ↔
      ¬ (q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2) := by
  constructor
  · rintro ⟨n, hn⟩ ⟨hd, htie⟩
    have hq : (q.num : ℚ) = q := by
      simpa [hd] using q.num_div_den
    have hqR : (q.num : ℝ) = (q : ℝ) := by
      exact_mod_cast hq
    apply aqNext_legendre_integer_tie_ne_convergent q.num n
    rw [hqR, ← htie, hq]
    exact hn
  · intro hnot
    rcases aqNext_legendre_window_complete ξ q h with hconv | htie
    · exact hconv
    · exact False.elim (hnot htie)

/-- Combines `clause25_endpoint` with the exact characterization of closed-window convergents by
exclusion of the integer half-tie. See [Cornwell2014]. -/
theorem clause25_accepted :
    clause25_endpoint ∧
    (∀ (ξ : ℝ) (q : ℚ), aqLegendreWindow ξ q →
      ((∃ n : ℕ, q = ξ.convergent n) ↔
        ¬ (q.den = 1 ∧ ξ = (q : ℝ) - 1 / 2))) := by
  exact ⟨clause25_endpoint_holds, aqNext_legendre_window_convergent_iff⟩

end Qatlib.Concepts.AmpTransform.LegendreWindow
