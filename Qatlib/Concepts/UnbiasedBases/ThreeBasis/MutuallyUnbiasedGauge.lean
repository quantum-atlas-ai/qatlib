/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MutuallyUnbiased

/-!
# Phase gauges for mutually unbiased bases

This module defines column and coordinate rephasing and proves that phases of unit modulus
preserve mutually unbiased families. The normalizations `normalize_first_row` and
`normalize_phase_gauge` choose constant positive entries while retaining a distinguished
computational basis, in the setting of [Sun2026].

## Main statements

* `isFamily_rephaseColumns`: independent unit phases on columns preserve mutual unbiasedness.
* `isFamily_rephaseCoordinates`: a common coordinate rephasing preserves mutual unbiasedness.
* `normalize_phase_gauge`: normalizes a selected row in every other basis and a selected column
  in one of them.

## References

* [Sun, 2026][Sun2026]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis

variable {d k : ℕ}

/-- Multiplies column `j` of basis `r` by the complex scalar `c r j`. -/
noncomputable def rephaseColumns (c : Fin k → Fin d → ℂ)
    (B : Fin k → Fin d → QState (Fin d)) : Fin k → Fin d → QState (Fin d) :=
  fun r j i => c r j * B r j i

/-- Scaling two vectors by `a` and `b` multiplies their inner product by `conj a * b`. -/
theorem inner_rephase (a b : ℂ) (ψ φ : QState (Fin d)) :
    Qatlib.Foundations.PureStateMath.Inner (fun i => a * ψ i) (fun i => b * φ i) =
      ((starRingEnd ℂ) a * b) * Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  rw [inner_apply, inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  ring

/-- Multiplying each column by a scalar of squared modulus one preserves a mutually unbiased
family. -/
theorem isFamily_rephaseColumns (c : Fin k → Fin d → ℂ)
    (hc : ∀ r j, Complex.normSq (c r j) = 1)
    (B : Fin k → Fin d → QState (Fin d)) (hB : IsFamily B) :
    IsFamily (rephaseColumns c B) := by
  constructor
  · intro r i j
    change Qatlib.Foundations.PureStateMath.Inner (fun t => c r i * B r i t)
        (fun t => c r j * B r j t) = _
    rw [inner_rephase, hB.1 r i j]
    by_cases hij : i = j
    · subst j
      simp [← Complex.normSq_eq_conj_mul_self, hc]
    · simp [hij]
  · intro r s hrs i j
    change Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (fun t => c r i * B r i t)
      (fun t => c s j * B s j t)) = _
    rw [inner_rephase, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_conj, hc, hc, one_mul, one_mul]
    exact hB.2 r s hrs i j

/-- Multiplies coordinate `i` of every column by the common scalar `ρ i`. -/
noncomputable def rephaseCoordinates (ρ : Fin d → ℂ)
    (B : Fin k → Fin d → QState (Fin d)) : Fin k → Fin d → QState (Fin d) :=
  fun r j i => ρ i * B r j i

/-- Multiplying both vectors coordinatewise by the same scalars of squared modulus one preserves
their inner product. -/
theorem inner_rephaseCoordinates (ρ : Fin d → ℂ)
    (hρ : ∀ i, Complex.normSq (ρ i) = 1) (ψ φ : QState (Fin d)) :
    Qatlib.Foundations.PureStateMath.Inner (fun i => ρ i * ψ i) (fun i => ρ i * φ i) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  rw [inner_apply, inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  calc
    (starRingEnd ℂ) (ρ i) * (starRingEnd ℂ) (ψ i) * (ρ i * φ i)
        = ((starRingEnd ℂ) (ρ i) * ρ i) *
          ((starRingEnd ℂ) (ψ i) * φ i) := by ring
    _ = _ := by rw [← Complex.normSq_eq_conj_mul_self, hρ]; simp

/-- A common coordinatewise rephasing by scalars of squared modulus one preserves a mutually
unbiased family. -/
theorem isFamily_rephaseCoordinates (ρ : Fin d → ℂ)
    (hρ : ∀ i, Complex.normSq (ρ i) = 1)
    (B : Fin k → Fin d → QState (Fin d)) (hB : IsFamily B) :
    IsFamily (rephaseCoordinates ρ B) := by
  constructor
  · intro r i j
    change Qatlib.Foundations.PureStateMath.Inner (fun t => ρ t * B r i t)
        (fun t => ρ t * B r j t) = _
    rw [inner_rephaseCoordinates ρ hρ]
    exact hB.1 r i j
  · intro r s hrs i j
    change Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (fun t => ρ t * B r i t)
      (fun t => ρ t * B s j t)) = _
    rw [inner_rephaseCoordinates ρ hρ]
    exact hB.2 r s hrs i j

/-- The scalar `conj z / q` used to align a complex number of modulus `q` with the positive real
axis. -/
noncomputable def alignPhase (q : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) z / (q : ℂ)

/-- If `q > 0` and `z` has squared modulus `q ^ 2`, then `alignPhase q z` has squared modulus
one. -/
theorem alignPhase_normSq {q : ℝ} (hq : 0 < q) {z : ℂ}
    (hz : Complex.normSq z = q ^ 2) : Complex.normSq (alignPhase q z) = 1 := by
  rw [alignPhase, Complex.normSq_div, Complex.normSq_conj,
    Complex.normSq_ofReal, hz]
  simp [pow_two, ne_of_gt hq]

/-- If `q > 0` and `z` has squared modulus `q ^ 2`, multiplying `z` by `alignPhase q z` gives
`q`. -/
theorem alignPhase_mul {q : ℝ} (hq : 0 < q) {z : ℂ}
    (hz : Complex.normSq z = q ^ 2) : alignPhase q z * z = (q : ℂ) := by
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hq)
  rw [alignPhase, div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
    hz, Complex.ofReal_pow]
  simp [pow_two, hqC]

/-- For positive `q`, the alignment phase of the real complex number `q` is one. -/
theorem alignPhase_ofReal {q : ℝ} (hq : 0 < q) :
    alignPhase q (q : ℂ) = 1 := by
  simp [alignPhase, ne_of_gt hq]

end Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB
variable {d k : ℕ}

/-- For a mutually unbiased family containing the computational basis and positive `q` with `q ^
2 = 1 / d`, there exists such a family retaining that basis with coordinate `a` of every
other column equal to `q`. -/
theorem normalize_first_row
    (B : Fin k → Fin d → QState (Fin d)) (hB : IsFamily B)
    (r₀ : Fin k) (a : Fin d) (hzero : ∀ j, B r₀ j = Qatlib.Foundations.PureStateMath.Ket j)
    (q : ℝ) (hq : 0 < q) (hq2 : q ^ 2 = (1 : ℝ) / d) :
    ∃ C : Fin k → Fin d → QState (Fin d),
      IsFamily C ∧ (∀ j, C r₀ j = Qatlib.Foundations.PureStateMath.Ket j) ∧
      ∀ r, r ≠ r₀ → ∀ j, C r j a = (q : ℂ) := by
  let c : Fin k → Fin d → ℂ :=
    fun r j => if r = r₀ then 1 else alignPhase q (B r j a)
  have hc : ∀ r j, Complex.normSq (c r j) = 1 := by
    intro r j
    dsimp [c]
    split_ifs with hr
    · simp
    · apply alignPhase_normSq hq
      rw [hq2]
      exact coordinate_normSq_of_ket_basis B hB r₀ r hzero (Ne.symm hr) a j
  refine ⟨rephaseColumns c B, isFamily_rephaseColumns c hc B hB, ?_, ?_⟩
  · intro j
    funext i
    simpa [rephaseColumns, c] using congrFun (hzero j) i
  · intro r hr j
    change c r j * B r j a = (q : ℂ)
    dsimp [c]
    rw [if_neg hr]
    apply alignPhase_mul hq
    rw [hq2]
    exact coordinate_normSq_of_ket_basis B hB r₀ r hzero (Ne.symm hr) a j

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB
variable {d k : ℕ}

/-- For positive `q` with `q ^ 2 = 1 / d`, there exists a mutually unbiased family retaining the
distinguished computational basis, with coordinate `a` of all other columns and every
coordinate of column `a` in basis `r₁` equal to `q`. -/
theorem normalize_phase_gauge
    (B : Fin k → Fin d → QState (Fin d)) (hB : IsFamily B)
    (r₀ r₁ : Fin k) (hne : r₁ ≠ r₀) (a : Fin d)
    (hzero : ∀ j, B r₀ j = Qatlib.Foundations.PureStateMath.Ket j)
    (q : ℝ) (hq : 0 < q) (hq2 : q ^ 2 = (1 : ℝ) / d) :
    ∃ C : Fin k → Fin d → QState (Fin d),
      IsFamily C ∧ (∀ j, C r₀ j = Qatlib.Foundations.PureStateMath.Ket j) ∧
      (∀ r, r ≠ r₀ → ∀ j, C r j a = (q : ℂ)) ∧
      ∀ i, C r₁ a i = (q : ℂ) := by
  obtain ⟨D, hD, hD0, hDa⟩ := normalize_first_row B hB r₀ a hzero q hq hq2
  have hamp : ∀ i, Complex.normSq (D r₁ a i) = q ^ 2 := by
    intro i
    rw [hq2]
    exact coordinate_normSq_of_ket_basis D hD r₀ r₁ hD0 (Ne.symm hne) i a
  let ρ : Fin d → ℂ := fun i => alignPhase q (D r₁ a i)
  have hρ : ∀ i, Complex.normSq (ρ i) = 1 :=
    fun i => alignPhase_normSq hq (hamp i)
  have hρa : ρ a = 1 := by
    dsimp [ρ]
    rw [hDa r₁ hne a]
    exact alignPhase_ofReal hq
  let c : Fin k → Fin d → ℂ :=
    fun r j => if r = r₀ then (starRingEnd ℂ) (ρ j) else 1
  have hc : ∀ r j, Complex.normSq (c r j) = 1 := by
    intro r j
    dsimp [c]
    split_ifs <;> simp [Complex.normSq_conj, hρ]
  let C := rephaseColumns c (rephaseCoordinates ρ D)
  refine ⟨C, isFamily_rephaseColumns c hc _
    (isFamily_rephaseCoordinates ρ hρ D hD), ?_, ?_, ?_⟩
  · intro j
    funext i
    change (if r₀ = r₀ then (starRingEnd ℂ) (ρ j) else 1) *
      (ρ i * D r₀ j i) = Qatlib.Foundations.PureStateMath.Ket j i
    rw [if_pos rfl, hD0 j]
    by_cases hij : i = j
    · subst i
      simp [Qatlib.Foundations.PureStateMath.Ket, ← Complex.normSq_eq_conj_mul_self, hρ]
    · simp [Qatlib.Foundations.PureStateMath.Ket, hij]
  · intro r hr j
    change c r j * (ρ a * D r j a) = (q : ℂ)
    simp only [c, if_neg hr, hρa, one_mul, hDa r hr j]
  · intro i
    change c r₁ a * (ρ i * D r₁ a i) = (q : ℂ)
    rw [show c r₁ a = 1 by simp [c, hne], one_mul]
    exact alignPhase_mul hq (hamp i)

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB
