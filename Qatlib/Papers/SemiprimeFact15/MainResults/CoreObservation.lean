/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiprimeFact15.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Divisors of `2q₁q₂` recover the factors of a safe semiprime

This file formalizes the core arithmetic recovery observation of
[Grosshans et al., 2015][GrosshansEtAl2015] (§III.C, p. 5, Algorithm 1):

> For a safe semiprime `N = p₁p₂ = (2q₁+1)(2q₂+1)`, the ideal QOFA output `d` always
> divides `2q₁q₂`, and every divisor of `2q₁q₂` except `1` and `2` recovers `{p₁, p₂}`.

Following Algorithm 1 (lines 4–6):

* unify the parity of `d` by `s = d` if `d` is even and `s = 2d` if `d` is odd
  (`sComplement`);
* the six useful divisors map to `s ∈ {2q₁, 2q₂, 2q₁q₂}` (`sComplement_classification`);
* for `s = 2q₁` (resp. `2q₂`), the factor is `p₁ = s + 1` (resp. `p₂ = s + 1`);
* for `s = 2q₁q₂`, solving `X² - (N + 1 - 2s)X + N = 0` via `M ± √(M² - N)` with
  `M = (N + 1)/2 - s` recovers `{p₁, p₂}` (`quadratic_recovery`).

## Main statements

* `qofaOutput_dvd_two_q1_q2`: every ideal QOFA output divides `2q₁q₂`.
* `sComplement_classification`: every divisor of `2q₁q₂` outside `{1, 2}` maps under
  `sComplement` into `{2q₁, 2q₂, 2q₁q₂}`.
* `linear_recovery_q1`, `linear_recovery_q2`: linear factor recovery from `q₁` and `q₂`.
* `quadratic_recovery`: quadratic factor recovery `{M - √(M² - N), M + √(M² - N)} = {p₁, p₂}`
  from `s = 2q₁q₂`.

## References

* [Grosshans et al., 2015][GrosshansEtAl2015]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SemiprimeFact15.MainResults

/-! ## Part (1): the QOFA output divides `2q₁q₂` -/

/-- **Core observation (divisibility).**  The ideal QOFA output `d = r/gcd(t,r)`
for the true order `r ∈ {q₁q₂, 2q₁q₂}` always divides `2q₁q₂`
([Grosshans et al., 2015][GrosshansEtAl2015], §III.C, p. 5). -/
theorem qofaOutput_dvd_two_q1_q2 (cs : SafeSemiprime) (r t : ℕ)
    (hr : r = cs.q1 * cs.q2 ∨ r = 2 * cs.q1 * cs.q2) :
    qofaOutput r t ∣ 2 * cs.q1 * cs.q2 := by
  have hrdvd : r ∣ 2 * cs.q1 * cs.q2 := by
    rcases hr with rfl | rfl
    · exact ⟨2, by ring⟩
    · exact dvd_refl _
  exact Nat.dvd_trans (qofaOutput_dvd r t) hrdvd

/-! ## Part (2): the parity unification `s = sComplement d` -/

/-- `sComplement` of an odd number is `2d`. -/
lemma sComplement_of_odd {d : ℕ} (h : ¬ 2 ∣ d) : sComplement d = 2 * d := by
  unfold sComplement
  simp [h]

/-- `sComplement` of an even number is `d`. -/
lemma sComplement_of_even {d : ℕ} (h : 2 ∣ d) : sComplement d = d := by
  unfold sComplement
  simp [h]

/-- `2 ∤ q₁` (`q₁` is an odd prime). -/
lemma not_two_dvd_q1 (cs : SafeSemiprime) : ¬ 2 ∣ cs.q1 :=
  cs.q1_odd.not_two_dvd_nat

/-- `2 ∤ q₂` (`q₂` is an odd prime). -/
lemma not_two_dvd_q2 (cs : SafeSemiprime) : ¬ 2 ∣ cs.q2 :=
  cs.q2_odd.not_two_dvd_nat

/-- `2 ∤ q₁q₂` (product of two odd primes). -/
lemma not_two_dvd_q1q2 (cs : SafeSemiprime) : ¬ 2 ∣ cs.q1 * cs.q2 :=
  (cs.q1_odd.mul cs.q2_odd).not_two_dvd_nat

/-- The six useful divisors of `2q₁q₂` unify, via `sComplement`, to one of
`2q₁`, `2q₂`, `2q₁q₂` ([Grosshans et al., 2015][GrosshansEtAl2015], Algorithm 1, lines 4–5). -/
theorem sComplement_classification (cs : SafeSemiprime) {d : ℕ}
    (hd : d ∣ 2 * cs.q1 * cs.q2) (h1 : d ≠ 1) (h2 : d ≠ 2) :
    sComplement d = 2 * cs.q1 ∨ sComplement d = 2 * cs.q2 ∨
      sComplement d = 2 * cs.q1 * cs.q2 := by
  rcases dvd_two_mul_q1q2 cs hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  · left; rw [sComplement_of_odd (not_two_dvd_q1 cs)]
  · right; left; rw [sComplement_of_odd (not_two_dvd_q2 cs)]
  · right; right; rw [sComplement_of_odd (not_two_dvd_q1q2 cs)]; ring
  · left; rw [sComplement_of_even ⟨cs.q1, rfl⟩]
  · right; left; rw [sComplement_of_even ⟨cs.q2, rfl⟩]
  · right; right; rw [sComplement_of_even ⟨cs.q1 * cs.q2, by ring⟩]

/-! ## Part (3): linear recovery `p = s + 1` -/

/-- `2q₁ + 1 = p₁`. -/
lemma two_q1_add_one (cs : SafeSemiprime) : 2 * cs.q1 + 1 = cs.p1 := by
  rw [cs.p1_eq]

/-- `2q₂ + 1 = p₂`. -/
lemma two_q2_add_one (cs : SafeSemiprime) : 2 * cs.q2 + 1 = cs.p2 := by
  rw [cs.p2_eq]

/-- **Linear recovery for `s = 2q₁`**: `s + 1 = p₁` and `(s + 1) · p₂ = N`
([Grosshans et al., 2015][GrosshansEtAl2015], Algorithm 1). -/
theorem linear_recovery_q1 (cs : SafeSemiprime) :
    sComplement cs.q1 + 1 = cs.p1 ∧ (sComplement cs.q1 + 1) * cs.p2 = cs.N := by
  have hs : sComplement cs.q1 = 2 * cs.q1 :=
    sComplement_of_odd (not_two_dvd_q1 cs)
  have hp : sComplement cs.q1 + 1 = cs.p1 := by rw [hs]; exact two_q1_add_one cs
  refine ⟨hp, ?_⟩
  rw [hp, cs.N_eq]

/-- **Linear recovery for `s = 2q₂`**: `s + 1 = p₂` and `(s + 1) · p₁ = N`
([Grosshans et al., 2015][GrosshansEtAl2015], Algorithm 1). -/
theorem linear_recovery_q2 (cs : SafeSemiprime) :
    sComplement cs.q2 + 1 = cs.p2 ∧ (sComplement cs.q2 + 1) * cs.p1 = cs.N := by
  have hs : sComplement cs.q2 = 2 * cs.q2 :=
    sComplement_of_odd (not_two_dvd_q2 cs)
  have hp : sComplement cs.q2 + 1 = cs.p2 := by rw [hs]; exact two_q2_add_one cs
  refine ⟨hp, ?_⟩
  rw [hp, cs.N_eq, Nat.mul_comm]

/-! ## Part (4): quadratic recovery `s = 2q₁q₂` -/

/-- `p₁ + p₂ = 2 · ((N + 1) / 2 - 2q₁q₂)`: the sum of the two safe primes is twice the
midpoint `M` used by the quadratic recovery. -/
theorem p1_add_p2_eq_two_M (cs : SafeSemiprime) :
    cs.p1 + cs.p2 = 2 * ((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) := by
  have hsum : cs.p1 + cs.p2 = cs.N + 1 - 4 * cs.q1 * cs.q2 := cs.p1_add_p2
  have hNplus : cs.N + 1 = 2 * (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1) := by
    rw [cs.N_eq, cs.p1_eq, cs.p2_eq]; ring
  have hk : (cs.N + 1) / 2 = 2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1 := by
    rw [hNplus, Nat.mul_comm 2 (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1)]
    exact Nat.mul_div_cancel _ (by norm_num : 0 < 2)
  have hinner : 2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1 - 2 * cs.q1 * cs.q2
      = cs.q1 + cs.q2 + 1 := by omega
  have h4 : 4 * cs.q1 * cs.q2 = 2 * (2 * cs.q1 * cs.q2) := by ring
  have hmul : 2 * (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1)
      = 2 * (2 * cs.q1 * cs.q2) + 2 * (cs.q1 + cs.q2 + 1) := by ring
  have hfinal : 2 * (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1) - 4 * cs.q1 * cs.q2
      = 2 * (cs.q1 + cs.q2 + 1) := by
    rw [h4, hmul]
    exact Nat.add_sub_cancel_left _ _
  calc cs.p1 + cs.p2 = cs.N + 1 - 4 * cs.q1 * cs.q2 := hsum
    _ = 2 * (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1) - 4 * cs.q1 * cs.q2 := by
          rw [hNplus]
    _ = 2 * (cs.q1 + cs.q2 + 1) := hfinal
    _ = 2 * (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1 - 2 * cs.q1 * cs.q2) := by
          rw [hinner]
    _ = 2 * ((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) := by rw [← hk]

/-- **Quadratic recovery for `s = 2q₁q₂`** ([Grosshans et al., 2015][GrosshansEtAl2015], §III.C,
Eq. (5) and Algorithm 1): with `M = (N + 1) / 2 - 2q₁q₂` and `k = √(M² - N)`, the two numbers
`M - k` and `M + k` are the safe primes `p₁, p₂`. -/
theorem quadratic_recovery (cs : SafeSemiprime) :
    ({((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) -
          Nat.sqrt (((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) *
                      ((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) - cs.N),
        ((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) +
          Nat.sqrt (((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) *
                      ((cs.N + 1) / 2 - 2 * cs.q1 * cs.q2) - cs.N)} : Finset ℕ)
      = {cs.p1, cs.p2} := by
  have hNplus : cs.N + 1 = (2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1) * 2 := by
    rw [cs.N_eq, cs.p1_eq, cs.p2_eq]; ring
  have hdiv : (cs.N + 1) / 2 = 2 * cs.q1 * cs.q2 + cs.q1 + cs.q2 + 1 := by
    rw [hNplus]
    exact Nat.mul_div_cancel _ (by norm_num : 0 < 2)
  have hM : (cs.N + 1) / 2 - 2 * cs.q1 * cs.q2 = cs.q1 + cs.q2 + 1 := by
    rw [hdiv]; omega
  rw [hM, cs.p1_eq, cs.p2_eq]
  rcases le_total cs.q1 cs.q2 with hle | hle
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hdiff : (cs.q1 + cs.q2 + 1) * (cs.q1 + cs.q2 + 1) - cs.N = d * d := by
      rw [cs.N_eq, cs.p1_eq, cs.p2_eq, hd]
      have hadd : (cs.q1 + (cs.q1 + d) + 1) * (cs.q1 + (cs.q1 + d) + 1) =
          (2 * cs.q1 + 1) * (2 * (cs.q1 + d) + 1) + d * d := by ring
      rw [hadd, Nat.add_sub_cancel_left]
    rw [hdiff, Nat.sqrt_eq, hd]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
    have hdiff : (cs.q1 + cs.q2 + 1) * (cs.q1 + cs.q2 + 1) - cs.N = d * d := by
      rw [cs.N_eq, cs.p1_eq, cs.p2_eq, hd]
      have hadd : (cs.q2 + d + cs.q2 + 1) * (cs.q2 + d + cs.q2 + 1) =
          (2 * (cs.q2 + d) + 1) * (2 * cs.q2 + 1) + d * d := by ring
      rw [hadd, Nat.add_sub_cancel_left]
    rw [hdiff, Nat.sqrt_eq, hd]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

end Qatlib.Papers.SemiprimeFact15.MainResults
