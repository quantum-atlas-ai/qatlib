/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.TermCountBound

set_option backward.isDefEq.respectTransparency false

/-!
# Lie-Algebraic Trotter-Suzuki Term Count for Coupled Quantum Harmonic Oscillators

This module formalizes the `M`-coupled quantum harmonic oscillator application
(`L = M^2`, `β = 1`, `y = m'`) of Somma's Lie-algebraic Trotter-Suzuki bound,
establishing `(M^2)^{2 + 1/p} = (M^4)^{1 + 1/(2p)}`, the Eq. (5) specialized
term-count bound, and the optimal-order subexponential scaling in `m'`.

## Main statements

* `sq_rpow_eq_fourth_rpow`: `(M^2)^{2 + 1 / p} = (M^4)^{1 + 1 / (2 p)}` for `M ≥ 0`.
* `coupledQHO_termCount_eq5`: coupled-QHO term-count bound for any order `p ≥ 1`.
* `coupledQHO_optimal_order`: subexponential term-count bound at `coupledQHOOptimalOrder`.

## References

* [Somma, 2016][Somma2016], Section III, p. 4.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

private lemma optimal_order_factor_le {R : ℝ} (hR : 1 ≤ R) :
    let p := max 1 (Nat.ceil (Real.sqrt (Real.log R / Real.log 5) / 2))
    ((5 : ℝ) ^ (2 * p)) * R ^ (1 / (2 * (p : ℝ))) ≤
      25 * Real.exp (2 * Real.sqrt (Real.log R * Real.log 5)) := by
  let z := Real.log R
  let L5 := Real.log 5
  let x := Real.sqrt (z / L5) / 2
  let p := max 1 (Nat.ceil x)
  change (5 : ℝ) ^ (2 * p) * R ^ (1 / (2 * (p : ℝ))) ≤
    25 * Real.exp (2 * Real.sqrt (z * L5))
  have hz : 0 ≤ z := Real.log_nonneg hR
  have hL : 0 < L5 := Real.log_pos (by norm_num)
  have hx : 0 ≤ x := by positivity
  have hp : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (le_max_left 1 (Nat.ceil x))
  have hxp : x ≤ (p : ℝ) := (Nat.le_ceil x).trans (by
    exact_mod_cast (le_max_right 1 (Nat.ceil x)))
  have hpx : (p : ℝ) ≤ x + 1 := by
    by_cases hc : Nat.ceil x ≤ 1
    · have he : p = 1 := max_eq_left hc
      rw [he]
      norm_num
      exact hx
    · have he : p = Nat.ceil x := max_eq_right (by omega)
      rw [he]
      exact (Nat.ceil_lt_add_one hx).le
  have hs : Real.sqrt (z / L5) * L5 = Real.sqrt (z * L5) := by
    calc
      _ = Real.sqrt (z / L5) * Real.sqrt (L5 ^ 2) := by rw [Real.sqrt_sq hL.le]
      _ = Real.sqrt (z / L5 * L5 ^ 2) :=
        (Real.sqrt_mul (div_nonneg hz hL.le) _).symm
      _ = _ := by congr 1; field_simp
  have hzprod : z = Real.sqrt (z / L5) * Real.sqrt (z * L5) := by
    rw [← hs, ← mul_assoc, ← pow_two, Real.sq_sqrt (div_nonneg hz hL.le)]
    field_simp
  have hfirst : (2 * (p : ℝ)) * L5 ≤ Real.sqrt (z * L5) + 2 * L5 := by
    have h := mul_le_mul_of_nonneg_right hpx hL.le
    dsimp [x] at h
    nlinarith only [h, hs]
  have hsecond : z / (2 * (p : ℝ)) ≤ Real.sqrt (z * L5) := by
    apply (div_le_iff₀ (by linarith : 0 < 2 * (p : ℝ))).2
    have hsle : Real.sqrt (z / L5) ≤ 2 * (p : ℝ) := by
      dsimp [x] at hxp
      linarith
    calc
      z = Real.sqrt (z / L5) * Real.sqrt (z * L5) := hzprod
      _ ≤ (2 * (p : ℝ)) * Real.sqrt (z * L5) :=
        mul_le_mul_of_nonneg_right hsle (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hpow : (5 : ℝ) ^ (2 * p) = Real.exp ((2 * (p : ℝ)) * L5) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    push_cast
    dsimp [L5]
    ring
  have hRpow : R ^ (1 / (2 * (p : ℝ))) = Real.exp (z / (2 * (p : ℝ))) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    dsimp [z]
    ring
  have h25 : Real.exp (2 * L5) = 25 := by
    rw [show 2 * L5 = L5 + L5 by ring, Real.exp_add, Real.exp_log (by norm_num)]
    norm_num
  rw [hpow, hRpow, ← Real.exp_add]
  calc
    _ ≤ Real.exp (2 * L5 + 2 * Real.sqrt (z * L5)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add, h25]

/-- `(M²)^{2+1/p} = (M⁴)^{1+1/(2p)}` for `M ≥ 0` (the `L`-absorption in the
coupled-QHO application). -/
theorem sq_rpow_eq_fourth_rpow {p : ℕ} {M : ℝ} (hM : 0 ≤ M) :
    (M ^ 2) ^ (2 + 1 / (p : ℝ)) = (M ^ 4) ^ (1 + 1 / (2 * (p : ℝ))) := by
  rw [← Real.rpow_natCast M 2, ← Real.rpow_natCast M 4,
    ← Real.rpow_mul hM, ← Real.rpow_mul hM]
  congr 1
  ring

/-- **Coupled-QHO term count (arXiv:1512.03416v1, p. 4, Eq. (5) applied)**:
with `L = M²`, `β = 1`, `y = m′` and `p ≥ 1`,
`N ≤ 20 · 5^{2p}(m′/ε)^{1/(2p)}(M⁴t)^{1+1/(2p)} + N_p`. -/
theorem coupledQHO_termCount_eq5 {p : ℕ} (hp : 1 ≤ p) {M m' t ε : ℝ}
    (hM : 1 ≤ M) (hm' : 1 ≤ m') (ht : 0 ≤ t) (hε : 0 < ε) :
    sourceNumTerms p (M ^ 2) 1 m' t ε ≤
      20 * ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
        (M ^ 4 * t) ^ (1 + 1 / (2 * (p : ℝ)))) + sourceMacroCount (M ^ 2) p := by
  have hM0 : (0 : ℝ) ≤ M := by linarith
  have hm'0 : (0 : ℝ) ≤ m' := by linarith
  have hM4 : (0 : ℝ) ≤ M ^ 4 := by positivity
  have hpow := sq_rpow_eq_fourth_rpow (p := p) hM0
  have heq : eq5Bound p (M ^ 2) 1 m' t ε =
      (5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
        (M ^ 4 * t) ^ (1 + 1 / (2 * (p : ℝ))) := by
    calc eq5Bound p (M ^ 2) 1 m' t ε
        = (5 : ℝ) ^ (2 * p) * (M ^ 4) ^ (1 + 1 / (2 * (p : ℝ))) *
            (m' ^ (1 / (2 * (p : ℝ))) / ε ^ (1 / (2 * (p : ℝ)))) *
            t ^ (1 + 1 / (2 * (p : ℝ))) := by
          unfold eq5Bound
          rw [hpow]
          ring
      _ = (5 : ℝ) ^ (2 * p) *
            ((M ^ 4) ^ (1 + 1 / (2 * (p : ℝ))) * t ^ (1 + 1 / (2 * (p : ℝ)))) *
            (m' ^ (1 / (2 * (p : ℝ))) / ε ^ (1 / (2 * (p : ℝ)))) := by ring
      _ = (5 : ℝ) ^ (2 * p) * (M ^ 4 * t) ^ (1 + 1 / (2 * (p : ℝ))) *
            (m' ^ (1 / (2 * (p : ℝ))) / ε ^ (1 / (2 * (p : ℝ)))) := by
          rw [Real.mul_rpow hM4 ht]
      _ = (5 : ℝ) ^ (2 * p) * (M ^ 4 * t) ^ (1 + 1 / (2 * (p : ℝ))) *
            (m' / ε) ^ (1 / (2 * (p : ℝ))) := by
          rw [Real.div_rpow hm'0 hε.le]
      _ = (5 : ℝ) ^ (2 * p) * (m' / ε) ^ (1 / (2 * (p : ℝ))) *
            (M ^ 4 * t) ^ (1 + 1 / (2 * (p : ℝ))) := by ring
  have hL : (1 : ℝ) ≤ M ^ 2 := by nlinarith
  exact (sourceNumTerms_le_eq5 hp (L := M ^ 2) (β := 1) (y := m')
    hL (by norm_num) hm'0 ht hε).trans (by rw [heq])

/-- **Optimal order for `M` coupled QHOs (arXiv:1512.03416v1, p. 4)**: choosing
the order `p` minimising the Eq. (5) shape gives
`N ≤ C · M⁴t · exp(2√(log(m′Mt/ε)·log 5)) + N_p`. -/
theorem coupledQHO_optimal_order {M m' t ε : ℝ}
    (hM : 1 ≤ M) (hm' : 0 < m') (ht : 0 ≤ t) (hε : 0 < ε)
    (hmt : 1 ≤ m' * M * t / ε) :
    ∃ C : ℝ, 0 < C ∧
      sourceNumTerms (coupledQHOOptimalOrder M m' t ε) (M ^ 2) 1 m' t ε ≤
        C * (M ^ 4 * t * Real.exp (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5))) +
          sourceMacroCount (M ^ 2) (coupledQHOOptimalOrder M m' t ε) := by
  let p := coupledQHOOptimalOrder M m' t ε
  let a := 1 / (2 * (p : ℝ))
  have hp : 1 ≤ p := le_max_left _ _
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hMpos : 0 < M := by linarith
  have hmM : 0 < m' * M := mul_pos hm' hMpos
  have htpos : 0 < t := by
    apply (mul_pos_iff_of_pos_left hmM).1
    have hprod := (le_div_iff₀ hε).1 hmt
    linarith
  have hM4 : 0 ≤ M ^ 4 := pow_nonneg hMpos.le _
  have hL : (1 : ℝ) ≤ M ^ 2 := by nlinarith only [hM, sq_nonneg (M - 1)]
  have heq : eq5Bound p (M ^ 2) 1 m' t ε =
      (5 : ℝ) ^ (2 * p) * (m' / ε) ^ a * (M ^ 4 * t) ^ (1 + a) := by
    unfold eq5Bound
    rw [sq_rpow_eq_fourth_rpow hMpos.le, Real.div_rpow hm'.le hε.le,
      Real.mul_rpow hM4 ht]
    dsimp [a]
    ring
  have hbase : sourceNumTerms p (M ^ 2) 1 m' t ε ≤
      20 * ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ a * (M ^ 4 * t) ^ (1 + a)) +
        sourceMacroCount (M ^ 2) p := by
    have h := sourceNumTerms_le_eq5 hp hL (by norm_num : (1 : ℝ) ≤ 1) hm'.le ht hε
    rwa [heq] at h
  have hsplit : (m' / ε) ^ a * (M ^ 4 * t) ^ (1 + a) =
      (M ^ 4 * t) * (m' * M * t / ε) ^ a * M ^ (3 * a) := by
    rw [Real.rpow_add (mul_pos (pow_pos hMpos _) htpos), Real.rpow_one,
      show m' * M * t / ε = (m' / ε) * (M * t) by ring,
      Real.mul_rpow (div_nonneg hm'.le hε.le) (mul_nonneg hMpos.le ht),
      show M ^ 4 * t = (M * t) * M ^ 3 by ring,
      Real.mul_rpow (mul_nonneg hMpos.le ht) (pow_nonneg hMpos.le _),
      ← Real.rpow_natCast M 3, ← Real.rpow_mul hMpos.le]
    ring_nf
  have ha : 3 * a ≤ 2 := by
    dsimp [a]
    rw [mul_one_div]
    apply (div_le_iff₀ (by linarith : 0 < 2 * (p : ℝ))).2
    linarith
  have hMpow : M ^ (3 * a) ≤ M ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le hM ha
    simpa only [Real.rpow_ofNat] using h
  have hfactor := optimal_order_factor_le hmt
  change (5 : ℝ) ^ (2 * p) * (m' * M * t / ε) ^ a ≤ _ at hfactor
  have hnonneg : 0 ≤ (20 : ℝ) * (M ^ 4 * t) * M ^ (3 * a) := by
    exact mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hM4 ht))
      (Real.rpow_nonneg hMpos.le _)
  refine ⟨500 * M ^ 2, by positivity, ?_⟩
  calc
    _ ≤ 20 * ((5 : ℝ) ^ (2 * p) * (m' / ε) ^ a * (M ^ 4 * t) ^ (1 + a)) +
        sourceMacroCount (M ^ 2) p := hbase
    _ = (20 * (M ^ 4 * t) * M ^ (3 * a)) *
        ((5 : ℝ) ^ (2 * p) * (m' * M * t / ε) ^ a) + sourceMacroCount (M ^ 2) p := by
      rw [mul_assoc ((5 : ℝ) ^ (2 * p)), hsplit]
      ring
    _ ≤ (20 * (M ^ 4 * t) * M ^ (3 * a)) *
        (25 * Real.exp (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5))) +
          sourceMacroCount (M ^ 2) p :=
      add_le_add (mul_le_mul_of_nonneg_left hfactor hnonneg) le_rfl
    _ = (500 * (M ^ 4 * t) * Real.exp
        (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5))) * M ^ (3 * a) +
          sourceMacroCount (M ^ 2) p := by ring
    _ ≤ (500 * (M ^ 4 * t) * Real.exp
        (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5))) * M ^ 2 +
          sourceMacroCount (M ^ 2) p := by
      exact add_le_add (mul_le_mul_of_nonneg_left hMpow (by positivity)) le_rfl
    _ = _ := by ring

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount
