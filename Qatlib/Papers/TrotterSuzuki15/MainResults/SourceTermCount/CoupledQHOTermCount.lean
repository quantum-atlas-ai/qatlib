/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.TermCountBound

@[expose] public section

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

/-- The rounded optimal order bounds `5^{2p} R^{1/(2p)}` by
`25 exp(2√(log R · log 5))` for `R ≥ 1`. -/
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

section

set_option backward.isDefEq.respectTransparency false

/-!
## Subpolynomiality of the coupled-QHO term count

Fixed paper version: arXiv:1512.03416v1 (R. D. Somma, 10 December 2015);
see [Somma2016], [arXiv:1512.03416v1](https://arxiv.org/abs/1512.03416v1),
[doi:10.1063/1.4952761](https://doi.org/10.1063/1.4952761).
Source: p. 4, the coupled quantum harmonic oscillator application: after the
Eq. (5) specialization the paper optimises the order `p`, concludes
`N = O(M^4 t exp(√(log(m′Mt/ε))))` and states that this "is subpolynomial in
`m′`".

The optimal-order bound
`Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.coupledQHO_optimal_order`
and the single-oscillator limit
`Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.qho_subpolynomial`
(at `t = ε = 1`) describe two related estimates. The coupled limit holds for
arbitrary `M ≥ 1`, `t ≥ 0` and `ε > 0`.

`sourceNumTerms (coupledQHOOptimalOrder M m′ t ε) (M^2) 1 m′ t ε / (m′)^α → 0`
as `m′ → ∞`, for every `α > 0`.

The proof makes the optimal-order bound uniform in `m′` with the explicit
constant `500 M²` of the locked proof, then compares both summands with
`exp(8 √(log m′))`: for the exponential term this uses
`log (m′Mt/ε) ≤ 2 log m′` and `log 5 ≤ 8`; for the `N_p = 2 M² 5^{p-1}` term it
uses `p - 1 ≤ √(log(m′Mt/ε)/log 5)/2` together with the identity
`√(z/log 5) · log 5 = √(z log 5)`.  The general squeeze
`exp(c √(log x)) / x^α → 0` is proved once, from
`c √(log x) ≤ (α/2) log x` eventually.

Boundary: `sourceNumTerms` is the paper's scalar ledger, not the length of a
word built from actual ladder operators, and the subpolynomial conclusion is
proved for the fixed parameters `M`, `t`, `ε` of the application; `M` itself is
not sent to infinity.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

namespace Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

/-- The optimal-order bound with the explicit constant
`500 M²` of its proof: this is
`Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount.coupledQHO_optimal_order`
with the existential constant instantiated, which is what makes the estimate
uniform in `m′`. -/
private lemma coupledQHO_optimal_order_bound {M m' t ε : ℝ}
    (hM : 1 ≤ M) (hm' : 0 < m') (ht : 0 ≤ t) (hε : 0 < ε)
    (hmt : 1 ≤ m' * M * t / ε) :
    sourceNumTerms (coupledQHOOptimalOrder M m' t ε) (M ^ 2) 1 m' t ε ≤
      (500 * M ^ 2) * (M ^ 4 * t *
        Real.exp (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5))) +
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

/-- `exp(c √(log x)) / x^α → 0` at infinity, for every `c ≥ 0` and `α > 0`:
eventually `c √(log x) ≤ (α/2) log x`, so the quotient is dominated by
`exp(-(α/2) log x) = x^{-α/2}`. -/
private lemma tendsto_exp_mul_sqrt_log_div_rpow {α c : ℝ} (hα : 0 < α) (hc : 0 ≤ c) :
    Filter.Tendsto (fun x : ℝ => Real.exp (c * Real.sqrt (Real.log x)) / x ^ α)
      Filter.atTop (nhds 0) := by
  have hdecay : Filter.Tendsto (fun x : ℝ => Real.exp (-(α / 2) * Real.log x))
      Filter.atTop (nhds 0) := by
    have hlog : Filter.Tendsto (fun x : ℝ => -(α / 2) * Real.log x) Filter.atTop Filter.atBot :=
      Real.tendsto_log_atTop.const_mul_atTop_of_neg (by linarith : -(α / 2) < 0)
    exact Real.tendsto_exp_atBot.comp hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    exact div_nonneg (Real.exp_pos _).le (Real.rpow_pos_of_pos hx0 _).le
  · have hcα : 0 ≤ 2 * c / α := by positivity
    filter_upwards [Filter.eventually_ge_atTop (max 1 (Real.exp ((2 * c / α) ^ 2)))]
      with x hx
    have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hexp : Real.exp ((2 * c / α) ^ 2) ≤ x := le_trans (le_max_right _ _) hx
    have hlog : (2 * c / α) ^ 2 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at h
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hsqrt : 2 * c / α ≤ Real.sqrt (Real.log x) := by
      rw [← Real.sqrt_sq hcα]
      exact Real.sqrt_le_sqrt hlog
    have hcoef : c ≤ (α / 2) * Real.sqrt (Real.log x) := by
      have hkey : (α / 2) * (2 * c / α) = c := by field_simp
      calc c = (α / 2) * (2 * c / α) := hkey.symm
        _ ≤ (α / 2) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_left hsqrt (by positivity)
    have hkey : c * Real.sqrt (Real.log x) ≤ (α / 2) * Real.log x := by
      calc c * Real.sqrt (Real.log x)
          ≤ ((α / 2) * Real.sqrt (Real.log x)) * Real.sqrt (Real.log x) :=
            mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)
        _ = (α / 2) * Real.log x := by
            rw [mul_assoc, Real.mul_self_sqrt hlog0]
    calc Real.exp (c * Real.sqrt (Real.log x)) / x ^ α
        = Real.exp (c * Real.sqrt (Real.log x)) /
            Real.exp (Real.log x * α) := by
          rw [Real.rpow_def_of_pos hx0]
      _ = Real.exp (c * Real.sqrt (Real.log x) - Real.log x * α) := by
          rw [Real.exp_sub]
      _ ≤ Real.exp (-(α / 2) * Real.log x) := by
          apply Real.exp_le_exp.2
          nlinarith [hkey]

/-- **Optimal-order bound in exponential form**: for the coupling constant
`M ≥ 1`, `t > 0` and `ε > 0`, the coupled-QHO term count at the optimal order is
eventually at most `K · exp(8 √(log m′))` with `K = 500 M⁶ t + 2 M²`. -/
private lemma coupledQHO_eventually_le {M t ε : ℝ} (hM : 1 ≤ M) (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ m' : ℝ in Filter.atTop,
      sourceNumTerms (coupledQHOOptimalOrder M m' t ε) (M ^ 2) 1 m' t ε ≤
        (500 * M ^ 2 * M ^ 4 * t + 10 * M ^ 2) * Real.exp (8 * Real.sqrt (Real.log m')) := by
  have hMt : (0 : ℝ) < M * t := by
    have : (0 : ℝ) < M := by linarith
    positivity
  have hlog5 : Real.log 5 ≤ 8 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)
    linarith
  have hlog5pos : 0 < Real.log 5 := Real.log_pos (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop
    (max 1 (max (M * t / ε) (ε / (M * t))))] with m' hm'
  have hm1 : 1 ≤ m' := le_trans (le_max_left _ _) hm'
  have hm0 : (0 : ℝ) < m' := by linarith
  have hcoef : M * t / ε ≤ m' :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm'
  have hquot : 1 ≤ m' * M * t / ε := by
    rw [le_div_iff₀ hε]
    have h : ε / (M * t) ≤ m' :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm'
    have h' : ε ≤ m' * (M * t) := by
      rw [div_le_iff₀ hMt] at h
      exact h
    nlinarith
  have hbound := coupledQHO_optimal_order_bound hM hm0 ht.le hε hquot
  have hlogm : 0 ≤ Real.log m' := Real.log_nonneg hm1
  have hlogR : Real.log (m' * M * t / ε) ≤ 2 * Real.log m' := by
    have hsplit : Real.log (m' * M * t / ε) = Real.log m' + Real.log (M * t / ε) := by
      rw [show m' * M * t / ε = m' * (M * t / ε) by ring,
        Real.log_mul (ne_of_gt hm0) (by positivity)]
    have hcoef' : Real.log (M * t / ε) ≤ Real.log m' :=
      Real.log_le_log (by positivity) hcoef
    linarith
  have hlogR0 : 0 ≤ Real.log (m' * M * t / ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    have h : ε / (M * t) ≤ m' :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm'
    have h' : ε ≤ m' * (M * t) := by
      rw [div_le_iff₀ hMt] at h
      exact h
    nlinarith
  have hsqrt : Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) ≤
      4 * Real.sqrt (Real.log m') := by
    have hprod : Real.log (m' * M * t / ε) * Real.log 5 ≤ (2 * Real.log m') * 8 := by
      nlinarith [hlogR, hlog5, hlogR0, hlog5pos.le, hlogm]
    calc Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5)
        ≤ Real.sqrt ((2 * Real.log m') * 8) := Real.sqrt_le_sqrt hprod
      _ = 4 * Real.sqrt (Real.log m') := by
          rw [show (2 * Real.log m') * 8 = 4 ^ 2 * Real.log m' by ring,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4 ^ 2),
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
  have hexp : Real.exp (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5)) ≤
      Real.exp (8 * Real.sqrt (Real.log m')) := by
    apply Real.exp_le_exp.2
    linarith
  have hpx : ((coupledQHOOptimalOrder M m' t ε : ℕ) : ℝ) ≤
      Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2 + 1 := by
    have hy : (0 : ℝ) ≤ Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2 := by
      positivity
    by_cases hc : Nat.ceil (Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2) ≤ 1
    · have he : coupledQHOOptimalOrder M m' t ε = 1 := by
        unfold coupledQHOOptimalOrder
        exact max_eq_left hc
      rw [he]
      push_cast
      norm_num
      exact hy
    · have he : coupledQHOOptimalOrder M m' t ε =
          Nat.ceil (Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2) := by
        unfold coupledQHOOptimalOrder
        exact max_eq_right (by omega)
      rw [he]
      exact (Nat.ceil_lt_add_one hy).le
  have hs : Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) * Real.log 5 =
      Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) := by
    calc Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) * Real.log 5
        = Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) *
            Real.sqrt (Real.log 5 ^ 2) := by rw [Real.sqrt_sq hlog5pos.le]
      _ = Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5 * Real.log 5 ^ 2) :=
          (Real.sqrt_mul (div_nonneg hlogR0 hlog5pos.le) _).symm
      _ = Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) := by
          congr 1
          field_simp
  have hNp : sourceMacroCount (M ^ 2) (coupledQHOOptimalOrder M m' t ε) ≤
      10 * M ^ 2 * Real.exp (8 * Real.sqrt (Real.log m')) := by
    have hpow : (5 : ℝ) ^ (coupledQHOOptimalOrder M m' t ε - 1) ≤
        5 * Real.exp (8 * Real.sqrt (Real.log m')) := by
      have hmono : (5 : ℝ) ^ (coupledQHOOptimalOrder M m' t ε - 1) ≤
          (5 : ℝ) ^ (coupledQHOOptimalOrder M m' t ε) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hrw : (5 : ℝ) ^ (coupledQHOOptimalOrder M m' t ε) ≤
          (5 : ℝ) ^ (((coupledQHOOptimalOrder M m' t ε : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
      have hexp' : (5 : ℝ) ^ (((coupledQHOOptimalOrder M m' t ε : ℕ) : ℝ)) ≤
          (5 : ℝ) ^ (Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2 + 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hpx
      have hval : (5 : ℝ) ^ (Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2 + 1)
          = 5 * Real.exp (Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) / 2) := by
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 5) _ 1, Real.rpow_one,
          Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
        have harg : Real.log 5 * (Real.sqrt (Real.log (m' * M * t / ε) / Real.log 5) / 2)
            = Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) / 2 := by
          rw [← hs]
          ring
        rw [harg]
        ring
      have hsmall : Real.exp (Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) / 2) ≤
          Real.exp (8 * Real.sqrt (Real.log m')) := by
        apply Real.exp_le_exp.2
        nlinarith [hsqrt, Real.sqrt_nonneg (Real.log m')]
      have hchain : (5 : ℝ) ^ (coupledQHOOptimalOrder M m' t ε - 1) ≤
          5 * Real.exp (Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5) / 2) :=
        hmono.trans (hrw.trans (hexp'.trans hval.le))
      refine hchain.trans ?_
      exact mul_le_mul_of_nonneg_left hsmall (by norm_num)
    unfold sourceMacroCount
    have hstep := hpow
    calc 2 * M ^ 2 * (5 : ℝ) ^ (coupledQHOOptimalOrder M m' t ε - 1)
        ≤ 2 * M ^ 2 * (5 * Real.exp (8 * Real.sqrt (Real.log m'))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = 10 * M ^ 2 * Real.exp (8 * Real.sqrt (Real.log m')) := by ring
  calc sourceNumTerms (coupledQHOOptimalOrder M m' t ε) (M ^ 2) 1 m' t ε
      ≤ (500 * M ^ 2) * (M ^ 4 * t * Real.exp
          (2 * Real.sqrt (Real.log (m' * M * t / ε) * Real.log 5))) +
          sourceMacroCount (M ^ 2) (coupledQHOOptimalOrder M m' t ε) := hbound
    _ ≤ (500 * M ^ 2) * (M ^ 4 * t * Real.exp (8 * Real.sqrt (Real.log m'))) +
          10 * M ^ 2 * Real.exp (8 * Real.sqrt (Real.log m')) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
          · apply mul_le_mul_of_nonneg_left hexp
            positivity
          · positivity
        · exact hNp
    _ = (500 * M ^ 2 * M ^ 4 * t + 10 * M ^ 2) * Real.exp (8 * Real.sqrt (Real.log m')) := by
        ring

/-- **Subpolynomiality of the coupled-QHO term count in `m′`
(arXiv:1512.03416v1, p. 4)**: for `M ≥ 1`, `t ≥ 0`, `ε > 0` and every `α > 0`,
the number of exponentials at the optimal order, divided by `(m′)^α`, tends to
`0` as `m′ → ∞`. -/
theorem coupledQHO_subpolynomial {α M t ε : ℝ} (hα : 0 < α) (hM : 1 ≤ M) (ht : 0 ≤ t)
    (hε : 0 < ε) :
    Filter.Tendsto
      (fun m' : ℝ => sourceNumTerms (coupledQHOOptimalOrder M m' t ε) (M ^ 2) 1 m' t ε / m' ^ α)
      Filter.atTop (nhds 0) := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst ht0
    have hzero : ∀ m' : ℝ,
        sourceNumTerms (coupledQHOOptimalOrder M m' 0 ε) (M ^ 2) 1 m' 0 ε = 0 := by
      intro m'
      have hexpne : (1 : ℝ) + 1 / (2 * ((coupledQHOOptimalOrder M m' 0 ε : ℕ) : ℝ)) ≠ 0 := by
        have h : (0 : ℝ) < 1 + 1 / (2 * ((coupledQHOOptimalOrder M m' 0 ε : ℕ) : ℝ)) := by
          positivity
        exact ne_of_gt h
      have hseg : sourceSegmentReal (coupledQHOOptimalOrder M m' 0 ε) (M ^ 2) 1 m' 0 ε = 0 := by
        unfold sourceSegmentReal
        rw [Real.zero_rpow hexpne]
        ring
      have hsegs : sourceSegments (coupledQHOOptimalOrder M m' 0 ε) (M ^ 2) 1 m' 0 ε = 0 := by
        unfold sourceSegments
        rw [hseg]
        exact Nat.ceil_zero
      unfold sourceNumTerms
      rw [hsegs]
      simp
    have hfun : (fun m' : ℝ =>
        sourceNumTerms (coupledQHOOptimalOrder M m' 0 ε) (M ^ 2) 1 m' 0 ε / m' ^ α)
        = fun _ : ℝ => (0 : ℝ) := by
      funext m'
      rw [hzero m']
      simp
    rw [hfun]
    exact tendsto_const_nhds
  · have hK := coupledQHO_eventually_le hM htpos hε
    have hdecay : Filter.Tendsto
        (fun m' : ℝ => (500 * M ^ 2 * M ^ 4 * t + 10 * M ^ 2) *
          Real.exp (8 * Real.sqrt (Real.log m')) / m' ^ α) Filter.atTop (nhds 0) := by
      have hlim := (tendsto_exp_mul_sqrt_log_div_rpow (α := α) (c := 8) hα
        (by norm_num : (0 : ℝ) ≤ 8)).const_mul (500 * M ^ 2 * M ^ 4 * t + 10 * M ^ 2)
      have heq : (fun m' : ℝ => (500 * M ^ 2 * M ^ 4 * t + 10 * M ^ 2) *
            (Real.exp (8 * Real.sqrt (Real.log m')) / m' ^ α))
          = fun m' : ℝ => (500 * M ^ 2 * M ^ 4 * t + 10 * M ^ 2) *
            Real.exp (8 * Real.sqrt (Real.log m')) / m' ^ α := by
        funext m'
        ring
      rw [heq] at hlim
      simpa only [mul_zero] using hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdecay ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m' hm1
      have hm0 : (0 : ℝ) < m' := by linarith
      apply div_nonneg
      · unfold sourceNumTerms sourceSegments sourceMacroCount
        positivity
      · exact (Real.rpow_pos_of_pos hm0 _).le
    · filter_upwards [hK, Filter.eventually_ge_atTop (1 : ℝ)] with m' hm' hm1
      have hm0 : (0 : ℝ) < m' := by linarith
      exact div_le_div_of_nonneg_right hm' (Real.rpow_pos_of_pos hm0 _).le

end Qatlib.Papers.TrotterSuzuki15.MainResults.SourceTermCount

end
