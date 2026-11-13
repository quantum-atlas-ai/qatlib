/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.AccessModel.Defs
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Expectations of finite phase laws

The root `omega` is primitive, and the uniform phase law has zero expectation for `q > 1`. A
Dirichlet-kernel identity and trigonometric estimates show that the right-arc law eventually has
real expectation strictly between `1/2` and `1`. This development supports the treatment in
[TangWright2025].

## Main statements

* `omega_isPrimitiveRoot`: primitivity of the chosen root of unity.
* `cExpect_mu0_phase`: zero mean of the uniform phase law.
* `lemma23_mu1_bounds`: the expectation bounds of Lemma 2.3.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.AmpInvReqTang26.RootLaws

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.AmpInvReqTang26.AccessModel

/-- The chosen `q`th root of unity raised to the positive order `q` equals one. -/
theorem omega_pow_card (q : ℕ) (hq : 0 < q) : omega q ^ q = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have harg : (q : ℂ) * (Complex.ofReal (2 * Real.pi / (q : ℝ)) * Complex.I) =
      (q : ℂ) * (2 * (Real.pi : ℂ) / (q : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [harg]
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [show (q : ℂ) * (2 * (Real.pi : ℂ) / (q : ℂ) * Complex.I) =
      (2 * (Real.pi : ℂ)) * Complex.I by
    field_simp]
  rw [show (2 * (Real.pi : ℂ)) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_ofReal_mul_I]
  simp [Real.cos_two_pi, Real.sin_two_pi]

/-- For positive `q`, `omega q` is a primitive root of unity of order `q`. -/
theorem omega_isPrimitiveRoot (q : ℕ) (hq : 0 < q) :
    IsPrimitiveRoot (omega q) q := by
  have h := Complex.isPrimitiveRoot_exp q hq.ne'
  convert! h using 2
  rw [omega]
  congr 1
  push_cast
  ring

/-- The sum of all `q` root phases is zero when `q > 1`. -/
theorem phase_sum_zero (q : ℕ) (hq : 1 < q) : ∑ k : Fin q, phase q k = 0 := by
  have hq0 : 0 < q := by omega
  have hζ : IsPrimitiveRoot (omega q) q := omega_isPrimitiveRoot q hq0
  have hsum := IsPrimitiveRoot.geom_sum_eq_zero hζ hq

  have htrans : (∑ k : Fin q, phase q k) =
      (Finset.range q).sum (fun i => omega q ^ i) := by
    simp only [phase]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => omega q ^ i)]
  rw [htrans]
  exact hsum

/-- The uniform finite phase law has zero complex expectation when `q > 1` [TangWright2025]. -/
theorem cExpect_mu0_phase (q : ℕ) (hq : 1 < q) :
    cExpect (mu0 q (by omega)) (phase q) = 0 := by
  have h : ∑ k : Fin q, phase q k = 0 := phase_sum_zero q hq
  simp only [cExpect, mu0]
  rw [← Finset.mul_sum, h, mul_zero]

/-- The difference of the complex exponentials with exponents `z * I` and `-z * I` equals `2 * I
* sin z`. -/
private theorem exp_sub_exp_eq (z : ℂ) :
    Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I))
      = 2 * Complex.I * Complex.sin z := by
  rw [Complex.sin]
  field_simp
  rw [Complex.I_sq]
  ring

/-- The complex sine of a real number is the complex embedding of its real sine. -/
private theorem sin_ofReal' (x : ℝ) :
    Complex.sin ((x : ℂ)) = ((Real.sin x : ℝ) : ℂ) := (Complex.ofReal_sin x).symm

/-- For `q ≥ 2`, the sum of the right-arc phases is the ratio `sin(halfCount(q) * π/q) /
sin(π/q)`. -/
private theorem rightPhase_dirichlet {q : ℕ} (hq : 2 ≤ q) :
    ∑ j : Fin (halfCount q), rightPhase q j
      = Complex.sin (Complex.ofReal (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))))
        / Complex.sin (Complex.ofReal (Real.pi / (q : ℝ))) := by
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hqRne : ((q : ℝ)) ≠ 0 := ne_of_gt hqR
  have hω0 : omega q ≠ 0 := by
    intro hcon
    have hn := norm_omega q
    rw [hcon] at hn
    simp at hn
  have hωne : omega q ≠ 1 := (omega_isPrimitiveRoot q hq0).ne_one (by omega)
  have hE : ∀ k : ℕ, (omega q) ^ (k : ℕ)
      = Complex.exp (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ)))) * Complex.I) := by
    intro k
    rw [omega, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring

  have hdiff : ∀ k : ℕ, (omega q) ^ (k : ℕ) - 1
      = Complex.exp (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2) * Complex.I)
        * (2 * Complex.I
          * Complex.sin (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2))) := by
    intro k
    rw [hE k]
    have hsum : Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
        + Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
        = Complex.ofReal ((k : ℝ) * (2 * Real.pi / (q : ℝ))) := by
      rw [← Complex.ofReal_add]
      ring
    have hprod : Complex.exp (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
          * Complex.I)
        * Complex.exp (Complex.ofReal (-(((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2))
          * Complex.I)
        = 1 := by
      rw [← Complex.exp_add, Complex.ofReal_neg, neg_mul]
      have hz : Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2) * Complex.I
          + -(Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2) * Complex.I)
          = 0 := by
        ring
      rw [hz, Complex.exp_zero]
    have hBB : Complex.exp (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
          * Complex.I)
        * Complex.exp (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
          * Complex.I)
        = Complex.exp (Complex.ofReal ((k : ℝ) * (2 * Real.pi / (q : ℝ))) * Complex.I) := by
      rw [← Complex.exp_add, ← _root_.add_mul, hsum]
    have hsplit : 2 * Complex.I
          * Complex.sin (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2))
        = Complex.exp (Complex.ofReal (((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
            * Complex.I)
          - Complex.exp (Complex.ofReal (-(((k : ℝ) * (2 * Real.pi / (q : ℝ))) / 2))
            * Complex.I) := by
      rw [Complex.ofReal_neg, neg_mul, exp_sub_exp_eq]
    rw [hsplit, mul_sub, hBB, hprod]

  have hS1 : ∑ j : Fin (halfCount q), rightPhase q j
      = (omega q ^ (-(q / 4 : ℕ) : ℤ))
        * ∑ j : Fin (halfCount q), (omega q ^ (j : ℕ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [rightPhase]
    rw [show (((j : ℕ) : ℤ) - ((q / 4 : ℕ) : ℤ))
        = ((j : ℕ) : ℤ) + (-((q / 4 : ℕ) : ℤ)) from by ring,
      zpow_add₀ hω0, zpow_natCast, mul_comm]
  have hS2 : ∑ j : Fin (halfCount q), (omega q ^ (j : ℕ) : ℂ)
      = ((omega q) ^ (halfCount q) - 1) / (omega q - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => omega q ^ j) (halfCount q), geom_sum_eq hωne]

  have hneg : (omega q ^ (-(q / 4 : ℕ) : ℤ))
      = Complex.exp (Complex.ofReal (-(((q / 4 : ℕ) : ℝ)
        * (2 * Real.pi / (q : ℝ)))) * Complex.I) := by
    rw [_root_.zpow_neg, zpow_natCast, hE, ← Complex.exp_neg, Complex.ofReal_neg, neg_mul]
  have hcard : ((halfCount q : ℕ) : ℝ) = 2 * ((q / 4 : ℕ) : ℝ) + 1 := by
    simp only [halfCount]
    push_cast
    ring
  have hv : (((halfCount q : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2
      = ((q / 4 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))
        + (((1 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2 := by
    rw [hcard, _root_.add_mul]
    ring
  have hsum2 : (-(((q / 4 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))))
      + ((((halfCount q : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
      = ((((1 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2) := by
    rw [hv]
    ring
  have hcexp : (omega q ^ (-(q / 4 : ℕ) : ℤ))
      * (Complex.exp (Complex.ofReal ((((halfCount q : ℕ) : ℝ)
        * (2 * Real.pi / (q : ℝ))) / 2) * Complex.I))
      = Complex.exp (Complex.ofReal ((((1 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
        * Complex.I) := by
    rw [hneg, ← Complex.exp_add, ← _root_.add_mul, ← Complex.ofReal_add, hsum2]
  have harghc : Complex.ofReal ((((halfCount q : ℕ) : ℝ)
        * (2 * Real.pi / (q : ℝ))) / 2)
      = Complex.ofReal (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))) := by
    congr 1
    field_simp
  have harg1 : Complex.ofReal ((((1 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
      = Complex.ofReal (Real.pi / (q : ℝ)) := by
    congr 1
    field_simp
    push_cast
    ring
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by norm_num [Complex.I_ne_zero]
  have hnum : (omega q ^ (-(q / 4 : ℕ) : ℤ))
      * (Complex.exp (Complex.ofReal ((((halfCount q : ℕ) : ℝ)
        * (2 * Real.pi / (q : ℝ))) / 2) * Complex.I)
        * (2 * Complex.I * Complex.sin (Complex.ofReal ((((halfCount q : ℕ) : ℝ)
          * (2 * Real.pi / (q : ℝ))) / 2))))
      = Complex.exp (Complex.ofReal ((((1 : ℕ) : ℝ) * (2 * Real.pi / (q : ℝ))) / 2)
        * Complex.I)
        * (2 * Complex.I * Complex.sin (Complex.ofReal ((((halfCount q : ℕ) : ℝ)
          * (2 * Real.pi / (q : ℝ))) / 2))) := by
    linear_combination (2 * Complex.I * Complex.sin (Complex.ofReal ((((halfCount q : ℕ)
      : ℝ) * (2 * Real.pi / (q : ℝ))) / 2))) * hcexp
  rw [hS1, hS2, hdiff (halfCount q),
    show (omega q - 1) = (omega q ^ (1 : ℕ) - 1) from by rw [pow_one], hdiff 1,
    mul_div_assoc', hnum, mul_div_mul_left _ _ (Complex.exp_ne_zero _),
    harghc, harg1, sin_ofReal', sin_ofReal', mul_div_mul_left _ _ hI]

/-- For nonnegative angles with sum at most `π`, sine of the sum is at most the sum of their
sines. -/
private theorem sin_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ Real.pi) :
    Real.sin (a + b) ≤ Real.sin a + Real.sin b := by
  rw [Real.sin_add]
  have hsa : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith)
  have hsb : 0 ≤ Real.sin b := Real.sin_nonneg_of_nonneg_of_le_pi hb (by linarith)
  calc Real.sin a * Real.cos b + Real.cos a * Real.sin b
      ≤ Real.sin a * 1 + 1 * Real.sin b := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (Real.cos_le_one b) hsa
        · exact mul_le_mul_of_nonneg_right (Real.cos_le_one a) hsb
    _ = Real.sin a + Real.sin b := by rw [mul_one, one_mul]

/-- For nonnegative `x` with `N * x ≤ π`, one has `sin(N * x) ≤ N * sin x`. -/
private theorem sin_le_mul_sin {N : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hpi : (N : ℝ) * x ≤ Real.pi) :
    Real.sin ((N : ℝ) * x) ≤ (N : ℝ) * Real.sin x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · simp [h0, Nat.cast_succ]
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h0
      have hpi' : ((N : ℝ) + 1) * x ≤ Real.pi := by
        push_cast at hpi
        exact hpi
      have hNxpi : (N : ℝ) * x ≤ Real.pi := by nlinarith
      have h1 : 0 ≤ Real.sin ((N : ℝ) * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hNxpi
      have h2 : 0 ≤ Real.sin x :=
        Real.sin_nonneg_of_nonneg_of_le_pi hx (by nlinarith [hN1])
      have hstep : Real.sin (((N : ℝ) + 1) * x) ≤ Real.sin ((N : ℝ) * x) + Real.sin x := by
        have hring : ((N : ℝ) + 1) * x = (N : ℝ) * x + x := by ring
        have hnonneg1 : 0 ≤ (N : ℝ) * x := by positivity
        have hsum : (N : ℝ) * x + x ≤ Real.pi := by
          rw [← hring]
          exact hpi'
        rw [hring]
        exact sin_add_le hnonneg1 hx hsum
      have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      calc Real.sin (((N : ℝ) + 1) * x)
          ≤ Real.sin ((N : ℝ) * x) + Real.sin x := hstep
        _ ≤ (N : ℝ) * Real.sin x + Real.sin x := add_le_add_left (ih hNxpi) _
        _ = ((N : ℝ) + 1) * Real.sin x := by ring

/-- For `N ≥ 2`, `0 < x ≤ π/2`, and `N * x ≤ π`, one has `sin(N * x) < N * sin x`. -/
private theorem sin_lt_mul_sin {N : ℕ} {x : ℝ} (hN : 2 ≤ N) (hx : 0 < x)
    (hx2 : x ≤ Real.pi / 2) (hNpi : (N : ℝ) * x ≤ Real.pi) :
    Real.sin ((N : ℝ) * x) < (N : ℝ) * Real.sin x := by
  have hbase : Real.sin (2 * x) < 2 * Real.sin x := by
    have hsx : 0 < Real.sin x := by
      apply Real.sin_pos_of_pos_of_lt_pi hx
      nlinarith [Real.pi_pos, hx2]
    have hcx : Real.cos x < 1 := by
      rcases eq_or_ne (Real.cos x) 1 with h | h
      · exfalso
        rw [Real.cos_eq_one_iff] at h
        obtain ⟨k, hk⟩ := h
        rcases lt_or_ge k 1 with hk1 | hk1
        · have hk0 : k ≤ 0 := by omega
          have hkR : ((k : ℝ)) ≤ 0 := by exact_mod_cast hk0
          rw [← hk] at hx
          nlinarith [Real.pi_pos, hkR]
        · have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
          rw [← hk] at hx hx2
          nlinarith [Real.pi_pos, hkR]
      · exact lt_of_le_of_ne (Real.cos_le_one x) h
    calc Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
          rw [(by ring : 2 * x = x + x), Real.sin_add]
          ring
      _ < 2 * Real.sin x * 1 := mul_lt_mul_of_pos_left hcx (by positivity)
      _ = 2 * Real.sin x := by rw [mul_one]
  have hle : (((N - 2 : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast (by omega)
  have hN2pi : (((N - 2 : ℕ) : ℝ)) * x ≤ Real.pi := by
    nlinarith [hNpi, mul_le_mul_of_nonneg_right hle hx.le]
  have hc2 : (((N - 2 : ℕ) : ℝ)) + 2 = (N : ℝ) := by exact_mod_cast (by omega)
  have heq : (((N - 2 : ℕ) : ℝ)) * x + 2 * x = (N : ℝ) * x := by
    rw [← hc2]
    ring
  have h1 : 0 ≤ Real.sin ((((N - 2 : ℕ) : ℝ)) * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hN2pi
  have h2 : 0 ≤ Real.sin (2 * x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [hNpi])
  have ha1 : 0 ≤ (((N - 2 : ℕ) : ℝ)) * x := by positivity
  have hb2 : 0 ≤ 2 * x := by positivity
  have hcomb : Real.sin ((((N - 2 : ℕ) : ℝ)) * x + 2 * x)
      ≤ Real.sin ((((N - 2 : ℕ) : ℝ)) * x) + Real.sin (2 * x) :=
    sin_add_le ha1 hb2 (by rw [heq]; exact hNpi)
  calc Real.sin ((N : ℝ) * x)
      = Real.sin ((((N - 2 : ℕ) : ℝ)) * x + 2 * x) := by rw [heq]
    _ ≤ Real.sin ((((N - 2 : ℕ) : ℝ)) * x) + Real.sin (2 * x) := hcomb
    _ < (((N - 2 : ℕ) : ℝ)) * Real.sin x + 2 * Real.sin x :=
        add_lt_add_of_le_of_lt (sin_le_mul_sin hx.le hN2pi) hbase
    _ = (N : ℝ) * Real.sin x := by
        rw [← hc2]
        ring

/-- The real number `π` is strictly less than `15/4`. -/
private theorem pi_lt_fifteen_quarters : Real.pi < 15 / 4 := by
  have h1 : (0 : ℝ) < 15 / 16 := by norm_num
  have h2 : (15 : ℝ) / 16 ≤ 1 := by norm_num
  have h3 : 15 / 16 - (15 / 16) ^ 3 / 4 < Real.sin (15 / 16) := by
    linarith [Real.sin_gt_sub_cube h1]
  have ha : (0 : ℝ) < 15 / 16 - (15 / 16) ^ 3 / 4 := by norm_num
  have hsq : (1 / 2 : ℝ) < (15 / 16 - (15 / 16) ^ 3 / 4) ^ 2 := by norm_num
  have hspos : 0 < Real.sin (15 / 16) := by
    apply Real.sin_pos_of_pos_of_lt_pi h1
    have h2pi := Real.two_le_pi
    nlinarith
  have hcos : Real.cos (15 / 8) = 1 - 2 * Real.sin (15 / 16) ^ 2 := by
    have h := Real.cos_two_mul' (15 / 16)
    rw [(by norm_num : (15 / 8 : ℝ) = 2 * (15 / 16)), h,
      ← Real.sin_sq_add_cos_sq (15 / 16)]
    ring
  have hcosneg : Real.cos (15 / 8) < 0 := by
    rw [hcos]
    nlinarith [h3, hsq, mul_pos hspos hspos, ha]
  rcases le_or_gt (15 / 8) (Real.pi / 2) with hle | hlt
  · exfalso
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := 15 / 8) (y := Real.pi / 2)
      (by norm_num) (show Real.pi / 2 ≤ Real.pi by linarith) hle
    rw [Real.cos_pi_div_two] at hc
    linarith
  · linarith

/-- For all sufficiently large root orders, the right-arc phase expectation is real with real
part strictly between `1/2` and `1` [Tang and Wright, Lemma 2.3][TangWright2025]. -/
theorem lemma23_mu1_bounds :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      (cExpect (mu1 q) (rightPhase q)).im = 0 ∧
      (1 / 2 : ℝ) < (cExpect (mu1 q) (rightPhase q)).re ∧
      (cExpect (mu1 q) (rightPhase q)).re < 1 := by
  refine ⟨500, ?_⟩
  intro q hq
  have hq4 : 4 ≤ q := by omega
  have hq0 : 0 < q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hqRne : ((q : ℝ)) ≠ 0 := ne_of_gt hqR
  have hd := rightPhase_dirichlet (by omega : 2 ≤ q)
  have hE : cExpect (mu1 q) (rightPhase q)
      = Complex.ofReal ((((halfCount q : ℕ) : ℝ)⁻¹
        * (Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
          / Real.sin (Real.pi / (q : ℝ))))) := by
    simp only [cExpect, mu1]
    rw [← Finset.mul_sum, hd, sin_ofReal', sin_ofReal',
      ← Complex.ofReal_div, ← Complex.ofReal_mul]

  have ht : (0 : ℝ) < Real.pi / (q : ℝ) := by positivity
  have ht2 : Real.pi / (q : ℝ) ≤ Real.pi / 2 := by
    have h2q : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 2 ≤ q by omega)
    rw [div_le_div_iff₀ hqR (by norm_num)]
    nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin (Real.pi / (q : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi ht
    rw [div_lt_iff₀ hqR]
    have hq4R : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq4
    nlinarith [Real.pi_pos, hq4R]

  have hdm : (q : ℝ) = 4 * ((q / 4 : ℕ) : ℝ) + ((q % 4 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod q 4).symm
  have hmod3 : ((q % 4 : ℕ) : ℝ) ≤ 3 := by
    exact_mod_cast (by omega)
  have hh : ((halfCount q : ℕ) : ℝ) = 2 * ((q / 4 : ℕ) : ℝ) + 1 := by
    simp only [halfCount]
    push_cast
    ring
  have hcgrow : ((q : ℝ) - 1) / 2 ≤ ((halfCount q : ℕ) : ℝ) := by
    rw [hh]
    linarith
  have hcshrink : ((halfCount q : ℕ) : ℝ) ≤ (q : ℝ) / 2 + 1 := by
    rw [hh]
    linarith
  have hqt : (q : ℝ) * (Real.pi / (q : ℝ)) = Real.pi := by
    field_simp

  have hlower : Real.pi / 2 - Real.pi / (q : ℝ)
      ≤ ((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right hcgrow ht.le
    have h2 : ((q : ℝ) - 1) / 2 * (Real.pi / (q : ℝ))
        = (Real.pi - Real.pi / (q : ℝ)) / 2 := by
      rw [div_mul_eq_mul_div, sub_mul, hqt, one_mul]
    rw [h2] at h1
    linarith
  have hupper : ((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))
      ≤ Real.pi / 2 + Real.pi / (q : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hcshrink ht.le
    have h2 : ((q : ℝ) / 2 + 1) * (Real.pi / (q : ℝ))
        = Real.pi / 2 + Real.pi / (q : ℝ) := by
      rw [add_mul, div_mul_eq_mul_div, hqt, one_mul]
    rw [h2] at h1
    exact h1
  have hwindow : Real.cos (Real.pi / (q : ℝ))
      ≤ Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))) := by
    have habs : |((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)) - Real.pi / 2|
        ≤ Real.pi / (q : ℝ) := by
      rw [abs_le]
      constructor <;> linarith [hlower, hupper]
    have hcongr : Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
        = Real.cos (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)) - Real.pi / 2) := by
      rw [← Real.cos_neg, neg_sub, Real.cos_pi_div_two_sub]
    rw [hcongr]
    have hcosabs : Real.cos (Real.pi / (q : ℝ))
        ≤ Real.cos |((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)) - Real.pi / 2| := by
      refine Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (show Real.pi / (q : ℝ) ≤ Real.pi by linarith [ht2]) habs
    rcases le_or_gt 0 (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)) - Real.pi / 2)
      with hpos | hneg
    · rw [abs_of_nonneg hpos] at hcosabs
      exact hcosabs
    · rw [abs_of_neg hneg, Real.cos_neg] at hcosabs
      exact hcosabs
  have hcoslb : 1 - (Real.pi / (q : ℝ)) ^ 2 / 2 ≤ Real.cos (Real.pi / (q : ℝ)) := by
    have hid : Real.cos (Real.pi / (q : ℝ))
        = 1 - 2 * Real.sin ((Real.pi / (q : ℝ)) / 2) ^ 2 := by
      have h := Real.cos_two_mul' ((Real.pi / (q : ℝ)) / 2)
      rw [(by field_simp : (Real.pi / (q : ℝ) : ℝ)
          = 2 * ((Real.pi / (q : ℝ)) / 2)), h,
        ← Real.sin_sq_add_cos_sq ((Real.pi / (q : ℝ)) / 2)]
      ring
    have hsinle : Real.sin ((Real.pi / (q : ℝ)) / 2) ≤ (Real.pi / (q : ℝ)) / 2 :=
      Real.sin_le (by positivity)
    have hsin2 : 0 ≤ Real.sin ((Real.pi / (q : ℝ)) / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
        (by nlinarith [ht2, Real.pi_le_four])
    rw [hid]
    nlinarith [hsinle, hsin2, mul_nonneg hsin2 hsin2]
  have hsmall : Real.pi / (q : ℝ) ≤ 1 / 100 := by
    rw [div_le_iff₀ hqR]
    have h4 := Real.pi_le_four
    have hq500 : (500 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith [h4, hq500, (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  have hden : ((halfCount q : ℕ) : ℝ) * Real.sin (Real.pi / (q : ℝ))
      ≤ Real.pi / 2 + Real.pi / (q : ℝ) := by
    have h1 : Real.sin (Real.pi / (q : ℝ)) ≤ Real.pi / (q : ℝ) := Real.sin_le ht.le
    have hhc : (0 : ℝ) ≤ ((halfCount q : ℕ) : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hhc, hupper]
  refine ⟨?_, ?_, ?_⟩
  · rw [hE, Complex.ofReal_im]
  · rw [hE, Complex.ofReal_re]
    have hc2 : 2 ≤ halfCount q := by simp only [halfCount]; omega
    have hchc : (0 : ℝ) < ((halfCount q : ℕ) : ℝ) :=
      by exact_mod_cast (show 0 < halfCount q by omega)
    have hA : (0 : ℝ) < 1 - (Real.pi / (q : ℝ)) ^ 2 / 2 := by nlinarith [hsmall]
    have hsh := le_trans hcoslb hwindow
    have hP : (0 : ℝ) < Real.pi / 2 + Real.pi / (q : ℝ) := by positivity
    have hstep : ((halfCount q : ℕ) : ℝ)⁻¹
        * (Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
          / Real.sin (Real.pi / (q : ℝ)))
        ≥ (1 - (Real.pi / (q : ℝ)) ^ 2 / 2) / (Real.pi / 2 + Real.pi / (q : ℝ)) := by
      rw [ge_iff_le, inv_mul_eq_div, div_le_div_iff₀ hP hchc, div_mul_eq_mul_div,
        le_div_iff₀ hsinpos]
      have hsinnn : (0 : ℝ) ≤ Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))) :=
        le_trans hA.le hsh
      have h1 : ((halfCount q : ℕ) : ℝ) * Real.sin (Real.pi / (q : ℝ))
          * (1 - (Real.pi / (q : ℝ)) ^ 2 / 2)
          ≤ ((halfCount q : ℕ) : ℝ) * Real.sin (Real.pi / (q : ℝ))
            * Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hsh (mul_nonneg hchc.le hsinpos.le)
      have h2 : ((halfCount q : ℕ) : ℝ) * Real.sin (Real.pi / (q : ℝ))
          * Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
          ≤ (Real.pi / 2 + Real.pi / (q : ℝ))
            * Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ))) :=
        mul_le_mul_of_nonneg_right hden hsinnn
      linarith
    have hpi : Real.pi / 2 + Real.pi / (q : ℝ) ≤ 15 / 8 + 1 / 100 := by
      nlinarith [hsmall, pi_lt_fifteen_quarters]
    have hnum' : (1 - (1 / 100 : ℝ) ^ 2 / 2)
        ≤ 1 - (Real.pi / (q : ℝ)) ^ 2 / 2 := by
      nlinarith [hsmall, ht.le, (by norm_num : (0 : ℝ) ≤ 1 / 100)]
    have hlast : (1 / 2 : ℝ) < (1 - (1 / 100 : ℝ) ^ 2 / 2) / (15 / 8 + 1 / 100) := by
      norm_num
    have hmid : (1 - (1 / 100 : ℝ) ^ 2 / 2) / (15 / 8 + 1 / 100)
        ≤ (1 - (Real.pi / (q : ℝ)) ^ 2 / 2) / (Real.pi / 2 + Real.pi / (q : ℝ)) := by
      have hnP : (0 : ℝ) ≤ Real.pi / 2 + Real.pi / (q : ℝ) := le_of_lt hP
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 15 / 8 + 1 / 100) hP]
      have e1 : (1 - (1 / 100 : ℝ) ^ 2 / 2) * (Real.pi / 2 + Real.pi / (q : ℝ))
          ≤ (1 - (Real.pi / (q : ℝ)) ^ 2 / 2) * (Real.pi / 2 + Real.pi / (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hnum' hnP
      have e2 : (1 - (Real.pi / (q : ℝ)) ^ 2 / 2) * (Real.pi / 2 + Real.pi / (q : ℝ))
          ≤ (1 - (Real.pi / (q : ℝ)) ^ 2 / 2) * (15 / 8 + 1 / 100) :=
        mul_le_mul_of_nonneg_left hpi hA.le
      linarith
    linarith
  · rw [hE, Complex.ofReal_re]
    have hc2 : 2 ≤ halfCount q := by simp only [halfCount]; omega
    have hchc : (0 : ℝ) < ((halfCount q : ℕ) : ℝ) :=
      by exact_mod_cast (show 0 < halfCount q by omega)
    have hinv : (0 : ℝ) < ((halfCount q : ℕ) : ℝ)⁻¹ := inv_pos.mpr hchc
    have hcpi : ((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)) ≤ Real.pi := by
      linarith [hupper, ht2]
    have hstrict := sin_lt_mul_sin (N := halfCount q) hc2 ht ht2 hcpi
    have hdiv2 : Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
        / Real.sin (Real.pi / (q : ℝ)) < ((halfCount q : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hsinpos]
      exact hstrict
    calc (((halfCount q : ℕ) : ℝ)⁻¹
        * (Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
          / Real.sin (Real.pi / (q : ℝ))))
        = (Real.sin (((halfCount q : ℕ) : ℝ) * (Real.pi / (q : ℝ)))
          / Real.sin (Real.pi / (q : ℝ))) * ((halfCount q : ℕ) : ℝ)⁻¹ := by ring
      _ < ((halfCount q : ℕ) : ℝ) * ((halfCount q : ℕ) : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_right hdiv2 hinv
      _ = 1 := mul_inv_cancel₀ hchc.ne'

end Qatlib.Papers.AmpInvReqTang26.RootLaws
