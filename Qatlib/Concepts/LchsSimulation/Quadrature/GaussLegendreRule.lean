/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.Quadrature.GaussLegendreAuxiliary

/-!
# Gauss-Legendre rules and cell remainder bounds

The module constructs positive Gauss-Legendre rules with distinct interior nodes, polynomial
exactness through degree `2 * Q - 1`, and the nodal-product integral formula. It proves the
correctly parenthesized cell remainder estimate and refutes the version with the quadrature sum
placed inside the integral. See [AnChildsLin2026] for the mathematical setting.

## Main statements

* `gauss_legendre_rule_exists`: For every positive `Q`, there exist distinct nodes in `(-1, 1)`
  and positive weights exact through degree `2 * Q - 1`, satisfying the stated squared
  nodal-product integral formula.
* `gauss_legendre_cell_error_bound`: For a positive cell width and a function of class `C^(2 *
  Q)`, the stated polynomial exactness and nodal-product identity bound the absolute quadrature
  error by the Gauss factorial coefficient times the supremum of the absolute `2 * Q`-th
  derivative.
* `gauss_legendre_cell_error_bound_false`: The proposed universal remainder inequality with the
  quadrature sum inside the interval integral is false.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.Quadrature
open Set MeasureTheory
open scoped BigOperators

/-- The midpoint rule integrates every real polynomial of natural degree at most one exactly on
any interval from `a` to `b`. -/
theorem gauss_midpoint_exact_linear (a b : ℝ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ 1) :
    (∫ x in a..b, p.eval x) = (b - a) * p.eval ((a + b) / 2) := by
  obtain ⟨u, v, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hp
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hc : Continuous (fun x : ℝ => u * x) := by fun_prop
  have hv : Continuous (fun _ : ℝ => v) := continuous_const
  rw [intervalIntegral.integral_add
    (hc.intervalIntegrable a b) (hv.intervalIntegrable a b),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- There exists a one-node positive Gauss-Legendre rule on `[-1, 1]` with an interior node,
degree-one exactness, and the stated squared nodal-product integral. -/
theorem gauss_legendre_rule_one : ∃ node weight : Fin 1 → ℝ,
    (∀ q, node q ∈ Ioo (-1) 1) ∧ Function.Injective node ∧ (∀ q, 0 < weight q) ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * 1 - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
    (∫ t in (-1 : ℝ)..1, ∏ q : Fin 1, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * 1 + 1) * (Nat.factorial 1 : ℝ) ^ 4) /
        (((2 * 1 + 1 : ℕ) : ℝ) * ((Nat.factorial (2 * 1) : ℕ) : ℝ) ^ 2) := by
  refine ⟨fun _ => 0, fun _ => 2, ?_, ?_, ?_, ?_, ?_⟩
  · intro q; norm_num
  · intro q r _; exact Subsingleton.elim q r
  · intro q; norm_num
  · intro p hp
    have hh := gauss_midpoint_exact_linear (-1) 1 p (by simpa using hp)
    norm_num at hh ⊢
    exact hh
  · norm_num [integral_pow]

/-- The proposed universal remainder inequality with the quadrature sum inside the interval
integral is false. -/
theorem gauss_legendre_cell_error_bound_false : ¬ (
    ∀ (Q : ℕ) (a h : ℝ) (node weight : Fin Q → ℝ) (f : ℝ → ℝ),
      1 ≤ Q → 0 < h →
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
        ∫ x in a..a + h, p.eval x =
          ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2)) →
      (∫ x in a..a + h, ∏ q : Fin Q, (x - (a + h * (node q + 1) / 2)) ^ 2) =
        (h ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) →
      ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) f →
      |∫ k in a..a + h, f k -
          ∑ q, (h / 2) * weight q * f (a + h * (node q + 1) / 2)| ≤
        ((Q.factorial : ℝ) ^ 4 * h ^ ((2 : ℝ) * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
          (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|)) := by
  intro hb
  have he : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * 1 - 1 →
      ∫ x in (0 : ℝ)..0 + 2, p.eval x =
        ∑ q : Fin 1, (2 / 2 : ℝ) * (2 : ℝ) * p.eval (0 + 2 * ((0 : ℝ) + 1) / 2) := by
    intro p hp
    have hh := gauss_midpoint_exact_linear 0 2 p (by simpa using hp)
    simpa using hh
  have hω : (∫ x in (0 : ℝ)..0 + 2,
      ∏ q : Fin 1, (x - (0 + 2 * ((0 : ℝ) + 1) / 2)) ^ 2) =
      (2 ^ (2 * 1 + 1) * (Nat.factorial 1 : ℝ) ^ 4) /
        (((2 * 1 + 1 : ℕ) : ℝ) * ((Nat.factorial (2 * 1) : ℕ) : ℝ) ^ 2) := by
    norm_num only [Fin.prod_univ_one, zero_add, zero_add, one_mul, mul_one,
      Nat.factorial, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat,
      div_self (by norm_num : (2 : ℝ) ≠ 0), one_pow]
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ 2) 1, integral_pow]
    norm_num
  have hh := hb 1 0 2 (fun _ => 0) (fun _ => 2) (fun _ => 1)
    (by norm_num) (by norm_num) he hω contDiff_const
  norm_num [iteratedDeriv_const, intervalIntegral.integral_const] at hh

/-- Any rule exact for the stated polynomial degree range on `[-1, 1]` has total weight two. -/
theorem gauss_rule_weight_sum (Q : ℕ) (node weight : Fin Q → ℝ)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) :
    ∑ q, weight q = 2 := by
  have hh := hexact 1 (by simp)
  norm_num at hh
  exact hh.symm

/-- Polynomial exactness on `[-1, 1]` transfers to the affinely rescaled cell `[a, a + h]` with
weights multiplied by `h / 2`. -/
theorem gauss_cell_rule_affine_exact (Q : ℕ) (a h : ℝ) (node weight : Fin Q → ℝ)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q))
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 2 * Q - 1) :
    (∫ x in a..a + h, p.eval x) =
      ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2) := by
  let u : Polynomial ℝ := Polynomial.C (h / 2) * Polynomial.X + Polynomial.C (a + h / 2)
  have hu : u.natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact le_trans Polynomial.natDegree_mul_le (by simp)
    · simp
  have hc : (p.comp u).natDegree ≤ 2 * Q - 1 :=
    (Polynomial.natDegree_comp_le.trans
      (Nat.mul_le_mul_left _ hu)).trans (by simpa using hp)
  have he := hexact (p.comp u) hc
  simp only [Polynomial.eval_comp, u, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X] at he
  have ht := intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    p.eval (h / 2) (a + h / 2)
  simp only [smul_eq_mul] at ht
  have hlo : h / 2 * (-1) + (a + h / 2) = a := by ring
  have hhi : h / 2 * 1 + (a + h / 2) = a + h := by ring
  rw [hlo, hhi] at ht
  rw [← ht, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [show a + h * (node q + 1) / 2 = h / 2 * node q + (a + h / 2) by ring]
  ring

/-- For a polynomial within the exactness degree range, the absolute difference between its cell
integral and the quadrature sum is zero. -/
theorem gauss_cell_polynomial_error_eq_zero (Q : ℕ) (a h : ℝ)
    (node weight : Fin Q → ℝ)
    (hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in a..a + h, p.eval x =
        ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2))
    (p : Polynomial ℝ) (hp : p.natDegree ≤ 2 * Q - 1) :
    |(∫ x in a..a + h, p.eval x) -
      ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2)| = 0 := by
  rw [hexact p hp, sub_self, abs_zero]

/-- The Rodrigues seed polynomial `(Polynomial.X * Polynomial.X - 1)^Q`. -/
private def rodPoly (Q : ℕ) : Polynomial ℝ :=
  (Polynomial.X * Polynomial.X - 1) ^ Q

/-- The Rodrigues seed `rodPoly Q` equals `(Polynomial.X * Polynomial.X - 1)^Q`. -/
private theorem rodPoly_def (Q : ℕ) :
    rodPoly Q = (Polynomial.X * Polynomial.X - 1) ^ Q := rfl

/-- The real value of `rodPoly Q` at `x` is `(x * x - 1)^Q`. -/
private theorem eval_rodPoly (Q : ℕ) (x : ℝ) :
    (rodPoly Q).eval x = (x * x - 1) ^ Q := by
  rw [rodPoly_def, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_one]

/-- The polynomial `Polynomial.X * Polynomial.X - 1` is monic. -/
private theorem monic_XmulX_sub_one :
    (Polynomial.X * Polynomial.X - 1 : Polynomial ℝ).Monic := by
  rw [show (Polynomial.X * Polynomial.X - 1 : Polynomial ℝ) =
      (Polynomial.X - Polynomial.C (1 : ℝ)) * (Polynomial.X + Polynomial.C (1 : ℝ)) by
        simp only [Polynomial.C_1]
        ring]
  exact (Polynomial.monic_X_sub_C (1 : ℝ)).mul (Polynomial.monic_X_add_C (1 : ℝ))

/-- The natural degree of `Polynomial.X * Polynomial.X - 1` is two. -/
private theorem natDegree_XmulX_sub_one :
    (Polynomial.X * Polynomial.X - 1 : Polynomial ℝ).natDegree = 2 := by
  rw [show (Polynomial.X * Polynomial.X - 1 : Polynomial ℝ) =
      (Polynomial.X - Polynomial.C (1 : ℝ)) * (Polynomial.X + Polynomial.C (1 : ℝ)) by
        simp only [Polynomial.C_1]
        ring,
    (Polynomial.monic_X_sub_C (1 : ℝ)).natDegree_mul (Polynomial.monic_X_add_C (1 : ℝ)),
    Polynomial.natDegree_X_sub_C, Polynomial.natDegree_X_add_C]

/-- The Rodrigues seed polynomial `rodPoly Q` is monic. -/
private theorem rodPoly_monic (Q : ℕ) : (rodPoly Q).Monic :=
  monic_XmulX_sub_one.pow Q

/-- The Rodrigues seed polynomial `rodPoly Q` is nonzero. -/
private theorem rodPoly_ne_zero (Q : ℕ) : rodPoly Q ≠ 0 :=
  (rodPoly_monic Q).ne_zero

/-- The natural degree of `rodPoly Q` is `2 * Q`. -/
private theorem natDegree_rodPoly (Q : ℕ) : (rodPoly Q).natDegree = 2 * Q := by
  rw [rodPoly_def, monic_XmulX_sub_one.natDegree_pow, natDegree_XmulX_sub_one]
  omega

/-- The polynomial `Polynomial.X * Polynomial.X - 1` evaluates to `x * x - 1` at `x`. -/
private theorem eval_XmulX_sub_one (x : ℝ) :
    (Polynomial.X * Polynomial.X - 1 : Polynomial ℝ).eval x = x * x - 1 := by
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one]

/-- Every derivative of `rodPoly Q` of order less than `Q` vanishes at a real point satisfying
`x * x = 1`. -/
private theorem rodPoly_iterate_eval_endpoints {Q k : ℕ} (hk : k < Q) (x : ℝ)
    (hx : x * x = 1) : (Polynomial.derivative^[k] (rodPoly Q)).eval x = 0 := by
  have hdvd : (Polynomial.X * Polynomial.X - 1 : Polynomial ℝ) ^ (Q - k) ∣
      Polynomial.derivative^[k] (rodPoly Q) :=
    Polynomial.pow_sub_dvd_iterate_derivative_pow _ _ _
  obtain ⟨s, hs⟩ := hdvd
  rw [hs, Polynomial.eval_mul, Polynomial.eval_pow, eval_XmulX_sub_one, hx, sub_self,
    zero_pow (Nat.sub_ne_zero_of_lt hk), zero_mul]

/-- The `Q`-fold derivative of `rodPoly Q` is orthogonal on `[-1, 1]` to every polynomial of
natural degree less than `Q`. -/
private theorem rodPoly_orthogonal (Q : ℕ) (g : Polynomial ℝ) (hg : g.natDegree < Q) :
    ∫ x in (-1 : ℝ)..1, (Polynomial.derivative^[Q] (rodPoly Q)).eval x * g.eval x = 0 := by
  rw [Qatlib.Concepts.LchsSimulation.Quadrature.integral_poly_iterate_parts (rodPoly Q) Q g (-1) 1
    (fun k hk => ⟨rodPoly_iterate_eval_endpoints hk (-1) (by norm_num),
      rodPoly_iterate_eval_endpoints hk 1 (by norm_num)⟩),
    Polynomial.iterate_derivative_eq_zero hg]
  simp

/-- The integral of `rodPoly Q` over `[-1, 1]` equals the stated signed factorial expression
`(-1)^Q * (2 * 4^Q * (Q.factorial)^2 / (2 * Q + 1).factorial)`. -/
private theorem integral_rodPoly (Q : ℕ) :
    ∫ x in (-1 : ℝ)..1, (rodPoly Q).eval x =
      (-1 : ℝ) ^ Q * (2 * 4 ^ Q * ((Q.factorial : ℝ) * (Q.factorial : ℝ)) /
        ((2 * Q + 1 : ℕ).factorial : ℝ)) := by
  have hpt : ∀ x : ℝ, (rodPoly Q).eval x = (-1 : ℝ) ^ Q * (1 - x ^ 2) ^ Q := by
    intro x
    rw [eval_rodPoly, show x * x - 1 = -((1 : ℝ) - x * x) by ring,
      neg_pow]
    ring
  have hI : ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) ^ Q =
      2 * 4 ^ Q * ((Q.factorial : ℝ) * (Q.factorial : ℝ)) /
        ((2 * Q + 1 : ℕ).factorial : ℝ) := by
    have ht := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => (1 - x ^ 2) ^ Q) (2 : ℝ) (-(1 : ℝ))
    rw [show (2 : ℝ) * 0 + -(1 : ℝ) = -1 by ring, show (2 : ℝ) * 1 + -(1 : ℝ) = 1 by ring] at ht
    rw [← ht, smul_eq_mul,
      intervalIntegral.integral_congr (fun t _ => by
        show (1 - (2 * t + -(1 : ℝ)) ^ 2) ^ Q = 4 ^ Q * (t ^ Q * (1 - t) ^ Q)
        have h1 : 1 - (2 * t + -(1 : ℝ)) ^ 2 = 4 * (t * (1 - t)) := by ring
        rw [h1, mul_pow, mul_pow]),
      intervalIntegral.integral_const_mul, Qatlib.Concepts.LchsSimulation.Quadrature.integral_pow_mul_one_sub_pow]
    have hQ21 : Q + Q + 1 = 2 * Q + 1 := by omega
    rw [hQ21]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x), intervalIntegral.integral_const_mul,
    hI]

/-- For `k ≤ Q`, the natural degree of the `k`-fold derivative of `rodPoly Q` is `2 * Q - k`. -/
private theorem natDegree_iterate_deriv_rodPoly (Q : ℕ) : ∀ k : ℕ, k ≤ Q →
    (Polynomial.derivative^[k] (rodPoly Q)).natDegree = 2 * Q - k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Function.iterate_zero_apply, natDegree_rodPoly]
    omega
  | succ k ih =>
    intro hk
    have hk' : k < Q := by omega
    have hndk := ih hk'.le
    have hp0 : (Polynomial.derivative^[k] (rodPoly Q)) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hndk
      omega
    have hpos : 0 < (Polynomial.derivative^[k] (rodPoly Q)).natDegree := by omega
    rw [Function.iterate_succ_apply',
        (Qatlib.Concepts.LchsSimulation.Quadrature.natDegree_derivative_eq hp0 hpos).1]
    omega

/-- For positive `Q`, the `Q`-fold derivative of `rodPoly Q` is nonzero. -/
private theorem legendre_deriv_ne_zero (Q : ℕ) (hQ : 1 ≤ Q) :
    Polynomial.derivative^[Q] (rodPoly Q) ≠ 0 := by
  intro h0
  have hnd := natDegree_iterate_deriv_rodPoly Q Q (le_refl Q)
  rw [h0, Polynomial.natDegree_zero] at hnd
  omega

/-- For `k ≤ Q`, the leading coefficient of the `k`-fold derivative of `rodPoly Q` is `(2 *
Q).factorial / (2 * Q - k).factorial`. -/
private theorem leadingCoeff_iterate_deriv_rodPoly (Q : ℕ) : ∀ k : ℕ, k ≤ Q →
    (Polynomial.derivative^[k] (rodPoly Q)).leadingCoeff =
      ((2 * Q).factorial : ℝ) / ((2 * Q - k).factorial : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Function.iterate_zero_apply, (rodPoly_monic Q).leadingCoeff, Nat.sub_zero,
      div_self (by positivity)]
  | succ k ih =>
    intro hk
    have hk' : k < Q := by omega
    have hndk := natDegree_iterate_deriv_rodPoly Q k hk'.le
    have hp0 : (Polynomial.derivative^[k] (rodPoly Q)) ≠ 0 := by
      intro h0
      rw [h0, Polynomial.natDegree_zero] at hndk
      omega
    have hpos : 0 < (Polynomial.derivative^[k] (rodPoly Q)).natDegree := by omega
    have hfac : ((2 * Q - k).factorial : ℝ) =
        ((2 * Q - k : ℕ) : ℝ) * ((2 * Q - k - 1).factorial : ℝ) := by
      rw [show 2 * Q - k = (2 * Q - k - 1) + 1 by omega, Nat.factorial_succ]
      push_cast
      ring
    rw [show 2 * Q - (k + 1) = 2 * Q - k - 1 from by omega,
      Function.iterate_succ_apply', (Qatlib.Concepts.LchsSimulation.Quadrature.natDegree_derivative_eq hp0 hpos).2, hndk,
      ih hk'.le, hfac]
    have h1 : ((2 * Q - k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : ((2 * Q - k - 1).factorial : ℝ) ≠ 0 := by positivity
    have h3 : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
    field_simp

/-- For positive `Q`, the `Q`-fold derivative of `rodPoly Q` has at least `Q` distinct roots of
odd multiplicity in `(-1, 1)`. -/
private theorem legendre_odd_root_count (Q : ℕ) (hQ : 1 ≤ Q) :
    Q ≤ (Finset.filter (fun ρ => ρ ∈ Ioo (-1 : ℝ) 1 ∧
        Odd ((Polynomial.derivative^[Q] (rodPoly Q)).rootMultiplicity ρ))
      (Polynomial.derivative^[Q] (rodPoly Q)).roots.toFinset).card := by
  by_contra hcon
  push Not at hcon
  set P : Polynomial ℝ := Polynomial.derivative^[Q] (rodPoly Q) with hPdef
  set D : Finset ℝ := Finset.filter (fun ρ => ρ ∈ Ioo (-1 : ℝ) 1 ∧ Odd (P.rootMultiplicity ρ))
      P.roots.toFinset with hDdef
  have hPne : P ≠ 0 := by
    rw [hPdef]
    exact legendre_deriv_ne_zero Q hQ
  set S : Polynomial ℝ := ∏ ρ ∈ D, (Polynomial.X - Polynomial.C ρ) with hSdef
  have hSne : S ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ _ => Polynomial.X_sub_C_ne_zero ρ
  have hdegS : S.natDegree = D.card := by
    rw [hSdef, Polynomial.natDegree_prod_of_monic D
      (fun ρ => Polynomial.X - Polynomial.C ρ)
      (fun ρ _ => Polynomial.monic_X_sub_C ρ)]
    simp
  have horth' : ∫ x in (-1 : ℝ)..1, P.eval x * S.eval x = 0 := by
    rw [hPdef]
    exact rodPoly_orthogonal Q S (by rw [hdegS]; omega)
  have hTne : P * S ≠ 0 := mul_ne_zero hPne hSne
  have heven : ∀ ρ ∈ Ioo (-1 : ℝ) 1, Even ((P * S).rootMultiplicity ρ) := by
    intro ρ hρ
    rw [Polynomial.rootMultiplicity_mul hTne]
    have hSrM : S.rootMultiplicity ρ = if ρ ∈ D then 1 else 0 :=
      Qatlib.Concepts.LchsSimulation.Quadrature.rootMultiplicity_prod_X_sub_C D ρ
    rw [hSrM]
    by_cases hDmem : ρ ∈ D
    · rw [if_pos hDmem]
      obtain ⟨m, hm⟩ := (Finset.mem_filter.1 hDmem).2.2
      exact ⟨m + 1, by omega⟩
    · rw [if_neg hDmem]
      by_cases hroot : P.eval ρ = 0
      · have hmem : ρ ∈ P.roots.toFinset := by
          rw [Multiset.mem_toFinset]
          exact (Polynomial.mem_roots hPne).mpr hroot
        have hnotodd : ¬ Odd (P.rootMultiplicity ρ) := fun hodd =>
          hDmem (Finset.mem_filter.mpr ⟨hmem, ⟨hρ, hodd⟩⟩)
        rcases Nat.even_or_odd (P.rootMultiplicity ρ) with h | h
        · obtain ⟨m, hm⟩ := h
          exact ⟨m, by omega⟩
        · exact absurd h hnotodd
      · have hrM0 : P.rootMultiplicity ρ = 0 := by
          by_contra hpos
          have hlt : 0 < P.rootMultiplicity ρ := by omega
          exact hroot ((Polynomial.rootMultiplicity_pos'.mp hlt).2)
        exact ⟨0, by omega⟩
  obtain ⟨y, hy, hny0⟩ : ∃ y ∈ Ioo (-1 : ℝ) 1, (P * S).eval y ≠ 0 := by
    by_contra hcon2
    push Not at hcon2
    have hsub : Set.Ioo (-1 : ℝ) 1 ⊆ ((P * S).roots.toFinset : Set ℝ) := by
      intro y hy
      have hy0 : (P * S).eval y = 0 := hcon2 y hy
      rw [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hTne).mpr hy0
    exact (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1))
      ((Finset.finite_toSet _).subset hsub)
  have hnn := Qatlib.Concepts.LchsSimulation.Quadrature.sign_of_even_rootMultiplicity (P * S) heven
  have hintT : ∫ x in (-1 : ℝ)..1, (P * S).eval x = 0 := by
    rw [intervalIntegral.integral_congr (fun _ _ => Polynomial.eval_mul)]
    exact horth'
  obtain ⟨U, hUne, hUnn, hUy, hintU⟩ : ∃ U : Polynomial ℝ, U ≠ 0 ∧
      (∀ x ∈ Ioo (-1 : ℝ) 1, 0 ≤ U.eval x) ∧ 0 < U.eval y ∧
      ∫ x in (-1 : ℝ)..1, U.eval x = 0 := by
    rcases hnn with h | h
    · refine ⟨P * S, hTne, h, ?_, hintT⟩
      rcases lt_or_ge ((P * S).eval y) 0 with hlt | hge
      · exact absurd hlt (not_lt.mpr (h y hy))
      · exact lt_of_le_of_ne hge (Ne.symm hny0)
    · refine ⟨-(P * S), neg_ne_zero.mpr hTne, fun x hx => by
          rw [Polynomial.eval_neg]
          exact neg_nonneg.mpr (h x hx), ?_, ?_⟩
      · rcases lt_or_ge ((P * S).eval y) 0 with hlt | hge
        · rw [Polynomial.eval_neg]
          exact neg_pos_of_neg hlt
        · exact absurd (lt_of_le_of_ne hge (Ne.symm hny0)) (not_lt.mpr (h y hy))
      · rw [intervalIntegral.integral_congr (fun x _ => Polynomial.eval_neg (P * S) x),
        intervalIntegral.integral_neg, hintT, neg_zero]
  have hUnnIcc : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ U.eval x := by
    intro x hx
    rcases lt_or_eq_of_le hx.1 with h1 | h1
    · rcases lt_or_eq_of_le hx.2 with h2 | h2
      · exact hUnn x ⟨h1, h2⟩
      · subst h2
        exact Qatlib.Concepts.LchsSimulation.Quadrature.nonneg_of_Ico (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval U) (by norm_num : (0 : ℝ) < 1)
          (fun t ht => hUnn t ⟨lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) ht.1, ht.2⟩)
    · subst h1
      exact Qatlib.Concepts.LchsSimulation.Quadrature.nonneg_of_Ioc (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval U) (by norm_num : (-1 : ℝ) < 0)
        (fun t ht => hUnn t ⟨ht.1, lt_of_le_of_lt ht.2 (by norm_num : (0 : ℝ) < 1)⟩)
  have hintpos : 0 < ∫ x in (-1 : ℝ)..1, U.eval x :=
    Qatlib.Concepts.LchsSimulation.Quadrature.integral_pos_of_nonneg_of_pos_at (by norm_num) (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval U) hUnnIcc
      ⟨hy.1.le, le_of_lt hy.2⟩ hUy
  rw [hintU] at hintpos
  exact absurd hintpos (lt_irrefl 0)

/-- For positive `Q`, the integral of the square of the `Q`-fold derivative of `rodPoly Q` over
`[-1, 1]` is `2 * 4^Q * (Q.factorial)^2 / (2 * Q + 1)`. -/
private theorem integral_legendre_sq (Q : ℕ) (hQ : 1 ≤ Q) :
    ∫ x in (-1 : ℝ)..1, ((Polynomial.derivative^[Q] (rodPoly Q)).eval x *
        (Polynomial.derivative^[Q] (rodPoly Q)).eval x) =
      2 * 4 ^ Q * ((Q.factorial : ℝ) * (Q.factorial : ℝ)) / ((2 * Q + 1 : ℕ) : ℝ) := by
  have key := Qatlib.Concepts.LchsSimulation.Quadrature.integral_poly_iterate_parts (rodPoly Q) Q
    (Polynomial.derivative^[Q] (rodPoly Q)) (-1) 1
    (fun k hk => ⟨rodPoly_iterate_eval_endpoints hk (-1) (by norm_num),
      rodPoly_iterate_eval_endpoints hk 1 (by norm_num)⟩)
  have h2Q : (Polynomial.derivative^[Q]) ((Polynomial.derivative^[Q]) (rodPoly Q)) =
      Polynomial.derivative^[2 * Q] (rodPoly Q) := by
    rw [show 2 * Q = Q + Q by omega, Function.iterate_add_apply]
  rw [h2Q,
      Qatlib.Concepts.LchsSimulation.Quadrature.iterate_derivative_eq_C (rodPoly_ne_zero Q)
      (natDegree_rodPoly Q)] at key
  rw [show (rodPoly Q).leadingCoeff = 1 from (rodPoly_monic Q).leadingCoeff] at key
  simp only [Polynomial.eval_C, mul_one] at key
  rw [intervalIntegral.integral_mul_const
    ((2 * Q).factorial : ℝ) (fun x : ℝ => (rodPoly Q).eval x)] at key
  rw [integral_rodPoly Q] at key
  rw [key]
  have hsign : ((-1 : ℝ) ^ Q) * ((-1 : ℝ) ^ Q) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  have hfac : ((2 * Q + 1 : ℕ).factorial : ℝ) =
      ((2 * Q + 1 : ℕ) : ℝ) * ((2 * Q).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h1 : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((2 * Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hfac, ← mul_assoc, ← mul_assoc, hsign, one_mul]
  field_simp

/-- For every positive `Q`, there exist distinct nodes in `(-1, 1)` and positive weights exact
through degree `2 * Q - 1`, satisfying the stated squared nodal-product integral formula.
See [AnChildsLin2026]. -/
theorem gauss_legendre_rule_exists : ∀ Q : ℕ, 1 ≤ Q → ∃ node weight : Fin Q → ℝ,
    (∀ q, node q ∈ Ioo (-1) 1) ∧ Function.Injective node ∧ (∀ q, 0 < weight q) ∧
    (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q)) ∧
    (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) := by
  intro Q hQ
  obtain ⟨E, hEsub, hEcard⟩ := Finset.exists_subset_card_eq (legendre_odd_root_count Q hQ)
  set e : Fin Q ≃o E := E.orderIsoOfFin hEcard with hedef
  set node : Fin Q → ℝ := fun q => (e q : ℝ) with hnodedef
  have hnodeIoo : ∀ q, node q ∈ Ioo (-1 : ℝ) 1 := by
    intro q
    have hD := hEsub (e q).2
    rw [Finset.mem_filter] at hD
    exact hD.2.1
  have hinj : Function.Injective node := by
    intro q q' hqq'
    exact e.injective (Subtype.ext hqq')
  have hnode_root : ∀ q, (Polynomial.derivative^[Q] (rodPoly Q)).eval (node q) = 0 := by
    intro q
    have hD := hEsub (e q).2
    rw [Finset.mem_filter] at hD
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (legendre_deriv_ne_zero Q hQ)] at hD
    exact hD.1
  set np : Polynomial ℝ := ∏ q : Fin Q, (Polynomial.X - Polynomial.C (node q)) with hnpdef
  have hnpmonic : np.Monic := by
    rw [hnpdef]
    exact Polynomial.monic_prod_X_sub_C node Finset.univ
  have hnpdeg : np.natDegree = Q := by
    rw [hnpdef, Polynomial.natDegree_prod_of_monic Finset.univ
      (fun q => Polynomial.X - Polynomial.C (node q))
      (fun q _ => Polynomial.monic_X_sub_C (node q))]
    simp
  have hnpnode : ∀ q, np.eval (node q) = 0 := by
    intro q
    rw [hnpdef, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
  have hPne0 : Polynomial.derivative^[Q] (rodPoly Q) ≠ 0 := legendre_deriv_ne_zero Q hQ
  have hPdeg : (Polynomial.derivative^[Q] (rodPoly Q)).natDegree = Q :=
    (natDegree_iterate_deriv_rodPoly Q Q (le_refl Q)).trans (by omega)
  set lc : ℝ := (Polynomial.derivative^[Q] (rodPoly Q)).leadingCoeff with hlcdef
  have hlcne : lc ≠ 0 := by
    rw [hlcdef]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne0
  have hPmod : (Polynomial.derivative^[Q] (rodPoly Q)) %ₘ np = 0 := by
    have hnpne1 : np ≠ 1 := by
      intro h1
      have h0 : np.natDegree = 0 := by rw [h1]; simp
      rw [h0] at hnpdeg
      omega
    exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
      (fun q => by
        rw [Polynomial.modByMonic_eq_sub_mul_div, Polynomial.eval_sub, Polynomial.eval_mul,
          hnpnode q, zero_mul, hnode_root q, sub_zero])
      ((Polynomial.natDegree_modByMonic_lt (Polynomial.derivative^[Q] (rodPoly Q)) hnpmonic
          hnpne1).trans_le (by rw [hnpdeg]; simp))
  have hquotne : (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np) ≠ 0 := by
    intro h0
    apply hPne0
    rw [← Polynomial.modByMonic_add_div (Polynomial.derivative^[Q] (rodPoly Q)) np, hPmod,
      zero_add, h0, mul_zero]
  have hquotdeg : (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np).natDegree = 0 := by
    have hmul : np * (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np)
        = Polynomial.derivative^[Q] (rodPoly Q) := by
      have h := Polynomial.modByMonic_add_div (Polynomial.derivative^[Q] (rodPoly Q)) np
      rw [hPmod, zero_add] at h
      exact h
    have hnd : (np * (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np)).natDegree
        = np.natDegree + (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np).natDegree :=
      hnpmonic.natDegree_mul' hquotne
    rw [hmul, hPdeg] at hnd
    omega
  have hquot : Polynomial.derivative^[Q] (rodPoly Q) /ₘ np = Polynomial.C lc := by
    have hmul : np * (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np)
        = Polynomial.derivative^[Q] (rodPoly Q) := by
      have h := Polynomial.modByMonic_add_div (Polynomial.derivative^[Q] (rodPoly Q)) np
      rw [hPmod, zero_add] at h
      exact h
    have hlcq : (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np).leadingCoeff = lc := by
      have h2 : (np * (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np)).leadingCoeff
          = (Polynomial.derivative^[Q] (rodPoly Q)).leadingCoeff := by rw [hmul]
      rw [Polynomial.leadingCoeff_mul'
        (show np.leadingCoeff * (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np).leadingCoeff ≠ 0 by
          rw [hnpmonic.leadingCoeff, one_mul]
          exact Polynomial.leadingCoeff_ne_zero.mpr hquotne),
        hnpmonic.leadingCoeff, one_mul] at h2
      exact h2
    refine Polynomial.eq_C_of_natDegree_eq_zero hquotdeg |>.trans ?_
    congr 1
    have hcc : (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np).coeff 0 =
        (Polynomial.derivative^[Q] (rodPoly Q) /ₘ np).leadingCoeff := by
      have hc := Polynomial.eq_C_of_natDegree_eq_zero hquotdeg
      exact ((congrArg Polynomial.leadingCoeff hc).trans (Polynomial.leadingCoeff_C _)).symm
    rw [hcc, hlcq]
  have hPfac : Polynomial.derivative^[Q] (rodPoly Q) = np * Polynomial.C lc := by
    have h := Polynomial.modByMonic_add_div (Polynomial.derivative^[Q] (rodPoly Q)) np
    rw [hPmod, zero_add, hquot] at h
    exact h.symm
  set weight : Fin Q → ℝ :=
    fun q => ∫ x in (-1 : ℝ)..1, (Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q).eval x with hweightdef
  have hnpne1 : np ≠ 1 := by
    intro h1
    have h0 : np.natDegree = 0 := by rw [h1, Polynomial.natDegree_one]
    rw [h0] at hnpdeg
    omega

  have hexact : ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
      ∫ x in (-1 : ℝ)..1, p.eval x = ∑ q, weight q * p.eval (node q) := by
    intro p hp
    have hrdeg : (p %ₘ np).natDegree < Q :=
      (Polynomial.natDegree_modByMonic_lt p hnpmonic hnpne1).trans_le (by rw [hnpdeg])
    have hsdeg : (p /ₘ np).natDegree < Q := by
      by_cases hs0 : p /ₘ np = 0
      · rw [hs0, Polynomial.natDegree_zero]
        omega
      · have hmul : p %ₘ np + np * (p /ₘ np) = p := Polynomial.modByMonic_add_div p np
        have hnd : (np * (p /ₘ np)).natDegree = np.natDegree + (p /ₘ np).natDegree :=
          hnpmonic.natDegree_mul' hs0
        have hlt : (p %ₘ np).natDegree < (np * (p /ₘ np)).natDegree := by
          rw [hnd]
          calc (p %ₘ np).natDegree < Q := hrdeg
            _ = np.natDegree := hnpdeg.symm
            _ ≤ np.natDegree + (p /ₘ np).natDegree := Nat.le_add_right _ _
        have hdegp : (p %ₘ np + np * (p /ₘ np)).natDegree = (np * (p /ₘ np)).natDegree :=
          Polynomial.natDegree_add_eq_right_of_natDegree_lt hlt
        rw [hmul] at hdegp
        omega
    have hpt : ∀ x : ℝ, np.eval x * (p /ₘ np).eval x
        = lc⁻¹ * ((Polynomial.derivative^[Q] (rodPoly Q)).eval x * (p /ₘ np).eval x) := by
      intro x
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hPfac]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      field_simp
    have hintnps : ∫ x in (-1 : ℝ)..1, np.eval x * (p /ₘ np).eval x = 0 := by
      rw [intervalIntegral.integral_congr (fun x _ => hpt x),
        intervalIntegral.integral_const_mul, rodPoly_orthogonal Q (p /ₘ np) hsdeg, mul_zero]
    have hint2 : IntervalIntegrable (fun x : ℝ => np.eval x * (p /ₘ np).eval x) volume (-1) 1 :=
      ((Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval np).mul (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval (p /ₘ np))).intervalIntegrable (-1) 1
    have hintp : ∫ x in (-1 : ℝ)..1, p.eval x = ∫ x in (-1 : ℝ)..1, (p %ₘ np).eval x := by
      rw [intervalIntegral.integral_congr (fun x _ => by
          rw [← Polynomial.modByMonic_add_div p np]),
        intervalIntegral.integral_congr (g := fun x =>
          (p %ₘ np).eval x + np.eval x * (p /ₘ np).eval x) (fun x _ => by
          rw [Polynomial.eval_add, Polynomial.eval_mul]),
        intervalIntegral.integral_add (Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval (p %ₘ np) (-1) 1)
          (hint2 : IntervalIntegrable (fun x : ℝ => np.eval x * (p /ₘ np).eval x) volume (-1) 1),
        hintnps, add_zero]
    have hlag : (p %ₘ np) = ∑ q, Polynomial.C ((p %ₘ np).eval (node q)) *
        Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q :=
      Qatlib.Concepts.LchsSimulation.Quadrature.lagrange_interpolation node hinj (p %ₘ np) hrdeg
    have hrnode : ∀ q, (p %ₘ np).eval (node q) = p.eval (node q) := by
      intro q
      have h := congrArg (Polynomial.eval (node q)) (Polynomial.modByMonic_add_div p np)
      rw [Polynomial.eval_add, Polynomial.eval_mul, hnpnode q, zero_mul, add_zero] at h
      exact h
    rw [hintp, intervalIntegral.integral_congr (fun x _ => by
      rw [hlag, Polynomial.eval_finsetSum _ _ x]),
      intervalIntegral.integral_finsetSum (fun q _ =>
        Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval (Polynomial.C ((p %ₘ np).eval (node q)) *
          Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) (-1) 1)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [intervalIntegral.integral_congr (fun x _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C]),
      intervalIntegral.integral_const_mul]
    simp only [hweightdef]
    rw [hrnode q]
    ring

  have hwpos : ∀ q, 0 < weight q := by
    intro q
    have hLne : (Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) ≠ 0 := by
      intro h0
      have h1 := Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_self node hinj q
      rw [h0] at h1
      simp at h1
    have hlb := Qatlib.Concepts.LchsSimulation.Quadrature.natDegree_lagrangeBasis_le node q
    have hsq : ((Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) ^ 2).natDegree ≤ 2 * Q - 1 := by
      rw [Polynomial.natDegree_pow'
        (pow_ne_zero 2 (Polynomial.leadingCoeff_ne_zero.mpr hLne))]
      omega
    have he := hexact ((Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) ^ 2) hsq
    have hsum : ∑ j, weight j * ((Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) ^ 2).eval (node j) = weight q := by
      rw [Finset.sum_eq_single q (fun j _ hj => by
        rw [Polynomial.eval_pow, Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_of_ne node hj,
          zero_pow two_ne_zero, mul_zero])
        (by simp)]
      rw [Polynomial.eval_pow,
          Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_self node hinj q, one_pow, mul_one]
    have hww : weight q
        = ∫ x in (-1 : ℝ)..1, ((Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) ^ 2).eval x := by
      rw [he]
      exact hsum.symm
    rw [hww]
    refine Qatlib.Concepts.LchsSimulation.Quadrature.integral_pos_of_nonneg_of_pos_at (by norm_num) ?_
      (fun x _ => by rw [Polynomial.eval_pow]; exact sq_nonneg _)
      ⟨(hnodeIoo q).1.le, (hnodeIoo q).2.le⟩ ?_
    · exact Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval
        ((Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis node q) ^ 2)
    · rw [Polynomial.eval_pow, Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_self node hinj q, one_pow]
      norm_num

  have homega : (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) := by
    have hnp_eval : ∀ t : ℝ, np.eval t = ∏ q : Fin Q, (t - node q) := by
      intro t
      rw [hnpdef, Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have hpe : ∀ t : ℝ, ∏ q : Fin Q, (t - node q) ^ 2 = np.eval t * np.eval t := by
      intro t
      rw [hnp_eval t, ← pow_two (∏ q : Fin Q, (t - node q)), Finset.prod_pow]
    have hpt2 : ∀ x : ℝ, np.eval x * np.eval x = lc⁻¹ * lc⁻¹ *
        ((Polynomial.derivative^[Q] (rodPoly Q)).eval x *
          (Polynomial.derivative^[Q] (rodPoly Q)).eval x) := by
      intro x
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hPfac]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      field_simp
    have hlcval : lc = ((2 * Q).factorial : ℝ) / (Q.factorial : ℝ) := by
      rw [hlcdef, leadingCoeff_iterate_deriv_rodPoly Q Q (le_refl Q),
        show 2 * Q - Q = Q from by omega]
    rw [intervalIntegral.integral_congr (fun t _ => hpe t),
      intervalIntegral.integral_congr (fun x _ => hpt2 x),
      intervalIntegral.integral_const_mul,
      integral_legendre_sq Q hQ, hlcval]
    have h4 : (4 : ℝ) ^ Q = (2 : ℝ) ^ (2 * Q) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, pow_mul]
    have hn1 : ((2 * Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hn2 : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
    have hn3 : (Q.factorial : ℝ) ≠ 0 := by positivity
    rw [h4]
    field_simp
    ring
  exact ⟨node, weight, hnodeIoo, hinj, hwpos, hexact, homega⟩

/-- A positive affine cell rescaling transforms the reference squared nodal-product integral
into the stated factorial expression proportional to `h^(2 * Q + 1)`. -/
theorem gauss_cell_omega (Q : ℕ) (a h : ℝ) (node : Fin Q → ℝ) (hpos : 0 < h)
    (href : (∫ t in (-1 : ℝ)..1, ∏ q : Fin Q, (t - node q) ^ 2) =
      ((2 : ℝ) ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2)) :
    (∫ x in a..a + h, ∏ q : Fin Q, (x - (a + h * (node q + 1) / 2)) ^ 2) =
      (h ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
        (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) := by
  have ht := intervalIntegral.smul_integral_comp_mul_add (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => ∏ q : Fin Q, (x - (a + h * (node q + 1) / 2)) ^ 2) (h / 2) (a + h / 2)
  rw [show h / 2 * (-1 : ℝ) + (a + h / 2) = a by ring,
    show h / 2 * (1 : ℝ) + (a + h / 2) = a + h by ring] at ht
  have hp : h / 2 * ((h / 2) ^ 2) ^ Q = h ^ (2 * Q + 1) / (2 : ℝ) ^ (2 * Q + 1) := by
    rw [← pow_mul, mul_comm (h / 2) ((h / 2) ^ (2 * Q)), ← pow_succ, div_pow]
  rw [← ht, smul_eq_mul, intervalIntegral.integral_congr (fun t _ => by
      rw [Finset.prod_congr rfl (fun q _ => by
          rw [show h / 2 * t + (a + h / 2) - (a + h * (node q + 1) / 2)
              = h / 2 * (t - node q) by ring]),
        Finset.prod_congr rfl (fun q _ => mul_pow (h / 2) (t - node q) 2),
        Finset.prod_mul_distrib, Finset.prod_const]),
    intervalIntegral.integral_const_mul, Finset.card_univ, Fintype.card_fin, href,
    ← mul_assoc, hp]
  have hn2 : (2 : ℝ) ≠ 0 := by norm_num
  have hnq : ((2 * Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hnf : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
  field_simp

set_option maxHeartbeats 1000000 in

/-- For a positive cell width and a function of class `C^(2 * Q)`, the stated polynomial
exactness and nodal-product identity bound the absolute quadrature error by the Gauss
factorial coefficient times the supremum of the absolute `2 * Q`-th derivative. See
[AnChildsLin2026]. -/
theorem gauss_legendre_cell_error_bound :
    ∀ (Q : ℕ) (a h : ℝ) (node weight : Fin Q → ℝ) (f : ℝ → ℝ),
      1 ≤ Q → 0 < h →
      (∀ p : Polynomial ℝ, p.natDegree ≤ 2 * Q - 1 →
        ∫ x in a..a + h, p.eval x =
          ∑ q, (h / 2) * weight q * p.eval (a + h * (node q + 1) / 2)) →
      (∫ x in a..a + h,
          ∏ q : Fin Q, (x - (a + h * (node q + 1) / 2)) ^ 2) =
        (h ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2) →
      ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) f →
      |(∫ k in a..a + h, f k) -
          ∑ q, (h / 2) * weight q * f (a + h * (node q + 1) / 2)| ≤
        ((Q.factorial : ℝ) ^ 4 * h ^ ((2 : ℝ) * Q + 1)) /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
          (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|) := by
  intro Q a h node weight f hQ hpos hexact homega hcd
  classical
  set xnode : Fin Q → ℝ := fun q => a + h * (node q + 1) / 2 with hxnodedef
  have hlab : a < a + h := by linarith

  have hinj : Function.Injective xnode := by
    intro i j hij
    by_contra hne
    set W' : Polynomial ℝ :=
      ∏ q ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (xnode q)) with hW'def
    have hmonic : W'.Monic := by
      rw [hW'def]
      exact Polynomial.monic_prod_X_sub_C _ _
    have hW'ne : W' ≠ 0 := hmonic.ne_zero
    set D : Polynomial ℝ := W' ^ 2 with hDdef
    have hdegD : D.natDegree ≤ 2 * Q - 1 := by
      have e := hmonic.natDegree_pow 2
      have hdegW' : W'.natDegree = Q - 1 := by
        rw [hW'def, Polynomial.natDegree_prod_of_monic (Finset.univ.erase j)
          (fun q => Polynomial.X - Polynomial.C (xnode q))
          (fun q _ => Polynomial.monic_X_sub_C (xnode q))]
        simp
      rw [hDdef]
      omega
    have hDnonneg : ∀ x : ℝ, 0 ≤ D.eval x := by
      intro x
      rw [hDdef, Polynomial.eval_pow]
      exact sq_nonneg _
    have hDnode : ∀ q : Fin Q, D.eval (xnode q) = 0 := by
      intro q
      have hzero : W'.eval (xnode q) = 0 := by
        rw [hW'def, Polynomial.eval_prod]
        rcases eq_or_ne q j with hqj | hqj
        · rw [hqj]
          exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩)
            (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← hij, sub_self])
        · exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqj, Finset.mem_univ q⟩)
            (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])
      rw [hDdef, Polynomial.eval_pow, hzero]
      exact zero_pow two_ne_zero
    have hintD : ∫ x in a..a + h, D.eval x = 0 := by
      rw [hexact D hdegD,
        Finset.sum_congr rfl (fun q _ => by rw [hDnode q, mul_zero]),
        Finset.sum_const_zero]
    obtain ⟨y, hy⟩ : ∃ y ∈ Icc a (a + h), 0 < D.eval y := by
      have hinf : ((Set.Ioo a (a + h)) \ (W'.roots.toFinset : Set ℝ)).Infinite :=
        (Set.Ioo_infinite hlab).diff (W'.roots.toFinset.finite_toSet)
      obtain ⟨y, hy⟩ := hinf.nonempty
      refine ⟨y, ⟨hy.1.1.le, hy.1.2.le⟩, ?_⟩
      rw [hDdef, Polynomial.eval_pow]
      refine sq_pos_of_ne_zero ?_
      intro h0
      exact absurd (Finset.mem_coe.mpr
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hW'ne).mpr h0))) hy.2
    have hcontra := Qatlib.Concepts.LchsSimulation.Quadrature.integral_pos_of_nonneg_of_pos_at hlab
      (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval D) (fun x _ => hDnonneg x) ⟨hy.1.1, hy.1.2⟩ hy.2
    rw [hintD] at hcontra
    exact lt_irrefl 0 hcontra

  have hnodeIoo : ∀ q, xnode q ∈ Ioo a (a + h) := by
    intro q
    by_contra hmem
    rw [Set.mem_Ioo] at hmem
    rcases not_and_or.mp hmem with hle | hge
    · exfalso
      set V : Polynomial ℝ :=
        ∏ i ∈ Finset.univ.erase q, (Polynomial.X - Polynomial.C (xnode i)) ^ 2 with hVdef
      set D2 : Polynomial ℝ := (Polynomial.X - Polynomial.C (xnode q)) * V with hD2def
      have hVne : V ≠ 0 := by
        rw [hVdef]
        exact (Polynomial.monic_prod_of_monic _ _
          (fun i _ => (Polynomial.monic_X_sub_C _).pow 2)).ne_zero
      have hcard : (Finset.univ.erase q).card = Q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, Fintype.card_fin]
      have hdegV : V.natDegree = 2 * (Q - 1) := by
        rw [hVdef, Polynomial.natDegree_prod_of_monic _ _
          (fun i _ => (Polynomial.monic_X_sub_C _).pow 2)]
        rw [Finset.sum_congr rfl (fun i _ => by
          rw [(Polynomial.monic_X_sub_C (xnode i)).natDegree_pow,
            Polynomial.natDegree_X_sub_C, mul_one])]
        rw [Finset.sum_const]
        simp [hcard, Nat.mul_comm]
      have hD2deg : D2.natDegree ≤ 2 * Q - 1 := by
        have e := Polynomial.natDegree_mul_le
          (p := Polynomial.X - Polynomial.C (xnode q)) (q := V)
        rw [Polynomial.natDegree_X_sub_C, hdegV] at e
        rw [hD2def]
        omega
      have hD2node : ∀ q' : Fin Q, D2.eval (xnode q') = 0 := by
        intro q'
        rw [hD2def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        rcases eq_or_ne q' q with hqq | hqq
        · rw [hqq, sub_self, zero_mul]
        · have hV0 : V.eval (xnode q') = 0 := by
            rw [hVdef, Polynomial.eval_prod]
            exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqq, Finset.mem_univ q'⟩)
              (by rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
                Polynomial.eval_C, sub_self, zero_pow two_ne_zero])
          rw [hV0, mul_zero]
      have hintD2 : ∫ x in a..a + h, D2.eval x = 0 := by
        rw [hexact D2 hD2deg,
          Finset.sum_congr rfl (fun q' _ => by rw [hD2node q', mul_zero]),
          Finset.sum_const_zero]
      obtain ⟨y, hyIoo, hyV, hyne⟩ : ∃ y ∈ Set.Ioo a (a + h), V.eval y ≠ 0 ∧ y ≠ xnode q := by
        have hfin : ((V.roots.toFinset : Set ℝ) ∪ {xnode q}).Finite :=
          (V.roots.toFinset.finite_toSet).union (Set.finite_singleton _)
        obtain ⟨y, hy⟩ := ((Set.Ioo_infinite hlab).diff hfin).nonempty
        refine ⟨y, hy.1, ?_, ?_⟩
        · intro h0
          exact hy.2 (Or.inl (Finset.mem_coe.mpr
            (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hVne).mpr h0))))
        · intro h0
          exact hy.2 (Or.inr (by rw [h0]; exact Set.mem_singleton (xnode q)))
      have hyVpos : 0 < V.eval y :=
        lt_of_le_of_ne' (by
          rw [hVdef, Polynomial.eval_prod]
          exact Finset.prod_nonneg fun i _ => by
            rw [Polynomial.eval_pow]
            exact sq_nonneg _) hyV
      have hcontra := Qatlib.Concepts.LchsSimulation.Quadrature.integral_pos_of_nonneg_of_pos_at hlab
        (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval D2)
        (fun z hz => by
          rw [hD2def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C, Polynomial.eval_prod]
          exact mul_nonneg (by linarith [hz.1, hle])
            (Finset.prod_nonneg fun i _ => by
              rw [Polynomial.eval_pow]
              exact sq_nonneg _))
        ⟨hyIoo.1.le, hyIoo.2.le⟩
        (by
          rw [hD2def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C]
          exact mul_pos (by linarith [hyIoo.1, hle]) hyVpos)
      rw [hintD2] at hcontra
      exact lt_irrefl 0 hcontra
    · exfalso
      set V : Polynomial ℝ :=
        ∏ i ∈ Finset.univ.erase q, (Polynomial.X - Polynomial.C (xnode i)) ^ 2 with hVdef
      set D2 : Polynomial ℝ := (Polynomial.X - Polynomial.C (xnode q)) * V with hD2def
      have hVne : V ≠ 0 := by
        rw [hVdef]
        exact (Polynomial.monic_prod_of_monic _ _
          (fun i _ => (Polynomial.monic_X_sub_C _).pow 2)).ne_zero
      have hcard : (Finset.univ.erase q).card = Q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ q), Finset.card_univ, Fintype.card_fin]
      have hdegV : V.natDegree = 2 * (Q - 1) := by
        rw [hVdef, Polynomial.natDegree_prod_of_monic _ _
          (fun i _ => (Polynomial.monic_X_sub_C _).pow 2)]
        rw [Finset.sum_congr rfl (fun i _ => by
          rw [(Polynomial.monic_X_sub_C (xnode i)).natDegree_pow,
            Polynomial.natDegree_X_sub_C, mul_one])]
        rw [Finset.sum_const]
        simp [hcard, Nat.mul_comm]
      have hD2deg : D2.natDegree ≤ 2 * Q - 1 := by
        have e := Polynomial.natDegree_mul_le
          (p := Polynomial.X - Polynomial.C (xnode q)) (q := V)
        rw [Polynomial.natDegree_X_sub_C, hdegV] at e
        rw [hD2def]
        omega
      have hD2node : ∀ q' : Fin Q, D2.eval (xnode q') = 0 := by
        intro q'
        rw [hD2def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C]
        rcases eq_or_ne q' q with hqq | hqq
        · rw [hqq, sub_self, zero_mul]
        · have hV0 : V.eval (xnode q') = 0 := by
            rw [hVdef, Polynomial.eval_prod]
            exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqq, Finset.mem_univ q'⟩)
              (by rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
                Polynomial.eval_C, sub_self, zero_pow two_ne_zero])
          rw [hV0, mul_zero]
      have hintD2 : ∫ x in a..a + h, D2.eval x = 0 := by
        rw [hexact D2 hD2deg,
          Finset.sum_congr rfl (fun q' _ => by rw [hD2node q', mul_zero]),
          Finset.sum_const_zero]
      obtain ⟨y, hyIoo, hyV, hyne⟩ : ∃ y ∈ Set.Ioo a (a + h), V.eval y ≠ 0 ∧ y ≠ xnode q := by
        have hfin : ((V.roots.toFinset : Set ℝ) ∪ {xnode q}).Finite :=
          (V.roots.toFinset.finite_toSet).union (Set.finite_singleton _)
        obtain ⟨y, hy⟩ := ((Set.Ioo_infinite hlab).diff hfin).nonempty
        refine ⟨y, hy.1, ?_, ?_⟩
        · intro h0
          exact hy.2 (Or.inl (Finset.mem_coe.mpr
            (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hVne).mpr h0))))
        · intro h0
          exact hy.2 (Or.inr (by rw [h0]; exact Set.mem_singleton (xnode q)))
      have hyVpos : 0 < V.eval y :=
        lt_of_le_of_ne' (by
          rw [hVdef, Polynomial.eval_prod]
          exact Finset.prod_nonneg fun i _ => by
            rw [Polynomial.eval_pow]
            exact sq_nonneg _) hyV
      have hcontra := Qatlib.Concepts.LchsSimulation.Quadrature.integral_pos_of_nonneg_of_pos_at hlab
        (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval (-D2))
        (fun z hz => by
          have hd : D2.eval z ≤ 0 := by
            rw [hD2def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
              Polynomial.eval_C, Polynomial.eval_prod]
            exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hz.2, hge])
              (Finset.prod_nonneg fun i _ => by
                rw [Polynomial.eval_pow]
                exact sq_nonneg _)
          show 0 ≤ (-D2).eval z
          rw [Polynomial.eval_neg]
          linarith)
        ⟨hyIoo.1.le, hyIoo.2.le⟩
        (by
          have hd : D2.eval y < 0 := by
            rw [hD2def, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
              Polynomial.eval_C]
            exact mul_neg_of_neg_of_pos (by linarith [hyIoo.2, hge]) hyVpos
          show 0 < (-D2).eval y
          rw [Polynomial.eval_neg]
          linarith)
      rw [intervalIntegral.integral_congr (fun z _ => Polynomial.eval_neg D2 z),
        intervalIntegral.integral_neg, hintD2] at hcontra
      simp at hcontra

  set L : Fin Q → Polynomial ℝ := fun i => Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis xnode i with hLdef
  have hLself : ∀ i, (L i).eval (xnode i) = 1 :=
    fun i => Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_self xnode hinj i
  have hLne_eval : ∀ i j, j ≠ i → (L i).eval (xnode j) = 0 :=
    fun i j hij => Qatlib.Concepts.LchsSimulation.Quadrature.lagrangeBasis_eval_of_ne xnode hij
  have hLpne : ∀ i, L i ≠ 0 := by
    intro i h0
    have h1 : (L i).eval (xnode i) = 1 := hLself i
    rw [h0] at h1
    simp at h1
  have hdegL2 : ∀ i, ((L i) ^ 2).natDegree ≤ 2 * Q - 2 := by
    intro i
    have hLdeg : (L i).natDegree ≤ Q - 1 :=
        Qatlib.Concepts.LchsSimulation.Quadrature.natDegree_lagrangeBasis_le xnode i
    rw [Polynomial.natDegree_pow'
      (pow_ne_zero 2 (Polynomial.leadingCoeff_ne_zero.mpr (hLpne i)))]
    omega
  have hL2eval : ∀ i j, ((L i) ^ 2).eval (xnode j) = if j = i then 1 else 0 := by
    intro i j
    rw [Polynomial.eval_pow]
    rcases eq_or_ne j i with hji | hji
    · rw [hji, hLself i, if_pos rfl, one_pow]
    · rw [hLne_eval i j hji, if_neg hji, zero_pow two_ne_zero]
  have hdL2 : ∀ i j, ((L i) ^ 2).derivative.eval (xnode j)
      = if j = i then 2 * (L i).derivative.eval (xnode i) else 0 := by
    intro i j
    have hdp : ((L i) ^ 2).derivative
        = Polynomial.C (2 : ℝ) * (L i) ^ (2 - 1) * (L i).derivative :=
      Polynomial.derivative_pow (L i) 2
    rw [hdp, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow]
    rcases eq_or_ne j i with hji | hji
    · rw [hji, hLself i, one_pow, if_pos rfl]
      ring
    · rw [hLne_eval i j hji, zero_pow (by norm_num), if_neg hji]
      ring
  set B : Fin Q → Polynomial ℝ :=
    fun i => (Polynomial.X - Polynomial.C (xnode i)) * (L i) ^ 2 with hBdef
  have hdegB : ∀ i, (B i).natDegree ≤ 2 * Q - 1 := by
    intro i
    have t := Polynomial.natDegree_mul_le
      (p := Polynomial.X - Polynomial.C (xnode i)) (q := (L i) ^ 2)
    rw [Polynomial.natDegree_X_sub_C] at t
    have t2 := hdegL2 i
    rw [congrFun hBdef i]
    omega
  have hBeval : ∀ i j, (B i).eval (xnode j) = (xnode j - xnode i) * (if j = i then 1 else 0) := by
    intro i j
    rw [congrFun hBdef i, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, hL2eval i j]
  have hdB : ∀ i j, (B i).derivative.eval (xnode j) = if j = i then 1 else 0 := by
    intro i j
    have hdb : (B i).derivative
        = (L i) ^ 2 + (Polynomial.X - Polynomial.C (xnode i)) * ((L i) ^ 2).derivative := by
      rw [congrFun hBdef i, Polynomial.derivative_mul, Polynomial.derivative_X_sub_C, one_mul]
    rw [hdb, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, hL2eval i j, hdL2 i j]
    rcases eq_or_ne j i with hji | hji
    · subst hji
      simp
    · simp [hji]
  set A : Fin Q → Polynomial ℝ :=
    fun i => (L i) ^ 2 - Polynomial.C (2 * (L i).derivative.eval (xnode i)) * B i with hAdef
  have hdegA : ∀ i, (A i).natDegree ≤ 2 * Q - 1 := by
    intro i
    have t3 := Polynomial.natDegree_mul_le
      (p := Polynomial.C (2 * (L i).derivative.eval (xnode i))) (q := B i)
    rw [Polynomial.natDegree_C, zero_add] at t3
    have e := Polynomial.natDegree_sub_le ((L i) ^ 2)
      (Polynomial.C (2 * (L i).derivative.eval (xnode i)) * B i)
    have t1 := hdegL2 i
    have t2 := hdegB i
    rw [congrFun hAdef i]
    omega
  have hAeval : ∀ i j, (A i).eval (xnode j) = if j = i then 1 else 0 := by
    intro i j
    rw [congrFun hAdef i, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      hL2eval i j, hBeval i j]
    rcases eq_or_ne j i with hji | hji
    · subst hji
      simp
    · simp [hji]
  have hdA : ∀ i j, (A i).derivative.eval (xnode j) = 0 := by
    intro i j
    have hda : (A i).derivative = ((L i) ^ 2).derivative
        - Polynomial.C (2 * (L i).derivative.eval (xnode i)) * (B i).derivative := by
      rw [congrFun hAdef i, Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_C, zero_mul, zero_add]
    rw [hda, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hdL2 i j, hdB i j]
    rcases eq_or_ne j i with hji | hji
    · subst hji
      simp
    · simp [hji]
  set S1 : Polynomial ℝ := ∑ i, Polynomial.C (f (xnode i)) * A i with hS1def
  set S2 : Polynomial ℝ := ∑ i, Polynomial.C (deriv f (xnode i)) * B i with hS2def
  set H : Polynomial ℝ := S1 + S2 with hHdef
  have hdegS1 : S1.natDegree ≤ 2 * Q - 1 := by
    have hper : ∀ i, (Polynomial.C (f (xnode i)) * A i).natDegree ≤ 2 * Q - 1 := by
      intro i
      have t := Polynomial.natDegree_mul_le
        (p := Polynomial.C (f (xnode i))) (q := A i)
      rw [Polynomial.natDegree_C, zero_add] at t
      exact le_trans t (hdegA i)
    rw [hS1def]
    exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun i => Polynomial.C (f (xnode i)) * A i) (fun i _ => hper i)
  have hdegS2 : S2.natDegree ≤ 2 * Q - 1 := by
    have hper : ∀ i, (Polynomial.C (deriv f (xnode i)) * B i).natDegree ≤ 2 * Q - 1 := by
      intro i
      have t := Polynomial.natDegree_mul_le
        (p := Polynomial.C (deriv f (xnode i))) (q := B i)
      rw [Polynomial.natDegree_C, zero_add] at t
      exact le_trans t (hdegB i)
    rw [hS2def]
    exact Polynomial.natDegree_sum_le_of_forall_le Finset.univ
      (fun i => Polynomial.C (deriv f (xnode i)) * B i) (fun i _ => hper i)
  have hdegH : H.natDegree ≤ 2 * Q - 1 := by
    have t := Polynomial.natDegree_add_le S1 S2
    rw [hHdef]
    omega
  have hdegHlt : H.natDegree < 2 * Q := by omega
  have hHval : ∀ j, H.eval (xnode j) = f (xnode j) := by
    intro j
    rw [hHdef, Polynomial.eval_add]
    have hS1v : S1.eval (xnode j) = f (xnode j) := by
      rw [hS1def, Polynomial.eval_finsetSum,
        Finset.sum_eq_single j (fun i _ hne => by
          rw [Polynomial.eval_mul, Polynomial.eval_C, hAeval i j, if_neg (Ne.symm hne),
            mul_zero])
          (by simp),
        Polynomial.eval_mul, Polynomial.eval_C, hAeval j j, if_pos rfl, mul_one]
    have hS2v : S2.eval (xnode j) = 0 := by
      rw [hS2def, Polynomial.eval_finsetSum,
        Finset.sum_eq_single j (fun i _ hne => by
          rw [Polynomial.eval_mul, Polynomial.eval_C, hBeval i j, if_neg (Ne.symm hne),
            mul_zero, mul_zero])
          (by simp),
        Polynomial.eval_mul, Polynomial.eval_C, hBeval j j, if_pos rfl]
      ring
    rw [hS1v, hS2v, add_zero]
  have hHder : ∀ j, H.derivative.eval (xnode j) = deriv f (xnode j) := by
    intro j
    rw [hHdef, Polynomial.derivative_add, Polynomial.eval_add]
    have hdS1 : S1.derivative.eval (xnode j) = 0 := by
      rw [hS1def, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
        Finset.sum_eq_single j (fun i _ hne => by
          rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
            Polynomial.eval_mul, Polynomial.eval_C, hdA i j, mul_zero])
          (by simp),
        Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
        Polynomial.eval_mul, Polynomial.eval_C, hdA j j, mul_zero]
    have hdS2 : S2.derivative.eval (xnode j) = deriv f (xnode j) := by
      rw [hS2def, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
        Finset.sum_eq_single j (fun i _ hne => by
          rw [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
            Polynomial.eval_mul, hdB i j, if_neg (Ne.symm hne), mul_zero])
          (by simp),
        Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
        Polynomial.eval_mul, Polynomial.eval_C, hdB j j, if_pos rfl, mul_one]
    rw [hdS1, hdS2, zero_add]

  set Wp : Polynomial ℝ := ∏ q, (Polynomial.X - Polynomial.C (xnode q)) with hWpdef
  have hWpmonic : Wp.Monic := by
    rw [hWpdef]
    exact Polynomial.monic_prod_X_sub_C _ _
  have hWpne : Wp ≠ 0 := hWpmonic.ne_zero
  have hWpval : ∀ x : ℝ, Wp.eval x = ∏ q, (x - xnode q) := by
    intro x
    rw [hWpdef, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hWpnode : ∀ q, Wp.eval (xnode q) = 0 := by
    intro q
    rw [hWpval]
    exact Finset.prod_eq_zero (Finset.mem_univ q) (by rw [sub_self])
  have hWproot : ∀ x : ℝ, Wp.eval x = 0 → ∃ q, xnode q = x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    refine absurd hx ?_
    rw [hWpval]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => sub_ne_zero_of_ne (Ne.symm (hcon q)))
  set ωpoly : Polynomial ℝ := Wp ^ 2 with hωpolydef
  have hωne : ωpoly ≠ 0 := (hWpmonic.pow 2).ne_zero
  have hWpdeg : Wp.natDegree = Q := by
    rw [hWpdef, Polynomial.natDegree_prod_of_monic Finset.univ
      (fun q => Polynomial.X - Polynomial.C (xnode q))
      (fun q _ => Polynomial.monic_X_sub_C (xnode q))]
    simp
  have hωdeg : ωpoly.natDegree = 2 * Q := by
    rw [hωpolydef, hWpmonic.natDegree_pow, hWpdeg]
  have hωval : ∀ x : ℝ, ωpoly.eval x = ∏ q : Fin Q, (x - xnode q) ^ 2 := by
    intro x
    rw [hωpolydef, Polynomial.eval_pow, hWpval, ← Finset.prod_pow]
  have hωpos : ∀ x : ℝ, 0 ≤ ωpoly.eval x := by
    intro x
    rw [hωpolydef, Polynomial.eval_pow]
    exact sq_nonneg _
  have hωnode : ∀ q, ωpoly.eval (xnode q) = 0 := by
    intro q
    rw [hωpolydef, Polynomial.eval_pow, hWpnode q, zero_pow two_ne_zero]
  have hdω : ∀ q, ωpoly.derivative.eval (xnode q) = 0 := by
    intro q
    have hdp2 : ωpoly.derivative = Wp.derivative * Wp + Wp * Wp.derivative := by
      rw [hωpolydef, pow_two, Polynomial.derivative_mul]
    rw [hdp2, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, hWpnode q]
    ring
  have hω2Q : (Polynomial.derivative)^[2 * Q] ωpoly = Polynomial.C (((2 * Q).factorial : ℝ)) := by
    have h := Qatlib.Concepts.LchsSimulation.Quadrature.iterate_derivative_eq_C hωne hωdeg
    rw [(hWpmonic.pow 2).leadingCoeff, mul_one] at h
    exact h

  have hpeano : ∀ x ∈ Icc a (a + h),
      |f x - H.eval x| ≤ ((⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|)
        / ((2 * Q).factorial : ℝ)) * ωpoly.eval x := by
    intro x hx
    by_cases hxω : ωpoly.eval x = 0
    · obtain ⟨q, hq⟩ := hWproot x (by
        have hp := hxω
        rw [hωpolydef, Polynomial.eval_pow] at hp
        exact sq_eq_zero_iff.mp hp)
      rw [← hq, hHval q, hωnode q, mul_zero, sub_self, abs_zero]
    · have hnx : ∀ q, xnode q ≠ x := by
        intro q hq
        refine hxω ?_
        rw [hωval x, ← hq]
        exact Finset.prod_eq_zero (Finset.mem_univ q)
          (by rw [sub_self, zero_pow two_ne_zero])
      set K : ℝ := (f x - H.eval x) / ωpoly.eval x with hKdef
      set G : ℝ → ℝ := fun y => f y - H.eval y - K * ωpoly.eval y with hGdef
      have hGcd : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) G :=
        ((hcd.sub (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ H)).sub
          (contDiff_const.mul (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ ωpoly)))
      have hGnode : ∀ q, G (xnode q) = 0 := by
        intro q
        show f (xnode q) - H.eval (xnode q) - K * ωpoly.eval (xnode q) = 0
        rw [hHval q, hωnode q, mul_zero, sub_self, sub_zero]
      have hfderiv : ∀ q, HasDerivAt f (deriv f (xnode q)) (xnode q) := by
        intro q
        have hne0 : (2 * Q : ℕ) ≠ 0 := by omega
        have hfd : Differentiable ℝ f := hcd.differentiable (by exact_mod_cast hne0)
        exact (hfd (xnode q)).hasDerivAt
      have hGdnode : ∀ q, deriv G (xnode q) = 0 := by
        intro q
        have h1 : HasDerivAt G (deriv f (xnode q) - H.derivative.eval (xnode q)
            - K * ωpoly.derivative.eval (xnode q)) (xnode q) :=
          ((hfderiv q).sub (Polynomial.hasDerivAt H (xnode q))).sub
            ((Polynomial.hasDerivAt ωpoly (xnode q)).const_mul K)
        rw [hHder q, hdω q, mul_zero] at h1
        rw [h1.deriv]
        ring
      have hGx : G x = 0 := by
        show f x - H.eval x - K * ωpoly.eval x = 0
        rw [hKdef, div_mul_cancel₀ _ hxω, sub_self]
      set node' : Fin (Q + 1) → ℝ :=
        fun i => if hi : (i : ℕ) < Q then xnode ⟨(i : ℕ), hi⟩ else x with hnode'def
      set mult' : Fin (Q + 1) → ℕ := fun i => if (i : ℕ) < Q then 2 else 1 with hmult'def
      have hnodeinj : Function.Injective node' := by
        intro i j hij
        have hiB := i.isLt
        have hjB := j.isLt
        by_cases hi : (i : ℕ) < Q
        · have hii : node' i = xnode ⟨(i : ℕ), hi⟩ := dif_pos hi
          rw [hii] at hij
          by_cases hj : (j : ℕ) < Q
          · have hjj : node' j = xnode ⟨(j : ℕ), hj⟩ := dif_pos hj
            rw [hjj] at hij
            have h4 := congrArg Fin.val (hinj hij)
            exact Fin.val_injective h4
          · have hjj : node' j = x := dif_neg hj
            rw [hjj] at hij
            exact absurd hij (hnx ⟨(i : ℕ), hi⟩)
        · have hii : node' i = x := dif_neg hi
          rw [hii] at hij
          by_cases hj : (j : ℕ) < Q
          · have hjj : node' j = xnode ⟨(j : ℕ), hj⟩ := dif_pos hj
            rw [hjj] at hij
            exact absurd hij.symm (hnx ⟨(j : ℕ), hj⟩)
          · have hjj : node' j = x := dif_neg hj
            rw [hjj] at hij
            exact Fin.val_injective (show (i : ℕ) = (j : ℕ) by omega)
      have hnodemem : ∀ i, node' i ∈ Icc a (a + h) := by
        intro i
        by_cases hi : (i : ℕ) < Q
        · have hii : node' i = xnode ⟨(i : ℕ), hi⟩ := dif_pos hi
          rw [hii]
          exact ⟨(hnodeIoo ⟨(i : ℕ), hi⟩).1.le, (hnodeIoo ⟨(i : ℕ), hi⟩).2.le⟩
        · show (if hi : (i : ℕ) < Q then xnode ⟨(i : ℕ), hi⟩ else x) ∈ Icc a (a + h)
          rw [dif_neg hi]
          exact hx
      have hmult1 : ∀ i, 1 ≤ mult' i := by
        intro i
        by_cases hi : (i : ℕ) < Q
        · have h : mult' i = 2 := if_pos hi
          omega
        · have h : mult' i = 1 := if_neg hi
          omega
      have hmultsum : ∑ i, mult' i = 2 * Q + 1 := by
        rw [Fin.sum_univ_castSucc]
        have hc : ∀ i : Fin Q, mult' (Fin.castSucc i) = 2 := by
          intro i
          have hlt : ((Fin.castSucc i : Fin (Q + 1)) : ℕ) < Q := by
            rw [Fin.val_castSucc]
            exact i.isLt
          exact if_pos hlt
        rw [Finset.sum_congr rfl (fun i _ => hc i)]
        have hlast : mult' (Fin.last Q) = 1 := by
          have hnl : ¬((Fin.last Q : Fin (Q + 1)) : ℕ) < Q := by
            rw [Fin.val_last]
            omega
          exact if_neg hnl
        rw [hlast, Finset.sum_const]
        simp [Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
      have hzeros : ∀ i (j : ℕ), j < mult' i → iteratedDeriv j G (node' i) = 0 := by
        intro i j hjlt
        by_cases hi : (i : ℕ) < Q
        · have hm : mult' i = 2 := if_pos hi
          have hn : node' i = xnode ⟨(i : ℕ), hi⟩ := dif_pos hi
          rw [hm] at hjlt
          rw [hn]
          rcases (by omega : j = 0 ∨ j = 1) with hj | hj
          · rw [hj, iteratedDeriv_zero]
            exact hGnode _
          · rw [hj, iteratedDeriv_one]
            exact hGdnode _
        · have hm : mult' i = 1 := if_neg hi
          have hn : node' i = x := dif_neg hi
          rw [hm] at hjlt
          rw [hn]
          have hj : j = 0 := by omega
          rw [hj, iteratedDeriv_zero]
          exact hGx
      obtain ⟨ξ, hξmem, hξ⟩ := Qatlib.Concepts.LchsSimulation.Quadrature.counted_zero_rolle (2 * Q) (Q + 1) a (a + h) G node' mult'
        (by linarith) hnodeinj hnodemem hmult1 (by rw [hmultsum]) hGcd hzeros
      have hcdF : ContDiff ℝ ((2 * Q : ℕ) : WithTop ℕ∞) (fun y => f y - H.eval y) :=
        hcd.sub (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ H)
      have hdouter : iteratedDeriv (2 * Q) G ξ
          = (iteratedDeriv (2 * Q) (fun y => f y - H.eval y) ξ
            - iteratedDeriv (2 * Q) (fun y => K * ωpoly.eval y) ξ) :=
        iteratedDeriv_sub (hcdF.contDiffAt)
          ((contDiff_const.mul (Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ ωpoly)).contDiffAt)
      have hdinner : iteratedDeriv (2 * Q) (fun y => f y - H.eval y) ξ
          = iteratedDeriv (2 * Q) f ξ - iteratedDeriv (2 * Q) (fun t => H.eval t) ξ :=
        iteratedDeriv_sub (hcd.contDiffAt) ((Qatlib.Concepts.LchsSimulation.Quadrature.contDiff_eval _ H).contDiffAt)
      have hdK : iteratedDeriv (2 * Q) (fun y => K * ωpoly.eval y) ξ
          = K * iteratedDeriv (2 * Q) (fun t => ωpoly.eval t) ξ :=
        iteratedDeriv_const_mul_field K (fun t => ωpoly.eval t)
      have hdωξ : iteratedDeriv (2 * Q) (fun t => ωpoly.eval t) ξ = ((2 * Q).factorial : ℝ) := by
        rw [Qatlib.Concepts.LchsSimulation.Quadrature.iteratedDeriv_eval, hω2Q]
        simp
      rw [hdouter, hdinner,
          Qatlib.Concepts.LchsSimulation.Quadrature.iteratedDeriv_eval_eq_zero hdegHlt ξ, sub_zero, hdK, hdωξ] at hξ
      have hKeq : K * ((2 * Q).factorial : ℝ) = iteratedDeriv (2 * Q) f ξ := by linarith
      have hcont : Continuous (fun k => iteratedDeriv (2 * Q) f k) :=
        hcd.continuous_iteratedDeriv (2 * Q) (by exact_mod_cast le_refl (2 * Q))
      have hbddimg : BddAbove ((fun k => |iteratedDeriv (2 * Q) f k|) '' Icc a (a + h)) :=
        isCompact_Icc.bddAbove_image hcont.abs.continuousOn
      have htrange : (⋃ i, Set.range (fun _ : i ∈ Icc a (a + h) =>
          |iteratedDeriv (2 * Q) f i|)) ⊆
          (fun k => |iteratedDeriv (2 * Q) f k|) '' Icc a (a + h) := by
        intro y hy
        rw [Set.mem_iUnion] at hy
        obtain ⟨i, hi⟩ := hy
        rw [Set.mem_range] at hi
        obtain ⟨x, hx⟩ := hi
        exact ⟨i, x, hx⟩
      have habsξ : |iteratedDeriv (2 * Q) f ξ|
          ≤ (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|) :=
        le_ciSup₂ (f := fun (k : ℝ) (_ : k ∈ Icc a (a + h)) => |iteratedDeriv (2 * Q) f k|)
          (hbddimg.mono htrange) ξ hξmem
      have hfpos : (0 : ℝ) < ((2 * Q).factorial : ℝ) := by positivity
      have hKbound : |K| * ((2 * Q).factorial : ℝ)
          ≤ (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|) := by
        have e1 : |K| * ((2 * Q).factorial : ℝ)
            = |K * ((2 * Q).factorial : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hfpos.le]
        rw [e1, hKeq]
        exact habsξ
      have hfH : f x - H.eval x = K * ωpoly.eval x := by
        rw [hKdef, div_mul_cancel₀ _ hxω]
      rw [hfH, abs_mul, abs_of_nonneg (hωpos x)]
      refine mul_le_mul_of_nonneg_right ?_ (hωpos x)
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((2 * Q).factorial : ℝ))]
      exact hKbound

  have hif : IntervalIntegrable f volume a (a + h) := hcd.continuous.intervalIntegrable _ _
  have hiH : IntervalIntegrable (fun x => H.eval x) volume a (a + h) :=
    Qatlib.Concepts.LchsSimulation.Quadrature.intervalIntegrable_eval H a (a + h)
  have hiabs : IntervalIntegrable (fun x => |f x - H.eval x|) volume a (a + h) :=
    ((hcd.continuous.sub (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval H)).abs).intervalIntegrable _ _
  have hiω : IntervalIntegrable (fun x => ((⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|)
      / ((2 * Q).factorial : ℝ)) * ωpoly.eval x) volume a (a + h) :=
    (continuous_const.mul (Qatlib.Concepts.LchsSimulation.Quadrature.continuous_eval ωpoly)).intervalIntegrable _ _
  have hint2 : ∑ q, (h / 2) * weight q * f (xnode q) = ∫ x in a..a + h, H.eval x := by
    rw [hexact H hdegH]
    exact Finset.sum_congr rfl fun q _ => by rw [hHval q]
  have hrpow : h ^ ((2 : ℝ) * Q + 1) = h ^ (2 * Q + 1) := by
    have hc : ((2 : ℝ) * Q + 1) = ((2 * Q + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hc, Real.rpow_natCast]
  calc |(∫ k in a..a + h, f k) - ∑ q, (h / 2) * weight q * f (xnode q)| =
          |∫ x in a..a + h, f x - H.eval x| := by
            rw [hint2, ← intervalIntegral.integral_sub hif hiH]
    _ ≤ ∫ x in a..a + h, |f x - H.eval x| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ x in a..a + h, ((⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|)
          / ((2 * Q).factorial : ℝ)) * ωpoly.eval x :=
          intervalIntegral.integral_mono_on (by linarith) hiabs hiω (fun z hz => hpeano z hz)
    _ = ((⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|) / ((2 * Q).factorial : ℝ)) *
          ∫ x in a..a + h, ωpoly.eval x := by
            rw [intervalIntegral.integral_const_mul]
    _ = ((⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|) / ((2 * Q).factorial : ℝ)) *
          (h ^ (2 * Q + 1) * (Q.factorial : ℝ) ^ 4 /
            (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 2)) := by
            rw [intervalIntegral.integral_congr (fun z _ => hωval z), homega]
    _ = ((Q.factorial : ℝ) ^ 4 * h ^ ((2 : ℝ) * Q + 1)) /
          (((2 * Q + 1 : ℕ) : ℝ) * (((2 * Q).factorial : ℕ) : ℝ) ^ 3) *
        (⨆ k ∈ Icc a (a + h), |iteratedDeriv (2 * Q) f k|) := by
            rw [hrpow]
            have hnq : ((2 * Q + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            have hnf : ((2 * Q).factorial : ℝ) ≠ 0 := by positivity
            field_simp

end Qatlib.Concepts.LchsSimulation.Quadrature
