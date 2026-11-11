/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Polynomial tools for Gauss-Legendre quadrature

The module develops polynomial differentiation and integration identities, Lagrange
interpolation, and sign control from even root multiplicities. Counted-zero Rolle theorems
provide the derivative-zero arguments needed for Gauss-Legendre remainder estimates. See
[AnChildsLin2026] for the mathematical setting.

## Main statements

* `lagrange_interpolation`: A polynomial of natural degree less than `Q` equals its Lagrange
  interpolation sum at `Q` injectively indexed nodes.
* `sign_of_even_rootMultiplicity`: If every root in `(a, b)` has even multiplicity, a real
  polynomial is either nonnegative throughout that interval or nonpositive throughout it.
* `counted_zero_rolle`: For finitely many distinct nodes indexed by `Fin s`, prescribed
  derivative-zero multiplicities of total at least `m + 1` force a zero of the `m`-th derivative
  of a function of class `C^m` on the closed interval.

## References

* [An, Childs, and Lin, 2026][AnChildsLin2026]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.LchsSimulation.Quadrature
open Set MeasureTheory
open scoped BigOperators

/-- Evaluation of a real polynomial is continuous as a function on the real line. -/
theorem continuous_eval (p : Polynomial ℝ) : Continuous (fun x : ℝ => p.eval x) :=
  p.differentiable.continuous

/-- A real polynomial is interval integrable on every finite real interval. -/
theorem intervalIntegrable_eval (p : Polynomial ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => p.eval x) volume a b :=
  (continuous_eval p).intervalIntegrable a b

/-- Evaluation of a real polynomial is differentiable to every specified order `n`. -/
theorem contDiff_eval (n : WithTop ℕ∞) (p : Polynomial ℝ) :
    ContDiff ℝ n (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
  | monomial m c =>
      simpa only [Polynomial.eval_monomial] using! contDiff_const.mul (contDiff_id.pow m)

/-- The real derivative of polynomial evaluation is evaluation of the polynomial derivative. -/
theorem deriv_eval (p : Polynomial ℝ) :
    deriv (fun x : ℝ => p.eval x) = fun x : ℝ => p.derivative.eval x :=
  funext fun _ => p.deriv

/-- Iterating the real derivative operator `n` times on polynomial evaluation agrees with
evaluating the `n`-fold polynomial derivative. -/
theorem iterate_deriv_eval (n : ℕ) (p : Polynomial ℝ) :
    (deriv)^[n] (fun t : ℝ => p.eval t) = fun t : ℝ => (Polynomial.derivative^[n] p).eval t := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
      have h1 : deriv^[n + 1] (fun t : ℝ => p.eval t)
          = deriv^[n] (fun t : ℝ => p.derivative.eval t) := by
        rw [Function.iterate_succ_apply, deriv_eval]
      rw [h1, ih p.derivative]
      exact congrArg (fun Q : Polynomial ℝ => fun t : ℝ => Q.eval t)
        (Function.iterate_succ_apply Polynomial.derivative n p).symm

/-- The `n`-th iterated real derivative of a polynomial at `x` equals the evaluation of its
`n`-fold polynomial derivative at `x`. -/
theorem iteratedDeriv_eval (n : ℕ) (p : Polynomial ℝ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => p.eval t) x = (Polynomial.derivative^[n] p).eval x := by
  rw [iteratedDeriv_eq_iterate, iterate_deriv_eval]

/-- The `n`-th iterated derivative of a polynomial vanishes when its natural degree is less than
`n`. -/
theorem iteratedDeriv_eval_eq_zero {n : ℕ} {p : Polynomial ℝ} (h : p.natDegree < n) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => p.eval t) x = 0 := by
  rw [iteratedDeriv_eval, Polynomial.iterate_derivative_eq_zero h, Polynomial.eval_zero]

/-- The interval integral of the evaluation of a polynomial product equals the integral of the
product of the evaluations. -/
theorem integral_eval_prod (p q : Polynomial ℝ) (a b : ℝ) :
    ∫ x in a..b, (p * q).eval x = ∫ x in a..b, p.eval x * q.eval x :=
  intervalIntegral.integral_congr fun _ _ => by rw [Polynomial.eval_mul]

/-- The interval integral of a polynomial derivative equals the difference of the polynomial
values at the endpoints. -/
theorem integral_poly_derivative (p : Polynomial ℝ) (a b : ℝ) :
    ∫ x in a..b, p.derivative.eval x = p.eval b - p.eval a := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.derivative_add, Polynomial.eval_add] at hp hq ⊢
      rw [intervalIntegral.integral_add (intervalIntegrable_eval p.derivative a b)
        (intervalIntegrable_eval q.derivative a b), hp, hq]
      ring
  | monomial n c =>
      rcases n with _ | m
      · simp only [Polynomial.monomial_zero_left, Polynomial.derivative_C,
          Polynomial.eval_zero, intervalIntegral.integral_zero, Polynomial.eval_C, sub_self]
      simp only [Polynomial.derivative_monomial_succ, Polynomial.eval_monomial]
      rw [intervalIntegral.integral_const_mul, integral_pow]
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp

/-- Integration by parts for the product of a polynomial derivative and another polynomial. -/
theorem integral_poly_derivative_mul (p q : Polynomial ℝ) (a b : ℝ) :
    ∫ x in a..b, p.derivative.eval x * q.eval x =
      (p * q).eval b - (p * q).eval a - ∫ x in a..b, p.eval x * q.derivative.eval x := by
  have h1 := integral_poly_derivative (p * q) a b
  rw [Polynomial.derivative_mul] at h1
  simp only [Polynomial.eval_add] at h1
  rw [intervalIntegral.integral_add (intervalIntegrable_eval (p.derivative * q) a b)
    (intervalIntegrable_eval (p * q.derivative) a b),
    integral_eval_prod p.derivative q a b, integral_eval_prod p q.derivative a b] at h1
  linarith

/-- If all derivatives of `A` below order `n` vanish at both endpoints, integrating its `n`-th
derivative against a polynomial transfers all `n` derivatives with sign `(-1)^n`. -/
theorem integral_poly_iterate_parts (A : Polynomial ℝ) (n : ℕ) (gp : Polynomial ℝ) (a b : ℝ)
    (hb : ∀ k < n, (Polynomial.derivative^[k] A).eval a = 0 ∧
      (Polynomial.derivative^[k] A).eval b = 0) :
    ∫ x in a..b, (Polynomial.derivative^[n] A).eval x * gp.eval x =
      (-1 : ℝ) ^ n * ∫ x in a..b, A.eval x * (Polynomial.derivative^[n] gp).eval x := by
  induction n generalizing gp with
  | zero => simp
  | succ n ih =>
      have key := integral_poly_derivative_mul (Polynomial.derivative^[n] A) gp a b
      have hb0 : (Polynomial.derivative^[n] A * gp).eval a = 0 := by
        rw [Polynomial.eval_mul, (hb n (Nat.lt_succ_self n)).1, zero_mul]
      have hb1 : (Polynomial.derivative^[n] A * gp).eval b = 0 := by
        rw [Polynomial.eval_mul, (hb n (Nat.lt_succ_self n)).2, zero_mul]
      rw [hb1, hb0, sub_zero, zero_sub] at key
      have hdA : (Polynomial.derivative^[n] A).derivative = Polynomial.derivative^[n + 1] A :=
        (Function.iterate_succ_apply' Polynomial.derivative n A).symm
      rw [hdA] at key
      have hgn : ∫ x in a..b, (Polynomial.derivative^[n] A).eval x * gp.derivative.eval x =
          (-1 : ℝ) ^ n * ∫ x in a..b, A.eval x * (Polynomial.derivative^[n + 1] gp).eval x := by
        rw [show Polynomial.derivative^[n + 1] gp = Polynomial.derivative^[n] gp.derivative from
          Function.iterate_succ_apply _ _ _]
        exact ih gp.derivative fun k hk => hb k (Nat.lt_succ_of_lt hk)
      rw [hgn] at key
      have hpow : (-1 : ℝ) ^ (n + 1) = -((-1 : ℝ) ^ n) := by
        rw [pow_succ, mul_neg_one]
      rw [hpow, neg_mul]
      exact key

/-- A continuous nonnegative function on a nondegenerate closed interval has positive integral
if it is positive at some point of that interval. -/
theorem integral_pos_of_nonneg_of_pos_at {a b : ℝ} (hab : a < b) {g : ℝ → ℝ} (hg : Continuous g)
    (hnn : ∀ x ∈ Icc a b, 0 ≤ g x) {y : ℝ} (hy : y ∈ Icc a b) (hgy : 0 < g y) :
    0 < ∫ x in a..b, g x := by
  have hcont : ContinuousAt g y := hg.continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont (g y / 2) (by positivity)
  set u : ℝ := max a (y - δ / 2) with hu
  set v : ℝ := min b (y + δ / 2) with hv
  have hu1 : y - δ / 2 ≤ u := by rw [hu]; exact le_max_right _ _
  have hv1 : v ≤ y + δ / 2 := by rw [hv]; exact min_le_right _ _
  have huy : u ≤ y := by rw [hu]; exact max_le hy.1 (by linarith)
  have hyv : y ≤ v := by rw [hv]; exact le_min hy.2 (by linarith)
  have hau : a ≤ u := le_max_left _ _
  have hvb : v ≤ b := min_le_left _ _
  have huv : u < v := by
    rcases le_or_gt (y - δ / 2) a with hle | hlt
    · rw [hu, max_eq_left hle]
      rcases le_or_gt b (y + δ / 2) with hle2 | hlt2
      · rw [hv, min_eq_left hle2]; exact hab
      · rw [hv, min_eq_right (by linarith)]
        exact lt_of_le_of_lt hy.1 (by linarith)
    · rw [hu, max_eq_right hlt.le]
      exact lt_of_lt_of_le (by linarith) hyv
  have hint : IntervalIntegrable g volume u v := hg.intervalIntegrable u v
  have hge : ∀ z ∈ Icc u v, g y / 2 < g z := by
    intro z hz
    have hd : |z - y| < δ := by
      rw [abs_lt]
      constructor
      · linarith [hu1, hz.1]
      · linarith [hv1, hz.2]
    have hballz := hball (by rw [Real.dist_eq]; exact hd)
    rw [Real.dist_eq, abs_lt] at hballz
    linarith
  have hmid : g y / 2 * (v - u) ≤ ∫ x in u..v, g x := by
    calc g y / 2 * (v - u) = ∫ x in u..v, g y / 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ x in u..v, g x := intervalIntegral.integral_mono_on (le_of_lt huv)
          ((continuous_const (y := g y / 2)).intervalIntegrable u v) hint
          (fun z hz => le_of_lt (hge z hz))
  have hleft : (0 : ℝ) ≤ ∫ x in a..u, g x := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ : ℝ => (0 : ℝ)) hau
      ((continuous_const (y := (0 : ℝ))).intervalIntegrable a u) (hg.intervalIntegrable a u)
      (fun z hz => hnn z (Icc_subset_Icc le_rfl (le_trans huv.le hvb) hz))
    simpa using h
  have hright : (0 : ℝ) ≤ ∫ x in v..b, g x := by
    have h := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ : ℝ => (0 : ℝ)) hvb
      ((continuous_const (y := (0 : ℝ))).intervalIntegrable v b) (hg.intervalIntegrable v b)
      (fun z hz => hnn z (Icc_subset_Icc (hau.trans huv.le) le_rfl hz))
    simpa using h
  have hsplit : ∫ x in a..b, g x =
      (∫ x in a..u, g x) + ((∫ x in u..v, g x) + ∫ x in v..b, g x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable a v)
      (hg.intervalIntegrable v b),
      ← intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable a u)
      (hg.intervalIntegrable u v)]
    ring
  have hpos : 0 < g y / 2 * (v - u) := by positivity
  rw [hsplit]
  linarith

/-- For natural `m` and `n`, the integral of `t^m * (1 - t)^n` over `[0, 1]` is `m.factorial *
n.factorial / (m + n + 1).factorial`. -/
theorem integral_pow_mul_one_sub_pow (m n : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ m * (1 - t) ^ n) =
      ((m.factorial * n.factorial : ℝ) / ((m + n + 1).factorial : ℝ)) := by
  induction n generalizing m with
  | zero =>
      have h0 : ∀ t : ℝ, t ^ m * (1 - t) ^ 0 = t ^ m := by
        intro t; rw [pow_zero, mul_one]
      rw [intervalIntegral.integral_congr (fun t _ => h0 t), integral_pow,
        one_pow, zero_pow (Nat.succ_ne_zero m), sub_zero, Nat.add_zero, Nat.factorial_succ,
        Nat.factorial_zero, Nat.cast_one, mul_one]
      push_cast
      have hm : (m.factorial : ℝ) ≠ 0 := by positivity
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      field_simp
  | succ n ih =>
      set Z : Polynomial ℝ := 1 - Polynomial.X with hZ
      have hZd : Z.derivative = -1 := by
        rw [hZ, Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_X,
          zero_sub]
      have hZe : ∀ x : ℝ, Z.eval x = 1 - x := by
        intro x; rw [hZ, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
      have hq' : (Z ^ (n + 1)).derivative =
          -Polynomial.C (((n + 1 : ℕ) : ℝ)) * Z ^ n := by
        rw [Polynomial.derivative_pow_succ, hZd]
        push_cast
        ring
      have key := integral_poly_derivative_mul (Polynomial.X ^ (m + 1)) (Z ^ (n + 1)) 0 1
      have hb1 : ((Polynomial.X ^ (m + 1)) * (Z ^ (n + 1))).eval 1 = 0 := by
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, hZe]
        rw [sub_self, zero_pow (Nat.succ_ne_zero n), mul_zero]
      have hb0 : ((Polynomial.X ^ (m + 1)) * (Z ^ (n + 1))).eval 0 = 0 := by
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
        rw [zero_pow (Nat.succ_ne_zero m), zero_mul]
      rw [hb1, hb0, sub_zero, zero_sub] at key
      have hL : ∫ x in (0 : ℝ)..1, (Polynomial.X ^ (m + 1)).derivative.eval x *
          (Z ^ (n + 1)).eval x =
          (((m + 1 : ℕ) : ℝ)) * ∫ x in (0 : ℝ)..1, x ^ m * (1 - x) ^ (n + 1) := by
        rw [Polynomial.derivative_X_pow_succ,
          ← intervalIntegral.integral_const_mul (((m + 1 : ℕ) : ℝ))
            (fun x : ℝ => x ^ m * (1 - x) ^ (n + 1))]
        refine intervalIntegral.integral_congr fun x _ => ?_
        simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hZe,
          Polynomial.eval_C]
        push_cast
        ring
      have hR : ∫ x in (0 : ℝ)..1, (Polynomial.X ^ (m + 1)).eval x *
          (Z ^ (n + 1)).derivative.eval x =
          -((((n + 1 : ℕ) : ℝ)) * ∫ x in (0 : ℝ)..1, x ^ (m + 1) * (1 - x) ^ n) := by
        have hR0 : ∫ x in (0 : ℝ)..1, (Polynomial.X ^ (m + 1)).eval x *
            (Z ^ (n + 1)).derivative.eval x =
            ∫ x in (0 : ℝ)..1, (-(((n + 1 : ℕ) : ℝ)) * (x ^ (m + 1) * (1 - x) ^ n : ℝ)) :=
          intervalIntegral.integral_congr fun x _ => by
            simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
              Polynomial.eval_X, hZe, hq', Polynomial.eval_neg]
            push_cast
            ring
        rw [hR0, intervalIntegral.integral_const_mul, neg_mul]
      rw [hL, hR, ih (m + 1), neg_neg] at key
      have e0 : m + (n + 1) + 1 = m + n + 1 + 1 := by omega
      have e1 : (m + 1 + n + 1) = (m + n + 1 + 1) := by omega
      rw [e1] at key
      rw [e0]
      push_cast at key ⊢
      have hfm : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hfn : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hfd : ((m + n + 1 + 1).factorial : ℝ) =
          ((m : ℝ) + ((n : ℝ) + 1) + 1) * ((m + n + 1).factorial : ℝ) := by
        rw [show m + n + 1 + 1 = (m + n + 1) + 1 from rfl, Nat.factorial_succ]; push_cast; ring
      rw [hfm, hfd] at key
      rw [hfn, hfd]
      have hE : ((m : ℝ) + ((n : ℝ) + 1) + 1) * ((m + n + 1).factorial : ℝ) ≠ 0 := by positivity
      have hA : (m.factorial : ℝ) ≠ 0 := by positivity
      refine mul_left_cancel₀ (a := ((m : ℝ) + 1)) (by positivity) ?_
      field_simp at key ⊢
      linear_combination key

/-- A nonzero real polynomial of positive degree has derivative degree one less and derivative
leading coefficient equal to its degree times its leading coefficient. -/
theorem natDegree_derivative_eq {p : Polynomial ℝ} (hp : p ≠ 0) (hpos : 0 < p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 ∧
      p.derivative.leadingCoeff = (p.natDegree : ℝ) * p.leadingCoeff := by
  have hc : ((p.natDegree - 1 : ℕ) : ℝ) + 1 = (p.natDegree : ℝ) := by
    rw [← Nat.cast_add_one (p.natDegree - 1), Nat.sub_add_cancel hpos]
  have heq : p.derivative.coeff (p.natDegree - 1) = (p.natDegree : ℝ) * p.leadingCoeff := by
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hpos, hc]
    show p.leadingCoeff * (p.natDegree : ℝ) = (p.natDegree : ℝ) * p.leadingCoeff
    ring
  have hne : p.derivative.coeff (p.natDegree - 1) ≠ 0 := by
    rw [heq]
    exact mul_ne_zero (by positivity) (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hdeg : p.derivative.natDegree = p.natDegree - 1 :=
    Nat.le_antisymm (Polynomial.natDegree_derivative_le p)
      (Polynomial.le_natDegree_of_ne_zero hne)
  refine ⟨hdeg, ?_⟩
  have h1 : p.derivative.leadingCoeff = p.derivative.coeff (p.natDegree - 1) := by
    show p.derivative.coeff p.derivative.natDegree = _
    rw [hdeg]
  rw [h1, heq]

/-- Differentiating a nonzero polynomial of natural degree `n` exactly `n` times gives the
constant polynomial with value `n.factorial * p.leadingCoeff`. -/
theorem iterate_derivative_eq_C {n : ℕ} {p : Polynomial ℝ} (hp : p ≠ 0)
    (hd : p.natDegree = n) :
    Polynomial.derivative^[n] p = Polynomial.C ((n.factorial : ℝ) * p.leadingCoeff) := by
  induction n generalizing p with
  | zero =>
      have h0 : p = Polynomial.C p.leadingCoeff := by
        refine (Polynomial.eq_C_of_natDegree_eq_zero hd).trans ?_
        congr 1
        show p.coeff 0 = p.coeff p.natDegree
        rw [hd]
      rw [Function.iterate_zero_apply, h0]
      simp
  | succ n ih =>
      have hpos : 0 < p.natDegree := by omega
      have hp' : p.derivative ≠ 0 := fun h0 =>
        hpos.ne' (Polynomial.natDegree_eq_zero_of_derivative_eq_zero h0)
      have hd' : p.derivative.natDegree = n := by
        have h := (natDegree_derivative_eq hp hpos).1
        omega
      have ih' := ih hp' hd'
      rw [Function.iterate_succ_apply, ih', (natDegree_derivative_eq hp hpos).2,
        Nat.factorial_succ, hd]
      push_cast
      ring

/-- The Lagrange basis polynomial for index `i`, formed from the normalized linear factors
associated with all other nodes. -/
def lagrangeBasis {Q : ℕ} (node : Fin Q → ℝ) (i : Fin Q) : Polynomial ℝ :=
  Polynomial.C ((Finset.prod (Finset.univ.erase i) fun j => node i - node j)⁻¹) *
    Finset.prod (Finset.univ.erase i) fun j => Polynomial.X - Polynomial.C (node j)

/-- For injective nodes, the Lagrange basis polynomial evaluates to one at its own node. -/
theorem lagrangeBasis_eval_self {Q : ℕ} (node : Fin Q → ℝ) (hinj : Function.Injective node)
    (i : Fin Q) : (lagrangeBasis node i).eval (node i) = 1 := by
  have hne : Finset.prod (Finset.univ.erase i) (fun j => node i - node j) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => sub_ne_zero_of_ne fun h => ?_
    exact Finset.ne_of_mem_erase hj (hinj h.symm)
  rw [lagrangeBasis, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact inv_mul_cancel₀ hne

/-- A Lagrange basis polynomial evaluates to zero at any node with a different index. -/
theorem lagrangeBasis_eval_of_ne {Q : ℕ} (node : Fin Q → ℝ) {i j : Fin Q} (hij : j ≠ i) :
    (lagrangeBasis node i).eval (node j) = 0 := by
  have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ j⟩
  rw [lagrangeBasis, Polynomial.eval_mul, Polynomial.eval_prod]
  refine mul_eq_zero.mpr (Or.inr ?_)
  exact Finset.prod_eq_zero hmem (by
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self])

/-- The natural degree of a Lagrange basis polynomial on `Fin Q` is at most `Q - 1`. -/
theorem natDegree_lagrangeBasis_le {Q : ℕ} (node : Fin Q → ℝ) (i : Fin Q) :
    (lagrangeBasis node i).natDegree ≤ Q - 1 := by
  have h2 : (Finset.prod (Finset.univ.erase i)
        fun j => Polynomial.X - Polynomial.C (node j)).natDegree = Q - 1 := by
    rw [Polynomial.natDegree_prod_of_monic (Finset.univ.erase i)
      (fun j => Polynomial.X - Polynomial.C (node j))
      (fun j _ => Polynomial.monic_X_sub_C _)]
    simp [Finset.card_erase_of_mem]
  rw [lagrangeBasis]
  refine Nat.le_trans (Polynomial.natDegree_mul_le.trans ?_) h2.le
  rw [Polynomial.natDegree_C, Nat.zero_add]

/-- A polynomial of natural degree less than `Q` equals its Lagrange interpolation sum at `Q`
injectively indexed nodes. -/
theorem lagrange_interpolation {Q : ℕ} (node : Fin Q → ℝ) (hinj : Function.Injective node)
    (r : Polynomial ℝ) (hr : r.natDegree < Q) :
    r = ∑ i, Polynomial.C (r.eval (node i)) * lagrangeBasis node i := by
  have hQ : 0 < Q := hr.bot_lt
  have hsup : Finset.univ.sup
      (fun i : Fin Q => (Polynomial.C (r.eval (node i)) * lagrangeBasis node i).natDegree)
      ≤ Q - 1 := by
    refine Finset.sup_le fun i _ => ?_
    exact Nat.le_trans (Polynomial.natDegree_mul_le.trans (by simp))
      (natDegree_lagrangeBasis_le node i)
  have hdeg : (∑ i, Polynomial.C (r.eval (node i)) * lagrangeBasis node i).natDegree < Q :=
    (Polynomial.natDegree_sum_le _ _).trans_lt
      (Nat.lt_of_le_of_lt hsup (Nat.sub_lt hQ (by omega)))
  have hsub : (r - ∑ i, Polynomial.C (r.eval (node i)) * lagrangeBasis node i).natDegree < Q := by
    have hle := Polynomial.natDegree_sub_le r
      (∑ i, Polynomial.C (r.eval (node i)) * lagrangeBasis node i)
    omega
  have key : ∀ (i j : Fin Q), (lagrangeBasis node j).eval (node i) = if j = i then 1 else 0 := by
    intro i j
    by_cases hj : j = i
    · subst hj
      rw [lagrangeBasis_eval_self node hinj j, if_pos rfl]
    · rw [lagrangeBasis_eval_of_ne node (Ne.symm hj), if_neg hj]
  have hzero := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (r - ∑ i, Polynomial.C (r.eval (node i)) * lagrangeBasis node i) hinj
    (fun i => by
      rw [Polynomial.eval_sub, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, key i,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self])
    (by simpa using hsub)
  rw [sub_eq_zero] at hzero
  exact hzero

/-- The root multiplicity in the product of the distinct factors `X - C ρ` is one for a root in
the finite set and zero otherwise. -/
theorem rootMultiplicity_prod_X_sub_C (F : Finset ℝ) (v : ℝ) :
    (Finset.prod F fun ρ => Polynomial.X - Polynomial.C ρ).rootMultiplicity v =
      if v ∈ F then 1 else 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      show (Polynomial.rootMultiplicity v) (1 : Polynomial ℝ) = _
      rw [show (1 : Polynomial ℝ) = Polynomial.C 1 from rfl, Polynomial.rootMultiplicity_C]
      simp
  | insert ρ F hρ ih =>
      have hne : (Polynomial.X - Polynomial.C ρ) *
          Finset.prod F (fun ρ => Polynomial.X - Polynomial.C ρ) ≠ 0 :=
        mul_ne_zero (Polynomial.monic_X_sub_C ρ).ne_zero
          (Polynomial.monic_prod_X_sub_C (fun ρ => ρ) F).ne_zero
      rw [Finset.prod_insert hρ, Polynomial.rootMultiplicity_mul hne, ih,
        Polynomial.rootMultiplicity_X_sub_C]
      by_cases hv : v = ρ
      · subst hv
        have hvF : v ∉ F := fun hmem => hρ hmem
        simp [hvF]
      · by_cases hvm : v ∈ F
        · simp [hv, hvm]
        · simp [hv, hvm]

/-- Negating a real polynomial preserves its root multiplicity at every real point. -/
theorem rootMultiplicity_neg (T : Polynomial ℝ) (ρ : ℝ) :
    (-T).rootMultiplicity ρ = T.rootMultiplicity ρ := by
  by_cases hT : T = 0
  · simp [hT]
  · have hfac : (-T : Polynomial ℝ) = Polynomial.C ((-1 : ℝ)) * T := by
      ext c
      simp [Polynomial.coeff_neg]
    rw [hfac, Polynomial.rootMultiplicity_mul (mul_ne_zero (by simp) hT),
      Polynomial.rootMultiplicity_C, zero_add]

/-- A continuous function nonnegative on `[u, z)` is nonnegative at `z` when `u < z`. -/
theorem nonneg_of_Ico {u z : ℝ} {φ : ℝ → ℝ} (hc : Continuous φ) (huz : u < z)
    (h : ∀ t ∈ Ico u z, 0 ≤ φ t) : 0 ≤ φ z := by
  by_contra h0
  push Not at h0
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousAt_iff.1 (hc.continuousAt (x := z)) (-φ z / 2) (by linarith)
  set s : ℝ := max u (z - δ / 2) with hs
  have hs1 : u ≤ s := le_max_left _ _
  have hs3 : z - δ / 2 ≤ s := by rw [hs]; exact le_max_right _ _
  have hs2 : s < z := by
    rw [hs, max_lt_iff]
    exact ⟨huz, by linarith⟩
  have hd : dist s z < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hballz := hball (x := s) hd
  rw [Real.dist_eq, abs_lt] at hballz
  exact absurd (h s ⟨hs1, hs2⟩) (by linarith)

/-- A continuous function nonnegative on `(u, z]` is nonnegative at `u` when `u < z`. -/
theorem nonneg_of_Ioc {u z : ℝ} {φ : ℝ → ℝ} (hc : Continuous φ) (huz : u < z)
    (h : ∀ t ∈ Ioc u z, 0 ≤ φ t) : 0 ≤ φ u := by
  by_contra h0
  push Not at h0
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousAt_iff.1 (hc.continuousAt (x := u)) (-φ u / 2) (by linarith)
  set s : ℝ := min z (u + δ / 2) with hs
  have hs1 : s ≤ z := min_le_left _ _
  have hs3 : u + δ / 2 ≥ s := by rw [hs]; exact min_le_right _ _
  have hs2 : u < s := by
    rw [hs, lt_min_iff]
    exact ⟨huz, by linarith⟩
  have hd : dist s u < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hballu := hball (x := s) hd
  rw [Real.dist_eq, abs_lt] at hballu
  exact absurd (h s ⟨hs2, hs1⟩) (by linarith)

/-- A polynomial whose roots in `(a, b)` all have even multiplicity cannot take a positive value
at `u` and a negative value at `v` there with `u ≤ v`. -/
theorem sign_aux {a b u v : ℝ} {T : Polynomial ℝ}
    (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (hTu : 0 < T.eval u) (hTv : T.eval v < 0)
    (huv : u ≤ v) (hev : ∀ ρ ∈ Ioo a b, Even (T.rootMultiplicity ρ)) : False := by
  have hTne : T ≠ 0 := by
    intro h0
    rw [h0] at hTu
    simp at hTu
  have hTe : Continuous (fun x : ℝ => T.eval x) := continuous_eval T
  set S : Set ℝ := {x | x ∈ Icc u v ∧ ∀ t ∈ Icc u x, 0 ≤ T.eval t} with hSdef
  have hSbd : BddAbove S := ⟨v, fun x hx => hx.1.2⟩
  have huS : u ∈ S := ⟨⟨le_refl u, huv⟩, fun t ht => by
      rw [le_antisymm ht.2 ht.1]
      exact hTu.le⟩
  have hSne : S.Nonempty := ⟨u, huS⟩
  set z : ℝ := sSup S with hzdef
  have huz : u ≤ z := le_csSup hSbd huS
  have hzv : z ≤ v := csSup_le hSne fun x hx => hx.1.2

  have hnn : ∀ t ∈ Icc u z, 0 ≤ T.eval t := by
    intro t ht
    rcases lt_or_ge t z with hlt | hle
    · obtain ⟨s, hsS, hts⟩ := exists_lt_of_lt_csSup hSne hlt
      exact hsS.2 t ⟨ht.1, hts.le⟩
    · have htz : t = z := le_antisymm ht.2 hle
      rw [htz]
      by_contra h0
      push Not at h0
      obtain ⟨δ, hδ, hball⟩ :=
        Metric.continuousAt_iff.1 (hTe.continuousAt (x := z)) (-T.eval z / 2) (by linarith)
      obtain ⟨s, hsS, hts⟩ :=
        exists_lt_of_lt_csSup hSne (show z - δ / 2 < z by linarith)
      have hsle : s ≤ z := le_csSup hSbd hsS
      have hd : dist s z < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      have hballz := hball (x := s) hd
      rw [Real.dist_eq, abs_lt] at hballz
      have hsn : T.eval s < 0 := by linarith
      exact absurd (hsS.2 s ⟨hsS.1.1, le_refl s⟩) (not_le.mpr hsn)

  have hzvlt : z < v := by
    rcases lt_or_ge z v with h | h
    · exact h
    · exact absurd (hnn v ⟨huv, h⟩) (not_le.mpr hTv)
  have hTeq0 : T.eval z = 0 := by
    rcases le_total 0 (T.eval z) with h0 | h0
    · refine le_antisymm ?_ h0
      by_contra hpos
      push Not at hpos
      obtain ⟨δ, hδ, hball⟩ :=
        Metric.continuousAt_iff.1 (hTe.continuousAt (x := z)) (T.eval z / 2) (by linarith)
      set z' : ℝ := min (z + δ / 2) v with hz'def
      have hz'le : z' ≤ z + δ / 2 := by rw [hz'def]; exact min_le_left _ _
      have hz'z : z < z' := lt_min (by linarith) hzvlt
      have hballz' : ∀ w ∈ Icc z z', T.eval z / 2 < T.eval w := by
        intro w hw
        have hd : dist w z < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hw.1, hw.2, hz'le]
        have hbw := hball (x := w) hd
        rw [Real.dist_eq, abs_lt] at hbw
        linarith
      have hz'S : z' ∈ S := by
        refine ⟨⟨huz.trans hz'z.le, min_le_right _ _⟩, fun t ht => ?_⟩
        rcases le_or_gt t z with hle | hlt
        · exact hnn t ⟨ht.1, hle⟩
        · exact le_trans (by linarith : (0 : ℝ) ≤ T.eval z / 2) (hballz' t ⟨hlt.le, ht.2⟩).le
      exact absurd (le_csSup hSbd hz'S) (by linarith)
    · exact le_antisymm h0 (hnn z ⟨huz, le_refl z⟩)
  have huzlt : u < z := by
    rcases eq_or_ne u z with h | h
    · exact absurd (h ▸ hTeq0) (ne_of_gt hTu)
    · exact lt_of_le_of_ne huz h
  have hzIoo : z ∈ Ioo a b := ⟨lt_of_lt_of_le hu.1 huz, lt_trans hzvlt hv.2⟩

  set m : ℕ := T.rootMultiplicity z with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact Polynomial.rootMultiplicity_pos'.mpr ⟨hTne, hTeq0⟩
  have hkeven : Even m := by
    rw [hmdef]
    exact hev z hzIoo
  obtain ⟨k, hk⟩ := hkeven
  have hm2 : 2 ≤ m := by omega
  set U : Polynomial ℝ := T /ₘ ((Polynomial.X - Polynomial.C z) ^ m) with hUdef
  have hTzfac : (Polynomial.X - Polynomial.C z) ^ m * U = T :=
    Polynomial.pow_mul_divByMonic_rootMultiplicity_eq T z
  have hUzne : U.eval z ≠ 0 := Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero z hTne
  have hpownn : ∀ w : ℝ, 0 ≤ (w - z) ^ m := by
    intro w
    rw [hk, ← Nat.two_mul, pow_mul]
    exact pow_nonneg (sq_nonneg _) k
  have hfacT : ∀ w : ℝ, T.eval w = (w - z) ^ m * U.eval w := by
    intro w
    rw [← hTzfac, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  have hUnnIco : ∀ t ∈ Ico u z, 0 ≤ U.eval t := by
    intro t ht
    have hpos : 0 < (t - z) ^ m := by
      rw [hk, ← Nat.two_mul, pow_mul]
      refine pow_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (ne_of_lt ht.2))) k
    have hdiv : T.eval t / (t - z) ^ m = U.eval t :=
      (div_eq_iff (ne_of_gt hpos)).mpr (by rw [hfacT t]; ring)
    calc 0 ≤ T.eval t / (t - z) ^ m := div_nonneg (hnn t ⟨ht.1, ht.2.le⟩) (hpownn t)
      _ = U.eval t := hdiv
  have hUz : 0 ≤ U.eval z := nonneg_of_Ico (continuous_eval U) huzlt hUnnIco
  have hUzpos : 0 < U.eval z := lt_of_le_of_ne hUz (Ne.symm hUzne)
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.continuousAt_iff.1 ((continuous_eval U).continuousAt (x := z)) (U.eval z / 2)
      (by linarith)
  set z'' : ℝ := min (z + δ / 2) v with hz''def
  have hz''le : z'' ≤ z + δ / 2 := by rw [hz''def]; exact min_le_left _ _
  have hz''z : z < z'' := lt_min (by linarith) hzvlt
  have hUpos : ∀ w : ℝ, |w - z| < δ → 0 < U.eval w := by
    intro w hw
    have hbw := hball (x := w) hw
    rw [Real.dist_eq, abs_lt] at hbw
    linarith
  have hz''S : z'' ∈ S := by
    refine ⟨⟨huz.trans hz''z.le, min_le_right _ _⟩, fun t ht => ?_⟩
    rcases le_or_gt t z with hle | hlt
    · exact hnn t ⟨ht.1, hle⟩
    · rw [hfacT t]
      refine mul_nonneg (hpownn t) ?_
      have habs : |t - z| < δ := by
        rw [abs_lt]
        constructor <;> linarith [ht.2, hz''le]
      exact (hUpos t habs).le
  exact absurd (le_csSup hSbd hz''S) (not_le.mpr hz''z)

/-- If every root in `(a, b)` has even multiplicity, a real polynomial is either nonnegative
throughout that interval or nonpositive throughout it. -/
theorem sign_of_even_rootMultiplicity {a b : ℝ} (T : Polynomial ℝ)
    (hev : ∀ ρ ∈ Ioo a b, Even (T.rootMultiplicity ρ)) :
    (∀ x ∈ Ioo a b, 0 ≤ T.eval x) ∨ (∀ x ∈ Ioo a b, T.eval x ≤ 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨p, hp, hpltn⟩, n, hn, hnlt⟩ := hcon
  rcases le_or_gt n p with hnp | hpn
  · exact sign_aux hn hp hnlt hpltn hnp hev
  · exact sign_aux (T := -T) hp hn (by simp [hpltn]) (by simp [hnlt]) hpn.le
      (fun ρ hρ => by rw [rootMultiplicity_neg]; exact hev ρ hρ)

/-- If a function of class `C^m` has derivative zeros at distinct closed-interval nodes with
positive prescribed multiplicities summing to at least `m + 1`, its `m`-th derivative
vanishes somewhere on the interval. -/
theorem counted_zero_rolle_aux : ∀ (m : ℕ) (ι : Type) [Fintype ι] (a b : ℝ) (f : ℝ → ℝ)
    (node : ι → ℝ) (mult : ι → ℕ), a ≤ b → Function.Injective node → (∀ i, node i ∈ Icc a b) →
    (∀ i, 1 ≤ mult i) → m + 1 ≤ ∑ i, mult i → ContDiff ℝ ((m : WithTop ℕ∞)) f →
    (∀ i (j : ℕ), j < mult i → iteratedDeriv j f (node i) = 0) →
    ∃ x ∈ Icc a b, iteratedDeriv m f x = 0 := by
  intro m
  induction m with
  | zero =>
    intro ι _ a b f node mult hab hinj hmem h1 hsum hcd hz
    obtain ⟨i, hi⟩ : ∃ i : ι, 0 < mult i := by
      by_contra hcon
      push Not at hcon
      have h0 : ∑ i, mult i = 0 :=
        Finset.sum_eq_zero (fun i _ => by have := hcon i; omega)
      omega
    exact ⟨node i, hmem i, hz i 0 hi⟩
  | succ m ih =>
    intro ι Finst a b f node mult hab hinj hmem h1 hsum hcd hz
    have hcd' : ContDiff ℝ (((m : WithTop ℕ∞)) + 1) f := by exact_mod_cast hcd
    obtain ⟨hdiff, -, hgd⟩ := contDiff_succ_iff_deriv.1 hcd'
    obtain ⟨i₀, -⟩ : ∃ i : ι, 1 ≤ mult i := by
      by_contra hcon
      push Not at hcon
      have h0 : ∑ i, mult i = 0 :=
        Finset.sum_eq_zero (fun i _ => by have := hcon i; omega)
      omega
    set n := Fintype.card ι with hndef
    have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨i₀⟩
    have hcard : (Finset.univ.image node).card = n := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

    obtain ⟨ξ, hξmono, hcov, hback⟩ : ∃ ξ : Fin n → ℝ, StrictMono ξ ∧
        (∀ i : ι, ∃ k : Fin n, node i = ξ k) ∧ (∀ k : Fin n, ∃ i : ι, ξ k = node i) := by
      refine ⟨(Finset.univ.image node).orderEmbOfFin hcard,
        ((Finset.univ.image node).orderEmbOfFin hcard).strictMono, ?_, ?_⟩
      · intro i
        have hmemi : node i ∈
            Finset.image ((Finset.univ.image node).orderEmbOfFin hcard) Finset.univ := by
          rw [Finset.image_orderEmbOfFin_univ]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
        obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmemi
        exact ⟨k, hk.symm⟩
      · intro k
        have hmemk : (Finset.univ.image node).orderEmbOfFin hcard k ∈ Finset.univ.image node :=
          Finset.orderEmbOfFin_mem _ hcard k
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hmemk
        exact ⟨i, hi.symm⟩

    set up : Fin (n - 1) → Fin n := fun k => ⟨k.1, by omega⟩ with hupdef
    set suc : Fin (n - 1) → Fin n := fun k => ⟨k.1 + 1, by omega⟩ with hsucdef
    have hrolle : ∀ k : Fin (n - 1), ∃ c : ℝ, c ∈ Ioo (ξ (up k)) (ξ (suc k)) ∧ deriv f c = 0 := by
      intro k
      obtain ⟨i₁, hi₁⟩ := hback (up k)
      obtain ⟨i₂, hi₂⟩ := hback (suc k)
      have hlt : ξ (up k) < ξ (suc k) := by
        have hlt' : (up k) < (suc k) := by rw [hupdef, hsucdef]; simp [Fin.lt_def]
        exact hξmono hlt'
      have hf1 : f (ξ (up k)) = 0 := by
        rw [hi₁]; exact hz i₁ 0 (by have := h1 i₁; omega)
      have hf2 : f (ξ (suc k)) = 0 := by
        rw [hi₂]; exact hz i₂ 0 (by have := h1 i₂; omega)
      obtain ⟨c, hcmem, hc⟩ := exists_deriv_eq_zero hlt hcd.continuous.continuousOn
        (by rw [hf1, hf2])
      exact ⟨c, hcmem, hc⟩
    choose η hη using hrolle

    have hinj' : Function.Injective
        (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => node di.1) η) := by
      intro x y hxy
      rcases x with di | k <;> rcases y with dj | k'
      · simp only [Sum.elim_inl] at hxy
        exact congrArg Sum.inl (Subtype.ext (hinj hxy))
      · exfalso
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        obtain ⟨κ, hκ⟩ := hcov di.1
        have hkey : ξ κ = η k' := by rw [← hκ]; exact hxy
        rcases le_or_gt κ.1 k'.1 with hcase | hcase
        · have hle : ξ κ ≤ ξ (up k') :=
            hξmono.monotone (by rw [hupdef]; exact Fin.le_def.mpr (by show κ.1 ≤ k'.1; omega))
          have hlt' := (hη k').1.1
          linarith
        · have hle : ξ (suc k') ≤ ξ κ :=
            hξmono.monotone (by rw [hsucdef]; exact Fin.le_def.mpr (by show k'.1 + 1 ≤ κ.1; omega))
          have hlt' := (hη k').1.2
          linarith
      · exfalso
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        obtain ⟨κ, hκ⟩ := hcov dj.1
        have hkey : ξ κ = η k := by rw [← hκ]; exact hxy.symm
        rcases le_or_gt κ.1 k.1 with hcase | hcase
        · have hle : ξ κ ≤ ξ (up k) :=
            hξmono.monotone (by rw [hupdef]; exact Fin.le_def.mpr (by show κ.1 ≤ k.1; omega))
          have hlt' := (hη k).1.1
          linarith
        · have hle : ξ (suc k) ≤ ξ κ :=
            hξmono.monotone (by rw [hsucdef]; exact Fin.le_def.mpr (by show k.1 + 1 ≤ κ.1; omega))
          have hlt' := (hη k).1.2
          linarith
      · by_contra hne
        simp only [Sum.elim_inr] at hxy
        have hne' : k.1 ≠ k'.1 := fun h => hne (congrArg Sum.inr (Fin.ext h))
        rcases lt_or_gt_of_ne hne' with hlt | hlt
        · have hle : ξ (suc k) ≤ ξ (up k') :=
            hξmono.monotone (by
              rw [hsucdef, hupdef]; exact Fin.le_def.mpr (by show k.1 + 1 ≤ k'.1; omega))
          have h1' := (hη k).1.2
          have h2' := (hη k').1.1
          linarith
        · have hle : ξ (suc k') ≤ ξ (up k) :=
            hξmono.monotone (by
              rw [hsucdef, hupdef]; exact Fin.le_def.mpr (by show k'.1 + 1 ≤ k.1; omega))
          have h1' := (hη k').1.2
          have h2' := (hη k).1.1
          linarith
    have hmem' : ∀ x : {i : ι // 2 ≤ mult i} ⊕ Fin (n - 1),
        (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => node di.1) η) x ∈ Icc a b := by
      rintro (di | k)
      · exact hmem di.1
      · obtain ⟨i₁, hi₁⟩ := hback (up k)
        obtain ⟨i₂, hi₂⟩ := hback (suc k)
        have hb1 := hmem i₁
        rw [← hi₁] at hb1
        have hb2 := hmem i₂
        rw [← hi₂] at hb2
        have hmemη := (hη k).1
        have he1 := hmemη.1
        have he2 := hmemη.2
        have hb1l := hb1.1
        have hb1r := hb1.2
        have hb2l := hb2.1
        have hb2r := hb2.2
        simp only [Sum.elim_inr]
        constructor <;> linarith
    have h1' : ∀ x : {i : ι // 2 ≤ mult i} ⊕ Fin (n - 1),
        1 ≤ (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => mult di.1 - 1) (fun _ => 1)) x := by
      rintro (di | k)
      · simp only [Sum.elim_inl]
        have := di.2
        omega
      · simp only [Sum.elim_inr]
        exact le_refl 1
    have honeR : ∑ _ : Fin (n - 1), 1 = n - 1 := by simp
    have hfiltermem : ∀ x : ι,
        x ∈ Finset.univ.filter (fun i => 2 ≤ mult i) ↔ 2 ≤ mult x := by
      intro x
      simp [Finset.mem_filter]
    have hAB : ∑ di : {i : ι // 2 ≤ mult i}, (mult di.1 - 1) = ∑ i : ι, (mult i - 1) := by
      have hA : ∑ di : {i : ι // 2 ≤ mult i}, (mult di.1 - 1)
          = ∑ i ∈ Finset.univ.filter (fun i => 2 ≤ mult i), (mult i - 1) :=
        (Finset.sum_subtype (Finset.univ.filter (fun i => 2 ≤ mult i)) hfiltermem
          (fun i => mult i - 1)).symm
      rw [hA]
      exact Finset.sum_subset (Finset.filter_subset _ _)
        (fun i _ hi => by
          have h2 : ¬ 2 ≤ mult i := fun hcon => hi (by simp [hcon])
          have := h1 i
          omega)
    have hsplit : ∑ i : ι, mult i = (∑ i : ι, (mult i - 1)) + n := by
      have honeN : n = ∑ i : ι, 1 := by simp [hndef]
      rw [honeN, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by have := h1 i; omega)
    have hsum' : m + 1 ≤ ∑ x : {i : ι // 2 ≤ mult i} ⊕ Fin (n - 1),
        (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => mult di.1 - 1) (fun _ => 1)) x := by
      rw [Fintype.sum_sumElim, honeR]
      omega
    have hz' : ∀ (x : {i : ι // 2 ≤ mult i} ⊕ Fin (n - 1)) (j : ℕ),
        j < (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => mult di.1 - 1) (fun _ => 1)) x →
        iteratedDeriv j (deriv f)
          ((Sum.elim (fun di : {i : ι // 2 ≤ mult i} => node di.1) η) x) = 0 := by
      rintro (di | k) j hj
      · simp only [Sum.elim_inl] at hj ⊢
        rw [← iteratedDeriv_succ']
        exact hz di.1 (j + 1) (by have := di.2; omega)
      · simp only [Sum.elim_inr] at hj ⊢
        have hj0 : j = 0 := by omega
        subst hj0
        exact (hη k).2
    obtain ⟨x, hxmem, hx⟩ := ih ({i : ι // 2 ≤ mult i} ⊕ Fin (n - 1)) a b (deriv f)
      (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => node di.1) η)
      (Sum.elim (fun di : {i : ι // 2 ≤ mult i} => mult di.1 - 1) (fun _ => 1))
      hab hinj' hmem' h1' hsum' hgd hz'
    exact ⟨x, hxmem, by rw [iteratedDeriv_succ']; exact hx⟩

/-- For finitely many distinct nodes indexed by `Fin s`, prescribed derivative-zero
multiplicities of total at least `m + 1` force a zero of the `m`-th derivative of a function
of class `C^m` on the closed interval. -/
theorem counted_zero_rolle : ∀ (m s : ℕ) (a b : ℝ) (f : ℝ → ℝ) (node : Fin s → ℝ)
    (mult : Fin s → ℕ), a ≤ b → Function.Injective node → (∀ i, node i ∈ Icc a b) →
    (∀ i, 1 ≤ mult i) → m + 1 ≤ ∑ i, mult i → ContDiff ℝ ((m : WithTop ℕ∞)) f →
    (∀ i (j : ℕ), j < mult i → iteratedDeriv j f (node i) = 0) →
    ∃ x ∈ Icc a b, iteratedDeriv m f x = 0 :=
  fun m s a b f node mult hab hinj hmem h1 hsum hcd hz =>
    counted_zero_rolle_aux m (Fin s) a b f node mult hab hinj hmem h1 hsum hcd hz

end Qatlib.Concepts.LchsSimulation.Quadrature
