/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PolynomialToolkit
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-!
# Complete-contract counterexample to the legacy rectangle degree budget

At epsilon one the stated logarithmic budget forces the truncation index to zero.
The actual source rectangle with width and gap one is then a strictly negative
constant. Its error at the center exceeds one. The supremum estimate below proves
boundedness explicitly; it does not rely on an unbounded-set convention for sSup.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.SpectralAmp17.MainResults.RectBudget
open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel

/-- The exact supremum error definition used by the original approximation toolkit. -/
def epsOn (p : Polynomial ℝ) (f : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  sSup ((fun x => |p.eval x - f x|) '' s)

/-- The zeroth modified Bessel series is summable and has its positive constant term. -/
theorem bessel_zero_pos (β : ℝ) : 0 < besselI 0 β := by
  let a : ℕ → ℝ := fun m => (β / 2) ^ (2 * m) /
    ((m.factorial : ℝ) * (m.factorial : ℝ))
  have ha : ∀ m, 0 ≤ a m := by
    intro m
    dsimp [a]
    rw [pow_mul]
    positivity
  have hle : ∀ m, a m ≤ ((β / 2) ^ 2) ^ m / (m.factorial : ℝ) := by
    intro m
    have hf : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have hf1 : (1 : ℝ) ≤ (m.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos m)
    have hden : (m.factorial : ℝ) ≤ (m.factorial : ℝ) * (m.factorial : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hf1 hf.le
    dsimp [a]
    rw [pow_mul]
    exact div_le_div_of_nonneg_left (pow_nonneg (sq_nonneg (β / 2)) m) hf hden
  have hs : Summable a := Summable.of_nonneg_of_le ha hle
    (Real.summable_pow_div_factorial ((β / 2) ^ 2))
  have hfirst := hs.le_tsum 0 (fun m _hm => ha m)
  have h1 : (1 : ℝ) ≤ besselI 0 β := by
    simpa [besselI, a] using hfirst
  linarith

/-- The degree-one error-function polynomial has this real linear coefficient. -/
def erfSlope (k : ℝ) : ℝ :=
  (2 * k * Real.exp (-(k ^ 2) / 2) / Real.sqrt Real.pi) * besselI 0 (k ^ 2 / 2)

/-- At truncation index one the error-function polynomial is exactly linear. -/
theorem erf_one_eval (k x : ℝ) : (pErf k 1).eval x = erfSlope k * x := by
  have hempty : Finset.Icc (1 : ℕ) 0 = ∅ := by decide
  simp [pErf, erfSlope, mul_assoc]

/-- The source rectangle at zero truncation index, width one and gap one is constant. -/
theorem rect_zero_eval (x : ℝ) :
    (pRect 1 1 (1 / 4) 0).eval x = -erfSlope (2 * kSgn 1 (1 / 4)) / 2 := by
  simp only [pRect, pSgn, pErfShift, Nat.zero_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_comp,
    Polynomial.eval_neg, Polynomial.eval_sub, Polynomial.eval_X, erf_one_eval]
  ring

/-- The particular smoothing parameter used by the counterexample is positive. -/
theorem counter_scale_pos : 0 < kSgn 1 (1 / 4) := by
  have harg : (1 : ℝ) < 2 / (Real.pi * (1 / 4 : ℝ) ^ 2) := by
    apply (lt_div_iff₀ (by positivity : 0 < Real.pi * (1 / 4 : ℝ) ^ 2)).2
    nlinarith [Real.pi_lt_four]
  unfold kSgn
  exact mul_pos (div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num))
    (Real.sqrt_pos.2 (Real.log_pos harg))

/-- The actual linear coefficient appearing in the counterexample is strictly positive. -/
theorem counter_slope_pos : 0 < erfSlope (2 * kSgn 1 (1 / 4)) := by
  have hk : 0 < 2 * kSgn 1 (1 / 4) := mul_pos (by norm_num) counter_scale_pos
  have hp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  unfold erfSlope
  exact mul_pos
    (div_pos (mul_pos (mul_pos (by norm_num) hk) (Real.exp_pos _)) hp)
    (bessel_zero_pos _)

/-- The rectangle target is globally bounded in absolute value by one. -/
theorem rect_target_bound (x : ℝ) : |rectFun x| ≤ 1 := by
  unfold rectFun
  split_ifs <;> norm_num

/-- The exact original union of error intervals at width and gap one. -/
def rectDomain : Set ℝ :=
  Set.Icc (-(1 / 2)) (1 / 2) ∪ Set.Icc (1 / 2 + 1) 1 ∪
    Set.Icc (-1) (-(1 / 2 + 1))

/-- The actual error-value set is bounded above, despite the discontinuous rectangle target. -/
theorem counter_error_bdd :
    BddAbove ((fun x => |(pRect 1 1 (1 / 4) 0).eval x - rectFun (x / 1)|) ''
      rectDomain) := by
  refine ⟨|-erfSlope (2 * kSgn 1 (1 / 4)) / 2| + 1, ?_⟩
  rintro y ⟨x, _hx, rfl⟩
  change |(pRect 1 1 (1 / 4) 0).eval x - rectFun (x / 1)| ≤
    |-erfSlope (2 * kSgn 1 (1 / 4)) / 2| + 1
  rw [rect_zero_eval]
  calc |-erfSlope (2 * kSgn 1 (1 / 4)) / 2 - rectFun (x / 1)|
      ≤ |-erfSlope (2 * kSgn 1 (1 / 4)) / 2| + |rectFun (x / 1)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (-erfSlope (2 * kSgn 1 (1 / 4)) / 2) (-rectFun (x / 1))
    _ ≤ |-erfSlope (2 * kSgn 1 (1 / 4)) / 2| + 1 := by
      linarith [rect_target_bound (x / 1)]

/-- The supremum error of the forced zero-index rectangle strictly exceeds the permitted unit tolerance. -/
theorem counter_error_gt_one :
    1 < epsOn (pRect 1 1 (1 / 4) 0) (fun x => rectFun (x / 1)) rectDomain := by
  have hx0 : (0 : ℝ) ∈ rectDomain := by norm_num [rectDomain]
  have hmem : |(pRect 1 1 (1 / 4) 0).eval 0 - rectFun ((0 : ℝ) / 1)| ∈
      ((fun x => |(pRect 1 1 (1 / 4) 0).eval x - rectFun (x / 1)|) '' rectDomain) :=
    ⟨0, hx0, rfl⟩
  have hneg : (pRect 1 1 (1 / 4) 0).eval 0 < 0 := by
    rw [rect_zero_eval]
    linarith [counter_slope_pos]
  have hrect : rectFun ((0 : ℝ) / 1) = 1 := by norm_num [rectFun]
  have herr : 1 < |(pRect 1 1 (1 / 4) 0).eval 0 - rectFun ((0 : ℝ) / 1)| := by
    rw [hrect, abs_of_neg (by linarith : (pRect 1 1 (1 / 4) 0).eval 0 - 1 < 0)]
    linarith
  exact lt_of_lt_of_le herr (le_csSup counter_error_bdd hmem)

/-- The complete legacy Lemma 14 contract fails at unit width, gap and tolerance. -/
theorem lemma14_pRect_false :
    ¬ (∀ (κ w ε : ℝ) (_hκ0 : 0 < κ) (_hκ : κ ≤ 2) (_hw0 : 0 ≤ w)
      (_hw : w ≤ 2 - κ) (_hε0 : 0 < ε) (_hε : ε ≤ 1),
      ∃ n : ℕ, Even n ∧ bigOConst (n : ℝ) (κ⁻¹ * Real.log (1 / ε)) ∧
        epsOn (pRect w κ (ε / 4) n) (fun x => rectFun (x / w))
          (Set.Icc (-(w / 2)) (w / 2) ∪ Set.Icc (w / 2 + κ) 1 ∪
            Set.Icc (-1) (-(w / 2 + κ))) ≤ ε) := by
  intro h
  obtain ⟨n, _heven, hcost, herr⟩ := h 1 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases hcost with ⟨C, _hC, hbound⟩
  have hreal : (n : ℝ) ≤ 0 := by simpa using hbound
  have hn : n = 0 := by
    have hnat : n ≤ 0 := by exact_mod_cast hreal
    omega
  subst n
  have hsmall :
      epsOn (pRect 1 1 (1 / 4) 0) (fun x => rectFun (x / 1)) rectDomain ≤ 1 := by
    simpa only [rectDomain] using herr
  exact (not_le_of_gt counter_error_gt_one) hsmall

end Qatlib.Papers.SpectralAmp17.MainResults.RectBudget
