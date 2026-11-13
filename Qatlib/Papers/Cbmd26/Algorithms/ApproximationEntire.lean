/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationCauchy
import Qatlib.Papers.Cbmd26.Algorithms.ApproximationWindow
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Bounded polynomial approximation from Cauchy truncations

`realCauchyTruncation` takes the real parts of Cauchy coefficients on the radius-two circle,
with geometric error and uniform size estimates. `bounded_holomorphic_polynomial_exists`
combines this truncation with a step polynomial to approximate on `[g, 1]` while remaining
bounded by `1 + ε` on `[-1, 1]`; `bounded_real_holomorphic_complex_polynomial_exists` treats
functions real on `[0, 1]`, and `holomorphic_degree_budget_le` gives a logarithmic degree
estimate.

These approximation bounds supply polynomial inputs for the CBMD algorithms associated with
[WangEtAl2026].

## Main statements

* `realCauchyTruncation_error` gives a geometric truncation-error estimate.
* `bounded_real_holomorphic_complex_polynomial_exists` supplies bounded complex polynomial
  approximation.
* `holomorphic_degree_budget_le` bounds the degree budget using logarithms.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Polynomial Complex Metric Set
open scoped BigOperators

/-- The real polynomial formed from the real parts of the first `N` Cauchy coefficients of `f`,
centered at `0` and defined using radius `2`. -/
def realCauchyTruncation (f : ℂ → ℂ) (N : ℕ) : Polynomial ℝ :=
  ∑ n ∈ Finset.range N, C (cauchyCoefficient f 0 2 n).re * X ^ n

/-- The real Cauchy truncation using the first `N` coefficients has natural degree at most `N`. -/
theorem realCauchyTruncation_degree (f : ℂ → ℂ) (N : ℕ) :
    (realCauchyTruncation f N).natDegree ≤ N := by
  apply natDegree_sum_le_of_forall_le
  intro n hn
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt (Finset.mem_range.mp hn))

/-- Evaluation of the real Cauchy truncation at a real point equals the real part of the
corresponding complex partial sum. -/
theorem realCauchyTruncation_eval (f : ℂ → ℂ) (N : ℕ) (x : ℝ) :
    (realCauchyTruncation f N).eval x =
      (∑ n ∈ Finset.range N, cauchyCoefficient f 0 2 n * (x : ℂ) ^ n).re := by
  simp [realCauchyTruncation, eval_finsetSum, Complex.mul_re, ← Complex.ofReal_pow]

/-- A norm bound `M` on the radius-two circle bounds the norm of the Cauchy term of order `n` at
every real `x` with `|x| ≤ 1` by `M * (1 / 2) ^ n`. -/
private theorem cauchyTerm_bound (f : ℂ → ℂ) (M : ℝ)
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (x : ℝ) (hx : |x| ≤ 1) (n : ℕ) :
    ‖cauchyCoefficient f 0 2 n * (x : ℂ) ^ n‖ ≤ M * (1 / 2 : ℝ) ^ n := by
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hp : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  calc
    _ ≤ ‖cauchyCoefficient f 0 2 n‖ * 1 :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ ≤ M * (1 / 2 : ℝ) ^ n := by
      simpa using cauchyCoefficient_norm_le f 0 2 M (by norm_num) hb n

/-- If `f` is complex differentiable on the radius-two closed disk and bounded by `M` on its
circle, its real Cauchy truncation approximates the real part of `f` on `[-1, 1]` with error
at most `2 * M * (1 / 2) ^ N`. -/
theorem realCauchyTruncation_error (f : ℂ → ℂ) (M : ℝ)
    (hf : DifferentiableOn ℂ f (closedBall 0 2))
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (N : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(realCauchyTruncation f N).eval x - (f (x : ℂ)).re| ≤
      2 * M * (1 / 2 : ℝ) ^ N := by
  have hs := cauchyCoefficient_hasSum f 0 2 (by norm_num) hf (x : ℂ)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.trans_lt (by norm_num : (1 : ℝ) < 2))
  simp only [zero_add] at hs
  have he := norm_sub_le_of_geometric_bound_of_hasSum (by norm_num : (1 / 2 : ℝ) < 1)
    (cauchyTerm_bound f M hb x hx) hs N
  rw [realCauchyTruncation_eval, ← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (he.trans_eq (by ring))

/-- A norm bound `M` on the radius-two circle bounds every real Cauchy truncation in absolute
value by `2 * M` on `[-1, 1]`. -/
theorem realCauchyTruncation_bound (f : ℂ → ℂ) (M : ℝ)
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (N : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(realCauchyTruncation f N).eval x| ≤ 2 * M := by
  rw [realCauchyTruncation_eval]
  have hM : 0 ≤ M := (norm_nonneg (f 2)).trans (hb 2 (by norm_num [mem_sphere_iff_norm]))
  have hgeom := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left M
  calc
    _ ≤ ‖∑ n ∈ Finset.range N, cauchyCoefficient f 0 2 n * (x : ℂ) ^ n‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ n ∈ Finset.range N, ‖cauchyCoefficient f 0 2 n * (x : ℂ) ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, M * (1 / 2 : ℝ) ^ n :=
      Finset.sum_le_sum (fun n _ => cauchyTerm_bound f M hb x hx n)
    _ ≤ ∑' n : ℕ, M * (1 / 2 : ℝ) ^ n :=
      hgeom.sum_le_tsum _ (fun _ _ => mul_nonneg hM (by positivity))
    _ = 2 * M := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; ring

/-- Suppose `g, ε > 0`, `M ≥ 1`, and `f` is complex differentiable on the radius-two closed
disk, bounded by `M` on its circle, with real part bounded in absolute value by `1` on `[0,
1]`. Then a real polynomial of degree at most `dyadicOrder (ε / (4 * M)) * (1 + 4 * ⌈512 /
g⌉₊)` is bounded by `1 + ε` on `[-1, 1]` and approximates that real part within `ε` on `[g,
1]`. -/
theorem bounded_holomorphic_polynomial_exists (f : ℂ → ℂ) (g M ε : ℝ)
    (hg : 0 < g) (hM : 1 ≤ M) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 2))
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, |(f (x : ℂ)).re| ≤ 1) :
    ∃ P : Polynomial ℝ,
      P.natDegree ≤ dyadicOrder (ε / (4 * M)) * (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 + ε) ∧
      (∀ x ∈ Icc g 1, |P.eval x - (f (x : ℂ)).re| ≤ ε) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  let δ := ε / (4 * M)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδle : δ ≤ ε / 4 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left hε.le (by norm_num)
    linarith
  let N := dyadicOrder δ
  let Q := realCauchyTruncation f N
  obtain ⟨W, hWd, hWb, hWl, hWh⟩ := bounded_step_polynomial_precision g δ hg hδ
  have hQe (x : ℝ) (hx : |x| ≤ 1) : |Q.eval x - (f (x : ℂ)).re| ≤ ε / 2 := by
    calc
      _ ≤ 2 * M * (1 / 2 : ℝ) ^ N := realCauchyTruncation_error f M hf hb N x hx
      _ ≤ 2 * M * δ := mul_le_mul_of_nonneg_left (dyadicOrder_error hδ) (by positivity)
      _ = ε / 2 := by dsimp [δ]; field_simp; ring
  refine ⟨Q * W, ?_, ?_, ?_⟩
  · exact natDegree_mul_le.trans
      ((Nat.add_le_add (realCauchyTruncation_degree f N) hWd).trans_eq (by dsimp [N]; ring))
  · intro x hx
    have hxa : |x| ≤ 1 := abs_le.mpr hx
    rw [eval_mul, abs_mul, abs_of_nonneg (hWb x hx).1]
    by_cases hx0 : 0 ≤ x
    · have hQb : |Q.eval x| ≤ 1 + ε / 2 := by
        calc
          _ ≤ |Q.eval x - (f (x : ℂ)).re| + |(f (x : ℂ)).re| := by
            simpa only [sub_add_cancel] using abs_add_le (Q.eval x - (f (x : ℂ)).re) (f (x : ℂ)).re
          _ ≤ ε / 2 + 1 := add_le_add (hQe x hxa) (hpos x ⟨hx0, hx.2⟩)
          _ = 1 + ε / 2 := by ring
      calc
        _ ≤ |Q.eval x| * 1 := mul_le_mul_of_nonneg_left (hWb x hx).2 (abs_nonneg _)
        _ ≤ 1 + ε := by nlinarith
    · have hl := hWl x ⟨hx.1, le_of_not_ge hx0⟩
      calc
        _ ≤ 2 * M * δ := mul_le_mul (realCauchyTruncation_bound f M hb N x hxa) hl
          (hWb x hx).1 (by positivity)
        _ = ε / 2 := by dsimp [δ]; field_simp; ring
        _ ≤ 1 + ε := by linarith
  · intro x hx
    have hx0 : 0 ≤ x := hg.le.trans hx.1
    have hx' : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, hx.2⟩
    have hxa : |x| ≤ 1 := abs_le.mpr hx'
    have hw := hWb x hx'
    have heq : (Q * W).eval x - (f (x : ℂ)).re =
        (Q.eval x - (f (x : ℂ)).re) * W.eval x + (f (x : ℂ)).re * (W.eval x - 1) := by
      rw [eval_mul]; ring
    rw [heq]
    calc
      _ ≤ |(Q.eval x - (f (x : ℂ)).re) * W.eval x| + |(f (x : ℂ)).re * (W.eval x - 1)| := abs_add_le _ _
      _ = |Q.eval x - (f (x : ℂ)).re| * W.eval x + |(f (x : ℂ)).re| * (1 - W.eval x) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hw.1, abs_of_nonpos (sub_nonpos.mpr hw.2)]; ring
      _ ≤ ε / 2 * 1 + 1 * δ := add_le_add
        (mul_le_mul (hQe x hxa) hw.2 hw.1 (by positivity))
        (mul_le_mul (hpos x ⟨hx0, hx.2⟩) (hWh x hx) (sub_nonneg.mpr hw.2) (by norm_num))
      _ ≤ ε := by linarith

/-- Suppose `g, ε > 0`, `M ≥ 1`, and `f` is complex differentiable on the radius-two closed
disk, bounded by `M` on its circle, and real with norm at most `1` on `[0, 1]`. Then a
complex polynomial with the stated dyadic degree budget is bounded by `1 + ε` on `[-1, 1]`
and approximates `f` within `ε` on `[g, 1]`. -/
theorem bounded_real_holomorphic_complex_polynomial_exists
    (f : ℂ → ℂ) (g M ε : ℝ) (hg : 0 < g) (hM : 1 ≤ M) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 2))
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (hpos : ∀ x ∈ Icc (0 : ℝ) 1, ‖f (x : ℂ)‖ ≤ 1)
    (hreal : ∀ x ∈ Icc (0 : ℝ) 1, ((f (x : ℂ)).re : ℂ) = f (x : ℂ)) :
    ∃ P : Polynomial ℂ,
      P.natDegree ≤ dyadicOrder (ε / (4 * M)) * (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + ε) ∧
      (∀ x ∈ Icc g 1, ‖P.eval (x : ℂ) - f (x : ℂ)‖ ≤ ε) := by
  obtain ⟨p, hd, hp, he⟩ := bounded_holomorphic_polynomial_exists f g M ε hg hM hε hf hb
    (fun x hx => (Complex.abs_re_le_norm _).trans (hpos x hx))
  have heval (x : ℝ) : (p.map Complex.ofRealHom).eval (x : ℂ) = ((p.eval x : ℝ) : ℂ) :=
    Polynomial.eval_map_apply (p := p) Complex.ofRealHom x
  refine ⟨p.map Complex.ofRealHom, (natDegree_map_le).trans hd, ?_, ?_⟩
  · intro x hx
    rw [heval, Complex.norm_real, Real.norm_eq_abs]
    exact hp x hx
  · intro x hx
    rw [heval, ← hreal x ⟨hg.le.trans hx.1, hx.2⟩, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact he x hx

/-- For `g > 0`, `M ≥ 1`, and `0 < ε ≤ 1`, the real-valued degree budget is at most `(log (4 * M
/ ε) / log 2 + 1) * (5 + 2048 / g)`. -/
theorem holomorphic_degree_budget_le (g M ε : ℝ) (hg : 0 < g)
    (hM : 1 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((dyadicOrder (ε / (4 * M)) * (1 + 4 * ⌈512 / g⌉₊) : ℕ) : ℝ) ≤
      (Real.log (4 * M / ε) / Real.log 2 + 1) * (5 + 2048 / g) := by
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hratio : 1 ≤ 4 * M / ε := (le_div_iff₀ hε).mpr (by nlinarith)
  have hlog : 0 ≤ Real.log (4 * M / ε) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hratio) (Real.log_pos (by norm_num)).le
  have hi : (ε / (4 * M))⁻¹ = 4 * M / ε := by field_simp
  have hN : (dyadicOrder (ε / (4 * M)) : ℝ) ≤ Real.log (4 * M / ε) / Real.log 2 + 1 := by
    unfold dyadicOrder
    rw [hi]
    exact (Nat.ceil_lt_add_one hlog).le
  have hK := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 512 / g)).le
  have hK' : 1 + 4 * (⌈512 / g⌉₊ : ℝ) ≤ 5 + 2048 / g := by
    calc
      _ ≤ 1 + 4 * (512 / g + 1) := by linarith
      _ = 5 + 2048 / g := by ring
  push_cast
  exact mul_le_mul hN hK' (by positivity) (by positivity)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
