/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Rational rotations for bounded payoffs

The bisection routine `rationalSqrtBracket` constructs rational square-root brackets with an
exact comparison count. A rational stereographic parameter gives `rationalPayoffCS` on the unit
circle and the controlled rotation `rationalPayoffRotation`.

For payoffs in [0, 1], the encoded probability differs by at most 64/2^k and the rotation
differs from the ideal one in operator norm by at most 32/2^k. This provides a rational payoff
encoding for the bounded-mean construction of [Montanaro2015].

## Main statements

* `rational_sqrt_bracket_actual_interval_and_comparisons`: bisection gives a bracket of width
  2^(-k) after `k` comparisons.
* `rationalPayoffCS_circle`: the rational rotation parameters lie exactly on the unit circle.
* `rational_payoff_unitary_value_and_operator_error`: the rotation is unitary with explicit
  probability and operator error bounds.

## References

* [Montanaro, 2015][Montanaro2015]
-/

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PayoffMedian

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

/-- Rational bisection from [0, 1], returning lower and upper square-root bracket endpoints and
the number of comparisons. -/
def rationalSqrtBracket (q : ℚ) : ℕ → ℚ × ℚ × ℕ
  | 0 => (0, 1, 0)
  | k+1 => let s := rationalSqrtBracket q k
           let m := (s.1+s.2.1)/2
           if m*m ≤ q then (m,s.2.1,s.2.2+1) else (s.1,m,s.2.2+1)

/-- The rational stereographic parameter formed from the lower square-root bracket for `q`
divided by one plus the lower bracket for `1 - q`. -/
def rationalPayoffParameter (q : ℚ) (k : ℕ) : ℚ :=
  (rationalSqrtBracket q k).1 / (1+(rationalSqrtBracket (1-q) k).1)

/-- The rational cosine-sine pair obtained from `rationalPayoffParameter` by the unit-circle
stereographic formulas. -/
def rationalPayoffCS (q : ℚ) (k : ℕ) : ℚ × ℚ :=
  let t := rationalPayoffParameter q k
  ((1-t^2)/(1+t^2),2*t/(1+t^2))

/-- The encoded rational payoff probability, defined as the square of the sine component of
`rationalPayoffCS`. -/
def rationalPayoffValue (q : ℚ) (k : ℕ) : ℚ := (rationalPayoffCS q k).2^2

/-- The controlled real rotation on an ancilla whose two-by-two blocks use the rational
cosine-sine pair for each payoff value. -/
def rationalPayoffRotation {I : Type} [DecidableEq I] (f : I → ℚ) (k : ℕ) :
    Matrix (I×Bool) (I×Bool) ℂ := fun p q =>
  if p.1=q.1 then
    match p.2,q.2 with
    | false,false => (rationalPayoffCS (f p.1) k).1
    | false,true => -(rationalPayoffCS (f p.1) k).2
    | true,false => (rationalPayoffCS (f p.1) k).2
    | true,true => (rationalPayoffCS (f p.1) k).1
  else 0

/-- For `q` in [0, 1], rational bisection produces ordered endpoints in [0, 1] whose squares
enclose `q`, with width 2^(-k) and comparison count `k`. -/
private theorem bracket_rat (q : ℚ) (k : ℕ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    let s := rationalSqrtBracket q k;
    0 ≤ s.1 ∧ s.1 ≤ s.2.1 ∧ s.2.1 ≤ 1 ∧ s.1 ^ 2 ≤ q ∧ q ≤ s.2.1 ^ 2 ∧
      s.2.1 - s.1 = (1 : ℚ) / 2 ^ k ∧ s.2.2 = k := by
  induction k with
  | zero => simpa [rationalSqrtBracket] using And.intro hq hq1
  | succ k ih =>
    dsimp only at ih
    obtain ⟨hl, hlu, hu, hlq, hqu, hw, hn⟩ := ih
    dsimp only [rationalSqrtBracket]
    split_ifs with hm
    · refine ⟨by linarith, by linarith, hu, by nlinarith, hqu, ?_, by simp only [hn]⟩
      rw [pow_succ]
      calc
        _ = ((rationalSqrtBracket q k).2.1 - (rationalSqrtBracket q k).1) / 2 := by ring
        _ = _ := by rw [hw]; ring
    · refine ⟨hl, by linarith, by linarith, hlq, by nlinarith, ?_, by simp only [hn]⟩
      rw [pow_succ]
      calc
        _ = ((rationalSqrtBracket q k).2.1 - (rationalSqrtBracket q k).1) / 2 := by ring
        _ = _ := by rw [hw]; ring

/-- For `q` in [0, 1], the rational bracket has width 2^(-k), uses exactly `k` comparisons,
encloses sqrt(q), and approximates it at the lower endpoint within 2^(-k). -/
theorem rational_sqrt_bracket_actual_interval_and_comparisons (q : ℚ) (k : ℕ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    let s : ℚ × ℚ × ℕ := rationalSqrtBracket q k;
    (0 : ℚ) ≤ s.1 ∧ s.1 ≤ s.2.1 ∧ s.2.1 ≤ 1 ∧ s.1 ^ 2 ≤ q ∧ q ≤ s.2.1 ^ 2 ∧
      s.2.1 - s.1 = (1 : ℚ) / 2 ^ k ∧ s.2.2 = k ∧
      |(s.1 : ℝ) - Real.sqrt (q : ℝ)| ≤ (1 : ℝ) / 2 ^ k := by
  (try dsimp only)
  obtain ⟨hl, hlu, hu, hlq, hqu, hw, hn⟩ := bracket_rat q k hq hq1
  refine ⟨hl, hlu, hu, hlq, hqu, hw, hn, ?_⟩
  have hlr : (0 : ℝ) ≤ (rationalSqrtBracket q k).1 := by exact_mod_cast hl
  have hur : (0 : ℝ) ≤ (rationalSqrtBracket q k).2.1 := by exact_mod_cast hl.trans hlu
  have hlqr : ((rationalSqrtBracket q k).1 : ℝ) ^ 2 ≤ (q : ℝ) := by exact_mod_cast hlq
  have hqur : (q : ℝ) ≤ ((rationalSqrtBracket q k).2.1 : ℝ) ^ 2 := by exact_mod_cast hqu
  have hwr : ((rationalSqrtBracket q k).2.1 : ℝ) - (rationalSqrtBracket q k).1 =
      (1 : ℝ) / 2 ^ k := by
    have h := congrArg (fun x : ℚ => (x : ℝ)) hw
    push_cast at h
    exact h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ q by exact_mod_cast hq)
  have hls : ((rationalSqrtBracket q k).1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    nlinarith [Real.sqrt_nonneg (q : ℝ)]
  have hsu : Real.sqrt (q : ℝ) ≤ ((rationalSqrtBracket q k).2.1 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (q : ℝ)]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- For `q` in [0, 1], the rational stereographic payoff parameter also lies in [0, 1]. -/
private theorem payoff_parameter_interval (q : ℚ) (k : ℕ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ rationalPayoffParameter q k ∧ rationalPayoffParameter q k ≤ 1 := by
  have h := bracket_rat q k hq hq1
  have h' := bracket_rat (1 - q) k (by linarith) (by linarith)
  dsimp only [rationalPayoffParameter]
  have hd : 0 < 1 + (rationalSqrtBracket (1 - q) k).1 := by linarith [h'.1]
  exact ⟨div_nonneg h.1 hd.le, (div_le_one hd).mpr (by linarith [h.2.1, h.2.2.1, h'.1])⟩

/-- The squares of the rational cosine and sine components sum exactly to one for every input
and precision. -/
theorem rationalPayoffCS_circle (q : ℚ) (k : ℕ) :
    (rationalPayoffCS q k).1 ^ 2 + (rationalPayoffCS q k).2 ^ 2 = 1 := by
  have hd : (1 + rationalPayoffParameter q k ^ 2 : ℚ) ≠ 0 := by positivity
  dsimp [rationalPayoffCS]
  field_simp
  ring

/-- For `q` in [0, 1], both rational rotation components are nonnegative and the encoded payoff
lies in [0, 1]. -/
theorem rationalPayoffCS_probability (q : ℚ) (k : ℕ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ (rationalPayoffCS q k).1 ∧ 0 ≤ (rationalPayoffCS q k).2 ∧
      0 ≤ rationalPayoffValue q k ∧ rationalPayoffValue q k ≤ 1 := by
  obtain ⟨ht, ht1⟩ := payoff_parameter_interval q k hq hq1
  have hts : rationalPayoffParameter q k ^ 2 ≤ 1 := by nlinarith
  have hc : 0 ≤ (rationalPayoffCS q k).1 := by dsimp [rationalPayoffCS]; positivity
  have hs : 0 ≤ (rationalPayoffCS q k).2 := by dsimp [rationalPayoffCS]; positivity
  refine ⟨hc, hs, sq_nonneg _, ?_⟩
  dsimp only [rationalPayoffValue]
  nlinarith [rationalPayoffCS_circle q k, sq_nonneg (rationalPayoffCS q k).1]

/-- For bounded rational payoffs, the rational rotation equals the ideal payoff rotation for its
encoded rational probability values. -/
theorem rationalPayoffRotation_eq_payoffRotation
    {I : Type} [Fintype I] [DecidableEq I] (f : I → ℚ) (k : ℕ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    rationalPayoffRotation f k = payoffRotation (fun i => (rationalPayoffValue (f i) k : ℝ)) := by
  have hcs (i : I) : Real.sqrt (1 - (rationalPayoffValue (f i) k : ℝ)) =
      ((rationalPayoffCS (f i) k).1 : ℝ) ∧
      Real.sqrt (rationalPayoffValue (f i) k : ℝ) = ((rationalPayoffCS (f i) k).2 : ℝ) := by
    obtain ⟨hc, hs, _, _⟩ := rationalPayoffCS_probability (f i) k (hf i).1 (hf i).2
    have hcircle : ((rationalPayoffCS (f i) k).1 : ℝ) ^ 2 +
        ((rationalPayoffCS (f i) k).2 : ℝ) ^ 2 = 1 := by exact_mod_cast rationalPayoffCS_circle (f i) k
    have hval : (rationalPayoffValue (f i) k : ℝ) = ((rationalPayoffCS (f i) k).2 : ℝ) ^ 2 := by
      simp only [rationalPayoffValue, Rat.cast_pow]
    rw [hval, show 1 - ((rationalPayoffCS (f i) k).2 : ℝ) ^ 2 =
      ((rationalPayoffCS (f i) k).1 : ℝ) ^ 2 by linarith]
    exact ⟨Real.sqrt_sq (by exact_mod_cast hc), Real.sqrt_sq (by exact_mod_cast hs)⟩
  ext ⟨i, b⟩ ⟨j, c⟩
  rw [payoffRotation_apply]
  by_cases hij : i = j
  · subst j
    cases b <;> cases c <;>
      simp [rationalPayoffRotation, (hcs i).1, (hcs i).2]
  · cases b <;> cases c <;> simp [rationalPayoffRotation, hij]

/-- For parameters in [0, 1] separated by at most a nonnegative `Δ`, each stereographic
unit-circle component differs by at most 4Δ. -/
private theorem cayley_lipschitz (t u Δ : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) (hΔ : 0 ≤ Δ) (hdiff : |t - u| ≤ Δ) :
    |(1 - t ^ 2) / (1 + t ^ 2) - (1 - u ^ 2) / (1 + u ^ 2)| ≤ 4 * Δ ∧
    |2 * t / (1 + t ^ 2) - 2 * u / (1 + u ^ 2)| ≤ 4 * Δ := by
  let D := (1 + t ^ 2) * (1 + u ^ 2)
  have hD : 1 ≤ D := by
    dsimp [D]; nlinarith [sq_nonneg t, sq_nonneg u, mul_nonneg (sq_nonneg t) (sq_nonneg u)]
  have hDp : 0 < D := by linarith
  have hnt : (1 + t ^ 2) ≠ 0 := by positivity
  have hnu : (1 + u ^ 2) ≠ 0 := by positivity
  have hc : (1 - t ^ 2) / (1 + t ^ 2) - (1 - u ^ 2) / (1 + u ^ 2) =
      2 * (u - t) * (u + t) / D := by dsimp [D]; field_simp; ring
  have hs : 2 * t / (1 + t ^ 2) - 2 * u / (1 + u ^ 2) =
      2 * (t - u) * (1 - t * u) / D := by dsimp [D]; field_simp; ring
  have hsum : |u + t| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hprod : |1 - t * u| ≤ 1 := by
    have htu : t * u ≤ 1 := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  constructor
  · rw [hc, abs_div, abs_of_pos hDp, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_sub_comm]
    apply (div_le_iff₀ hDp).mpr
    calc
      _ ≤ 2 * Δ * 2 := mul_le_mul (by nlinarith) hsum (abs_nonneg _) (by positivity)
      _ ≤ 4 * Δ * D := by nlinarith
  · rw [hs, abs_div, abs_of_pos hDp, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_iff₀ hDp).mpr
    calc
      _ ≤ 2 * Δ * 1 := mul_le_mul (by nlinarith) hprod (abs_nonneg _) (by positivity)
      _ ≤ 4 * Δ * D := by nlinarith

/-- For nonnegative unit-circle coordinates `s` and `c`, the stereographic parameter s/(1 + c)
recovers `c` and `s` by the rational circle formulas. -/
private theorem sqrt_stereographic (s c : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hcircle : s ^ 2 + c ^ 2 = 1) :
    (1 - (s / (1 + c)) ^ 2) / (1 + (s / (1 + c)) ^ 2) = c ∧
      2 * (s / (1 + c)) / (1 + (s / (1 + c)) ^ 2) = s := by
  have hden : 1 + c ≠ 0 := by positivity
  have hden2 : 1 + (s / (1 + c)) ^ 2 ≠ 0 := by positivity
  constructor
  · field_simp
    nlinarith [hcircle]
  · field_simp
    nlinarith [hcircle]

/-- For `q` in [0, 1], the rational cosine and sine approximate sqrt(1 - q) and sqrt(q),
respectively, within 16/2^k. -/
theorem rationalPayoffCS_sqrt_error (q : ℚ) (k : ℕ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    |((rationalPayoffCS q k).1 : ℝ) - Real.sqrt (1 - (q : ℝ))| ≤ 16 / 2 ^ k ∧
      |((rationalPayoffCS q k).2 : ℝ) - Real.sqrt (q : ℝ)| ≤ 16 / 2 ^ k := by
  let l : ℝ := (rationalSqrtBracket q k).1
  let m : ℝ := (rationalSqrtBracket (1 - q) k).1
  let s := Real.sqrt (q : ℝ)
  let c := Real.sqrt (1 - (q : ℝ))
  let d : ℝ := 1 / 2 ^ k
  have hl := rational_sqrt_bracket_actual_interval_and_comparisons q k hq hq1
  have hm :=
      rational_sqrt_bracket_actual_interval_and_comparisons (1 - q) k (by linarith) (by linarith)
  have hl0 : 0 ≤ l := by dsimp [l]; exact_mod_cast hl.1
  have hm0 : 0 ≤ m := by dsimp [m]; exact_mod_cast hm.1
  have hld : |l - s| ≤ d := hl.2.2.2.2.2.2.2
  have hmd : |m - c| ≤ d := by simpa only [Rat.cast_sub, Rat.cast_one] using hm.2.2.2.2.2.2.2
  have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hsq : s ^ 2 = (q : ℝ) := Real.sq_sqrt hq0
  have hcq : c ^ 2 = 1 - (q : ℝ) := Real.sq_sqrt (by linarith)
  have hs1 : s ≤ 1 := by nlinarith
  have hc1 : c ≤ 1 := by nlinarith
  let t := l / (1 + m)
  let u := s / (1 + c)
  have htr : (rationalPayoffParameter q k : ℝ) = t := by
    dsimp [rationalPayoffParameter, t, l, m]
    push_cast
    rfl
  have ht : 0 ≤ t ∧ t ≤ 1 := by
    rw [← htr]
    exact_mod_cast payoff_parameter_interval q k hq hq1
  have hu : 0 ≤ u ∧ u ≤ 1 :=
    ⟨div_nonneg hs (by linarith), (div_le_one (by linarith : 0 < 1 + c)).mpr (by linarith)⟩
  let D := (1 + m) * (1 + c)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [mul_nonneg hm0 hc]
  have hDp : 0 < D := by linarith
  have hid : t - u = ((l - s) * (1 + c) + s * (c - m)) / D := by
    dsimp [t, u, D]
    field_simp
    ring
  have htu : |t - u| ≤ 4 * d := by
    rw [hid, abs_div, abs_of_pos hDp]
    apply (div_le_iff₀ hDp).mpr
    have hn : |(l - s) * (1 + c) + s * (c - m)| ≤ 3 * d := by
      calc
        _ ≤ |l - s| * |1 + c| + |s| * |c - m| := by
          simpa only [abs_mul] using abs_add_le ((l - s) * (1 + c)) (s * (c - m))
        _ ≤ d * 2 + 1 * d := add_le_add
          (mul_le_mul hld (by rw [abs_of_nonneg (by linarith)]; linarith) (abs_nonneg _) (by positivity))
          (mul_le_mul (by rw [abs_of_nonneg hs]; exact hs1) (by rwa [abs_sub_comm])
            (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    have hd : 0 ≤ d := by dsimp [d]; positivity
    nlinarith
  have hcs := sqrt_stereographic s c hs hc (by linarith)
  have he := cayley_lipschitz t u (4 * d) ht.1 ht.2 hu.1 hu.2 (by dsimp [d]; positivity) htu
  rw [hcs.1, hcs.2] at he
  have ha : ((rationalPayoffCS q k).1 : ℝ) = (1 - t ^ 2) / (1 + t ^ 2) := by
    dsimp [rationalPayoffCS]
    push_cast
    rw [htr]
  have hb : ((rationalPayoffCS q k).2 : ℝ) = 2 * t / (1 + t ^ 2) := by
    dsimp [rationalPayoffCS]
    push_cast
    rw [htr]
  rw [ha, hb]
  rw [show 4 * (4 * d) = 16 / 2 ^ k by dsimp [d]; ring] at he
  exact he

/-- For `q` in [0, 1], the encoded rational probability differs from `q` by at most 64/2^k. -/
theorem rationalPayoffValue_error (q : ℚ) (k : ℕ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    |(rationalPayoffValue q k : ℝ) - (q : ℝ)| ≤ 64 / 2 ^ k := by
  let b : ℝ := (rationalPayoffCS q k).2
  let s := Real.sqrt (q : ℝ)
  have hp := rationalPayoffCS_probability q k hq hq1
  have hb : 0 ≤ b := by dsimp [b]; exact_mod_cast hp.2.1
  have hb2 : b ^ 2 ≤ 1 := by
    dsimp [b]
    have h := hp.2.2.2
    dsimp only [rationalPayoffValue] at h
    exact_mod_cast h
  have hs2 : s ^ 2 = (q : ℝ) := Real.sq_sqrt (by exact_mod_cast hq)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := by
    have h : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    nlinarith
  have hbs : |b + s| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; nlinarith
  have he := (rationalPayoffCS_sqrt_error q k hq hq1).2
  have hv : (rationalPayoffValue q k : ℝ) - (q : ℝ) = (b - s) * (b + s) := by
    dsimp only [rationalPayoffValue]
    push_cast
    dsimp [b, s] at *
    nlinarith
  rw [hv, abs_mul]
  calc
    _ ≤ (16 / 2 ^ k) * 2 := mul_le_mul he hbs (abs_nonneg _) (by positivity)
    _ ≤ 64 / 2 ^ k := by
      rw [show (16 : ℝ) / 2 ^ k * 2 = 32 / 2 ^ k by ring]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- For rational payoffs in [0, 1], the operator norm distance between the rational and ideal
payoff rotations is at most 32/2^k. -/
theorem rationalPayoffRotation_error {I : Type} [Fintype I] [DecidableEq I]
    (f : I → ℚ) (k : ℕ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    ‖rationalPayoffRotation f k - payoffRotation (fun i => (f i : ℝ))‖ ≤ 32 / 2 ^ k := by
  let dc : I → ℝ := fun i => ((rationalPayoffCS (f i) k).1 : ℝ) - Real.sqrt (1 - (f i : ℝ))
  let ds : I → ℝ := fun i => ((rationalPayoffCS (f i) k).2 : ℝ) - Real.sqrt (f i : ℝ)
  let C : Matrix (I × Bool) (I × Bool) ℂ := Matrix.diagonal (fun p => (dc p.1 : ℂ))
  let S : Matrix (I × Bool) (I × Bool) ℂ :=
    Matrix.diagonal (fun p => ((if p.2 then ds p.1 else -ds p.1 : ℝ) : ℂ))
  let X : Matrix (I × Bool) (I × Bool) ℂ := TensorGate (1 : Matrix I I ℂ) PauliX
  have herr : rationalPayoffRotation f k - payoffRotation (fun i => (f i : ℝ)) = C + S * X := by
    ext ⟨i, b⟩ ⟨j, c⟩
    simp only [Matrix.sub_apply, Matrix.add_apply, S, Matrix.diagonal_mul, X,
      payoffRotation_apply]
    by_cases hij : i = j
    · subst j
      cases b <;> cases c <;>
        simp [C, dc, ds, rationalPayoffRotation, TensorGate,
          PauliX, permMatrix, Complex.ofReal_sub, Complex.ofReal_ratCast]
      all_goals ring
    · cases b <;> cases c <;>
        simp [C, rationalPayoffRotation, TensorGate, hij]
  have hC : ‖C‖ ≤ 16 / 2 ^ k := by
    change ‖Matrix.diagonal (fun p : I × Bool => (dc p.1 : ℂ))‖ ≤ _
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (rationalPayoffCS_sqrt_error (f p.1) k (hf p.1).1 (hf p.1).2).1
  have hS : ‖S‖ ≤ 16 / 2 ^ k := by
    change ‖Matrix.diagonal (fun p : I × Bool => ((if p.2 then ds p.1 else -ds p.1 : ℝ) : ℂ))‖ ≤ _
    rw [Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
    intro p
    rw [Complex.norm_real, Real.norm_eq_abs]
    cases p.2 <;> simp only [Bool.false_eq_true, if_false, if_true, abs_neg]
    all_goals exact (rationalPayoffCS_sqrt_error (f p.1) k (hf p.1).1 (hf p.1).2).2
  have hX : ‖X‖ ≤ 1 := l2_norm_unitary_le_one (tensorGate_unitary (by simp) pauliX_unitary)
  rw [herr]
  calc
    _ ≤ ‖C‖ + ‖S * X‖ := norm_add_le _ _
    _ ≤ 16 / 2 ^ k + (16 / 2 ^ k) * 1 := add_le_add hC
      ((norm_mul_le _ _).trans (mul_le_mul hS hX (norm_nonneg X) (by positivity)))
    _ = _ := by ring

/-- For bounded rational payoffs, the rational rotation is unitary, its encoded probabilities
lie in [0, 1] with error at most 64/2^k, and its operator norm error is at most 32/2^k. This
supports the payoff encoding of [Montanaro2015, Algorithm 1][Montanaro2015]. -/
theorem rational_payoff_unitary_value_and_operator_error
    (I : Type) [Fintype I] [DecidableEq I] (f : I → ℚ) (k : ℕ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    rationalPayoffRotation f k ∈ Matrix.unitaryGroup (I × Bool) ℂ ∧
      (∀ i, 0 ≤ rationalPayoffValue (f i) k ∧ rationalPayoffValue (f i) k ≤ 1 ∧
        |(rationalPayoffValue (f i) k : ℝ) - (f i : ℝ)| ≤ 64 / 2 ^ k) ∧
      ‖rationalPayoffRotation f k - payoffRotation (fun i => (f i : ℝ))‖ ≤ 32 / 2 ^ k := by
  refine ⟨?_, ?_, rationalPayoffRotation_error f k hf⟩
  · rw [rationalPayoffRotation_eq_payoffRotation f k hf]
    apply payoffRotation_mem_unitaryGroup
    intro i
    have hp := (rationalPayoffCS_probability (f i) k (hf i).1 (hf i).2).2.2
    exact ⟨by exact_mod_cast hp.1, by exact_mod_cast hp.2⟩
  · intro i
    have hp := (rationalPayoffCS_probability (f i) k (hf i).1 (hf i).2).2.2
    exact ⟨hp.1, hp.2, rationalPayoffValue_error (f i) k (hf i).1 (hf i).2⟩

end Qatlib.Concepts.MonteCarloMean.PayoffRotation
