/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAOABddOcc14.MainResults.StateModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


/-! # Random signs, scalar optimization and finite tail arithmetic
These independent closed members do not use the admitted mean/variance claims.
The Markov and tail lemmas also hold for arbitrary nonnegative weights.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QAOABddOcc14.MainResults
open scoped BigOperators
open Qatlib.Papers.QAOABddOcc14.MainResults

/-- The random instance attached to a fixed triple collection `T` and a choice
`ε : T → Bool` of equation signs (paper (46): each `d_abc` is `±1`).  Triples
outside `T` carry no equation. -/
def ofAssign {n : ℕ} (T : Finset (Triple n)) (ε : T → Bool) : E3Instance n where
  d p := if h : p ∈ T then (if ε ⟨p, h⟩ then 1 else -1) else 0
  dval p := by
    by_cases h : p ∈ T
    · simp only [dite_eq_left h]; split <;> simp
    · simp only [dite_eq_right h]; simp

/-- `m = |T|` equations are present in every realization. -/
theorem ofAssign_numEquations {n : ℕ} (T : Finset (Triple n)) (ε : T → Bool) :
    (ofAssign T ε).numEquations = T.card := by
  unfold E3Instance.numEquations
  have h : (Finset.univ.filter (fun p => (ofAssign T ε).d p ≠ 0)) = T := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hp : p ∈ T
    · simp only [ofAssign, dite_eq_left hp]
      split <;> simp [hp]
    · simp only [ofAssign, dite_eq_right hp, ne_eq, not_true_eq_false]
      simp [hp]
  rw [h]

/-- The uniform weight `2^{-|T|}` of one sign assignment. -/
def assignWeight {n : ℕ} (T : Finset (Triple n)) : ℝ := ((2 : ℝ) ^ T.card)⁻¹

/-- Expected QAOA expectation over the `2^{|T|}` random instances of (46). -/
def meanExp {n : ℕ} (T : Finset (Triple n)) (γ β : ℝ) : ℝ :=
  ∑ ε : T → Bool, assignWeight T * qaoaExp (ofAssign T ε) γ β

/-- Variance of the QAOA expectation over the random instances of (46). -/
def varExp {n : ℕ} (T : Finset (Triple n)) (γ β : ℝ) : ℝ :=
  ∑ ε : T → Bool, assignWeight T * (qaoaExp (ofAssign T ε) γ β - meanExp T γ β) ^ 2

/-- **Source (52)–(53): the one-variable optimization.**  For `g ≥ 0`,
`g · exp(−(3/2)g²) ≤ 1/√(3e)`, with equality at `g = 1/√3`; this is the step from
(51)-(52) to (53).

Proof: with `u = √3·g` the claim is `u e^{−u²/2} ≤ e^{−1/2}`, which follows by
taking logarithms from `log u ≤ u − 1 ≤ (u² − 1)/2`. -/
theorem gamma_optimization (g : ℝ) (hg : 0 ≤ g) :
    g * Real.exp (-(3 / 2) * g ^ 2) ≤ 1 / Real.sqrt (3 * Real.exp 1) := by
  rcases eq_or_lt_of_le hg with hg0 | hgpos
  · rw [← hg0]; simp
  have key : ∀ u : ℝ, 0 < u → u * Real.exp (-(u ^ 2) / 2) ≤ Real.exp (-(1 / 2)) := by
    intro u hu
    have hlog : Real.log u ≤ (u ^ 2 - 1) / 2 := by
      have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hu
      have h2 : u - 1 ≤ (u ^ 2 - 1) / 2 := by nlinarith [sq_nonneg (u - 1)]
      linarith
    have hexp : u ≤ Real.exp ((u ^ 2 - 1) / 2) := by
      calc u = Real.exp (Real.log u) := (Real.exp_log hu).symm
        _ ≤ Real.exp ((u ^ 2 - 1) / 2) := (Real.exp_le_exp).mpr hlog
    have hEpos : (0 : ℝ) ≤ Real.exp (-(u ^ 2) / 2) := (Real.exp_pos _).le
    calc u * Real.exp (-(u ^ 2) / 2)
        ≤ Real.exp ((u ^ 2 - 1) / 2) * Real.exp (-(u ^ 2) / 2) :=
          mul_le_mul_of_nonneg_right hexp hEpos
      _ = Real.exp ((u ^ 2 - 1) / 2 + -(u ^ 2) / 2) := (Real.exp_add _ _).symm
      _ = Real.exp (-(1 / 2)) := by
          congr 1
          ring
  set u : ℝ := Real.sqrt 3 * g with hu
  have hpos3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hu_pos : 0 < u := by rw [hu]; positivity
  have hkey := key u hu_pos
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have harg : -(3 / 2) * g ^ 2 = -(u ^ 2) / 2 := by
    rw [hu]; nlinarith [hsqrt3]
  have hrhs : (1 / Real.sqrt (3 * Real.exp 1)) =
      (1 / Real.sqrt 3) * Real.exp (-(1 / 2)) := by
    rw [Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (Real.exp 1) = Real.exp (1 / 2) from by
      rw [← Real.exp_half 1]]
    rw [Real.exp_neg]
    field_simp
  have hgsqrt : g = u / Real.sqrt 3 := by
    rw [hu]; field_simp
  rw [harg, hrhs, hgsqrt]
  calc u / Real.sqrt 3 * Real.exp (-(u ^ 2) / 2)
      = (u * Real.exp (-(u ^ 2) / 2)) / Real.sqrt 3 := by ring
    _ ≤ Real.exp (-(1 / 2)) / Real.sqrt 3 :=
        div_le_div_of_nonneg_right hkey hpos3.le
    _ = 1 / Real.sqrt 3 * Real.exp (-(1 / 2)) := by ring

/-- The uniform weights `2^{-|T|}` over the `2^{|T|}` sign assignments sum to one. -/
theorem assignWeight_sum {n : ℕ} (T : Finset (Triple n)) :
    (∑ _ε : T → Bool, assignWeight T) = 1 := by
  unfold assignWeight
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_coe, nsmul_eq_mul]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

/-- Finite Markov inequality for a probability weight vector. -/
theorem finite_markov {ι : Type*} [Fintype ι] (w X : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hX : ∀ i, 0 ≤ X i) (t : ℝ) (ht : 0 < t) :
    ∑ i, w i * (if t ≤ X i then (1 : ℝ) else 0) ≤ (∑ i, w i * X i) / t := by
  have hkey : ∀ i, t * (if t ≤ X i then (1 : ℝ) else 0) ≤ X i := by
    intro i
    by_cases h : t ≤ X i
    · simp [h]
    · simp [h]; exact hX i
  have hmul : t * ∑ i, w i * (if t ≤ X i then (1 : ℝ) else 0) ≤ ∑ i, w i * X i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc t * (w i * (if t ≤ X i then (1 : ℝ) else 0))
        = w i * (t * (if t ≤ X i then (1 : ℝ) else 0)) := by ring
      _ ≤ w i * X i := by nlinarith [hw i, hkey i]
  rw [le_div_iff₀ ht]
  linarith [hmul]

/-- **Chebyshev's inequality** for a finite probability law, in the form used in
§III: the mass of the event `X < μ − t` is at most `Var/t²`. -/
theorem chebyshev_tail {ι : Type*} [Fintype ι] (w X : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (μ : ℝ) (t : ℝ) (ht : 0 < t) :
    ∑ i, w i * (if X i < μ - t then (1 : ℝ) else 0) ≤
      (∑ i, w i * (X i - μ) ^ 2) / t ^ 2 := by
  have hmarkov := finite_markov w (fun i => (X i - μ) ^ 2) hw (fun i => sq_nonneg _) (t ^ 2)
    (by positivity)
  have hset : ∑ i, w i * (if X i < μ - t then (1 : ℝ) else 0) ≤
      ∑ i, w i * (if t ^ 2 ≤ (X i - μ) ^ 2 then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro i _
    have hw' := hw i
    by_cases h : X i < μ - t
    · have hge : t ^ 2 ≤ (X i - μ) ^ 2 := by
        have : X i - μ < -t := by linarith
        nlinarith
      simp [h, hge]
    · simp [h]; positivity
  linarith [hset, hmarkov]

end Qatlib.Papers.QAOABddOcc14.MainResults
