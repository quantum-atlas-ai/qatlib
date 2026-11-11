/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZeroSumGames19.MainResults.GameModel.SourceGameModel
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.Harmonic.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# ZeroSumGames19 — Lemma 1 (multiplicative-weights convergence)

Fixed source: arXiv:1904.03180v1, Lemma 1, pp.3–5.

Paper statement (p.3): let `δ ∈ (0,1/3)`. With probability at least `1−δ`
Algorithm 1 produces, for all `t`, intermediate solutions `x⁽ᵗ⁾/‖x⁽ᵗ⁾‖₁` and
`y⁽ᵗ⁾/‖y⁽ᵗ⁾‖₁` that are `ε′`-optimal with
`ε′ = (2/√t)·(3 ln t + ln(nm) + ln(1/δ) + 2)`.
If instead `η⁽ᵗ⁾ := ε/4`, then with probability at least `1−δ` the solutions are
`ε`-optimal after `T = ⌈16 ln(nm/δ)/ε²⌉` iterations.

What is proved here:

* `exp_add_bound` — the scalar inequality `eˣ ≤ 1 + x + (3/4)x²` for `x ∈ [-1,1]`
  used on p.4 (`e^{η(A_ia−A_bj)} ≤ 1 + η(A_ia−A_bj) + (3/4)η²`); proved from
  Mathlib's `Real.exp_bound`.
* `potential_bound_yields_eq3` — the deterministic core of the proof (p.4–5,
  equation (3)): a multiplicative bound on the potential `Φ = (∑P)(∑Q)` forces
  `(Ay)_i − (Aᵀx)_j ≤ ln(nm/δ) + 3∑η²`; proved.
* `source_lemma1_eq3` — the probability-`1−δ` event of (3), reduced to the paper's
  Markov/union-bound step (`hmarkov`); proved from that step by
  `epsOptimal_of_normalized`.
* `source_lemma1_fixed_accuracy` — the `η = ε/4`, `T = ⌈16 ln(nm/δ)/ε²⌉`
  conclusion, proved from the same Markov event using
  `fixed_accuracy_rounds_suffices`.
* `source_lemma1_streaming` — the `ε′` form of Lemma 1, proved from
  `source_lemma1_eq3` by the two running-step-size bounds `stepSum_lower`
  (`∑η ≥ √t/2`, telescoping `√(τ+1) − √τ ≤ 1/√(τ+1)`) and `stepSqSum_upper`
  (`∑η² ≤ (ln t + 1)/4`, Mathlib's `harmonic_le_one_add_log`), plus the
  `epsPrime_ge_generic` comparison.  The weight hypothesis is pointwise over
  trajectories (Algorithm 1's weight dynamics are deterministic functions of
  the sampled actions), matching `source_lemma1_eq3`.

Boundary: the paper's sampling process (`a ∼ p⁽ᵗ⁾`, `b ∼ q⁽ᵗ⁾`) and the
expectation/Markov computation `E[Φ⁽ᵗ⁾] ≤ nm·e^{3∑η²}` are not modelled; the
resulting high-probability potential bound is taken as the explicit hypothesis
`hmarkov`, and everything downstream of it is proved.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ZeroSumGames19.MainResults.MatrixWeights

open Finset BigOperators MeasureTheory
open Qatlib.Papers.ZeroSumGames19.MainResults.GameModel

/-! ## The scalar exponential bound (p.4) -/

/-- Paper p.4: for all `x ∈ [-1,1]`, `eˣ ≤ 1 + x + (3/4)x²`.
    This is the inequality applied to `x = η(A_ia − A_bj)`, where `|A_ia − A_bj| ≤ 2`
    and `η ≤ 1/2`, so `|x| ≤ 1`. -/
theorem exp_add_bound {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    Real.exp x ≤ 1 + x + (3 / 4) * x ^ 2 := by
  have habs : |x| ≤ 1 := abs_le.mpr ⟨hx1, hx2⟩
  have h := Real.exp_bound habs (n := 3) (by norm_num)
  have hsum_eq : (∑ m ∈ Finset.range 3, x ^ m / m.factorial) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  have hupper : Real.exp x - (1 + x + x ^ 2 / 2) ≤ (2 / 9) * |x| ^ 3 := by
    have h' := (abs_le.mp h).2
    rw [hsum_eq] at h'
    norm_num at h'
    linarith
  have hx3 : |x| ^ 3 ≤ |x| ^ 2 := by
    calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
      _ ≤ |x| ^ 2 * 1 := by gcongr
      _ = |x| ^ 2 := by ring
  have hfin : (2 / 9 : ℝ) * |x| ^ 3 ≤ (1 / 4) * x ^ 2 := by
    have h2 : (2 / 9 : ℝ) * |x| ^ 2 ≤ (1 / 4) * x ^ 2 := by
      rw [sq_abs]
      nlinarith
    have h3 : (2 / 9 : ℝ) * |x| ^ 3 ≤ (2 / 9 : ℝ) * |x| ^ 2 := by
      nlinarith [hx3, abs_nonneg x]
    linarith
  nlinarith [hupper, hfin]

/-! ## The deterministic potential ⇒ equation (3) step (p.4–5) -/

/-- Proof of Lemma 1, p.4–5, equation (3), deterministic part. With
    `P_j = e^{−(Aᵀx)_j}`, `Q_i = e^{(Ay)_i}` and potential
    `Φ = (∑_j P_j)(∑_i Q_i)`, the bound `Φ ≤ (nm/δ)e^{3S}` gives, for every `i,j`,
    `(Ay)_i − (Aᵀx)_j ≤ ln(nm/δ) + 3S`. -/
theorem potential_bound_yields_eq3
    {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) (y : Fin m → ℝ)
    (P : Fin m → ℝ) (Q : Fin n → ℝ) {δ S : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hδ : 0 < δ) (hS : 0 ≤ S)
    (hP : ∀ j, P j = Real.exp (-(colPayoff A x j)))
    (hQ : ∀ i, Q i = Real.exp (rowPayoff A y i))
    (hΦ : (∑ j, P j) * (∑ i, Q i) ≤ ((n : ℝ) * m / δ) * Real.exp (3 * S)) :
    ∀ i j, rowPayoff A y i - colPayoff A x j ≤ Real.log ((n : ℝ) * m / δ) + 3 * S := by
  have hPpos : ∀ j, 0 < P j := fun j => by rw [hP j]; exact Real.exp_pos _
  have hQpos : ∀ i, 0 < Q i := fun i => by rw [hQ i]; exact Real.exp_pos _
  have hsumP_nonneg : 0 ≤ ∑ j, P j := Finset.sum_nonneg (fun j _ => le_of_lt (hPpos j))
  have hsumQ_nonneg : 0 ≤ ∑ i, Q i := Finset.sum_nonneg (fun i _ => le_of_lt (hQpos i))
  have hsq_pos : (0 : ℝ) < (n : ℝ) * m / δ := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    exact div_pos (mul_pos hn' hm') hδ
  intro i j
  have hP_le : P j ≤ ∑ j', P j' := by
    apply Finset.single_le_sum (f := P) (fun j' _ => le_of_lt (hPpos j'))
    exact Finset.mem_univ j
  have hQ_le : Q i ≤ ∑ i', Q i' := by
    apply Finset.single_le_sum (f := Q) (fun i' _ => le_of_lt (hQpos i'))
    exact Finset.mem_univ i
  have hprod_le : P j * Q i ≤ (∑ j', P j') * (∑ i', Q i') :=
    mul_le_mul hP_le hQ_le (le_of_lt (hQpos i)) hsumP_nonneg
  have hexp_eq : P j * Q i = Real.exp (rowPayoff A y i - colPayoff A x j) := by
    rw [hP j, hQ i, ← Real.exp_add]
    congr 1
    ring
  have hchain : Real.exp (rowPayoff A y i - colPayoff A x j)
      ≤ Real.exp (Real.log ((n : ℝ) * m / δ) + 3 * S) := by
    rw [← hexp_eq]
    calc P j * Q i ≤ (∑ j', P j') * (∑ i', Q i') := hprod_le
      _ ≤ ((n : ℝ) * m / δ) * Real.exp (3 * S) := hΦ
      _ = Real.exp (Real.log ((n : ℝ) * m / δ) + 3 * S) := by
          rw [Real.exp_add, Real.exp_log hsq_pos]
  exact Real.exp_le_exp.mp hchain

/-! ## The stopping rule `T = ⌈16 ln(nm/δ)/ε²⌉` (p.3, second half) -/

/-- Lemma 1, p.5, fixed-accuracy stopping rule: with `η = ε/4`, for every
    `t ≥ T = ⌈16 ln(nm/δ)/ε²⌉` the generic bound (3)
    `(ln(nm/δ) + 3tη²)/(tη)` is at most `ε`. -/
theorem fixed_accuracy_rounds_suffices
    {n m t : ℕ} {ε δ : ℝ} (hn : 0 < n) (hm : 0 < m)
    (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ht : fixedAccuracyRounds n m ε δ ≤ t) (ht1 : 1 ≤ t) :
    (Real.log ((n : ℝ) * m / δ) + 3 * (t : ℝ) * (ε / 4) ^ 2)
        / ((t : ℝ) * (ε / 4)) ≤ ε := by
  have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm_prod : (1 : ℝ) ≤ (n : ℝ) * m := by nlinarith
  have hnm : (1 : ℝ) ≤ (n : ℝ) * m / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith
  have hL : 0 ≤ Real.log ((n : ℝ) * m / δ) := Real.log_nonneg hnm
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
  have hkey : (16 : ℝ) * Real.log ((n : ℝ) * m / δ) / ε ^ 2 ≤ (t : ℝ) :=
    Nat.ceil_le.mp ht
  have hkey' : (16 : ℝ) * Real.log ((n : ℝ) * m / δ) ≤ (t : ℝ) * ε ^ 2 :=
    (div_le_iff₀ hε2).mp hkey
  have hden : (0 : ℝ) < (t : ℝ) * (ε / 4) := by positivity
  have h1 : Real.log ((n : ℝ) * m / δ) / ((t : ℝ) * (ε / 4)) ≤ ε / 4 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have h2 : 3 * (t : ℝ) * (ε / 4) ^ 2 / ((t : ℝ) * (ε / 4)) = 3 * ε / 4 := by
    field_simp
  rw [add_div, h2]
  linarith

/-! ## The probability-`1−δ` statement of equation (3) -/

/-- Lemma 1, p.3–5, equation (3) with the paper's running step size
    `η⁽τ⁾ = 1/(2√τ)`. Given the paper's Markov/union-bound event `hmarkov`
    (`Φ⁽ᵗ⁾ ≤ (nm/δ)e^{3∑η²}` with probability at least `1−δ`), the normalised
    intermediate solutions satisfy display (3) with probability at least `1−δ`.

    The generic error is `(ln(nm/δ) + 3∑_{τ≤t}η⁽τ⁾²) / ∑_{τ≤t}η⁽τ⁾`, which the
    paper then specialises to `ε′(t)` in `source_lemma1_streaming`. -/
theorem source_lemma1_eq3
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : PayoffMatrix n m)
    {δ : ℝ} (hδ0 : 0 < δ)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℕ → Fin n → ℝ) (Y : Ω → ℕ → Fin m → ℝ)
    (hweights : ∀ ω t, 1 ≤ t →
      (∑ i, X ω t i) = ∑ τ ∈ Finset.range t, stepSize (τ + 1) ∧
      (∑ j, Y ω t j) = ∑ τ ∈ Finset.range t, stepSize (τ + 1))
    (hmarkov : 1 - δ ≤ μ.real {ω | ∀ t, 1 ≤ t →
      potential A (X ω t) (Y ω t) ≤
        ((n : ℝ) * m / δ) * Real.exp (3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2)}) :
    1 - δ ≤ μ.real {ω | ∀ t, 1 ≤ t →
      EpsOptimal A (fun i => X ω t i / (∑ i, X ω t i))
        (fun j => Y ω t j / (∑ j, Y ω t j))
        ((Real.log ((n : ℝ) * m / δ)
          + 3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2)
          / ∑ τ ∈ Finset.range t, stepSize (τ + 1))} := by
  refine le_trans hmarkov (measureReal_mono ?_)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  intro t ht
  set S1 : ℝ := ∑ τ ∈ Finset.range t, stepSize (τ + 1) with hS1def
  set S2 : ℝ := ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2 with hS2def
  have hS1 : S1 = ∑ τ ∈ Finset.range t, stepSize (τ + 1) := hS1def
  have hw := hweights ω t ht
  have hSpos : 0 < S1 := by
    have hlt : 0 < t := lt_of_lt_of_le (by norm_num : 0 < 1) ht
    rw [hS1def]
    apply Finset.sum_pos
    · intro τ _
      unfold stepSize
      positivity
    · exact ⟨0, Finset.mem_range.mpr hlt⟩
  have hS2nonneg : 0 ≤ S2 := by
    rw [hS2def]
    apply Finset.sum_nonneg
    intro τ _
    positivity
  have hbound := potential_bound_yields_eq3 A (X ω t) (Y ω t)
    (fun j => Real.exp (-(colPayoff A (X ω t) j)))
    (fun i => Real.exp (rowPayoff A (Y ω t) i))
    hn hm hδ0 hS2nonneg
    (fun j => rfl) (fun i => rfl) (hω t ht)
  have hmain : EpsOptimal A (fun i => X ω t i / S1) (fun j => Y ω t j / S1)
      ((Real.log ((n : ℝ) * m / δ) + 3 * S2) / S1) := by
    apply epsOptimal_of_normalized A (X ω t) (Y ω t) hSpos
    intro i j
    have h := hbound i j
    have hmul : ((Real.log ((n : ℝ) * m / δ) + 3 * S2) / S1) * S1
        = Real.log ((n : ℝ) * m / δ) + 3 * S2 := by
      field_simp
    rw [hmul]
    exact h
  simpa only [hw.1, hw.2] using hmain

/-! ## The `ε′` (streaming) form of Lemma 1 -/

/-- `EpsOptimal` is monotone in the accuracy parameter. -/
theorem epsOptimal_mono {n m : ℕ} (A : PayoffMatrix n m) (x : Fin n → ℝ) (y : Fin m → ℝ)
    {e e' : ℝ} (h : EpsOptimal A x y e) (hle : e ≤ e') :
    EpsOptimal A x y e' := fun i j => (h i j).trans hle

/-- Rationalisation identity for consecutive square roots:
    `√(τ+1) − √τ = 1/(√(τ+1) + √τ)` (used for the `∑η ≥ √t/2` bound). -/
theorem sqrt_succ_sub (τ : ℕ) :
    (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))
      = 1 / (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ)) := by
  have hring : (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))
      * (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ)) = 1 := by
    have hexpand : (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))
        * (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ))
        = (Real.sqrt ((τ : ℝ) + 1)) ^ 2 - (Real.sqrt (τ : ℝ)) ^ 2 := by ring
    rw [hexpand, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hne : (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ)) ≠ 0 := by positivity
  calc (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))
      = ((Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ)) * (Real.sqrt ((τ : ℝ) + 1)
          + Real.sqrt (τ : ℝ))) * (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ))⁻¹ := by
        field_simp
    _ = 1 * (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ))⁻¹ := by rw [hring]
    _ = 1 / (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ)) := by rw [one_div, one_mul]

/-- Telescoping: `∑_{τ<t} (√(τ+1) − √τ) = √t`. -/
theorem sqrt_telescope (t : ℕ) :
    (∑ τ ∈ Finset.range t, (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))) = Real.sqrt t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Paper p.5, lower bound: the running step sizes satisfy `∑_{τ<t} η⁽τ⁾ ≥ √t/2`,
    by rationalising `√(τ+1) − √τ = 1/(√(τ+1)+√τ) ≤ 1/√(τ+1)` and telescoping. -/
theorem stepSum_lower (t : ℕ) :
    Real.sqrt t / 2 ≤ ∑ τ ∈ Finset.range t, stepSize (τ + 1) := by
  have hterm : ∀ τ ∈ Finset.range t,
      (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ)) / 2 ≤ stepSize (τ + 1) := by
    intro τ _
    push_cast
    have hkey : (1 : ℝ) / (Real.sqrt ((τ : ℝ) + 1) + Real.sqrt (τ : ℝ))
        ≤ 1 / Real.sqrt ((τ : ℝ) + 1) := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt ((τ : ℝ) + 1)
              + Real.sqrt (τ : ℝ)) (by positivity : (0 : ℝ) < Real.sqrt ((τ : ℝ) + 1))]
      nlinarith [Real.sqrt_nonneg ((τ : ℝ) + 1), Real.sqrt_nonneg (τ : ℝ)]
    have hchain : (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))
        ≤ 1 / Real.sqrt ((τ : ℝ) + 1) := (sqrt_succ_sub τ).le.trans hkey
    unfold stepSize
    push_cast
    rw [show ((1 : ℝ) / (2 * Real.sqrt ((τ : ℝ) + 1)))
          = ((1 : ℝ) / Real.sqrt ((τ : ℝ) + 1)) / 2 from by ring,
      div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_right hchain (by norm_num)
  calc Real.sqrt t / 2
      = (∑ τ ∈ Finset.range t, (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ))) / 2 := by
        rw [sqrt_telescope]
    _ = ∑ τ ∈ Finset.range t,
        (Real.sqrt ((τ : ℝ) + 1) - Real.sqrt (τ : ℝ)) / 2 := by rw [Finset.sum_div]
    _ ≤ ∑ τ ∈ Finset.range t, stepSize (τ + 1) := Finset.sum_le_sum hterm

/-- The real-coerced harmonic sum is the sum of reciprocal successors. -/
theorem harmonic_cast (t : ℕ) :
    ((harmonic t : ℚ) : ℝ) = ∑ τ ∈ Finset.range t, 1 / ((τ : ℝ) + 1) := by
  unfold harmonic
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  push_cast
  field_simp

/-- Paper p.5, upper bound: the squared running step sizes satisfy
    `∑_{τ<t} (η⁽τ⁾)² ≤ (ln t + 1)/4`, via Mathlib's `harmonic_le_one_add_log`. -/
theorem stepSqSum_upper (t : ℕ) :
    (∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2) ≤ (Real.log t + 1) / 4 := by
  have hterm : ∀ τ : ℕ,
      (stepSize (τ + 1)) ^ 2 = (1 / 4) * (1 / ((τ : ℝ) + 1)) := by
    intro τ
    have hs : (Real.sqrt ((τ : ℝ) + 1)) ^ 2 = ((τ : ℝ) + 1) := Real.sq_sqrt (by positivity)
    have h2 : (2 * Real.sqrt ((τ : ℝ) + 1)) ^ 2 = 4 * ((τ : ℝ) + 1) := by
      rw [mul_pow, hs]
      norm_num
    calc (stepSize (τ + 1)) ^ 2
        = (1 / (2 * Real.sqrt ((τ : ℝ) + 1))) ^ 2 := by unfold stepSize; push_cast; rfl
      _ = 1 / (2 * Real.sqrt ((τ : ℝ) + 1)) ^ 2 := by rw [div_pow, one_pow]
      _ = 1 / (4 * ((τ : ℝ) + 1)) := by rw [h2]
      _ = (1 / 4) * (1 / ((τ : ℝ) + 1)) := by field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← harmonic_cast]
  have hle : ((harmonic t : ℚ) : ℝ) ≤ 1 + Real.log t := by
    exact_mod_cast harmonic_le_one_add_log t
  linarith

/-- The generic error of equation (3) at the running step size is at most
    Lemma 1's `ε′(t) = (2/√t)(3 ln t + ln(nm) + ln(1/δ) + 2)`. -/
theorem epsPrime_ge_generic {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3) {t : ℕ} (ht : 1 ≤ t) :
    ((Real.log ((n : ℝ) * m / δ)
        + 3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2)
      / ∑ τ ∈ Finset.range t, stepSize (τ + 1)) ≤ epsPrime n m δ t := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm : (1 : ℝ) < (n : ℝ) * m / δ := by
    rw [lt_div_iff₀ hδ0]
    nlinarith
  have hLpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ) := Real.log_nonneg (le_of_lt hnm)
  have htpos : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hlnt : (0 : ℝ) ≤ Real.log t := Real.log_nonneg htpos
  have hS2 : (0 : ℝ) ≤ ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2 :=
    Finset.sum_nonneg (fun τ _ => by positivity)
  have hNpos : (0 : ℝ) ≤ Real.log ((n : ℝ) * m / δ)
      + 3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2 := by
    have := stepSqSum_upper t
    linarith
  have hS1pos : (0 : ℝ) < ∑ τ ∈ Finset.range t, stepSize (τ + 1) :=
    lt_of_lt_of_le (by positivity) (stepSum_lower t)
  have hNle : Real.log ((n : ℝ) * m / δ) + 3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2
      ≤ Real.log ((n : ℝ) * m / δ) + 3 * ((Real.log t + 1) / 4) := by
    have h2 := stepSqSum_upper t
    nlinarith
  have hsplit : Real.log ((n : ℝ) * m / δ)
      = Real.log ((n : ℝ) * m) + Real.log (1 / δ) := by
    have hδne : (δ : ℝ) ≠ 0 := ne_of_gt hδ0
    rw [Real.log_div (by nlinarith : ((n : ℝ) * m) ≠ 0) hδne, one_div,
      Real.log_inv]
    ring
  have hfinal : Real.log ((n : ℝ) * m / δ) + 3 * ((Real.log t + 1) / 4)
      ≤ 3 * Real.log t + Real.log ((n : ℝ) * m) + Real.log (1 / δ) + 2 := by
    rw [hsplit]
    nlinarith
  have hsqrt2pos : (0 : ℝ) < Real.sqrt t / 2 := by positivity
  have hstep : ((Real.log ((n : ℝ) * m / δ) + 3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2)
      / ∑ τ ∈ Finset.range t, stepSize (τ + 1))
      ≤ (Real.log ((n : ℝ) * m / δ) + 3 * ((Real.log t + 1) / 4)) / (Real.sqrt t / 2) := by
    rw [div_le_div_iff₀ hS1pos hsqrt2pos]
    have h1 := mul_le_mul_of_nonneg_left (stepSum_lower t) hNpos
    have h2 := mul_le_mul_of_nonneg_right hNle hS1pos.le
    exact h1.trans h2
  calc ((Real.log ((n : ℝ) * m / δ) + 3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2)
        / ∑ τ ∈ Finset.range t, stepSize (τ + 1))
      ≤ (Real.log ((n : ℝ) * m / δ) + 3 * ((Real.log t + 1) / 4)) / (Real.sqrt t / 2) := hstep
    _ = (2 / Real.sqrt t) * (Real.log ((n : ℝ) * m / δ) + 3 * ((Real.log t + 1) / 4)) := by
        field_simp
    _ ≤ (2 / Real.sqrt t) * (3 * Real.log t + Real.log ((n : ℝ) * m)
        + Real.log (1 / δ) + 2) :=
          mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = epsPrime n m δ t := by unfold epsPrime; ring

/-- Lemma 1, p.3–5, streaming form: with probability at least `1−δ` all
    intermediate solutions are `ε′(t)`-optimal with
    `ε′(t) = (2/√t)(3 ln t + ln(nm) + ln(1/δ) + 2)`.

    Proof (paper p.5): from `source_lemma1_eq3` (the generic error of display
    (3) at the running step size) via `epsPrime_ge_generic`.  The weight
    identity is taken pointwise over trajectories, as in `source_lemma1_eq3`. -/
theorem source_lemma1_streaming
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : PayoffMatrix n m)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℕ → Fin n → ℝ) (Y : Ω → ℕ → Fin m → ℝ)
    (hweights : ∀ ω t, 1 ≤ t →
      (∑ i, X ω t i) = ∑ τ ∈ Finset.range t, stepSize (τ + 1) ∧
      (∑ j, Y ω t j) = ∑ τ ∈ Finset.range t, stepSize (τ + 1))
    (hmarkov : 1 - δ ≤ μ.real {ω | ∀ t, 1 ≤ t →
      potential A (X ω t) (Y ω t) ≤
        ((n : ℝ) * m / δ) * Real.exp (3 * ∑ τ ∈ Finset.range t, (stepSize (τ + 1)) ^ 2)}) :
    1 - δ ≤ μ.real {ω | ∀ t, 1 ≤ t →
      EpsOptimal A (fun i => X ω t i / (∑ i, X ω t i))
        (fun j => Y ω t j / (∑ j, Y ω t j)) (epsPrime n m δ t)} := by
  refine le_trans (source_lemma1_eq3 hn hm A hδ0 X Y hweights hmarkov)
    (measureReal_mono ?_)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  intro t ht
  exact epsOptimal_mono A _ _ (hω t ht) (epsPrime_ge_generic hn hm hδ0 hδ1 ht)

/-! ## The fixed-accuracy form of Lemma 1 -/

/-- Lemma 1, p.3, fixed-accuracy form: running with `η⁽τ⁾ = ε/4`, after
    `T = ⌈16 ln(nm/δ)/ε²⌉` iterations the intermediate solutions are
    `ε`-optimal with probability at least `1−δ`.

    Proof: from `potential_bound_yields_eq3` at `S = t(ε/4)²` and
    `fixed_accuracy_rounds_suffices`; the only probabilistic input is the paper's
    Markov/union-bound event `hmarkov`. -/
theorem source_lemma1_fixed_accuracy
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : PayoffMatrix n m)
    {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 3)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℕ → Fin n → ℝ) (Y : Ω → ℕ → Fin m → ℝ)
    (hweights : ∀ ω t, 1 ≤ t →
      (∑ i, X ω t i) = (t : ℝ) * (ε / 4) ∧
      (∑ j, Y ω t j) = (t : ℝ) * (ε / 4))
    (hmarkov : 1 - δ ≤ μ.real {ω | ∀ t, fixedAccuracyRounds n m ε δ ≤ t →
      potential A (X ω t) (Y ω t) ≤
        ((n : ℝ) * m / δ) * Real.exp (3 * (t : ℝ) * (ε / 4) ^ 2)}) :
    1 - δ ≤ μ.real {ω | ∀ t, fixedAccuracyRounds n m ε δ ≤ t →
      EpsOptimal A (fun i => X ω t i / (∑ i, X ω t i))
        (fun j => Y ω t j / (∑ j, Y ω t j)) ε} := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnm : (1 : ℝ) < (n : ℝ) * m / δ := by
    rw [lt_div_iff₀ hδ0]
    nlinarith
  have hceilpos : (0 : ℝ) < 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2 := by
    have hlog : (0 : ℝ) < Real.log ((n : ℝ) * m / δ) := Real.log_pos hnm
    positivity
  have hT1 : 1 ≤ fixedAccuracyRounds n m ε δ := by
    have hle : 16 * Real.log ((n : ℝ) * m / δ) / ε ^ 2
        ≤ (fixedAccuracyRounds n m ε δ : ℝ) := Nat.le_ceil _
    have hpos : (0 : ℝ) < (fixedAccuracyRounds n m ε δ : ℝ) :=
      lt_of_lt_of_le hceilpos hle
    have hposn : 0 < fixedAccuracyRounds n m ε δ := by exact_mod_cast hpos
    exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt hposn)
  refine le_trans hmarkov (measureReal_mono ?_)
  intro ω hω
  rw [Set.mem_setOf_eq] at hω ⊢
  intro t ht
  have ht1 : 1 ≤ t := hT1.trans ht
  have htpos : (0 : ℝ) < (t : ℝ) * (ε / 4) := by positivity
  have hS2nn : (0 : ℝ) ≤ (t : ℝ) * (ε / 4) ^ 2 := by positivity
  have hw := hweights ω t ht1
  have hbound := potential_bound_yields_eq3 A (X ω t) (Y ω t)
    (fun j => Real.exp (-(colPayoff A (X ω t) j)))
    (fun i => Real.exp (rowPayoff A (Y ω t) i))
    hn hm hδ0 hS2nn (fun j => rfl) (fun i => rfl)
    (by simpa only [potential, mul_assoc] using hω t ht)
  have hkey : ∀ i j, rowPayoff A (Y ω t) i - colPayoff A (X ω t) j
      ≤ ε * ((t : ℝ) * (ε / 4)) := by
    intro i j
    have h2 := fixed_accuracy_rounds_suffices hn hm hε0 hδ0
      (by linarith : δ < 1) ht ht1
    rw [div_le_iff₀ htpos] at h2
    refine (hbound i j).trans ?_
    simpa only [mul_assoc] using h2
  have hmain : EpsOptimal A (fun i => X ω t i / ((t : ℝ) * (ε / 4)))
      (fun j => Y ω t j / ((t : ℝ) * (ε / 4))) ε :=
    epsOptimal_of_normalized A (X ω t) (Y ω t) htpos hkey
  simpa only [hw.1, hw.2] using hmain

end Qatlib.Papers.ZeroSumGames19.MainResults.MatrixWeights
