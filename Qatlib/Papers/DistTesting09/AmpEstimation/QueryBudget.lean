/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Amplitude-estimation accuracy and the Theorem 5 query budget

Theorem 5 of [BravyiHarrowHassidim2011] states that the probability-estimation algorithm
`EstProb` makes exactly `M` queries and estimates `p_A` to additive accuracy `δ` with failure
probability at most `ω`, provided

`M ≥ c * sqrt p_A / (ω * δ)` and `M ≥ c / (ω * sqrt δ)`.

The proof of the paper invokes Theorem 12 of Brassard, Høyer, Mosca and Tapp.  Phase estimation
with `k` repetitions and `n` applications of the phase-flip operator returns an estimate with
accuracy

`2 * π * k * sqrt (p_A * (1 - p_A)) / n + k ^ 2 * π ^ 2 / n ^ 2`

except with probability at most `1 / (2 * (k - 1))`.  This module isolates the arithmetic
conversion of that interface into the two query conditions of Theorem 5.  The estimate itself is
an arbitrary real-valued function on a finite probability space; the phase-estimation guarantee
is the only input taken from the cited theorem.  No algorithm or measurement is constructed
here.

The constants are explicit and uniform: `48` bounds the phase-flip count and `96` bounds the
total query count on the same scale for every `p_A ∈ [0,1]`, `δ ∈ (0,1]` and `ω ∈ (0,1/2]`.
The paper's combined query count is `M = 2 * n`,
because one query to the oracle and one to its adjoint implement one phase flip.

## Four-bin example with an off-grid phase

If one of four equally weighted seeds is accepted, then `p_A = 1/4`. The ideal Grover
iterate has eigenphases `±1/6` in turns, each with weight `1/2` in the starting state.
Four-bin inverse Fourier readout gives probabilities `(3,6,1,6)/16` in bin order.
Decoding with `sin²(π y/4)` gives `(0,1/2,1,1/2)`. At inclusive error `δ = 1/4`,
only bin `y = 2` fails, so the success probability is `15/16`.

This analytic example checks the ideal readout and decoder, not the oracle query circuit.

## References

* [Bravyi et al., 2011][BravyiHarrowHassidim2011], Theorem 5 and its proof
* Brassard, Høyer, Mosca, Tapp, *Quantum amplitude amplification and estimation*, Theorem 12
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.DistTesting09.AmpEstimation

variable {Ω : Type*} [Fintype Ω]

/-- The probability of a decidable event under a finite distribution, written as a filtered
mass sum. -/
def eventMass (Pr : FinDist Ω) (E : Ω → Prop) : ℝ := by
  classical exact ∑ x, if E x then Pr.prob x else 0

/-- A finite probability mass is nonnegative on every event. -/
theorem eventMass_nonneg (Pr : FinDist Ω) (E : Ω → Prop) : 0 ≤ eventMass Pr E := by
  classical
  unfold eventMass
  exact Finset.sum_nonneg fun x _ => by
    by_cases h : E x <;> simp [h, Pr.nonneg x]

/-- The probability of any event is at most one. -/
theorem eventMass_le_one (Pr : FinDist Ω) (E : Ω → Prop) : eventMass Pr E ≤ 1 := by
  classical
  unfold eventMass
  calc ∑ x, (if E x then Pr.prob x else 0) ≤ ∑ x, Pr.prob x :=
        Finset.sum_le_sum fun x _ => by
          by_cases h : E x <;> simp [h, Pr.nonneg x]
    _ = 1 := Pr.sum_one

/-- The probability of the complement of an event is one minus the probability of the event. -/
theorem eventMass_compl (Pr : FinDist Ω) (E : Ω → Prop) :
    eventMass Pr (fun x => ¬ E x) = 1 - eventMass Pr E := by
  classical
  unfold eventMass
  rw [← Pr.sum_one, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : E x <;> simp [h]

/-- An event contained in another has no larger probability. -/
theorem eventMass_mono (Pr : FinDist Ω) {E F : Ω → Prop} (h : ∀ x, E x → F x) :
    eventMass Pr E ≤ eventMass Pr F := by
  classical
  unfold eventMass
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hx : E x
  · have hF : F x := h x hx
    simp [hx, hF]
  · simp only [hx, ite_false]
    by_cases hF : F x
    · simp [hF, Pr.nonneg x]
    · simp [hF]

/-- An event that holds everywhere has probability one. -/
theorem eventMass_true (Pr : FinDist Ω) {E : Ω → Prop} (h : ∀ x, E x) :
    eventMass Pr E = 1 := by
  classical
  unfold eventMass
  rw [show (∑ x, (if E x then Pr.prob x else 0)) = ∑ x, Pr.prob x from
    Finset.sum_congr rfl fun x _ => by simp [h x]]
  exact Pr.sum_one

/-- An event that holds nowhere has probability zero. -/
theorem eventMass_false (Pr : FinDist Ω) {E : Ω → Prop} (h : ∀ x, ¬ E x) :
    eventMass Pr E = 0 := by
  classical
  unfold eventMass
  refine Finset.sum_eq_zero fun x _ => ?_
  simp [h x]

/-- The accuracy produced by phase estimation with `k` repetitions and `n` phase-flip
applications, as stated in the proof of Theorem 12 of Brassard, Høyer, Mosca and Tapp. -/
def phaseAccuracy (pA k n : ℝ) : ℝ :=
  2 * Real.pi * k * Real.sqrt (pA * (1 - pA)) / n + k ^ 2 * Real.pi ^ 2 / n ^ 2

/-- The failure probability of phase estimation with `k` repetitions. -/
def phaseFailure (k : ℝ) : ℝ := 1 / (2 * (k - 1))

/-- The phase-estimation accuracy is nonnegative for every nonnegative repetition count and
budget. -/
theorem phaseAccuracy_nonneg (pA k n : ℝ) (hk : 0 ≤ k) (hn : 0 ≤ n) :
    0 ≤ phaseAccuracy pA k n := by
  unfold phaseAccuracy
  have h1 : 0 ≤ 2 * Real.pi * k * Real.sqrt (pA * (1 - pA)) := by
    have : 0 ≤ 2 * Real.pi * k := by positivity
    positivity
  have h2 : 0 ≤ k ^ 2 * Real.pi ^ 2 := by positivity
  exact add_nonneg (div_nonneg h1 hn) (div_nonneg h2 (by positivity))

/-- The phase-estimation failure probability is nonnegative from two repetitions on. -/
theorem phaseFailure_nonneg {k : ℕ} (hk : 2 ≤ k) : 0 ≤ phaseFailure (k : ℝ) := by
  unfold phaseFailure
  have hk1 : (0 : ℝ) < (k : ℝ) - 1 := by
    have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith
  positivity

/-- Repetition counts above `1 + 1 / (2 ω)` turn the phase-estimation failure bound
`1 / (2 (k - 1))` into at most `ω`. -/
theorem phaseFailure_le_omega {k ω : ℝ} (hω : 0 < ω) (hk : 1 + 1 / (2 * ω) ≤ k) :
    phaseFailure k ≤ ω := by
  have hden : 0 < 2 * ω := by positivity
  have hk1 : 1 < k := by
    have : 0 < 1 / (2 * ω) := by positivity
    linarith
  have hprod : 1 ≤ 2 * ω * (k - 1) := by
    have h : 1 / (2 * ω) ≤ k - 1 := by linarith
    calc (1 : ℝ) = 2 * ω * (1 / (2 * ω)) := by field_simp
      _ ≤ 2 * ω * (k - 1) := by
          exact mul_le_mul_of_nonneg_left h hden.le
  unfold phaseFailure
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (k - 1))]
  linarith

/-- With `n ≥ 13 k sqrt p_A / δ` and `n ≥ 5 k / sqrt δ`, the phase-estimation accuracy is at
most `δ` for every `p_A ∈ [0,1]`.  The constants `13` and `5` absorb the factors `2 π` and
`sqrt 2 π`, using `π < 3.15`. -/
theorem phaseAccuracy_le_delta {pA δ : ℝ} (k n : ℕ)
    (hp0 : 0 ≤ pA) (_hp1 : pA ≤ 1) (hδ : 0 < δ) (hnpos : 0 < n)
    (hn1 : 13 * (k : ℝ) * Real.sqrt pA / δ ≤ (n : ℝ))
    (hn2 : 5 * (k : ℝ) / Real.sqrt δ ≤ (n : ℝ)) :
    phaseAccuracy pA (k : ℝ) (n : ℝ) ≤ δ := by
  have hpi := Real.pi_lt_d2
  have hpi2 := Real.pi_pos
  have hnpos' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hsqrtδ : 0 < Real.sqrt δ := Real.sqrt_pos_of_pos hδ
  have hknn : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hsqrtp : 0 ≤ Real.sqrt pA := Real.sqrt_nonneg pA
  have hprod_le : pA * (1 - pA) ≤ pA := by nlinarith
  have hsqrt_le : Real.sqrt (pA * (1 - pA)) ≤ Real.sqrt pA := Real.sqrt_le_sqrt hprod_le
  -- First term: `2 π k sqrt (p_A (1 - p_A)) ≤ 6.3 k sqrt p_A ≤ (13/2) k sqrt p_A ≤ n δ / 2`.
  have hterm1 : 2 * Real.pi * (k : ℝ) * Real.sqrt (pA * (1 - pA)) / (n : ℝ) ≤ δ / 2 := by
    have hA : 2 * Real.pi * (k : ℝ) * Real.sqrt (pA * (1 - pA))
        ≤ (63 / 10) * (k : ℝ) * Real.sqrt pA := by
      have h1 : 2 * Real.pi * (k : ℝ) * Real.sqrt (pA * (1 - pA))
          ≤ 2 * Real.pi * (k : ℝ) * Real.sqrt pA := by
        have := mul_le_mul_of_nonneg_left hsqrt_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (k : ℝ))
        linarith
      have h2 : 2 * Real.pi * (k : ℝ) * Real.sqrt pA
          ≤ (63 / 10) * (k : ℝ) * Real.sqrt pA := by
        have hpi7 : 2 * Real.pi ≤ 63 / 10 := by linarith
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hpi7 hknn) hsqrtp
        nlinarith
      linarith
    have hnd : 13 * (k : ℝ) * Real.sqrt pA ≤ (n : ℝ) * δ := by
      rw [div_le_iff₀ hδ] at hn1
      linarith
    have hkn : (63 / 10) * (k : ℝ) * Real.sqrt pA ≤ (n : ℝ) * δ / 2 := by
      nlinarith
    rw [div_le_iff₀ hnpos']
    nlinarith
  -- Second term: `k ^ 2 π ^ 2 ≤ (5 k / sqrt δ) ^ 2 π ^ 2 ≤ n ^ 2 δ / 2`.
  have hterm2 : (k : ℝ) ^ 2 * Real.pi ^ 2 / (n : ℝ) ^ 2 ≤ δ / 2 := by
    have hsq : (5 * (k : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 * δ := by
      have h : 5 * (k : ℝ) ≤ (n : ℝ) * Real.sqrt δ := by
        rw [div_le_iff₀ hsqrtδ] at hn2
        linarith
      nlinarith [sq_nonneg (5 * (k : ℝ) - (n : ℝ) * Real.sqrt δ), Real.sq_sqrt hδ.le]
    have hpi2le : Real.pi ^ 2 ≤ 25 / 2 := by nlinarith [Real.pi_pos, hpi]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    nlinarith
  unfold phaseAccuracy
  linarith

/-- For every admissible accuracy and failure level there are a repetition count `k` and a
phase-flip budget `n` achieving both bounds, with `n` bounded by the uniform constant `48`
times `sqrt p_A / (ω δ) + 1 / (ω sqrt δ)`. -/
theorem exists_phase_scale (pA δ ω : ℝ) (hp0 : 0 ≤ pA) (hp1 : pA ≤ 1) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1 / 2) :
    ∃ k n : ℕ, 2 ≤ k ∧ 0 < n ∧ phaseFailure (k : ℝ) ≤ ω ∧
      phaseAccuracy pA (k : ℝ) (n : ℝ) ≤ δ ∧
      (n : ℝ) ≤ 48 * (Real.sqrt pA / (ω * δ) + 1 / (ω * Real.sqrt δ)) := by
  have hden : 0 < 2 * ω := by positivity
  set k : ℕ := Nat.ceil (1 + 1 / (2 * ω)) with hkdef
  have hkle : 1 + 1 / (2 * ω) ≤ (k : ℝ) := Nat.le_ceil _
  have hklt : (k : ℝ) < 1 + 1 / (2 * ω) + 1 := by
    have hnonneg : (0 : ℝ) ≤ 1 + 1 / (2 * ω) := by positivity
    exact Nat.ceil_lt_add_one hnonneg
  have hk2 : 2 ≤ k := by
    have h2 : (2 : ℝ) ≤ 1 + 1 / (2 * ω) := by
      have : (1 : ℝ) ≤ 1 / (2 * ω) := by
        rw [le_div_iff₀ hden]
        nlinarith
      linarith
    exact_mod_cast le_trans h2 hkle
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hk2)
  have hkub : (k : ℝ) ≤ 5 / (2 * ω) := by
    have hω2 : (2 : ℝ) ≤ 1 / ω := by
      rw [le_div_iff₀ hω]
      nlinarith
    have hstep : 2 + 1 / (2 * ω) ≤ 3 / (2 * ω) := by
      have hmm : (2 : ℝ) ≤ 2 / (2 * ω) := by
        rw [show (2 : ℝ) / (2 * ω) = 1 / ω by field_simp]
        exact hω2
      have hsum : (2 : ℝ) + 1 / (2 * ω) ≤ 2 / (2 * ω) + 1 / (2 * ω) := by linarith
      have heq : (2 : ℝ) / (2 * ω) + 1 / (2 * ω) = 3 / (2 * ω) := by
        field_simp
        ring
      linarith
    have hfin : (3 : ℝ) / (2 * ω) ≤ 5 / (2 * ω) := by
      exact div_le_div_of_nonneg_right (by norm_num) hden.le
    linarith
  have hconst2 : 0 < 5 * (k : ℝ) / Real.sqrt δ := by positivity
  set X : ℝ := max (13 * (k : ℝ) * Real.sqrt pA / δ) (5 * (k : ℝ) / Real.sqrt δ) with hXdef
  have hXpos : 0 < X := lt_of_lt_of_le hconst2 (le_max_right _ _)
  set n : ℕ := Nat.ceil X with hndef
  have hnle : X ≤ (n : ℝ) := Nat.le_ceil _
  have hnlt : (n : ℝ) < X + 1 := Nat.ceil_lt_add_one hXpos.le
  have hnpos : 0 < n := by
    have : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hXpos hnle
    exact_mod_cast this
  have hn1 : 13 * (k : ℝ) * Real.sqrt pA / δ ≤ (n : ℝ) :=
    le_trans (le_max_left _ _) hnle
  have hn2 : 5 * (k : ℝ) / Real.sqrt δ ≤ (n : ℝ) :=
    le_trans (le_max_right _ _) hnle
  refine ⟨k, n, hk2, hnpos, phaseFailure_le_omega hω hkle,
    phaseAccuracy_le_delta k n hp0 hp1 hδ hnpos hn1 hn2, ?_⟩
  have hsqrtωδ : 0 < ω * Real.sqrt δ := by positivity
  have hy : (1 : ℝ) ≤ 1 / (ω * Real.sqrt δ) := by
    rw [le_div_iff₀ hsqrtωδ]
    nlinarith [Real.sqrt_le_one.mpr hδ1]
  have hx0 : 0 ≤ Real.sqrt pA / (ω * δ) := by positivity
  have hy0 : 0 ≤ 1 / (ω * Real.sqrt δ) := by positivity
  have h1 : 13 * (k : ℝ) * Real.sqrt pA / δ ≤ (65 / 2) * (Real.sqrt pA / (ω * δ)) := by
    have hsplit : 13 * (k : ℝ) * Real.sqrt pA / δ
        = 13 * (k : ℝ) * (Real.sqrt pA / δ) := by ring
    rw [hsplit]
    have hk' : 13 * (k : ℝ) ≤ 13 * (5 / (2 * ω)) := by nlinarith
    calc 13 * (k : ℝ) * (Real.sqrt pA / δ)
        ≤ (13 * (5 / (2 * ω))) * (Real.sqrt pA / δ) :=
          mul_le_mul_of_nonneg_right hk' (by positivity)
      _ = (65 / 2) * (Real.sqrt pA / (ω * δ)) := by
          field_simp
          ring
  have h2 : 5 * (k : ℝ) / Real.sqrt δ ≤ (25 / 2) * (1 / (ω * Real.sqrt δ)) := by
    have hk' : 5 * (k : ℝ) ≤ 5 * (5 / (2 * ω)) := by nlinarith
    have := mul_le_mul_of_nonneg_right hk' (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt δ)
    calc 5 * (k : ℝ) / Real.sqrt δ = 5 * (k : ℝ) * (1 / Real.sqrt δ) := by ring
      _ ≤ (5 * (5 / (2 * ω))) * (1 / Real.sqrt δ) := this
      _ = (25 / 2) * (1 / (ω * Real.sqrt δ)) := by
          field_simp
          ring
  have hsum : X ≤ (65 / 2) * (Real.sqrt pA / (ω * δ)) + (25 / 2) * (1 / (ω * Real.sqrt δ)) := by
    rw [hXdef]
    apply max_le
    · linarith [hy0]
    · linarith [hx0]
  have hfinal : (65 / 2) * (Real.sqrt pA / (ω * δ)) + (25 / 2) * (1 / (ω * Real.sqrt δ)) + 1
      ≤ 48 * (Real.sqrt pA / (ω * δ) + 1 / (ω * Real.sqrt δ)) := by
    nlinarith [hx0, hy0, hy]
  linarith

/-- A uniform constant bounds the total query cost `2 * n` of the phase-flip budget on the
scale of [BravyiHarrowHassidim2011], Theorem 5. At this budget any estimator satisfying the
cited phase-estimation tail succeeds with probability at least `1 - ω`. -/
theorem exists_estprob_budget :
    ∃ C : ℝ, 0 < C ∧ ∀ (pA δ ω : ℝ), 0 ≤ pA → pA ≤ 1 → 0 < δ → δ ≤ 1 →
      0 < ω → ω ≤ 1 / 2 →
      ∃ k n : ℕ, 2 ≤ k ∧ 0 < n ∧
        2 * (n : ℝ) ≤ C * (Real.sqrt pA / (ω * δ) + 1 / (ω * Real.sqrt δ)) ∧
        (∀ (Ω : Type) [Fintype Ω] (Pr : FinDist Ω) (est : Ω → ℝ),
          eventMass Pr (fun x => ¬ (|est x - pA| ≤ phaseAccuracy pA (k : ℝ) (n : ℝ)))
            ≤ phaseFailure (k : ℝ) →
          1 - ω ≤ eventMass Pr (fun x => |est x - pA| ≤ δ)) := by
  refine ⟨96, by norm_num, ?_⟩
  intro pA δ ω hp0 hp1 hδ hδ1 hω hω1
  obtain ⟨k, n, hk2, hnpos, hfail, hacc, hn⟩ :=
    exists_phase_scale pA δ ω hp0 hp1 hδ hδ1 hω hω1
  refine ⟨k, n, hk2, hnpos, by linarith, ?_⟩
  intro Ω _ Pr est hbad
  have hmono : eventMass Pr (fun x => ¬ (|est x - pA| ≤ δ))
      ≤ eventMass Pr (fun x => ¬ (|est x - pA| ≤ phaseAccuracy pA (k : ℝ) (n : ℝ))) := by
    refine eventMass_mono Pr ?_
    intro x hx
    simp only [not_le] at hx ⊢
    exact lt_of_le_of_lt hacc hx
  have hbad_le : eventMass Pr (fun x => ¬ (|est x - pA| ≤ δ)) ≤ phaseFailure (k : ℝ) :=
    le_trans hmono hbad
  have hcompl := eventMass_compl Pr (fun x => |est x - pA| ≤ δ)
  linarith

/-- When `p_A = 0`, the estimate `0` has error zero and hence succeeds with probability one,
matching the last sentence of Theorem 5. -/
theorem estprob_zero_certain (Pr : FinDist Ω) (est : Ω → ℝ) (hzero : ∀ x, est x = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    eventMass Pr (fun x => |est x - 0| ≤ δ) = 1 := by
  refine eventMass_true Pr ?_
  intro x
  rw [hzero x]
  simpa using hδ.le

end Qatlib.Papers.DistTesting09.AmpEstimation
