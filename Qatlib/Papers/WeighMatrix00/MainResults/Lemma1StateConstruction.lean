/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

def groverIterations (n k : ℕ) : ℕ :=
  Nat.ceil (Real.pi / 4 * Real.sqrt ((n : ℝ) / (k : ℝ)))

def statePreparationCalls (n k : ℕ) : ℕ :=
  if k = n then 1 else groverIterations n k + 1

theorem phaseKickback_preserves_norm {n : ℕ} (f : Fin n → ℤ) (x : Fin n → ℝ)
    (hentry : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1) :
    ∑ i : Fin n, ((if f i = 0 then (1 : ℝ) else (f i : ℝ)) * x i) ^ 2 =
      ∑ i : Fin n, (x i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  rcases hentry i with h | h | h <;> simp [h]

theorem sum_sq_eq_card_nonzero {n k : ℕ} (f : Fin n → ℤ)
    (hentry : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1)
    (hcard : (Finset.univ.filter (fun i => f i ≠ 0)).card = k) :
    ∑ i : Fin n, (f i : ℝ) ^ 2 = (k : ℝ) := by
  have hterm : ∀ i : Fin n, (f i : ℝ) ^ 2 = if f i ≠ 0 then (1 : ℝ) else 0 := by
    intro i
    rcases hentry i with h | h | h <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hnat : (∑ i : Fin n, if f i ≠ 0 then (1 : ℕ) else 0) = k := by
    rw [← Finset.card_filter (fun i : Fin n => f i ≠ 0) Finset.univ]
    exact hcard
  have hcast : (∑ i : Fin n, (if f i ≠ 0 then (1 : ℝ) else 0)) = (k : ℝ) := by
    exact_mod_cast hnat
  exact hcast

def sourceStateAmplitude {n : ℕ} (f : Fin n → ℤ) (k : ℕ) (i : Fin n) : ℝ :=
  (f i : ℝ) / Real.sqrt (k : ℝ)

theorem sourceState_norm {n k : ℕ} (f : Fin n → ℤ)
    (hentry : ∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1)
    (hcard : (Finset.univ.filter (fun i => f i ≠ 0)).card = k) (hk : 0 < k) :
    ∑ i : Fin n, (sourceStateAmplitude f k i) ^ 2 = 1 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsq : ∑ i : Fin n, (sourceStateAmplitude f k i) ^ 2 =
      (∑ i : Fin n, (f i : ℝ) ^ 2) / (Real.sqrt (k : ℝ)) ^ 2 := by
    simp only [sourceStateAmplitude, div_pow]
    rw [Finset.sum_div]
  rw [hsq, sum_sq_eq_card_nonzero f hentry hcard, Real.sq_sqrt hk0.le]
  exact div_self hk0.ne'

theorem groverIterations_suffice {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    Real.pi / 2 ≤ (2 * (groverIterations n k : ℝ) + 1) *
      Real.arcsin (Real.sqrt ((k : ℝ) / (n : ℝ))) := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hk hkn)
  have ha0 : 0 ≤ (k : ℝ) / (n : ℝ) := le_of_lt (div_pos hk0 hn0)
  have ha1 : (k : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn0]
    exact_mod_cast hkn
  set θ : ℝ := Real.arcsin (Real.sqrt ((k : ℝ) / (n : ℝ))) with hθdef
  have hsqrt0 : 0 ≤ Real.sqrt ((k : ℝ) / (n : ℝ)) := Real.sqrt_nonneg _
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    exact Real.arcsin_nonneg.mpr hsqrt0
  have hsin : Real.sin θ = Real.sqrt ((k : ℝ) / (n : ℝ)) := by
    rw [hθdef]
    exact Real.sin_arcsin (by linarith [Real.pi_pos, hsqrt0]) (Real.sqrt_le_one.mpr ha1)
  have hsinle : Real.sqrt ((k : ℝ) / (n : ℝ)) ≤ θ := by
    have := Real.sin_le hθ0
    linarith

  have hprod : Real.sqrt ((n : ℝ) / (k : ℝ)) * Real.sqrt ((k : ℝ) / (n : ℝ)) = 1 := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hn0 hk0))]
    have h : ((n : ℝ) / (k : ℝ)) * ((k : ℝ) / (n : ℝ)) = 1 := by
      field_simp
    rw [h, Real.sqrt_one]

  have hm : (Real.pi / 4) * Real.sqrt ((n : ℝ) / (k : ℝ)) ≤
      (groverIterations n k : ℝ) := Nat.le_ceil _

  have hkey : Real.pi / 2 ≤ 2 * (groverIterations n k : ℝ) *
      Real.sqrt ((k : ℝ) / (n : ℝ)) := by
    have hstep : 2 * ((Real.pi / 4) * Real.sqrt ((n : ℝ) / (k : ℝ))) ≤
        2 * (groverIterations n k : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hstep hsqrt0
    have heq : 2 * (Real.pi / 4) * Real.sqrt ((n : ℝ) / (k : ℝ)) *
        Real.sqrt ((k : ℝ) / (n : ℝ)) = Real.pi / 2 := by
      calc 2 * (Real.pi / 4) * Real.sqrt ((n : ℝ) / (k : ℝ)) *
            Real.sqrt ((k : ℝ) / (n : ℝ))
          = (2 * (Real.pi / 4)) *
              (Real.sqrt ((n : ℝ) / (k : ℝ)) * Real.sqrt ((k : ℝ) / (n : ℝ))) := by ring
        _ = (2 * (Real.pi / 4)) * 1 := by rw [hprod]
        _ = Real.pi / 2 := by ring
    calc Real.pi / 2 = 2 * (Real.pi / 4) * Real.sqrt ((n : ℝ) / (k : ℝ)) *
          Real.sqrt ((k : ℝ) / (n : ℝ)) := heq.symm
      _ = 2 * ((Real.pi / 4) * Real.sqrt ((n : ℝ) / (k : ℝ))) *
          Real.sqrt ((k : ℝ) / (n : ℝ)) := by ring
      _ ≤ 2 * (groverIterations n k : ℝ) *
          Real.sqrt ((k : ℝ) / (n : ℝ)) := hmul
  have h2m0 : 0 ≤ 2 * (groverIterations n k : ℝ) := by positivity
  have hstep2 : 2 * (groverIterations n k : ℝ) * Real.sqrt ((k : ℝ) / (n : ℝ)) ≤
      2 * (groverIterations n k : ℝ) * θ :=
    mul_le_mul_of_nonneg_left hsinle h2m0
  have h2m0' : 0 ≤ 2 * (groverIterations n k : ℝ) * θ := by positivity
  nlinarith [hkey, hstep2, hθ0]

theorem source_lemma1_stateConstruction {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    statePreparationCalls n k ≤ Nat.ceil (Real.pi / 4 * Real.sqrt ((n : ℝ) / (k : ℝ))) + 1 ∧
    statePreparationCalls n n ≤ 1 ∧
    Real.pi / 2 ≤ (2 * (groverIterations n k : ℝ) + 1) *
      Real.arcsin (Real.sqrt ((k : ℝ) / (n : ℝ))) ∧
    (∀ f : Fin n → ℤ, (∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1) →
      (Finset.univ.filter (fun i => f i ≠ 0)).card = k →
      ∑ i : Fin n, (sourceStateAmplitude f k i) ^ 2 = 1) ∧
    (∀ (f : Fin n → ℤ) (x : Fin n → ℝ), (∀ i, f i = -1 ∨ f i = 0 ∨ f i = 1) →
      ∑ i : Fin n, ((if f i = 0 then (1 : ℝ) else (f i : ℝ)) * x i) ^ 2 =
        ∑ i : Fin n, (x i) ^ 2) := by
  refine ⟨?_, ?_, groverIterations_suffice hk hkn, ?_, phaseKickback_preserves_norm⟩
  · unfold statePreparationCalls
    split_ifs with h
    · exact Nat.le_add_left 1 _
    · exact le_refl _
  · simp [statePreparationCalls]
  · intro f hentry hcard
    exact sourceState_norm f hentry hcard hk

end Qatlib.Papers.WeighMatrix00.MainResults
