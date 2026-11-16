/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier.SourceInfluenceFourier

@[expose] public section


/-! # Preserved complete legacy mathematical components

These definitions and conditional estimates retain their complete original
mathematics. Free success/query fields are not an oracle algorithm; scalar
amplification estimates are not a repetition or termination proof.
-/
set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open scoped BigOperators ENNReal
namespace Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath

def sampleDist {n : ℕ} (F : Reg n → ℝ) (s : Reg n) (b : Bool) (u : Reg n) : ℝ :=
  if b = parityDot s u then (fourierCoef F u) ^ 2 else 0

/-- The signed lift of a Boolean function is `{+1,-1}`-valued, equation (1). -/
theorem signedSquare {n : ℕ} (f : Reg n → Bool) (x : Reg n) :
    signedFun f x * signedFun f x = 1 := by
  unfold signedFun
  by_cases h : f x <;> simp [h]

/-- The sampling distribution is nonnegative. -/
theorem sampleNonneg {n : ℕ} (F : Reg n → ℝ) (s : Reg n) (b : Bool) (u : Reg n) :
    0 ≤ sampleDist F s b u := by
  unfold sampleDist
  split <;> positivity

/-- Equation (2) consistency: a positive-weight outcome always satisfies
`b = ⟨u,s⟩`. This is the fact that makes the linear system of Theorem 1,
step 4, always accept the hidden shift. -/
theorem sampleConsist {n : ℕ} (F : Reg n → ℝ) (s : Reg n) {b : Bool} {u : Reg n}
    (h : sampleDist F s b u ≠ 0) : b = parityDot s u := by
  unfold sampleDist at h
  by_cases hb : b = parityDot s u
  · exact hb
  · rw [ite_eq_right hb] at h
    exact absurd rfl h

/-- The marginal distribution in `u` is `F̂(u)²` (the paper's `D_f^U(u) ≡ F̂(u)²`). -/
theorem sampleMarginal {n : ℕ} (F : Reg n → ℝ) (s : Reg n) (u : Reg n) :
    (∑ b : Bool, sampleDist F s b u) = (fourierCoef F u) ^ 2 := by
  unfold sampleDist
  rcases h : parityDot s u <;> simp

/-- The sampling distribution is normalized: `Σ F̂(u)² = 1` (Parseval). -/
theorem sampleTotal {n : ℕ} (F : Reg n → ℝ)
    (hF : ∀ x : Reg n, F x * F x = 1) (s : Reg n) :
    (∑ p : Reg n × Bool, sampleDist F s p.2 p.1) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sampleMarginal]
  exact sum_sq_fourier F hF

/-- **Theorem 1, equation (2)**: the sampling subroutine's output distribution
is consistent with the hidden shift, has marginal `F̂(u)²` and is normalized. -/
theorem sampleCorrect {n : ℕ} (inst : BHSPInstance n) :
    (∀ u : Reg n, (∑ b : Bool, sampleDist (signedFun inst.f) inst.shift b u)
        = (fourierCoef (signedFun inst.f) u) ^ 2) ∧
    (∀ (b : Bool) (u : Reg n),
        sampleDist (signedFun inst.f) inst.shift b u ≠ 0 → b = parityDot inst.shift u) ∧
    (∑ p : Reg n × Bool, sampleDist (signedFun inst.f) inst.shift p.2 p.1) = 1 :=
  ⟨fun u => sampleMarginal _ _ u,
   fun _b _u => sampleConsist _ _,
   sampleTotal _ (signedSquare inst.f) _⟩

/-! ### Probabilities of leaving a subspace -/

/-- The influence is nonnegative. -/
theorem influenceNonneg {n : ℕ} (F : Reg n → ℝ) (v : Reg n) : 0 ≤ influence F v := by
  unfold influence uniformWeight
  have hsum : (0 : ℝ) ≤ ∑ x : Reg n, (if F x = F (regXor x v) then (0 : ℝ) else 1) := by
    apply Finset.sum_nonneg
    intro x _
    split <;> norm_num
  exact mul_nonneg (by positivity) hsum

/-- **Key termination estimate** (Theorem 1 proof, p.3): for the sampling
distribution, the probability that `⟨v,u⟩ = 1` is exactly the influence
`γ_{f,v}`, by Lemma 1. -/
theorem crossInfluence {n : ℕ} (F : Reg n → ℝ)
    (hF : ∀ x : Reg n, F x * F x = 1) (v : Reg n) :
    (∑ u ∈ Finset.univ.filter (fun u => parityDot v u = true),
        (fourierCoef F u) ^ 2) = influence F v :=
  (source_lemma1_influence F hF v).symm

/-- `γ_f ≤ γ_{f,v}` for every nonzero shift, from the definition of the minimum
influence over nonzero shifts. -/
theorem minBound {n : ℕ} (F : Reg n → ℝ) {v : Reg n}
    (hv : v ≠ ZeroStr n) : minInfluence F ≤ influence F v := by
  unfold minInfluence
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨w, _, rfl⟩; exact influenceNonneg F w⟩
  · exact ⟨v, hv, rfl⟩


end Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath
