/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationStat
import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.CoherentAmplificationContracts

/-!
# Probability bounds for coherent amplitude amplification

This module proves the coherent amplification statement used in [Ambainis2012]. It bounds the
marked probability of a unitary-prepared basis state, establishes the sine-window inequalities,
and combines them with the exact prepared amplification formula.

## Main statements

* `vt_sin_window`: Bound the amplified sine-squared probability.
* `coherentAmplificationWindow_proof`: Prove the exact prepared amplification formula and its
  bounds.
* `coherentAmplification_answer`: Establish `CoherentAmplification`.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.CoherentAA

open Matrix

/-- The probability of a marked set in a basis state prepared by a unitary matrix lies between
zero and one. -/
theorem vt_prepared_mass_bounds {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (hW : W ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I) :
    0 ≤ MeasureProb (ApplyGate W (Ket j₀)) S ∧
      MeasureProb (ApplyGate W (Ket j₀)) S ≤ 1 := by
  refine ⟨measureProb_nonneg _ _, ?_⟩
  have hn := normalized_applyGate hW (normalized_ket j₀)
  calc
    _ ≤ MeasureProb (ApplyGate W (Ket j₀)) Finset.univ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => bornProb_nonneg _ i)
    _ = 1 := hn

/-- For `0 ≤ θ ≤ π / 2`, `n ≥ 0`, and `a = sin² θ`, bound `sin²(nθ)` above by `min ((π² / 4) *
n² * a) 1` and below by `(4 / π²) * n² * a` when `nθ ≤ π / 2`. -/
theorem vt_sin_window (θ n a : ℝ) (hθ : 0 ≤ θ) (hθmax : θ ≤ Real.pi / 2)
    (hn : 0 ≤ n) (ha : Real.sin θ ^ 2 = a) :
    (n * θ ≤ Real.pi / 2 → (4 / Real.pi ^ 2) * n ^ 2 * a ≤ Real.sin (n * θ) ^ 2) ∧
    Real.sin (n * θ) ^ 2 ≤ min ((Real.pi ^ 2 / 4) * n ^ 2 * a) 1 := by
  have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ (by linarith [Real.pi_pos])
  have hb : θ ≤ (Real.pi / 2) * Real.sin θ := by
    calc
      θ = (Real.pi / 2) * ((2 / Real.pi) * θ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.mul_le_sin hθ hθmax) (by positivity)
  have hb2 : θ ^ 2 ≤ (Real.pi ^ 2 / 4) * a := by
    have he := pow_le_pow_left₀ hθ hb 2
    nlinarith [ha]
  constructor
  · intro hwin
    have hnt : 0 ≤ n * θ := mul_nonneg hn hθ
    have hs := Real.mul_le_sin hnt hwin
    have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ (2 / Real.pi) * (n * θ)) hs 2
    have he : (4 / Real.pi ^ 2) * n ^ 2 * θ ^ 2 ≤ Real.sin (n * θ) ^ 2 := by
      convert! hs2 using 1
      field_simp
      ring
    have hθ2 : a ≤ θ ^ 2 := by rw [← ha]; exact Real.sin_sq_le_sq
    exact (mul_le_mul_of_nonneg_left hθ2 (by positivity :
      0 ≤ (4 / Real.pi ^ 2) * n ^ 2)).trans (by simpa only [mul_assoc] using! he)
  · apply le_min
    · calc
        _ ≤ (n * θ) ^ 2 := Real.sin_sq_le_sq
        _ = n ^ 2 * θ ^ 2 := mul_pow _ _ _
        _ ≤ n ^ 2 * ((Real.pi ^ 2 / 4) * a) :=
          mul_le_mul_of_nonneg_left hb2 (sq_nonneg n)
        _ = _ := by ring
    · exact Real.sin_sq_le_one _

/-- Prepared amplitude amplification satisfies the exact success formula and both bounds
specified by `coherentAmplificationWindow`. -/
theorem coherentAmplificationWindow_proof : coherentAmplificationWindow := by
  intro I _ _ W hW j₀ S k
  (try dsimp only)
  let a := MeasureProb (ApplyGate W (Ket j₀)) S
  let θ := Real.arcsin (Real.sqrt a)
  have ha0 : 0 ≤ a := (vt_prepared_mass_bounds W hW j₀ S).1
  have ha1 : a ≤ 1 := (vt_prepared_mass_bounds W hW j₀ S).2
  have hroot1 : Real.sqrt a ≤ 1 := (Real.sqrt_le_one).2 ha1
  have hθ0 : 0 ≤ θ := Real.arcsin_nonneg.2 (Real.sqrt_nonneg a)
  have hθ1 : θ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two _
  have hsin : Real.sin θ ^ 2 = a := by
    rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1]
    exact Real.sq_sqrt ha0
  have he : MeasureProb (Run (preparedMark S) (preparedAACircuit W j₀ k) (Ket j₀)) S =
      Real.sin ((2 * (k : ℝ) + 1) * θ) ^ 2 := by
    by_cases hz : a = 0
    · rw [(prepared_aa_endpoint_states W j₀ S k hW).1 hz]
      change a = _
      simp [θ, hz]
    · by_cases ho : a = 1
      · rw [(prepared_aa_endpoint_states W j₀ S k hW).2 ho, measureProb_smul]
        have hang : (2 * (k : ℝ) + 1) * θ = Real.pi / 2 + (k : ℝ) * Real.pi := by
          simp only [θ, ho, Real.sqrt_one, Real.arcsin_one]
          ring
        rw [hang, Real.sin_add_nat_mul_pi]
        simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul,
          Real.sin_pi_div_two, mul_one]
        change a = ((-1 : ℝ) ^ k) ^ 2
        rw [ho, ← pow_mul, Nat.mul_comm, pow_mul]
        norm_num
      · exact prepared_aa_born_success W j₀ S θ k hW
          (Real.arcsin_pos.2 (Real.sqrt_pos.2 (lt_of_le_of_ne ha0 (Ne.symm hz))))
          (Real.arcsin_lt_pi_div_two.2 (by
            simpa only [Real.sqrt_one] using!
              Real.sqrt_lt_sqrt ha0 (lt_of_le_of_ne ha1 ho)))
          hsin.symm
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact (vt_sin_window θ (2 * (k : ℝ) + 1) a hθ0 hθ1 (by positivity) hsin).1
  · rw [he]
    exact (vt_sin_window θ (2 * (k : ℝ) + 1) a hθ0 hθ1 (by positivity) hsin).2

/-- The coherent amplitude-amplification proposition holds [Ambainis2012]. -/
theorem coherentAmplification_answer : CoherentAmplification := coherentAmplificationWindow_proof
end Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
