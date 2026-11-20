/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments

@[expose] public section


/-!
# Input-dependent bounds for executed pilot arithmetic

The size measure includes the number of supplied samples, their binary rational
widths, and the width of the divisor. One explicit polynomial bounds the Boolean
gate counter `run.bitOps` for every input. Representation interpretation and
structural control are outside this counter; no machine-time bound is asserted.
No existential resource record is supplied by the caller.
The width theorem bounds the two output registers only; it is not a peak-space
theorem for the arithmetic implementation or for the complete shadows algorithm.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments

open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.FiniteSelection
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.RationalNormalization

/-- Size of the supplied rational table, including its length word and list cells. -/
def encodedSize (as : List ℚ) : ℕ :=
  as.length + (as.map width).sum + width (as.length : ℚ) + 1

/-- Squaring at input width `B` pays the primitive costs and at most doubles widths. -/
theorem squares_bounds (as : List ℚ) (B : ℕ) (ha : ∀ a ∈ as, width a ≤ B) :
    (squares as).1.length = as.length ∧
      ((squares as).1.map width).sum ≤ 2 * (as.map width).sum ∧
      (squares as).2 ≤ as.length * binomialRatOpGateCap (2 * B) := by
  induction as with
  | nil => simp [squares]
  | cons a as ih =>
    have ht := ih (fun x hx => ha x (List.mem_cons_of_mem a hx))
    have h := binomial_rat_mul_bits a a
    have hw : width a + width a ≤ 2 * B := by
      have := ha a List.mem_cons_self
      omega
    have hg := h.2.2.trans (product_cap_mono hw)
    have hvalue : width (binomialRatMulBits a a).1 ≤ width a + width a := h.2.1
    simp only [squares, List.length_cons, List.map_cons, List.sum_cons]
    refine ⟨congrArg Nat.succ ht.1, ?_, ?_⟩
    · omega
    · simpa only [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hg ht.2.2

/-- The multiplication/division cap is bounded by the common addition cap. -/
theorem op_cap_le_add_cap (w : ℕ) : binomialRatOpGateCap w ≤ binomialRatAddGateCap w := by
  unfold binomialRatOpGateCap binomialRatAddGateCap
  omega

/-- The evaluator's arithmetic cost is bounded uniformly by its actual encoded input size. -/
theorem run_cost_bound (as : List ℚ) :
    (run as).bitOps ≤ 3565 * (encodedSize as + 1) ^ 4 := by
  let S := encodedSize as
  have hlen : as.length ≤ S := by dsimp [S, encodedSize]; omega
  have hall : ∀ a ∈ as, width a ≤ S := by
    intro a ha
    have h : width a ≤ (as.map width).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩)
    dsimp [S, encodedSize]
    omega
  have hsq := squares_bounds as S hall
  have hfirst := sum_bounds as
  have hsecond := sum_bounds (squares as).1
  have hfirstWidth : width (sumBits as).1 + width (as.length : ℚ) ≤ 2 * S := by
    dsimp [S, encodedSize]
    omega
  have hsecondWidth : width (sumBits (squares as).1).1 + width (as.length : ℚ) ≤
      2 * S := by
    dsimp [S, encodedSize]
    omega
  have hfirstSum : (sumBits as).2 ≤ as.length * binomialRatAddGateCap (2 * S) :=
    hfirst.2.trans (Nat.mul_le_mul_left _ (add_cap_mono (by
      dsimp [S, encodedSize]
      omega)))
  have hsecondSum : (sumBits (squares as).1).2 ≤
      as.length * binomialRatAddGateCap (2 * S) := by
    have hcap : 1 + (squares as).1.length + ((squares as).1.map width).sum ≤ 2 * S := by
      dsimp [S, encodedSize]
      omega
    simpa only [hsq.1] using hsecond.2.trans
      (Nat.mul_le_mul_left _ (add_cap_mono hcap))
  have hdiv1 := (binomial_rat_div_bits (sumBits as).1 (as.length : ℚ)).2.2.trans
    ((product_cap_mono hfirstWidth).trans (op_cap_le_add_cap _))
  have hdiv2 := (binomial_rat_div_bits (sumBits (squares as).1).1 (as.length : ℚ)).2.2.trans
    ((product_cap_mono hsecondWidth).trans (op_cap_le_add_cap _))
  have hsqCost := hsq.2.2.trans (Nat.mul_le_mul_left _ (op_cap_le_add_cap _))
  have hcost : (run as).bitOps ≤ (3 * as.length + 2) * binomialRatAddGateCap (2 * S) := by
    dsimp only [run]
    nlinarith only [hsqCost, hfirstSum, hsecondSum, hdiv1, hdiv2]
  calc
    (run as).bitOps ≤ (3 * as.length + 2) * binomialRatAddGateCap (2 * S) := hcost
    _ ≤ (3 * S + 2) * binomialRatAddGateCap (2 * S) := by gcongr
    _ ≤ 3565 * (S + 1) ^ 4 := by
      unfold binomialRatAddGateCap
      ring_nf
      omega

/-- Both returned rational registers have width at most twice the encoded input size. -/
theorem run_output_width (as : List ℚ) :
    width (run as).mean ≤ 2 * encodedSize as ∧
      width (run as).secondMoment ≤ 2 * encodedSize as := by
  have hfirst := sum_bounds as
  have hsq := squares_bounds as ((as.map width).sum) (by
    intro a ha
    exact List.le_sum_of_mem (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have hsecond := sum_bounds (squares as).1
  have hdiv1 := (binomial_rat_div_bits (sumBits as).1 (as.length : ℚ)).2.1
  have hdiv2 := (binomial_rat_div_bits (sumBits (squares as).1).1 (as.length : ℚ)).2.1
  change width (binomialRatDivBits (sumBits as).1 (as.length : ℚ)).1 ≤
    width (sumBits as).1 + width (as.length : ℚ) at hdiv1
  change width (binomialRatDivBits (sumBits (squares as).1).1 (as.length : ℚ)).1 ≤
    width (sumBits (squares as).1).1 + width (as.length : ℚ) at hdiv2
  change width (binomialRatDivBits (sumBits as).1 (as.length : ℚ)).1 ≤ _ ∧
    width (binomialRatDivBits (sumBits (squares as).1).1 (as.length : ℚ)).1 ≤ _
  dsimp [encodedSize]
  constructor <;> omega

/-- A uniform input-size bound gives one constant and degree for the entire family. -/
theorem run_family_polynomial (inputs : ℕ → List ℚ) (B d : ℕ)
    (hsize : ∀ n, encodedSize (inputs n) ≤ B * (n + 1) ^ d) :
    ∃ c e : ℕ, ∀ n, (run (inputs n)).bitOps ≤ c * (n + 1) ^ e := by
  refine ⟨3565 * (B + 1) ^ 4, 4 * d, fun n => ?_⟩
  have hpos : 0 < (n + 1) ^ d := by positivity
  have hp : 1 ≤ (n + 1) ^ d := hpos
  have h : encodedSize (inputs n) + 1 ≤ (B + 1) * (n + 1) ^ d := by
    have := hsize n
    nlinarith only [this, hp]
  calc
    (run (inputs n)).bitOps ≤ 3565 * (encodedSize (inputs n) + 1) ^ 4 := run_cost_bound _
    _ ≤ 3565 * ((B + 1) * (n + 1) ^ d) ^ 4 := by gcongr
    _ = (3565 * (B + 1) ^ 4) * (n + 1) ^ (4 * d) := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm d 4]
      ring

end Qatlib.Concepts.MonteCarloMean.PilotVariance.BitMoments
