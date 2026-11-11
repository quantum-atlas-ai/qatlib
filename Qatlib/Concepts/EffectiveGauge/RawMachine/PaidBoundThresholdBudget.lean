/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RawMachine.PaidBoundThresholdExecution

set_option backward.isDefEq.respectTransparency false

/-!
# Paid Bound Threshold Budget

Raw Machine constructions for Effective Gauge.
Proves `comparison_cube`, `drain_cube`, `polynomial_budget`.
-/

set_option autoImplicit false
open Turing
namespace Qatlib.Concepts.EffectiveGauge.RawMachine
open Qatlib.Concepts.EffectiveGauge.CodedFloor Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.BitWordCompiler
open Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine
open CanonicalCodec.TM
namespace PaidBoundCompression.Threshold

/-- Original `comparison_cube` guarantee for the `PaidBoundThresholdBudget` construction; the complete source hypotheses are retained. -/
private theorem comparison_cube (x y B : ℕ) (h : x+y≤2*B+2) :
    (1+x+y)^2≤9*(1+B)^3 := by
  have hl : 1+x+y≤3*(1+B) := by omega
  have hs := Nat.pow_le_pow_left hl 2
  have hc : (1+B)^2≤(1+B)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  nlinarith only [hs,hc]

/-- Original `drain_cube` guarantee for the `PaidBoundThresholdBudget` construction; the complete source hypotheses are retained. -/
private theorem drain_cube (x B : ℕ) (h : x≤2*B+2) :
    x^2+3*x+3≤100*(1+B)^3 := by
  have hl : x≤2*(1+B) := by omega
  have hs := Nat.pow_le_pow_left hl 2
  have hc : (1+B)^2≤(1+B)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1+B≤(1+B)^3 := Nat.le_pow (by decide)
  have hp : 0<(1+B)^3 := by positivity
  nlinarith only [hl,hs,hc,h1,hp]

/-- Original `polynomial_budget` guarantee for the `PaidBoundThresholdBudget` construction; the complete source hypotheses are retained. -/
private theorem polynomial_budget (L R x y : ℕ) (hx : x≤2*L+1) (hy : y≤2*R+1) :
    (((((200000*(1+L)^3+200000*(1+R)^3)+100*(1+x+y)^2)+4)+
      (x^2+3*x+3))+(y^2+3*y+3))+1≤500000*(1+L+R)^3 := by
  have hl : (1+L)^3≤(1+(L+R))^3 := Nat.pow_le_pow_left (by omega) 3
  have hr : (1+R)^3≤(1+(L+R))^3 := Nat.pow_le_pow_left (by omega) 3
  have hcmp := comparison_cube x y (L+R) (by omega)
  have hdx := drain_cube x (L+R) (by omega)
  have hdy := drain_cube y (L+R) (by omega)
  have hp : 0<(1+(L+R))^3 := by positivity
  rw [Nat.add_assoc 1 L R]
  omega

/-- Original `execution_budget_bound` guarantee for the `PaidBoundThresholdBudget` construction; the complete source hypotheses are retained. -/
theorem execution_budget_bound (q : RedundantRational.Frac) (j : ℕ) :
    executionBudget q j≤500000*(1+(leftInput q j).length+(rightInput q j).length)^3 := by
  have hx := PaidSumProducts.output_length 256 (positiveDen q).num.1 j (positiveDen q).den.2
  have hy := PaidSumProducts.output_length 256 (positiveDen q).num.2 j (positiveDen q).den.1
  have h := polynomial_budget (leftInput q j).length (rightInput q j).length
    (CanonicalCodec.natBits (leftSum q j)).length (CanonicalCodec.natBits (rightSum q j)).length hx hy
  simpa only [executionBudget,leftWord,rightWord,List.length_reverse] using h

/-- The native threshold test has cubic total stack clock in the exact
prepared input length. This bound includes result comparison and cleanup,
but not the caller's construction of its two argument banks. -/
theorem prepared_execution_cubic (q : RedundantRational.Frac) (j : ℕ) :
    Stacks.Execution program
      ⟨some default,default,state (preparedInputs q j) (fun _ => []) [] (fun _ => [])⟩
      ⟨none,default,Function.update (fun _ => []) Slot.output [enoughBit q j]⟩
      (500000*(1+(leftInput q j).length+(rightInput q j).length)^3) :=
  (prepared_execution q j).mono (execution_budget_bound q j)

/-- Raw cancellation width is retained. The only other variable width is
the binary counter field; neither is replaced by a semantic norm bound. -/
theorem prepared_execution_raw_length (q : RedundantRational.Frac) (j : ℕ) :
    Stacks.Execution program
      ⟨some default,default,state (preparedInputs q j) (fun _ => []) [] (fun _ => [])⟩
      ⟨none,default,Function.update (fun _ => []) Slot.output [enoughBit q j]⟩
      (500000*(39+(PaidRationalBridge.encode q).length+2*(CanonicalCodec.natBits j).length)^3) := by
  have h := prepared_execution_cubic q j
  rw [Nat.add_assoc 1,prepared_length] at h
  have he : 1+(38+(PaidRationalBridge.encode q).length+2*(CanonicalCodec.natBits j).length)=
      39+(PaidRationalBridge.encode q).length+2*(CanonicalCodec.natBits j).length := by omega
  rw [he] at h
  exact h

end PaidBoundCompression.Threshold
end Qatlib.Concepts.EffectiveGauge.RawMachine
