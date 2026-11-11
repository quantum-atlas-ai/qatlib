/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.CompiledJump

/-!
# Coherent native PRN jumps and cost receipts

`paidNative` attaches the native jump program length to the Born distribution of its output. The
module proves exact and upper bounds for this recorded cost and extends basis-state PRN jump
semantics to finite coherent superpositions. See [KanekoEtAl2020].

## Main statements

* `paidNative_exact` and `paidNative_budget`: exact expected cost and the rung-count budget.
* `native_coherent`: linear action on superpositions of framed PRN states.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open scoped Classical ENNReal
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Receipts
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled

/-- Constructs a unit modulo `2^n` from an odd natural-number multiplier. -/
def oddMultiplier (n a : ℕ) (ha : Odd a) : (ZMod (2^n))ˣ :=
  ZMod.unitOfCoprime a ((Nat.coprime_two_right.mpr ha).pow_right n)

/-- The unit constructed from an odd multiplier has the expected residue value. See
[KanekoEtAl2020]. -/
theorem oddMultiplier_value (n a : ℕ) (ha : Odd a) :
    (oddMultiplier n a ha : ZMod (2^n)) = (a : ZMod (2^n)) := ZMod.coe_unitOfCoprime _ _

/-- The Born output law of a native jump program with its gate-program length recorded as a
constant cost. -/
noncomputable def paidNative {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (ψ : QState (Reg (width n k))) (hψ : Normalized ψ) : CostedLaw (Reg (width n k)) :=
  (bornDistribution (Run 1 (reflectionCompile (nativeWord a c qs)) ψ)
    ((native_unitary a c qs).normalized_run
      (show (1 : Matrix (Reg (width n k)) (Reg (width n k)) ℂ) ∈ Matrix.unitaryGroup _ ℂ by simp) hψ)).map
    (fun out => (out,(nativeWord a c qs).length))

/-- The expected recorded cost of `paidNative` equals the exact native program length. -/
theorem paidNative_exact {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (ψ : QState (Reg (width n k))) (hψ : Normalized ψ) :
    CostedLaw.expectedCost (paidNative a c qs ψ hψ) = ((nativeWord a c qs).length : ℝ≥0∞) := by
  simp only [CostedLaw.expectedCost,paidNative,CostedLaw.expectation_map,CostedLaw.expectation_const]

/-- The expected recorded cost is at most the number of selected exponent bits times
`rungBound`. See [KanekoEtAl2020]. -/
theorem paidNative_budget {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (ψ : QState (Reg (width n k))) (hψ : Normalized ψ) :
    CostedLaw.expectedCost (paidNative a c qs ψ hψ) ≤ (qs.length*rungBound n k : ℕ) := by
  rw [paidNative_exact]
  exact_mod_cast (native_resources a c qs).2.1

/-- The native jump program acts coherently on finite superpositions, preserving exponent bits
and applying the corresponding LCG jump to each framed state. -/
theorem native_coherent {n k : ℕ} {S : Type*} [Fintype S]
    (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (z : S → ℂ) (bits : S → Reg k) (x : S → ZMod (2^n)) :
    Run 1 (reflectionCompile (nativeWord a c qs)) (∑ s, z s • Ket (frame (bits s) (x s))) =
      ∑ s, z s • Ket (frame (bits s)
        (Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg.lcg (a:ZMod (2^n)) c (x s)
          (Qatlib.Papers.MonteCarloInt20.PrnJump.Affine.exponent qs (bits s)))) := by
  rw [run_reflectionCompile_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [run_reflectionCompile_smul,native_basis]
end Qatlib.Papers.MonteCarloInt20.PrnJump.Receipts
