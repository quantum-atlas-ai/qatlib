/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder

/-!
# Specification of the bounded-error near-period distinguisher

Defines `BoundedErrorNearPeriodDistinguisher`, a proposition specifying the resource ledger and
output-event bounds of Simon decoding on `n + k` samples. It requires the ledger `(n + k, 2 * (n
+ k), n + k)` and bounds the probability of not returning the zero string by `(1 / 2) ^ k` for
injective functions.

For each nonzero translation with at most `2 ^ n / (n + k)` violating inputs, it requires a
lower bound `(1 - 1 / (n + k)) ^ (n + k)` on the same output event. The specification is
motivated by the bounded-error extension in [Simon1997].

## Main statements

* `BoundedErrorNearPeriodDistinguisher`: states the resource and probability requirements.

## References

* [Simon, 1997][Simon1997]
-/

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline
set_option autoImplicit false
open scoped ENNReal Classical
namespace Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib

/-- The specification that Simon decoding with `m = n + k` has ledger `(m, 2 * m, m)` and
probability at most `(1 / 2) ^ k` of not returning the zero string for injective functions.
For each nonzero translation with at most `2 ^ n / m` violating inputs, it also requires
probability at least `(1 - 1 / m) ^ m` of not returning the zero string. -/
def BoundedErrorNearPeriodDistinguisher : Prop :=
  ∀ (n : ℕ) (k : ℕ) (R : Type) [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R),
    (simonDecodedRun f (n + k)).2 = (n + k, 2 * (n + k), n + k) ∧
    (Function.Injective f →
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (simonDecodedRun f (n + k)).1
          (fun out => out ≠ some (ZeroStr n)) ≤ ENNReal.ofReal ((1 / 2 : ℝ)^k)) ∧
    (∀ s : BooleanVec n, s ≠ 0 →
      Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n →
      ENNReal.ofReal ((1 - 1 / (n + k) : ℝ)^(n + k)) ≤
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (simonDecodedRun f (n + k)).1
          (fun out => out ≠ some (ZeroStr n)))
end Qatlib.Concepts.HspRecovery.Distinguisher
