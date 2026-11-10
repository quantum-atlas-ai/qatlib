/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
set_option warningAsError false

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
