/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.QRAMModel.TruncationHybridQuan
import Qatlib.Concepts.WalkFind.QRAMModel.TruncatedDataStructureBadMass

/-!
# QRAM truncation and bad-state bounds

This module packages the hybrid truncation estimate and a bad-state norm estimate as named
statements. The latter derives a norm bound for a normalized Johnson-walk type expansion from
per-type bounds on the fraction of slow data-structure operations.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `lemma5`: proves the hybrid truncation statement.
* `lemma6`: bounds the bad-state norm from per-type counting hypotheses.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.WalkFind.QRAMModel

open Qatlib
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open scoped BigOperators Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The hybrid truncation proposition `TruncationHybrid` used for the QRAM comparison. -/
def Lemma5Statement : Prop :=
  Qatlib.Concepts.WalkFind.QRAMModel.TruncationHybrid

/-- The hybrid truncation statement holds [Ambainis2007ElementDistinctness]. -/
theorem lemma5 : Lemma5Statement :=
  Qatlib.Concepts.WalkFind.QRAMModel.truncationHybrid_answer

/-- The proposition that per-type slow-operation fractions at most `1 / N^3` imply bad-state
norm at most `1 / sqrt (N^3)` for a normalized type expansion with a uniform seed. -/
def Lemma6Statement : Prop :=
  ∀ (k N M r : ℕ) (D : CollisionDataStructure N M r) (x : Fin N → ZMod M)
    (I : Finset (Fin N)) (a : Fin (2 * k + 1) → ℂ) (clock : ℕ),
    0 < N → 0 < M → k ≤ r → k < N - r →
    Normalized a →
    (∀ i : Fin (2 * k + 1),
      ((Finset.univ.filter (fun z : JRState N r × Fin (2 ^ D.seedBits) =>
          jwTypeOf I z.1 = jwPsiCoord k i ∧
            ¬ dataOperationsFast D x z.1.val.1 z.2 clock)).card : ℝ) /
        ((jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) *
          (2 ^ D.seedBits : ℝ)) ≤ 1 / (N : ℝ) ^ 3) →
    ‖toEuclidean_fromVec (fun z : JRState N r × Fin (2 ^ D.seedBits) =>
      if dataOperationsFast D x z.1.val.1 z.2 clock then 0
      else (∑ i, a i * jwPsiBigAt k N r I i z.1) *
        ((1 / Real.sqrt (2 ^ D.seedBits : ℝ) : ℝ) : ℂ))‖ ≤
      1 / Real.sqrt ((N : ℝ) ^ 3)

/-- Under the stated per-type slow-operation counting hypotheses, the bad-state norm is at most
`1 / sqrt (N^3)` [Ambainis2007ElementDistinctness]. -/
theorem lemma6 : Lemma6Statement := by
  intro k N M r D x I a clock hN hM hkr hkNr ha hfail
  have hsq : (1 / Real.sqrt ((N : ℝ) ^ 3)) ^ 2 = 1 / (N : ℝ) ^ 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  refine dataBad_bound_of_type_masses D k x I a ha clock _ (by positivity) ?_
  intro i
  rw [dataBad_type_count_identity D k hkr hkNr x I i clock, hsq]
  exact hfail i

end Qatlib.Concepts.WalkFind.QRAMModel
