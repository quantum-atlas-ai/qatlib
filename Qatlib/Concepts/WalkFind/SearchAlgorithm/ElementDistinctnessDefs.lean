/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs
import Qatlib.Concepts.WalkFind.UniqueCollision.GeneralQueryMemory
import Qatlib.Concepts.WalkFind.WalkSpectrum.GeneralOptimizedQueries
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3Native
import Qatlib.Concepts.WalkFind.WalkSpectrum.ElementDistinctnessDefs
import Qatlib.Concepts.WalkFind.WalkSpectrum.ElementDistinctness
import Qatlib.Concepts.WalkFind.WalkSpectrum.EffectiveQRAMImplementation
import Mathlib.NumberTheory.Bertrand

/-!
# Collision-search specifications and residual obligations

This module defines the specifications used by the collision-search endpoints: verified
collision correctness with read-all resource bounds, the exact read-all success law, a
prime-square existence window, and conditional QRAM implementation statements. The optimized
quantum-walk algorithm of [Ambainis2007ElementDistinctness] provides the broader context.

`clause28Spec` through `clause33Spec` name these propositions, while the corresponding residual
lists record additional optimized-query, effective-implementation, or narrow prime-window
obligations. In particular, `CoreNearPrimePowerWindow` uses the explicit bound `4 * (N + 1)^2`.

## Main statements

* `CoreVerifiedCollisionAlgorithm`: correctness with `N` queries and `N * dataBits N M` work
  bits.
* `CoreUniformSuccessLaw`: the collision-indicator success law for read-all search.
* `CoreNearPrimePowerWindow`: existence of a prime square in the specified interval.
* `clause28Residual`–`clause33Residual`: remaining obligations associated with the
  specifications.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Concepts.WalkFind.WalkSpectrum

namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

open Qatlib
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The specification that verified `k`-collision search has a correct randomized query
algorithm using at most `N` queries per seed and at most `N * dataBits N M` work bits. -/
def CoreVerifiedCollisionAlgorithm : Prop :=
  ∀ (k N M : ℕ) [NeZero M], 2 ≤ k → 0 < N → 0 < M →
    ∃ A : RandomQueryAlgorithm N M k,
      algorithmCorrect A ∧
        (∀ s, (QueryCount (A.program s) : ℝ) ≤ (N : ℝ)) ∧
        (A.workBits : ℝ) ≤ (N : ℝ) * dataBits N M

/-- The specification that the native read-all algorithm has average success equal to the
indicator of `HasCollision k x`. -/
def CoreUniformSuccessLaw : Prop :=
  ∀ (k N M : ℕ) [NeZero M] (hN : 0 < N) (x : Fin N → ZMod M),
    averageSuccess (nativeReadAll N M k hN) x = if HasCollision k x then 1 else 0

/-- The prime-square existence specification requiring, for each `N ≥ 2`, a prime `p` with `N ≤
p^2 ≤ 4 * (N + 1)^2`. -/
def CoreNearPrimePowerWindow : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ^ 2 ∧ p ^ 2 ≤ 4 * (N + 1) ^ 2

/-- The clause 28 specification, identified with `CoreVerifiedCollisionAlgorithm`. -/
def clause28Spec : Prop := CoreVerifiedCollisionAlgorithm

/-- The clause 29 specification that `EffectiveQRAMImplementationContract` implies
`QRAMImplementationContract`. -/
def clause29Spec : Prop :=
  EffectiveQRAMImplementationContract → QRAMImplementationContract

/-- The conjunction of the effective-to-QRAM implication, the near-prime-power consequence of
`Algorithm3NativeContract`, and the stated failure of a `9/8` window for binary prime
powers. -/
def clause30Spec : Prop :=
  (EffectiveQRAMImplementationContract → QRAMImplementationContract) ∧
  (∀ (h : Algorithm3NativeContract) (k : ℕ), 2 ≤ k →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ q : ℕ, N ≤ q ∧ (q : ℝ) ≤ (1 + 1 / (2 * (k : ℝ) ^ 2)) * N ∧
        ∃ p a : ℕ, Nat.Prime p ∧ 0 < a ∧ q = p ^ (2 * a)) ∧
  (∀ a : ℕ, ¬∃ b : ℕ, 2 * 4 ^ a ≤ 4 ^ b ∧ (4 ^ b : ℝ) ≤ (9 / 8 : ℝ) * (2 * 4 ^ a))

/-- The clause 31 specification, identified with `CoreUniformSuccessLaw`. -/
def clause31Spec : Prop := CoreUniformSuccessLaw

/-- The clause 32 specification, identified with the walk-spectrum `CompactMemorySpec`. -/
def clause32Spec : Prop := Qatlib.Concepts.WalkFind.WalkSpectrum.CompactMemorySpec

/-- The clause 33 specification, identified with `CoreNearPrimePowerWindow`. -/
def clause33Spec : Prop := CoreNearPrimePowerWindow

/-- The list of outstanding optimized-query and query-memory obligations beyond verified
correctness of the native read-all algorithm. -/
def clause28Residual : List String :=
  [ "the optimized query ledger of the frozen `GeneralQueryMemoryContract` (the \
`Ck * queryScale k N r` bound) is not discharged here: the native read-all algorithm \
reads all `N` entries, and the paper's `O(N^{k/(k+1)})` program with arbitrary \
multiplicity and no promise is not constructed",
    "the frozen `GeneralQueryMemoryContract` itself is therefore not proved here; only \
the verified-collision correctness with the large-memory ledger is" ]

/-- The list recording the outstanding effective QRAM implementation and compiler obligations
beyond the conditional implementation bridge. -/
def clause29Residual : List String :=
  [ "the effective QRAM implementation contract is not discharged here: the frozen \
package needs the full QRAM finite implementation and its fixed bit-machine compiler \
on top of it",
    "only the conditional bridge from the effective contract to the QRAM implementation \
contract is proved" ]

/-- The list recording the outstanding effective QRAM implementation obligation beyond the
bridge and prime-power reduction results. -/
def clause30Residual : List String :=
  [ "the effective QRAM implementation contract is not discharged here; only the \
conditional bridge, the necessity of the near-prime-power reduction and the failure of \
the binary prime-power window are proved" ]

/-- The list recording the outstanding full Ambainis program and uniform marked-mass resource
analysis beyond the native read-all success law. -/
def clause31Residual : List String :=
  [ "the full Ambainis program with the verified output and the uniform marked-mass \
ledger is not constructed here; only the uniform success law of the native read-all \
algorithm is proved" ]

/-- The list recording that the compact-memory result is supplied by the existing
element-distinctness development. -/
def clause32Residual : List String :=
  [ "the compact-memory answer is the frozen answer of the element-distinctness unit; no \
additional Dev-side construction is provided for it" ]

/-- The list recording the outstanding narrow near-prime-power window and distinguishing it from
the weaker prime-square window established here. -/
def clause33Residual : List String :=
  [ "the near-prime-power existence with the paper's factor `1 + 1/(2k^2)` is not proved \
here: it needs short-interval prime existence at the prime-number-theorem level, and \
the pinned Mathlib only provides Bertrand's postulate with a factor-`2` window",
    "only the unconditional factor-`4` window of the Dev-side contract is proved" ]

end Qatlib.Concepts.WalkFind.SearchAlgorithm
