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

def CoreVerifiedCollisionAlgorithm : Prop :=
  ∀ (k N M : ℕ) [NeZero M], 2 ≤ k → 0 < N → 0 < M →
    ∃ A : RandomQueryAlgorithm N M k,
      algorithmCorrect A ∧
        (∀ s, (QueryCount (A.program s) : ℝ) ≤ (N : ℝ)) ∧
        (A.workBits : ℝ) ≤ (N : ℝ) * dataBits N M

def CoreUniformSuccessLaw : Prop :=
  ∀ (k N M : ℕ) [NeZero M] (hN : 0 < N) (x : Fin N → ZMod M),
    averageSuccess (nativeReadAll N M k hN) x = if HasCollision k x then 1 else 0

def CoreNearPrimePowerWindow : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∃ p : ℕ, Nat.Prime p ∧ N ≤ p ^ 2 ∧ p ^ 2 ≤ 4 * (N + 1) ^ 2

def clause28Spec : Prop := CoreVerifiedCollisionAlgorithm

def clause29Spec : Prop :=
  EffectiveQRAMImplementationContract → QRAMImplementationContract

def clause30Spec : Prop :=
  (EffectiveQRAMImplementationContract → QRAMImplementationContract) ∧
  (∀ (h : Algorithm3NativeContract) (k : ℕ), 2 ≤ k →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∃ q : ℕ, N ≤ q ∧ (q : ℝ) ≤ (1 + 1 / (2 * (k : ℝ) ^ 2)) * N ∧
        ∃ p a : ℕ, Nat.Prime p ∧ 0 < a ∧ q = p ^ (2 * a)) ∧
  (∀ a : ℕ, ¬∃ b : ℕ, 2 * 4 ^ a ≤ 4 ^ b ∧ (4 ^ b : ℝ) ≤ (9 / 8 : ℝ) * (2 * 4 ^ a))

def clause31Spec : Prop := CoreUniformSuccessLaw

def clause32Spec : Prop := Qatlib.Concepts.WalkFind.WalkSpectrum.CompactMemorySpec

def clause33Spec : Prop := CoreNearPrimePowerWindow

def clause28Residual : List String :=
  [ "the optimized query ledger of the frozen `GeneralQueryMemoryContract` (the \
`Ck * queryScale k N r` bound) is not discharged here: the native read-all algorithm \
reads all `N` entries, and the paper's `O(N^{k/(k+1)})` program with arbitrary \
multiplicity and no promise is not constructed",
    "the frozen `GeneralQueryMemoryContract` itself is therefore not proved here; only \
the verified-collision correctness with the large-memory ledger is" ]

def clause29Residual : List String :=
  [ "the effective QRAM implementation contract is not discharged here: the frozen \
package needs the full QRAM finite implementation and its fixed bit-machine compiler \
on top of it",
    "only the conditional bridge from the effective contract to the QRAM implementation \
contract is proved" ]

def clause30Residual : List String :=
  [ "the effective QRAM implementation contract is not discharged here; only the \
conditional bridge, the necessity of the near-prime-power reduction and the failure of \
the binary prime-power window are proved" ]

def clause31Residual : List String :=
  [ "the full Ambainis program with the verified output and the uniform marked-mass \
ledger is not constructed here; only the uniform success law of the native read-all \
algorithm is proved" ]

def clause32Residual : List String :=
  [ "the compact-memory answer is the frozen answer of the element-distinctness unit; no \
additional Dev-side construction is provided for it" ]

def clause33Residual : List String :=
  [ "the near-prime-power existence with the paper's factor `1 + 1/(2k^2)` is not proved \
here: it needs short-interval prime existence at the prime-number-theorem level, and \
the pinned Mathlib only provides Bertrand's postulate with a factor-`2` window",
    "only the unconditional factor-`4` window of the Dev-side contract is proved" ]

end Qatlib.Concepts.WalkFind.SearchAlgorithm
