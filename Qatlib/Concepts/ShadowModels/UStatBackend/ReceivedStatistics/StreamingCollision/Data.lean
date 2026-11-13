/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Bindings

/-!
# Streaming collision data and evaluation

This module defines the state, event ledger, and rational operations of a streaming
weighted-collision estimator. `step` updates a per-label weight bank and pair sum, while
`finish` normalizes the accumulated statistic; these form an executable backend for pair
estimators relevant to nonlinear shadow estimation [HuangKuengPreskill2020].

## Main statements

* `State`: weight bank, pair sum, sample count, and cost data.
* `run`: streaming evaluation followed by normalization.
* `kernel`: the rational weighted-collision pair kernel.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- A finite label paired with a rational record weight. -/
abbrev Weighted (m : ℕ) := Fin m × ℚ

/-- The event categories counted by the streaming collision evaluator, including record and
storage access, rational arithmetic, initialization, and pair-count calls. -/
inductive Event
  | records | coefficientReads | bankReads | bankWrites
  | rationalAdds | rationalMuls | rationalSubs | rationalDivs
  | initialSlots | pairCountCalls
  deriving DecidableEq, Repr
/-- A natural-number ledger indexed by streaming collision events. -/
abbrev Counts := Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event → ℕ

/-- The streaming state consisting of the per-label rational weight bank, accumulated pair sum,
sample count, scheduled gate count, and event ledger. -/
structure State (m : ℕ) where
  bank : Vector ℚ m
  pairs : ℚ
  samples : ℕ
  scheduledGates : ℕ
  counts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts

/-- A finalized rational estimate with its scheduled gate count and event ledger. -/
structure Result where
  value : ℚ
  scheduledGates : ℕ
  counts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts

/-- The initial event ledger, charging `m` bank slots and zero for all other events. -/
def initialCounts (m : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .initialSlots => m
  | _ => 0

/-- The per-record event ledger, charging one record, bank read, bank write, and multiplication,
and two additions. -/
def stepCounts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .records | .bankReads | .bankWrites | .rationalMuls => 1
  | .rationalAdds => 2
  | _ => 0

/-- The finalization ledger, charging one multiplication, one division, and one pair-count call. -/
def finishCounts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .rationalMuls | .rationalDivs | .pairCountCalls => 1
  | _ => 0

/-- The initial streaming state with a zero bank and zero pair, sample, and gate counters,
together with initialization costs. -/
def initial (m : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  ⟨Vector.replicate m 0, 0, 0, 0, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m⟩

/-- Process one weighted record by adding its product with the existing label mass to the pair
sum, updating the bank, and accumulating sample and arithmetic costs. -/
def step {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  let old := s.bank[r.1]
  let product :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits old r.2
  let pairs :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatAddBits s.pairs product.1
  let entry :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatAddBits old r.2
  ⟨s.bank.set r.1 entry.1, pairs.1, s.samples+1,
    s.scheduledGates+product.2+pairs.2+entry.2, s.counts+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts⟩

/-- Fold the weighted-record update over a list from an initial streaming state. -/
def scan {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  xs.foldl Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s

/-- The number of unordered pairs among `n` samples, computed as `n * (n - 1) / 2`. -/
def pairCount (n : ℕ) : ℕ := n*(n-1)/2

/-- Scale the pair accumulator by the label count, divide by the sample pair count, and record
the final arithmetic costs. -/
def finish {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) : Result :=
  let scaled :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits
      (m : ℚ) s.pairs
  let out :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatDivBits scaled.1
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.pairCount s.samples : ℚ)
  ⟨out.1, s.scheduledGates+scaled.2+out.2, s.counts+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts⟩

/-- Initialize, scan a list of weighted records, and finalize the streaming collision estimate. -/
def run {m : ℕ}
    (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) :
    Result :=
    Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) xs)

/-- The rational pair kernel equal to the label count times the two weights on matching labels,
and zero on different labels. -/
def kernel {m : ℕ} (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) : ℚ :=
  if l.1=r.1 then (m : ℚ)*l.2*r.2 else 0

end Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
