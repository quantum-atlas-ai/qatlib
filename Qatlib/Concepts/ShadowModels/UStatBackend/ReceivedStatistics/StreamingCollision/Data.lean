/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Bindings
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

abbrev Weighted (m : ℕ) := Fin m × ℚ

inductive Event
  | records | coefficientReads | bankReads | bankWrites
  | rationalAdds | rationalMuls | rationalSubs | rationalDivs
  | initialSlots | pairCountCalls
  deriving DecidableEq, Repr
abbrev Counts := Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event → ℕ

structure State (m : ℕ) where
  bank : Vector ℚ m
  pairs : ℚ
  samples : ℕ
  scheduledGates : ℕ
  counts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts

structure Result where
  value : ℚ
  scheduledGates : ℕ
  counts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts

def initialCounts (m : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .initialSlots => m
  | _ => 0

def stepCounts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .records | .bankReads | .bankWrites | .rationalMuls => 1
  | .rationalAdds => 2
  | _ => 0

def finishCounts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .rationalMuls | .rationalDivs | .pairCountCalls => 1
  | _ => 0

def initial (m : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  ⟨Vector.replicate m 0, 0, 0, 0, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m⟩

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

def scan {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  xs.foldl Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s

def pairCount (n : ℕ) : ℕ := n*(n-1)/2

def finish {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) : Result :=
  let scaled :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits
      (m : ℚ) s.pairs
  let out :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatDivBits scaled.1
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.pairCount s.samples : ℚ)
  ⟨out.1, s.scheduledGates+scaled.2+out.2, s.counts+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts⟩

def run {m : ℕ}
    (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) :
    Result :=
    Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) xs)

def kernel {m : ℕ} (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) : ℚ :=
  if l.1=r.1 then (m : ℚ)*l.2*r.2 else 0

end Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
