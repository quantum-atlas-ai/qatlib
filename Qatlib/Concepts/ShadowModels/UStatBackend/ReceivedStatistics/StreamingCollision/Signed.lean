/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.StreamingCollision.Correctness

/-!
# Streaming signed collision evaluation

This module converts label-bit records into rational residual weights and evaluates their
collision statistic in a streaming pass. It proves agreement with explicit rational pair
evaluation and gives exact counts for coefficient access and arithmetic, supporting the
received-record estimators associated with nonlinear estimation [HuangKuengPreskill2020].

## Main statements

* `runSigned_ofFn`: agreement with explicit pair evaluation on raw records.
* `signed_call_counts`: exact per-record and finalization event counts.
* `rawKernel_symmetric`: symmetry of the signed pair kernel.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- A raw signed record consisting of a finite label and a bit. -/
abbrev Raw (m : ℕ) := Fin m × Bool

/-- The rational sign equal to negative one on true and positive one on false. -/
def sign (b : Bool) : ℚ := if b then -1 else 1

/-- Convert a raw record to the rational residual weight `a * sign r.2 - b * u[r.1]` at its
original label. -/
def weighted {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m :=
  (r.1, a*Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.sign r.2-b*u[r.1])

/-- The cost of forming a residual weight: one coefficient read, two rational multiplications,
and one subtraction. -/
def weightCounts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .coefficientReads | .rationalSubs => 1
  | .rationalMuls => 2
  | _ => 0

/-- Compute the residual-weighted record using counted rational arithmetic and return its
scheduled gate cost. -/
def makeWeighted {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m × ℕ :=
  let signed :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits a
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.sign r.2)
  let baseline :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits b u[r.1]
  let value :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatSubBits signed.1 baseline.1
  ((r.1,value.1),signed.2+baseline.2+value.2)

/-- The record returned by counted weight construction equals `weighted a b u r`. -/
@[simp] theorem makeWeighted_value {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted a b u r).1 = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u r := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted]

/-- Add the weight-construction gate cost and event ledger to a streaming state. -/
def chargeWeight {m : ℕ} (out : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (gates : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  {out with scheduledGates := out.scheduledGates+gates, counts := out.counts+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts}

/-- Construct a residual weight from one raw signed record, perform the weighted streaming step,
and charge the weight-construction costs. -/
def signedStep {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  let value := Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted a b u r
  Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.chargeWeight (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s value.1) value.2

/-- Fold the signed-record streaming step over a list from the given state. -/
def scanSigned {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  xs.foldl (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep a b u) s

/-- Initialize the state, scan raw signed records, and finalize the rational collision estimate. -/
def runSigned {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) : Result :=
  Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned a b u (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) xs)

/-- The numerical part of a streaming state: its bank, pair accumulator, and sample count. -/
private def numeric {m : ℕ}
    (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) :=
    (s.bank,s.pairs,s.samples)
/-- Update the bank, pair accumulator, and sample count for a weighted record without cost
fields. -/
private def numericStep {m : ℕ} (s : Vector ℚ m × ℚ × ℕ) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :=
  (s.1.set r.1 (s.1[r.1]+r.2), s.2.1+s.1[r.1]*r.2, s.2.2+1)

/-- Projecting a weighted streaming step to its numerical fields gives `numericStep`. -/
private theorem numeric_step {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) = numericStep (numeric s) r := by
  simp [numeric, numericStep, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step]

/-- The numerical fields of a weighted scan equal the fold of `numericStep` over the records. -/
private theorem numeric_scan {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs) = xs.foldl numericStep (numeric s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons r xs ih =>
    change numeric
        (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) xs) = _
    rw [ih, numeric_step]
    rfl

/-- Charging weight-construction costs preserves the numerical fields of the streaming state. -/
private theorem numeric_chargeWeight {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (gates : ℕ) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.chargeWeight s gates) = numeric s := rfl

/-- The numerical fields of a signed step equal a numerical weighted step applied to `weighted a
b u r`. -/
private theorem numeric_signed_step {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep a b u s r) = numericStep (numeric s) (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u r) := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep,
      numeric_chargeWeight, numeric_step, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted_value]

/-- The numerical fields of a signed scan equal a numerical fold over the corresponding
residual-weighted records. -/
private theorem numeric_signed_scan {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned a b u s xs) =
      (xs.map (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u)).foldl numericStep (numeric s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons r xs ih =>
    change numeric
        (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned a b u (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep a b u s r) xs) = _
    rw [ih, numeric_signed_step]
    rfl

/-- The signed streaming estimate equals the weighted streaming estimate after mapping each raw
record to its residual weight. -/
theorem runSigned_value {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).value = (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run (xs.map (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u))).value := by
  have hs :=
      numeric_signed_scan a b u
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) xs
  have ht :=
      numeric_scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m)
      (xs.map (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u))
  have he := hs.trans ht.symm
  have hp := congrArg (fun t => t.2.1) he
  have hn := congrArg (fun t => t.2.2) he
  simp only [numeric] at hp hn
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish_value, hp, hn]

/-- The weighted collision kernel applied to the residual-weighted versions of two raw signed
records. -/
def rawKernel {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : ℚ :=
  Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u l) (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u r)

/-- Signed streaming evaluation on a finite record list equals the rational pair evaluator for
`rawKernel`. -/
theorem runSigned_ofFn {m n : ℕ} (a b : ℚ) (u : Vector ℚ m) (w : Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value =
      (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) w).1 := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_value, List.map_ofFn,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run_value]
  rfl

/-- Each signed-scan event count increases by the list length times the sum of the weighted-step
and weight-construction event counts. -/
theorem scanSigned_counts {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned a b u s xs).counts e =
      s.counts e + xs.length*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts e) := by
  induction xs generalizing s with
  | nil => simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned]
  | cons r xs ih =>
    change (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned a b u (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep a b u s r) xs).counts e = _
    rw [ih]
    simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep,
        Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.chargeWeight, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step, Pi.add_apply, List.length_cons]
    ring

/-- A signed run event count equals initialization plus the per-record weighted-step and
weight-construction costs plus finalization. -/
theorem runSigned_counts {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts e = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m e +
      xs.length*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts e)+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts e := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish, Pi.add_apply, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned_counts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial]

/-- A signed run uses one record, coefficient read, bank read, bank write, and subtraction per
entry, two additions per entry, three multiplications per entry plus one, one division, and
`m` initial slots. -/
theorem signed_call_counts {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .records = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .coefficientReads = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .bankReads = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .bankWrites = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .rationalAdds = 2*xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .rationalMuls = 3*xs.length+1 ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .rationalSubs = xs.length ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .rationalDivs = 1 ∧
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts .initialSlots = m := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_counts,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts, Nat.mul_comm]

/-- The residual-weighted raw collision kernel is symmetric in its two records. -/
theorem rawKernel_symmetric {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u r l := by
  by_cases h : l.1=r.1
  · simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted, h]
    ring
  · simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted, h, Ne.symm h]

end Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
