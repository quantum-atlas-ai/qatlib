/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.ReceivedStatistics.StreamingCollision.Correctness
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

abbrev Raw (m : ℕ) := Fin m × Bool

def sign (b : Bool) : ℚ := if b then -1 else 1

def weighted {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m :=
  (r.1, a*Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.sign r.2-b*u[r.1])

def weightCounts : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Counts
  | .coefficientReads | .rationalSubs => 1
  | .rationalMuls => 2
  | _ => 0

def makeWeighted {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m × ℕ :=
  let signed :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits a
      (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.sign r.2)
  let baseline :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatMulBits b u[r.1]
  let value :=
      Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.binomialRatSubBits signed.1 baseline.1
  ((r.1,value.1),signed.2+baseline.2+value.2)

@[simp] theorem makeWeighted_value {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted a b u r).1 = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u r := by
  simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted]

def chargeWeight {m : ℕ} (out : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (gates : ℕ) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  {out with scheduledGates := out.scheduledGates+gates, counts := out.counts+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts}

def signedStep {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  let value := Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted a b u r
  Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.chargeWeight (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s value.1) value.2

def scanSigned {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m :=
  xs.foldl (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep a b u) s

def runSigned {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) : Result :=
  Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned a b u (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial m) xs)

private def numeric {m : ℕ}
    (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) :=
    (s.bank,s.pairs,s.samples)
private def numericStep {m : ℕ} (s : Vector ℚ m × ℚ × ℕ) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :=
  (s.1.set r.1 (s.1[r.1]+r.2), s.2.1+s.1[r.1]*r.2, s.2.2+1)

private theorem numeric_step {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) = numericStep (numeric s) r := by
  simp [numeric, numericStep, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step]

private theorem numeric_scan {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Weighted m)) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan s xs) = xs.foldl numericStep (numeric s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons r xs ih =>
    change numeric
        (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scan (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.step s r) xs) = _
    rw [ih, numeric_step]
    rfl

private theorem numeric_chargeWeight {m : ℕ} (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (gates : ℕ) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.chargeWeight s gates) = numeric s := rfl

private theorem numeric_signed_step {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (s : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.State m) (r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    numeric (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep a b u s r) = numericStep (numeric s) (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u r) := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.signedStep,
      numeric_chargeWeight, numeric_step, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.makeWeighted_value]

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

def rawKernel {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) : ℚ :=
  Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u l) (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted a b u r)

theorem runSigned_ofFn {m n : ℕ} (a b : ℚ) (u : Vector ℚ m) (w : Fin n → Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u (List.ofFn w)).value =
      (Qatlib.Concepts.ShadowModels.UStatBackend.RationalPairMedian.evaluate (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u) w).1 := by
  rw [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned_value, List.map_ofFn,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.run_value]
  rfl

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

theorem runSigned_counts {m : ℕ} (a b : ℚ) (u : Vector ℚ m)
    (xs : List (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m)) (e : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Event) :
    (Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned a b u xs).counts e = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initialCounts m e +
      xs.length*(Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.stepCounts e+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weightCounts e)+Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finishCounts e := by
  simp only [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.runSigned,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.finish, Pi.add_apply, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.scanSigned_counts, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.initial]

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

theorem rawKernel_symmetric {m : ℕ} (a b : ℚ) (u : Vector ℚ m) (l r : Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.Raw m) :
    Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u l r = Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel a b u r l := by
  by_cases h : l.1=r.1
  · simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted, h]
    ring
  · simp [Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.rawKernel,
      Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.kernel, Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision.weighted, h, Ne.symm h]

end Qatlib.Concepts.ShadowModels.UStatBackend.StreamingCollision
