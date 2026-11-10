/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.IntervalArith.IntervalOps.RationalIntervalArithmetic
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordEmitterDefs
import Qatlib.Concepts.RawChannelWord.CptpWordBound.RawChannelWord
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs

open Qatlib.Foundations.IntervalArith.IntervalOps (Interval Valid Contains unit width roundDown rounded)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)

structure Dyadic where

  mant : ℤ

  exp : ℕ
  deriving DecidableEq, Repr

namespace Dyadic

def toRat (d : Dyadic) : ℚ := d.mant / (2 : ℚ) ^ d.exp

noncomputable def toReal (d : Dyadic) : ℝ := (d.mant : ℝ) / (2 : ℝ) ^ d.exp

def neg (d : Dyadic) : Dyadic := ⟨-d.mant, d.exp⟩

def add (a b : Dyadic) : Dyadic :=
  ⟨a.mant * (2 : ℤ) ^ b.exp + b.mant * (2 : ℤ) ^ a.exp, a.exp + b.exp⟩

def sub (a b : Dyadic) : Dyadic := a.add b.neg

def mul (a b : Dyadic) : Dyadic := ⟨a.mant * b.mant, a.exp + b.exp⟩

def size (d : Dyadic) : ℕ := d.mant.natAbs.size + d.exp

end Dyadic

def cert (q : ℚ) (k : ℕ) : Interval := ⟨q - unit k, q + unit k⟩

structure RealName where

  approx : ℕ → ℚ

  timeC : ℕ

  timeD : ℕ

def RealName.clock (N : RealName) (p : ℕ) : ℕ := N.timeC * (p + 1) ^ N.timeD

def RealName.Spec (N : RealName) (x : ℝ) : Prop :=
  0 < N.timeC ∧ ∀ p : ℕ, Contains (cert (N.approx p) p) x

def RealName.const (q : ℚ) : RealName := ⟨fun _ => q, 1, 0⟩

def RealName.add (Nx Ny : RealName) : RealName :=
  ⟨fun p => Nx.approx (p + 1) + Ny.approx (p + 1),
    Nx.timeC + Ny.timeC, max Nx.timeD Ny.timeD + 1⟩

def RealName.neg (N : RealName) : RealName := ⟨fun p => -N.approx p, N.timeC, N.timeD⟩

def RealName.sub (Nx Ny : RealName) : RealName := Nx.add Ny.neg

def RealName.mul (Nx Ny : RealName) (s : ℕ) : RealName :=
  ⟨fun p => Nx.approx (p + s) * Ny.approx (p + s),
    Nx.timeC + Ny.timeC, max Nx.timeD Ny.timeD + 1⟩

def ratSqrtLo (a : ℚ) (k : ℕ) : ℚ :=
  (Nat.sqrt (Int.toNat ⌊a * (2 : ℚ) ^ (2 * k)⌋)) / (2 : ℚ) ^ k

def RealName.sqrtName (N : RealName) : RealName :=
  ⟨fun p => ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1),
    N.timeC * 5 ^ N.timeD, 2 * N.timeD + 2⟩

def RealName.divName (Nx Ny : RealName) (s : ℕ) : RealName :=
  ⟨fun p => Nx.approx (p + s) / Ny.approx (p + s),
    Nx.timeC + Ny.timeC, max Nx.timeD Ny.timeD + 1⟩

def sinPartial (a : ℚ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (-1 : ℚ) ^ k * a ^ (2 * k + 1) / (2 * k + 1).factorial

def logPartial (t : ℚ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (-1 : ℚ) ^ k * t ^ (k + 1) / (k + 1)

def SinWindow (x : ℝ) : Prop := |x| ≤ 1 / 4

def LogWindow (x : ℝ) : Prop := |x - 1| ≤ 1 / 4

def RealName.sinName (N : RealName) : RealName :=
  ⟨fun p => sinPartial (N.approx (p + 3)) (p + 2), N.timeC * 5 ^ N.timeD, N.timeD + 3⟩

def RealName.logName (N : RealName) : RealName :=
  ⟨fun p => logPartial (N.approx (p + 3) - 1) (p + 2),
    N.timeC * 5 ^ N.timeD, N.timeD + 3⟩

structure ComplexName where

  re : RealName

  im : RealName

def ComplexName.Spec (N : ComplexName) (z : ℂ) : Prop :=
  N.re.Spec z.re ∧ N.im.Spec z.im

def DivPremise (gap : ℚ) (y : ℝ) : Prop := 0 < gap ∧ (gap : ℝ) ≤ y

def SqrtPremise (x : ℝ) : Prop := 0 ≤ x

def LogPremise (x : ℝ) : Prop := 0 < x

def MagnitudeBound (B : ℚ) (x : ℝ) : Prop := 0 < B ∧ |x| ≤ (B : ℝ)

def polyBound (C D n : ℕ) : ℕ := C * (n + 1) ^ D

def intBits (n : ℤ) : Bits :=
    decide (n < 0) :: Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n.natAbs

def ratBits (r : ℚ) : Bits :=
    intBits r.num ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r.den

def dyadicBits (d : Dyadic) : Bits :=
    intBits d.mant ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d.exp

def Dyadic.inputSize (d : Dyadic) : ℕ := (dyadicBits d).length

def Clause1Claim : Prop :=

  (∃ N0 N1 : RealName, N0.Spec 0 ∧ N1.Spec 1) ∧

  (∀ a b : Dyadic,
      (a.add b).toReal = a.toReal + b.toReal ∧
      (a.sub b).toReal = a.toReal - b.toReal ∧
      (a.mul b).toReal = a.toReal * b.toReal ∧
      (a.neg).toReal = -a.toReal) ∧
  (∀ a b : Dyadic,
      (a.add b).size ≤ polyBound 2 1 (a.size + b.size) ∧
      (a.mul b).size ≤ polyBound 2 1 (a.size + b.size)) ∧

  (∀ q : ℚ, ∀ p : ℕ,
      Valid (cert q p) ∧ Valid (rounded q p) ∧ Contains (rounded q p) q ∧
      width (rounded q p) = unit p) ∧

  (∀ a b : Interval, Valid a → Valid b →
      Valid (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) ∧
      Valid (Qatlib.Foundations.IntervalArith.IntervalOps.mul a b) ∧
      (∀ x y : ℝ, Contains a x → Contains b y →
          Contains (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) (x + y)) ∧
      (∀ x y : ℝ, Contains a x → Contains b y →
          Contains (Qatlib.Foundations.IntervalArith.IntervalOps.mul a b) (x * y)) ∧
      width (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) = width a + width b) ∧

  (∀ a b : Interval, ∀ gap : ℚ, ∀ x y : ℝ,
      Valid a → Valid b → Contains a x → Contains b y → DivPremise gap y →
      ∀ c : Interval,
        Qatlib.Foundations.IntervalArith.IntervalOps.divPositive a b gap = some c →
        Contains c (x / y)) ∧
  (∀ a b : Interval, ∀ gap : ℚ, gap ≤ 0 →
      Qatlib.Foundations.IntervalArith.IntervalOps.divPositive a b gap = none) ∧

  (∀ (Nx Ny : RealName) (x y : ℝ), Nx.Spec x → Ny.Spec y →
      ∃ N : RealName, N.Spec (x + y) ∧ ∀ p : ℕ,
        Nx.clock p + Ny.clock p ≤ N.clock (p + 3)) ∧
  (∀ (Nx Ny : RealName) (x y : ℝ), Nx.Spec x → Ny.Spec y → DivPremise 1 y →
      ∃ N : RealName, N.Spec (x / y) ∧ ∀ p : ℕ,
        Nx.clock p + Ny.clock p ≤ N.clock (p + 3)) ∧
  (∀ (Nx : RealName) (x : ℝ), Nx.Spec x → SqrtPremise x →
      ∃ N : RealName, N.Spec (Real.sqrt x)) ∧
  (∀ (Nx : RealName) (x : ℝ), Nx.Spec x → LogPremise x →
      ∃ N : RealName, N.Spec (Real.log x)) ∧
  (∀ (Nx : RealName) (x : ℝ), Nx.Spec x →
      ∃ N : RealName, N.Spec (Real.sin x)) ∧

  (∃ (C D : ℕ) (f : Bits → Bits), 0 < C ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ComputesAt f
        (fun bs => polyBound C D bs.length) (fun bs => polyBound C D bs.length) ∧
      ∀ a b : Dyadic,
        f (dyadicBits a ++ dyadicBits b) = dyadicBits (a.add b)) ∧

  (∀ p : ℕ, Contains (cert (0 : ℚ) p) 0 ∧ Contains (cert (1 : ℚ) p) 1 ∧
      Contains (cert (-1 : ℚ) p) (-1)) ∧
  (∀ Nre Nim : RealName, ∀ x y : ℝ, Nre.Spec x → Nim.Spec y →
      (⟨Nre, Nim⟩ : ComplexName).Spec ⟨x, y⟩) ∧
  (∀ gap : ℚ, 0 < gap → DivPremise gap (gap : ℝ)) ∧
  (¬ SqrtPremise (-1 : ℝ) ∧ ¬ LogPremise (0 : ℝ))

def LayerSound {D : ℕ} (s : Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D) : Prop :=
  0 ≤ s.error ∧
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondDistance s.actual.map s.ideal.map ≤
      ENNReal.ofReal s.error

noncomputable def totalAccount {D : ℕ}
    (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) (readClock : ℝ) : ℝ :=
  Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p + readClock

def Clause2Claim : Prop :=

  (∀ (D : ℕ), Qatlib.Concepts.RawChannelWord.CptpWordBound.budget
      ([] : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) = 0) ∧
  (∀ (D : ℕ) (p q : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)),
      Qatlib.Concepts.RawChannelWord.CptpWordBound.budget (p ++ q) =
        Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p +
          Qatlib.Concepts.RawChannelWord.CptpWordBound.budget q) ∧

  (∀ (D : ℕ) (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)),
      (∀ s ∈ p, LayerSound s) →
        Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondDistance
          (Qatlib.Concepts.RawChannelWord.CptpWordBound.actualWord p).map
          (Qatlib.Concepts.RawChannelWord.CptpWordBound.idealWord p).map ≤
          ENNReal.ofReal (Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p)) ∧

  (∀ q : ℚ, ∀ p : ℕ, (width (cert q p) : ℚ) = 2 * unit p) ∧

  (∃ (D : ℕ) (F : ℕ → Matrix (Fin D) (Fin D) ℂ →
        List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)),
      ∀ (pub : ℕ) (u v : Matrix (Fin D) (Fin D) ℂ),
        (F pub u).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.error =
          (F pub v).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.error) ∧

  (∀ (D : ℕ) (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D))
      (readClock : ℝ), 0 ≤ readClock →
      Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p ≤ totalAccount p readClock)

structure AccessCap where

  adj : Bool

  ctrl : Bool

  addrWidth : ℕ
  deriving DecidableEq, Repr

def AccessCap.inverseGranted (c : AccessCap) : Option Unit :=
  if c.adj then some () else none

def AccessCap.controlGranted (c : AccessCap) : Option Unit :=
  if c.ctrl then some () else none

def FairCoinLaw (p : Bool → ℝ) : Prop :=
  p true = 1 / 2 ∧ p false = 1 / 2 ∧ ∀ b : Bool, 0 ≤ p b

def Clause3Claim : Prop :=

  (Nat.gcd 12 18 = 6 ∧ (3 * 4) % 5 = 2 ∧ (2 ^ 3) % 5 = 3 ∧ 2 + 3 = 5) ∧

  (∃ p : Bool → ℝ, FairCoinLaw p) ∧

  (∀ (c : AccessCap), c.adj = false → c.inverseGranted = none) ∧
  (∀ (c : AccessCap), c.ctrl = false → c.controlGranted = none) ∧

  (∃ (C D : ℕ) (f : Bits → Bits), 0 < C ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ComputesAt f
        (fun bs => polyBound C D bs.length) (fun bs => polyBound C D bs.length) ∧
      ∀ a b : ℕ,
        f (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits b) =
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (Nat.gcd a b))

def Clause1V2SqrtLift : Prop :=
  ∀ (N : RealName) (x : ℝ), N.Spec x → SqrtPremise x →
    N.sqrtName.Spec (Real.sqrt x) ∧
      ∀ p : ℕ, N.clock (2 * p + 4) ≤ N.sqrtName.clock p

def Clause1V2DivLift : Prop :=
  ∀ (Nx Ny : RealName) (s B : ℕ) (x y : ℝ) (gap : ℚ),
    Nx.Spec x → Ny.Spec y → DivPremise gap y →
    MagnitudeBound B x → MagnitudeBound B y →
    (2 : ℚ) ≤ gap * 2 ^ s → (4 : ℚ) * B ≤ gap ^ 2 * 2 ^ s →
    (Nx.divName Ny s).Spec (x / y) ∧
      ∀ p : ℕ, Nx.clock p + Ny.clock p ≤ (Nx.divName Ny s).clock (p + 3)

def Clause1V2SinLift : Prop :=
  ∀ (N : RealName) (x : ℝ), N.Spec x → SinWindow x →
    N.sinName.Spec (Real.sin x) ∧
      ∀ p : ℕ, N.clock p ≤ N.sinName.clock (p + 2)

def Clause1V2LogLift : Prop :=
  ∀ (N : RealName) (x : ℝ), N.Spec x → LogWindow x →
    N.logName.Spec (Real.log x) ∧
      ∀ p : ℕ, N.clock p ≤ N.logName.clock (p + 2)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs
