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

/-!
# Definitions for finite-precision arithmetic and accounting

This module defines dyadic representations, rational approximation names for real and complex
values, interval certificates, arithmetic name constructors, and explicit domain premises. A
`RealName` carries an approximation function and polynomial clock parameters; its semantic
specification requires interval containment and a positive clock coefficient.

The module also defines proposition bundles for numerical arithmetic, channel error budgets,
finite access capabilities, and elementary arithmetic computations. These definitions state
requirements for later analysis. The computational setting has general background in
[KitaevShenVyalyi2002], while the representations and proposition bundles are specific to this
development.

## Main statements

* `Dyadic`, `RealName`, and `ComplexName` describe numerical data and their interpretations.
* `Clause1Claim`, `Clause2Claim`, and `Clause3Claim` collect arithmetic, error-accounting, and
  access requirements.
* `Clause1V2SqrtLift`, `Clause1V2DivLift`, `Clause1V2SinLift`, and `Clause1V2LogLift` state
  correctness and clock comparisons for the named constructors under their domain and precision
  hypotheses.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002] provides general background on finite
  classical and quantum computation.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs

open Qatlib.Foundations.IntervalArith.IntervalOps (Interval Valid Contains unit width roundDown rounded)
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits)

/-- A dyadic representation with integer mantissa `mant` and natural denominator exponent `exp`,
representing `mant / 2^exp`. -/
structure Dyadic where

  mant : ℤ

  exp : ℕ
  deriving DecidableEq, Repr

namespace Dyadic

/-- Interprets a dyadic representation as the rational number `d.mant / 2^d.exp`. -/
def toRat (d : Dyadic) : ℚ := d.mant / (2 : ℚ) ^ d.exp

/-- Interprets a dyadic representation as the real number `d.mant / 2^d.exp`. -/
noncomputable def toReal (d : Dyadic) : ℝ := (d.mant : ℝ) / (2 : ℝ) ^ d.exp

/-- Negates the mantissa of a dyadic representation and preserves its exponent. -/
def neg (d : Dyadic) : Dyadic := ⟨-d.mant, d.exp⟩

/-- Adds dyadic representations by cross-multiplying their mantissas by powers of two and using
exponent `a.exp + b.exp`. -/
def add (a b : Dyadic) : Dyadic :=
  ⟨a.mant * (2 : ℤ) ^ b.exp + b.mant * (2 : ℤ) ^ a.exp, a.exp + b.exp⟩

/-- Subtracts dyadic representations by adding the negation of the second operand. -/
def sub (a b : Dyadic) : Dyadic := a.add b.neg

/-- Multiplies dyadic representations by multiplying their mantissas and adding their exponents. -/
def mul (a b : Dyadic) : Dyadic := ⟨a.mant * b.mant, a.exp + b.exp⟩

/-- Measures a dyadic representation by the binary size of the absolute mantissa plus the value
of its exponent. -/
def size (d : Dyadic) : ℕ := d.mant.natAbs.size + d.exp

end Dyadic

/-- The rational interval centered at `q` with radius `unit k = 1 / 2^k`. -/
def cert (q : ℚ) (k : ℕ) : Interval := ⟨q - unit k, q + unit k⟩

/-- A rational approximation function indexed by precision, together with a coefficient and
degree for its associated polynomial clock. Correctness is expressed separately by
`RealName.Spec`. -/
structure RealName where

  approx : ℕ → ℚ

  timeC : ℕ

  timeD : ℕ

/-- The polynomial clock `N.timeC * (p + 1)^N.timeD` associated with precision `p`. -/
def RealName.clock (N : RealName) (p : ℕ) : ℕ := N.timeC * (p + 1) ^ N.timeD

/-- Requires a positive clock coefficient and containment of `x` in `cert (N.approx p) p` at
every precision `p`. -/
def RealName.Spec (N : RealName) (x : ℝ) : Prop :=
  0 < N.timeC ∧ ∀ p : ℕ, Contains (cert (N.approx p) p) x

/-- The constant rational approximation name for `q`, with clock coefficient one and degree
zero. -/
def RealName.const (q : ℚ) : RealName := ⟨fun _ => q, 1, 0⟩

/-- Forms an addition name from the sum of the two approximations at precision `p + 1`. Its
clock coefficient is the sum of the coefficients and its degree is one more than their
maximum degree. -/
def RealName.add (Nx Ny : RealName) : RealName :=
  ⟨fun p => Nx.approx (p + 1) + Ny.approx (p + 1),
    Nx.timeC + Ny.timeC, max Nx.timeD Ny.timeD + 1⟩

/-- Negates every approximation of `N` while preserving its clock parameters. -/
def RealName.neg (N : RealName) : RealName := ⟨fun p => -N.approx p, N.timeC, N.timeD⟩

/-- Forms a subtraction name by adding the negated second name to the first. -/
def RealName.sub (Nx Ny : RealName) : RealName := Nx.add Ny.neg

/-- Forms a multiplication name by multiplying both approximations at precision `p + s`. Its
clock coefficient is the sum of the coefficients and its degree is one more than their
maximum degree. -/
def RealName.mul (Nx Ny : RealName) (s : ℕ) : RealName :=
  ⟨fun p => Nx.approx (p + s) * Ny.approx (p + s),
    Nx.timeC + Ny.timeC, max Nx.timeD Ny.timeD + 1⟩

/-- Computes a dyadic square-root approximation by flooring `a * 2^(2*k)`, converting to a
natural number, taking its integer square root, and dividing by `2^k`. -/
def ratSqrtLo (a : ℚ) (k : ℕ) : ℚ :=
  (Nat.sqrt (Int.toNat ⌊a * (2 : ℚ) ^ (2 * k)⌋)) / (2 : ℚ) ^ k

/-- Forms a square-root name by clipping the approximation at precision `2 * p + 4` to zero and
applying `ratSqrtLo` at precision `p + 1`. Its clock parameters are `N.timeC * 5^N.timeD`
and `2 * N.timeD + 2`. -/
def RealName.sqrtName (N : RealName) : RealName :=
  ⟨fun p => ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1),
    N.timeC * 5 ^ N.timeD, 2 * N.timeD + 2⟩

/-- Forms a division name by dividing both approximations at precision `p + s`. Its clock
coefficient is the sum of the coefficients and its degree is one more than their maximum
degree. -/
def RealName.divName (Nx Ny : RealName) (s : ℕ) : RealName :=
  ⟨fun p => Nx.approx (p + s) / Ny.approx (p + s),
    Nx.timeC + Ny.timeC, max Nx.timeD Ny.timeD + 1⟩

/-- The first `K` rational terms of the sine series at `a`, summing `(-1)^k * a^(2*k + 1) / (2*k
+ 1)!`. -/
def sinPartial (a : ℚ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (-1 : ℚ) ^ k * a ^ (2 * k + 1) / (2 * k + 1).factorial

/-- The first `K` rational terms of the series for `log (1 + t)`, summing `(-1)^k * t^(k + 1) /
(k + 1)`. -/
def logPartial (t : ℚ) (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, (-1 : ℚ) ^ k * t ^ (k + 1) / (k + 1)

/-- The sine approximation window given by `|x| <= 1 / 4`. -/
def SinWindow (x : ℝ) : Prop := |x| ≤ 1 / 4

/-- The logarithm approximation window given by `|x - 1| <= 1 / 4`. -/
def LogWindow (x : ℝ) : Prop := |x - 1| ≤ 1 / 4

/-- Forms a sine name using `p + 2` series terms at the approximation `N.approx (p + 3)`. Its
clock parameters are `N.timeC * 5^N.timeD` and `N.timeD + 3`. -/
def RealName.sinName (N : RealName) : RealName :=
  ⟨fun p => sinPartial (N.approx (p + 3)) (p + 2), N.timeC * 5 ^ N.timeD, N.timeD + 3⟩

/-- Forms a logarithm name using `p + 2` series terms at `N.approx (p + 3) - 1`. Its clock
parameters are `N.timeC * 5^N.timeD` and `N.timeD + 3`. -/
def RealName.logName (N : RealName) : RealName :=
  ⟨fun p => logPartial (N.approx (p + 3) - 1) (p + 2),
    N.timeC * 5 ^ N.timeD, N.timeD + 3⟩

/-- A pair of real approximation names for the real and imaginary parts of a complex number. -/
structure ComplexName where

  re : RealName

  im : RealName

/-- Requires the real and imaginary names to satisfy their specifications for the corresponding
components of `z`. -/
def ComplexName.Spec (N : ComplexName) (z : ℂ) : Prop :=
  N.re.Spec z.re ∧ N.im.Spec z.im

/-- Requires a strictly positive rational `gap` whose real value is at most the divisor `y`. -/
def DivPremise (gap : ℚ) (y : ℝ) : Prop := 0 < gap ∧ (gap : ℝ) ≤ y

/-- The nonnegativity condition `0 <= x` for square-root approximation. -/
def SqrtPremise (x : ℝ) : Prop := 0 ≤ x

/-- The strict positivity condition `0 < x` for logarithm approximation. -/
def LogPremise (x : ℝ) : Prop := 0 < x

/-- Requires a strictly positive rational bound `B` with `|x| <= B` after coercion to the reals. -/
def MagnitudeBound (B : ℚ) (x : ℝ) : Prop := 0 < B ∧ |x| ≤ (B : ℝ)

/-- The natural-number polynomial bound `C * (n + 1)^D`. -/
def polyBound (C D n : ℕ) : ℕ := C * (n + 1) ^ D

/-- Encodes an integer as a bit indicating negativity followed by `natBits` of its absolute
value. -/
def intBits (n : ℤ) : Bits :=
    decide (n < 0) :: Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n.natAbs

/-- Encodes a rational by concatenating the signed integer encoding of its numerator with
`natBits` of its denominator. -/
def ratBits (r : ℚ) : Bits :=
    intBits r.num ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits r.den

/-- Encodes a dyadic representation by concatenating the signed mantissa encoding with `natBits`
of its exponent. -/
def dyadicBits (d : Dyadic) : Bits :=
    intBits d.mant ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits d.exp

/-- The length of the bit list produced by `dyadicBits d`. -/
def Dyadic.inputSize (d : Dyadic) : ℕ := (dyadicBits d).length

/-- Collects requirements for dyadic arithmetic and size bounds, interval certificates and
operations, real and complex approximation names, and domain premises. It also requires a
bit function implementing the specified dyadic addition encoding with polynomial time and
space bounds. -/
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

/-- Requires a nonnegative layer error that bounds the diamond distance between the layer's
actual and ideal channel maps via `ENNReal.ofReal`. -/
def LayerSound {D : ℕ} (s : Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D) : Prop :=
  0 ≤ s.error ∧
    Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondDistance s.actual.map s.ideal.map ≤
      ENNReal.ofReal s.error

/-- Adds the real input-reading charge `readClock` to the accumulated approximation budget of
the layer list `p`. -/
noncomputable def totalAccount {D : ℕ}
    (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) (readClock : ℝ) : ℝ :=
  Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p + readClock

/-- Collects additive channel budget identities, composition of sound layer errors, certificate
width, and monotonicity after adding a nonnegative reading charge. It also requires a
layer-list family whose error sequence, for fixed public parameter, is independent of the
matrix argument. -/
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

/-- Finite access-capability data consisting of adjoint and controlled-operation flags together
with an address width. -/
structure AccessCap where

  adj : Bool

  ctrl : Bool

  addrWidth : ℕ
  deriving DecidableEq, Repr

/-- Returns `some ()` exactly when the adjoint-access flag is true, and `none` otherwise. -/
def AccessCap.inverseGranted (c : AccessCap) : Option Unit :=
  if c.adj then some () else none

/-- Returns `some ()` exactly when the controlled-access flag is true, and `none` otherwise. -/
def AccessCap.controlGranted (c : AccessCap) : Option Unit :=
  if c.ctrl then some () else none

/-- Requires probability `1 / 2` for each Boolean outcome and nonnegative values for both
outcomes. -/
def FairCoinLaw (p : Bool → ℝ) : Prop :=
  p true = 1 / 2 ∧ p false = 1 / 2 ∧ ∀ b : Bool, 0 ≤ p b

/-- Collects concrete arithmetic identities, existence of a fair Boolean law, and denial of
inverse or controlled access when the corresponding flag is false. It also requires a bit
function implementing the specified concatenated-input greatest-common-divisor encoding with
polynomial time and space bounds. -/
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

/-- Requires `sqrtName` to name `Real.sqrt x` for every specified nonnegative input, with
`N.clock (2 * p + 4) <= N.sqrtName.clock p` at every precision. -/
def Clause1V2SqrtLift : Prop :=
  ∀ (N : RealName) (x : ℝ), N.Spec x → SqrtPremise x →
    N.sqrtName.Spec (Real.sqrt x) ∧
      ∀ p : ℕ, N.clock (2 * p + 4) ≤ N.sqrtName.clock p

/-- Requires `divName` to name `x / y` under the input specifications, positive divisor gap,
common magnitude bound `B`, and shift conditions `2 <= gap * 2^s` and `4 * B <= gap^2 *
2^s`. It also requires the sum of input clocks at `p` to be bounded by the output clock at
`p + 3`. -/
def Clause1V2DivLift : Prop :=
  ∀ (Nx Ny : RealName) (s B : ℕ) (x y : ℝ) (gap : ℚ),
    Nx.Spec x → Ny.Spec y → DivPremise gap y →
    MagnitudeBound B x → MagnitudeBound B y →
    (2 : ℚ) ≤ gap * 2 ^ s → (4 : ℚ) * B ≤ gap ^ 2 * 2 ^ s →
    (Nx.divName Ny s).Spec (x / y) ∧
      ∀ p : ℕ, Nx.clock p + Ny.clock p ≤ (Nx.divName Ny s).clock (p + 3)

/-- Requires `sinName` to name `Real.sin x` for every specified input in `SinWindow`, with the
input clock at `p` bounded by the output clock at `p + 2`. -/
def Clause1V2SinLift : Prop :=
  ∀ (N : RealName) (x : ℝ), N.Spec x → SinWindow x →
    N.sinName.Spec (Real.sin x) ∧
      ∀ p : ℕ, N.clock p ≤ N.sinName.clock (p + 2)

/-- Requires `logName` to name `Real.log x` for every specified input in `LogWindow`, with the
input clock at `p` bounded by the output clock at `p + 2`. -/
def Clause1V2LogLift : Prop :=
  ∀ (N : RealName) (x : ℝ), N.Spec x → LogWindow x →
    N.logName.Spec (Real.log x) ∧
      ∀ p : ℕ, N.clock p ≤ N.logName.clock (p + 2)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs
