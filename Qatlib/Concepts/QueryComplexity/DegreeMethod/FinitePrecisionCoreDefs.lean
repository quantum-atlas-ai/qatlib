/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Finite-precision inputs and classical backend contracts

This module defines finite bit encodings, computable names for real and complex numbers,
numerical error certificates, and explicit time and space requirements for classical backends.
It also gives register-program semantics with prescribed coin records and access contracts,
together with TM0 and three-stack TM2 compilation specifications. The classical computation
framework in [KitaevShenVyalyi2002] provides background for these local definitions.

The consumer predicates record numerical and classical postprocessing requirements for QPE, HHL,
LCU, Shor, Simon, and QFT interfaces; they are specifications rather than constructions of
machines satisfying them. Parameter serialization and input costs are defined explicitly, so the
precise information supplied to a machine can be inspected independently of a correctness
requirement.

## Main statements

* `CertifiesApproximation` and `FiniteInputBoundary` specify the accepted numerical inputs.
* `BackendSound`, `RunRealizes`, and `BackendCostOk` specify numerical outputs, accuracy, and
  resource bounds.
* `TM0Compiled`, `TM2Compiled`, `TM0LawPreserved`, and `TM2LawPreserved` specify output and
  distribution preservation.
* `AccessRestrictionPreserved` and the consumer predicates state the access and application
  requirements.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs

set_option autoImplicit false

noncomputable section

open Turing

/-- Encodes a natural number as a run of `true` bits of length `n.bits.length`, a `false`
separator, and the binary digits `n.bits`. -/
def natBits (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- Encodes an integer by a bit indicating negativity followed by `natBits` of its absolute
value. -/
def intBits (n : ℤ) : List Bool :=
  decide (n < 0) :: natBits n.natAbs

/-- Encodes a rational number by concatenating the signed encoding of its numerator and the
natural-number encoding of its denominator. -/
def ratBits (q : ℚ) : List Bool :=
  intBits q.num ++ natBits q.den

/-- Reads a finite Boolean word as an optional-bit tape, returning `some` of an in-range bit and
`none` beyond the word. -/
def tapeAt (l : List Bool) (i : ℕ) : Option Bool :=
  (l.map some).getD i none

/-- Requires the tape starting at the current head and extending right to equal `ratBits q`,
with blank cells after that finite encoding. -/
def RatOnTape {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ) (q : ℚ) : Prop :=
  ∀ i : ℕ, cfg.Tape.right₀.nth i = tapeAt (ratBits q) i

/-- Requires the tape starting at the current head and extending right to contain the
concatenated encodings of `qs`, followed by blanks. -/
def RatsOnTape {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ)
    (qs : List ℚ) : Prop :=
  ∀ i : ℕ, cfg.Tape.right₀.nth i = tapeAt (qs.flatMap ratBits) i

/-- Requires the tape starting at the current head and extending right to contain the
concatenated `natBits` encodings of `ns`, followed by blanks. -/
def NatsOnTape {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ)
    (ns : List ℕ) : Prop :=
  ∀ i : ℕ, cfg.Tape.right₀.nth i = tapeAt (ns.flatMap natBits) i

/-- Counts the nonblank entries of an optional-bit list, namely the entries unequal to `none`. -/
def blankCells (xs : List (Option Bool)) : ℕ :=
  (xs.filter (fun x => x ≠ none)).length

/-- Filtering nonblank cells from any finite repetition of the default optional bit yields the
empty list. -/
theorem filter_ne_none_replicate (n : ℕ) :
    (List.replicate n (default : Option Bool)).filter (fun x => x ≠ none) = [] := by
  apply List.filter_eq_nil_iff.2
  intro x hx
  obtain ⟨_, rfl⟩ := List.mem_replicate.1 hx
  show ¬(decide ((default : Option Bool) ≠ none) = true)
  decide

/-- Counts nonblank cells in a `ListBlank` by lifting `blankCells`; appending default blank
cells does not change the count. -/
def blankUsedCells (l : Turing.ListBlank (Option Bool)) : ℕ :=
  Turing.ListBlank.liftOn l blankCells (fun l₁ l₂ h => by
    obtain ⟨n, rfl⟩ := h
    show blankCells l₁ = blankCells (l₁ ++ List.replicate n default)
    unfold blankCells
    rw [List.filter_append, filter_ne_none_replicate, List.append_nil])

/-- Measures tape space as the number of nonblank cells strictly left and right of the head,
plus one for the head cell regardless of its contents. -/
def tapeSpace (T : Turing.Tape (Option Bool)) : ℕ :=
  blankUsedCells T.left + 1 + blankUsedCells T.right

/-- Measures a TM0 configuration by applying `tapeSpace` to its tape. -/
def cfgSpace {Λ : Type} [Inhabited Λ] (cfg : Turing.TM0.Cfg (Option Bool) Λ) : ℕ :=
  tapeSpace cfg.Tape

/-- Takes the maximum configuration-space measure over times zero through `t`, assigning zero to
an absent configuration. -/
def peakSpaceAfter {Λ : Type} [Inhabited Λ] (M : Turing.TM0.Machine (Option Bool) Λ)
    (input : List (Option Bool)) (t : ℕ) : ℕ :=
  (List.range (t + 1)).foldl
    (fun acc s => max acc ((BitMachineAfter M input s).elim 0 cfgSpace)) 0

/-- Interprets the integer numerator `m` at precision `k` as the real dyadic number `m / 2^k`. -/
def dyadicVal (k : ℕ) (m : ℤ) : ℝ :=
  (m : ℝ) / (2 ^ k : ℝ)

/-- Requires the dyadic value `m / 2^k` to approximate `x` with absolute error at most `2^(-k)`. -/
def RoundedDyadic (k : ℕ) (m : ℤ) (x : ℝ) : Prop :=
  |dyadicVal k m - x| ≤ ((2 : ℝ)⁻¹) ^ k

/-- Certifies that `x` lies between the rational endpoints `lo` and `hi` and that their width is
at most `2 * 2^(-k)`. -/
def IntervalCert (k : ℕ) (lo hi : ℚ) (x : ℝ) : Prop :=
  (lo : ℝ) ≤ x ∧ x ≤ hi ∧ (hi - lo : ℝ) ≤ 2 * ((2 : ℝ)⁻¹) ^ k

/-- Stores a TM0 approximation machine with state type `Fin (states + 1)` and a declared size.
Approximation correctness and any relationship between the size and machine description are
separate from this structure. -/
structure FiniteRealInput where

  states : ℕ

  approx : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

  size : ℕ

/-- Requires the named machine, on each encoded precision `k`, to reach a halting configuration
containing a rational approximation to `x` within `2^(-k)`. No time or space bound is
imposed. -/
def CertifiesApproximation (d : FiniteRealInput) (x : ℝ) : Prop :=
  ∀ k : ℕ, ∃ t q cfg,
    BitMachineAfter d.approx ((natBits k).map some) t = some cfg ∧
    Turing.TM0.step d.approx cfg = none ∧
    RatOnTape cfg q ∧
    |(q : ℝ) - x| ≤ ((2 : ℝ)⁻¹) ^ k

/-- States that a real number has a finite machine name satisfying `CertifiesApproximation` at
every natural precision. -/
def ComputablyApproximable (x : ℝ) : Prop :=
  ∃ d : FiniteRealInput, CertifiesApproximation d x

/-- Defines an accepted finite real input to be a computably approximable real number. -/
def IsFiniteReal (x : ℝ) : Prop :=
  ComputablyApproximable x

/-- Stores separate finite machine names for the real and imaginary components of a complex
input. -/
structure FiniteComplexInput where
  re : FiniteRealInput
  im : FiniteRealInput

/-- Requires the two component names to certify rational approximations to the real and
imaginary parts of `z`, respectively. -/
def CertifiesComplexApproximation (d : FiniteComplexInput) (z : ℂ) : Prop :=
  CertifiesApproximation d.re z.re ∧ CertifiesApproximation d.im z.im

/-- Defines an accepted finite complex input by computable approximability of both its real and
imaginary parts. -/
def IsFiniteComplex (z : ℂ) : Prop :=
  ComputablyApproximable z.re ∧ ComputablyApproximable z.im

/-- Collects the equivalences identifying accepted real and complex inputs with computably
approximable components, together with exclusion of nonapproximable reals. -/
def FiniteInputBoundary : Prop :=
  (∀ x : ℝ, IsFiniteReal x ↔ ComputablyApproximable x) ∧
  (∀ z : ℂ, IsFiniteComplex z ↔ (ComputablyApproximable z.re ∧ ComputablyApproximable z.im)) ∧
  (∀ x : ℝ, ¬ ComputablyApproximable x → ¬ IsFiniteReal x)

/-- Lists the real arithmetic operations covered by the backend interface: addition,
multiplication, division, square root, sine, cosine, arctangent, and logarithm. -/
inductive ArithOp where
  | add
  | mul
  | div
  | sqrt
  | sin
  | cos
  | arctan
  | log
  deriving DecidableEq, Repr

/-- Assigns operation tags zero through seven to addition, multiplication, division, square
root, sine, cosine, arctangent, and logarithm, in that order. -/
def ArithOp.code : ArithOp → ℕ
  | .add => 0
  | .mul => 1
  | .div => 2
  | .sqrt => 3
  | .sin => 4
  | .cos => 5
  | .arctan => 6
  | .log => 7

/-- Evaluates an arithmetic operation on real inputs using the corresponding real function.
Unary operations use `x` and ignore `y`. -/
noncomputable def ArithOpValue (op : ArithOp) (x y : ℝ) : ℝ :=
  match op with
  | .add => x + y
  | .mul => x * y
  | .div => x / y
  | .sqrt => Real.sqrt x
  | .sin => Real.sin x
  | .cos => Real.cos x
  | .arctan => Real.arctan x
  | .log => Real.log x

/-- Specifies a `2^(-gap)` lower bound on the denominator magnitude for division and on `x` for
logarithms, and nonnegativity of `x` for square roots. All other operations have the premise
`True`. -/
def OpPremise (op : ArithOp) (x y : ℝ) (gap : ℕ) : Prop :=
  match op with
  | .add | .mul | .sin | .cos | .arctan => True
  | .div => ((2 : ℝ)⁻¹) ^ gap ≤ |y|
  | .sqrt => 0 ≤ x
  | .log => ((2 : ℝ)⁻¹) ^ gap ≤ x

/-- States that every operation premise is exactly its displayed domain or separation condition,
with no additional conditions for the remaining operations. -/
def PremisesExplicit : Prop :=
  ∀ (op : ArithOp) (x y : ℝ) (gap : ℕ),
    OpPremise op x y gap ↔
      match op with
      | .add | .mul | .sin | .cos | .arctan => True
      | .div => ((2 : ℝ)⁻¹) ^ gap ≤ |y|
      | .sqrt => 0 ≤ x
      | .log => ((2 : ℝ)⁻¹) ^ gap ≤ x

/-- Serializes the operation tag, target precision, gap parameter, and two rational arguments,
then embeds each bit as a nonblank tape symbol. -/
def ArithOpInput (op : ArithOp) (k gap : ℕ) (r1 r2 : ℚ) : List (Option Bool) :=
  ((natBits op.code ++ natBits k ++ natBits gap ++ ratBits r1 ++ ratBits r2).map some)

/-- Stores a TM0 machine for each arithmetic operation, all using the same finite state type
determined by `states`. -/
structure ArithBackend where
  states : ℕ
  run : ArithOp → Turing.TM0.Machine (Option Bool) (Fin (states + 1))

/-- Requires each operation machine, given rational inputs within `2^(-(k + 1))` of admissible
real inputs, to halt with a dyadic approximation of error at most `2^(-k)` and its
surrounding interval certificate. Time and peak space must each be at most `C * (1 +
input.length + gap + k)^D + C`. -/
def BackendSound (be : ArithBackend) (C D : ℕ) : Prop :=
  ∀ (op : ArithOp) (x y : ℝ) (gap k : ℕ) (r1 r2 : ℚ),
    OpPremise op x y gap →
    |(r1 : ℝ) - x| ≤ ((2 : ℝ)⁻¹) ^ (k + 1) →
    |(r2 : ℝ) - y| ≤ ((2 : ℝ)⁻¹) ^ (k + 1) →
    let input := ArithOpInput op k gap r1 r2
    ∃ (t : ℕ) (m : ℤ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (be.states + 1))),
      BitMachineAfter (be.run op) input t = some cfg ∧
      Turing.TM0.step (be.run op) cfg = none ∧
      RatOnTape cfg ((m : ℚ) / (2 ^ k : ℚ)) ∧
      RoundedDyadic k m (ArithOpValue op x y) ∧
      IntervalCert k ((m : ℚ) / (2 ^ k : ℚ) - (2 ^ k : ℚ)⁻¹)
        ((m : ℚ) / (2 ^ k : ℚ) + (2 ^ k : ℚ)⁻¹) (ArithOpValue op x y) ∧
      t ≤ C * (1 + input.length + gap + k) ^ D + C ∧
      peakSpaceAfter (be.run op) input t ≤ C * (1 + input.length + gap + k) ^ D + C

/-- Classifies numerical parameters as phases, rotations, preparation coefficients, or spectral
gaps. -/
inductive NumericalKind where
  | phase
  | rotation
  | prepareCoeff
  | spectralGap
  deriving DecidableEq, Repr

/-- Assigns tags zero through three to phases, rotations, preparation coefficients, and spectral
gaps, respectively. -/
def NumericalKind.code : NumericalKind → ℕ
  | .phase => 0
  | .rotation => 1
  | .prepareCoeff => 2
  | .spectralGap => 3

/-- Stores a numerical parameter's kind, finite real machine name, and natural gap parameter. -/
structure NumericalParam where
  kind : NumericalKind
  name : FiniteRealInput
  gap : ℕ

/-- States that every numerical parameter has one of the four constructors of `NumericalKind`. -/
def NumericalKindsComplete : Prop :=
  ∀ p : NumericalParam,
    p.kind = NumericalKind.phase ∨ p.kind = NumericalKind.rotation ∨
    p.kind = NumericalKind.prepareCoeff ∨ p.kind = NumericalKind.spectralGap

/-- Stores a word length, a real amplification factor and parameter list for each position, and
a target error `ε`. The structure itself imposes no sign or accuracy conditions. -/
structure SameWordInstance where
  L : ℕ
  amplification : Fin L → ℝ
  params : Fin L → List NumericalParam
  ε : ℝ

/-- Sums `p.name.size + p.gap` over all parameter occurrences at all word positions. This is a
declared input cost rather than the length of `backendInput`. -/
def inputReadCost (inst : SameWordInstance) : ℕ :=
  (Finset.univ.sum fun i : Fin inst.L =>
    (inst.params i).foldl (fun acc p => acc + p.name.size + p.gap) 0)

/-- Sums pairwise products of amplification factors and error values, truncating at the shorter
list through `zipWith`. -/
def accumulatedWordError (amps : List ℝ) (deltas : List ℝ) : ℝ :=
  (amps.zipWith (· * ·) deltas).sum

/-- Sums the word's amplification factors multiplied by the common local error `2^(-k)`. -/
def amplifiedWordError (inst : SameWordInstance) (k : ℕ) : ℝ :=
  accumulatedWordError (List.ofFn inst.amplification)
    (List.replicate inst.L (((2 : ℝ)⁻¹) ^ k))

/-- Collects total input cost, word length, summed amplification, maximum gap parameter, and
target error for selecting a precision. -/
structure BackendParams where
  totalBits : ℕ
  length : ℕ
  ampSum : ℝ
  gap : ℕ
  ε : ℝ

/-- Extracts a word instance's input cost, length, amplification sum, target error, and maximum
parameter gap, using zero when there are no gaps. -/
noncomputable def paramsOf (inst : SameWordInstance) : BackendParams where
  totalBits := inputReadCost inst
  length := inst.L
  ampSum := (Finset.univ.sum fun i : Fin inst.L => inst.amplification i)
  gap := (Finset.univ.sup fun i : Fin inst.L =>
    ((inst.params i).foldl (fun acc p => max acc p.gap) 0))
  ε := inst.ε

/-- The type of functions choosing a natural precision from aggregated backend parameters. -/
def PrecisionChoice : Type := BackendParams → ℕ

/-- Stores a TM0 backend machine and the natural number determining its finite state type. -/
structure BackendRun where
  states : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

/-- Encodes a parameter's kind tag, declared name size, gap, and requested precision. The
approximation machine stored in the name is not serialized here. -/
def paramBits (k : ℕ) (p : NumericalParam) : List Bool :=
  natBits p.kind.code ++ natBits p.name.size ++ natBits p.gap ++ natBits k

/-- Encodes the word length and precision followed by `paramBits` for every parameter in
word-position order, with all bits mapped to nonblank tape symbols. -/
def backendInput (inst : SameWordInstance) (k : ℕ) : List (Option Bool) :=
  let paramWord := (List.ofFn fun i : Fin inst.L => (inst.params i).flatMap (paramBits k)).flatten
  ((natBits inst.L ++ natBits k ++ paramWord).map some)

/-- Requires the backend to halt on `backendInput inst k` with a rational list matching all
parameter occurrences in order, each within `2^(-k)` of its assigned value. The requirement
ranges over every value assignment certified by the parameter names and imposes no resource
bound. -/
def RunRealizes (r : BackendRun) (inst : SameWordInstance) (k : ℕ) : Prop :=
  ∀ (val : NumericalParam → ℝ),
    (∀ (i : Fin inst.L) (p : NumericalParam), p ∈ inst.params i →
      CertifiesApproximation p.name (val p)) →
    ∃ (t : ℕ) (qs : List ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine (backendInput inst k) t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatsOnTape cfg qs ∧
      List.Forall₂ (fun (q : ℚ) (p : NumericalParam) =>
        |(q : ℝ) - val p| ≤ ((2 : ℝ)⁻¹) ^ k)
        qs ((List.ofFn fun i : Fin inst.L => inst.params i).flatten)

/-- Requires runtime `t` to cover the declared input-read cost and to be at most `C * (1 +
inputReadCost inst + inst.L + (paramsOf inst).gap + k)^D + C`. -/
def BackendCostOk (inst : SameWordInstance) (k t : ℕ) (C D : ℕ) : Prop :=
  inputReadCost inst ≤ t ∧
  t ≤ C * (1 + inputReadCost inst + inst.L + (paramsOf inst).gap + k) ^ D + C

/-- States that every runtime satisfying `BackendCostOk` is at least the instance's declared
input-read cost. -/
def InputReadCostCharged : Prop :=
  ∀ (inst : SameWordInstance) (k t C D : ℕ),
    BackendCostOk inst k t C D → inputReadCost inst ≤ t

/-- States that any real value certified by the finite name of a parameter occurring in a word
instance is computably approximable. -/
def NoExactRealOracle : Prop :=
  ∀ (inst : SameWordInstance) (i : Fin inst.L) (p : NumericalParam) (x : ℝ),
    p ∈ inst.params i → CertifiesApproximation p.name x → ComputablyApproximable x

/-- Requires a halting rational estimate of each certified phase with error at most `2 * Real.pi
/ M + amp * 2^(-k)`, for positive `M` and nonnegative rational `amp`. The machine input
encodes `M`, `k`, `amp`, and the name's declared size, and runtime must lie between that
size and `1 + name.size + M + k`. -/
def OffGridQPEConsumer (r : BackendRun) : Prop :=
  ∀ (M : ℕ) (_hM : 0 < M) (name : FiniteRealInput) (θ : ℝ) (k : ℕ) (amp : ℚ),
    CertifiesApproximation name θ →
    0 ≤ amp →
    ∃ (t : ℕ) (q : ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine
        ((natBits M ++ natBits k ++ ratBits amp ++ natBits name.size).map some) t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatOnTape cfg q ∧
      |(q : ℝ) - θ| ≤ 2 * Real.pi / (M : ℝ) + (amp : ℝ) * ((2 : ℝ)⁻¹) ^ k ∧
      name.size ≤ t ∧
      t ≤ 1 + name.size + M + k

/-- Requires a halting rational approximation to the inner product of rational entry and
preparation arrays, with error at most `κ * (n * 2^(-k)) + ε` when `2^(-gap) ≤ Δ`, `κ =
2^gap`, and `ε > 0`. Runtime must cover the encoded arrays' total length and be at most `1 +
n * (k + gap) + gap + k`. -/
def RationalHHLConsumer (r : BackendRun) : Prop :=
  ∀ (n gap k : ℕ) (entries : Fin n → ℚ) (prep : Fin n → ℚ) (κ : ℝ) (Δ : ℝ) (ε : ℝ),
    ((2 : ℝ)⁻¹) ^ gap ≤ Δ →
    κ = (2 : ℝ) ^ gap →
    0 < ε →
    ∃ (t : ℕ) (q : ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine
        ((natBits n ++ natBits gap ++ natBits k ++
          ((List.ofFn fun i : Fin n => ratBits (entries i) ++ ratBits (prep i))).flatten).map some)
          t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatOnTape cfg q ∧
      |(q : ℝ) - (∑ i : Fin n, (entries i : ℝ) * (prep i : ℝ))| ≤
        κ * (n * ((2 : ℝ)⁻¹) ^ k) + ε ∧
      (∑ i : Fin n, (ratBits (entries i) ++ ratBits (prep i)).length) ≤ t ∧
      t ≤ 1 + n * (k + gap) + gap + k

/-- Requires a halting rational approximation to the sum of rational coefficients with error at
most `Λ * 2^(-k) + ε`, given positive `Λ`, positive `ε`, and an absolute-coefficient sum
bounded by `Λ`. Runtime must cover the coefficient encodings' total length and be at most `1
+ m * k + k`. -/
def RationalLCUConsumer (r : BackendRun) : Prop :=
  ∀ (m k : ℕ) (coef : Fin m → ℚ) (Λ : ℚ) (ε : ℝ),
    0 < (Λ : ℝ) →
    0 < ε →
    (∑ i : Fin m, |(coef i : ℝ)|) ≤ Λ →
    ∃ (t : ℕ) (q : ℚ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (r.states + 1))),
      BitMachineAfter r.machine
        ((natBits m ++ natBits k ++ ratBits Λ ++
          ((List.ofFn fun i : Fin m => ratBits (coef i))).flatten).map some) t = some cfg ∧
      Turing.TM0.step r.machine cfg = none ∧
      RatOnTape cfg q ∧
      |(q : ℝ) - (∑ i : Fin m, (coef i : ℝ))| ≤ (Λ : ℝ) * ((2 : ℝ)⁻¹) ^ k + ε ∧
      (∑ i : Fin m, (ratBits (coef i)).length) ≤ t ∧
      t ≤ 1 + m * k + k

/-- Lists the forward, inverse, and controlled forms by which a program may request an oracle
slot. -/
inductive AccessForm where
  | forward
  | inverse
  | controlled
  deriving DecidableEq, Repr

/-- Encodes forward, inverse, and controlled access by tags zero, one, and two, respectively. -/
def AccessForm.code : AccessForm → ℕ
  | .forward => 0
  | .inverse => 1
  | .controlled => 2

/-- Stores a supplied-access flag and an optional natural-number function for each slot and
access form. Agreement between the flags and implementations is expressed separately by
`WellFormed`. -/
structure AccessContract (L : ℕ) where
  supplied : Fin L → AccessForm → Bool
  impl : Fin L → AccessForm → Option (ℕ → ℕ)

/-- Requires an implementation to be present exactly when its slot and access form are marked
supplied. -/
def AccessContract.WellFormed {L : ℕ} (c : AccessContract L) : Prop :=
  ∀ (s : Fin L) (f : AccessForm), (c.impl s f).isSome = c.supplied s f

/-- Lists the register arithmetic operations addition, multiplication, greatest common divisor,
and modular exponentiation. -/
inductive ArithCode where
  | add
  | mul
  | gcd
  | modexp
  deriving DecidableEq, Repr

/-- Encodes addition, multiplication, greatest common divisor, and modular exponentiation by
tags zero through three, respectively. -/
def ArithCode.code : ArithCode → ℕ
  | .add => 0
  | .mul => 1
  | .gcd => 2
  | .modexp => 3

/-- Maps `[a, b]` to `[a, a + b]` or `[a, a * b]`, and replaces the final entry of `[a, b, _]`
or `[a, e, m, _]` by `Nat.gcd a b` or `a^e % m`, respectively. Lists of any other shape are
unchanged. -/
def arithSem (code : ArithCode) (ws : List ℕ) : List ℕ :=
  match code, ws with
  | .add, [a, b] => [a, a + b]
  | .mul, [a, b] => [a, a * b]
  | .gcd, [a, b, _] => [a, b, Nat.gcd a b]
  | .modexp, [a, e, m, _] => [a, e, m, a ^ e % m]
  | _, ws => ws

/-- Instructions over `w` natural-number registers and `L` oracle slots: read a fair-coin bit,
apply an oracle form, perform arithmetic on a register window, or emit a register value. -/
inductive ProbInstr (w L : ℕ) where
  | fairCoin (dst : Fin w)
  | oracle (slot : Fin L) (form : AccessForm) (addr : Fin w) (val : Fin w)
  | arith (code : ArithCode) (ws : List (Fin w))
  | emit (src : Fin w)

/-- A finite instruction list over a fixed register width and oracle-slot count. -/
structure ProbProgram (w L : ℕ) where
  steps : List (ProbInstr w L)

/-- Counts the fair-coin instructions in a program, determining the length of coin records used
in its output law. -/
def ProbProgram.coins {w L : ℕ} (p : ProbProgram w L) : ℕ :=
  (p.steps.filter (fun s => match s with | .fairCoin _ => true | _ => false)).length

/-- Requires every oracle instruction to request an access form marked supplied by the contract;
other instructions impose no condition. -/
def ProbProgram.LegalFor {w L : ℕ} (p : ProbProgram w L) (c : AccessContract L) : Prop :=
  ∀ s ∈ p.steps, match s with
    | ProbInstr.oracle slot form _ _ => c.supplied slot form = true
    | _ => True

/-- Stores the natural-number register contents, remaining coin record, and accumulated output
list of a program execution. -/
structure ProbState (w : ℕ) where
  regs : Fin w → ℕ
  coins : List Bool
  out : List ℕ

/-- Writes zipped register-index and output-value pairs from left to right, leaving unpaired
entries unused. If an index repeats, its last paired value takes precedence. -/
def writeWindow {w : ℕ} (regs : Fin w → ℕ) (ws : List (Fin w)) (outs : List ℕ) : Fin w → ℕ :=
  (ws.zip outs).foldl (fun m iv => Function.update m iv.1 iv.2) regs

/-- Executes one instruction by consuming a coin bit, applying an available oracle function,
updating an arithmetic window, or appending an emitted value. A coin instruction with no
remaining bit and an oracle instruction with no implementation leave the state unchanged. -/
def probStep {w L : ℕ} (c : AccessContract L) (s : ProbState w) :
    ProbInstr w L → ProbState w
  | .fairCoin dst =>
    match s.coins with
    | b :: rest => { s with regs := Function.update s.regs dst (if b then 1 else 0),
                            coins := rest }
    | [] => s
  | .oracle slot form addr val =>
    match c.impl slot form with
    | some g => { s with regs := Function.update s.regs val (g (s.regs addr)) }
    | none => s
  | .arith code ws =>
    let vals := ws.map (fun i => s.regs i)
    let outs := arithSem code vals
    { s with regs := writeWindow s.regs ws outs }
  | .emit src => { s with out := s.out ++ [s.regs src] }

/-- Executes the instruction list from zeroed registers, the supplied coin record, and an empty
output list. -/
def runProb {w L : ℕ} (c : AccessContract L) (p : ProbProgram w L)
    (record : List Bool) : ProbState w :=
  p.steps.foldl (probStep c) { regs := fun _ => 0, coins := record, out := [] }

/-- The probability of output `ω`, computed by counting length-`p.coins` Boolean records
producing it and dividing by `2^p.coins`. -/
def ProbLaw {w L : ℕ} (c : AccessContract L) (p : ProbProgram w L) (ω : List ℕ) : ℝ :=
  ((Finset.univ.filter fun r : Fin p.coins → Bool =>
      (runProb c p (List.ofFn r)).out = ω).card : ℝ) / (2 ^ p.coins : ℝ)

/-- Serializes an instruction as a natural-number tag followed by its indices and operation
fields, including the window length for arithmetic instructions. -/
def probInstrFields {w L : ℕ} : ProbInstr w L → List ℕ
  | .fairCoin dst => [0, dst.val]
  | .oracle slot form addr val => [1, slot.val, form.code, addr.val, val.val]
  | .arith code ws => [2, code.code, ws.length] ++ ws.map (fun i => i.val)
  | .emit src => [3, src.val]

/-- Encodes the register width, slot count, instruction count, coin count, and flattened
instruction fields by concatenating their `natBits` encodings. -/
def probProgramBits {w L : ℕ} (p : ProbProgram w L) : List Bool :=
  ([w, L, p.steps.length, p.coins] ++ p.steps.flatMap probInstrFields).flatMap natBits

/-- Stores a finite-state TM0 machine intended to execute serialized probabilistic programs and
coin records; correctness is specified separately. -/
structure ProbTM0Compiler where
  states : ℕ
  machine : Turing.TM0.Machine (Option Bool) (Fin (states + 1))

/-- Returns the last available TM0 configuration among times zero through `clock`, or `none` if
none is available. The selected configuration is not required to be halting by this
definition. -/
def tm0Final (comp : ProbTM0Compiler) (input : List (Option Bool)) (clock : ℕ) :
    Option (Turing.TM0.Cfg (Option Bool) (Fin (comp.states + 1))) :=
  ((List.range (clock + 1)).filterMap (fun s => BitMachineAfter comp.machine input s)).getLast?

/-- Requires every coin record of the prescribed length to yield a halting TM0 execution of the
encoded program and record within the given time and peak-space bounds. The final tape must
encode exactly the natural-number output of `runProb`. -/
def TM0Compiled {w L : ℕ} (comp : ProbTM0Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock space : ℕ) : Prop :=
  ∀ (record : List Bool) (_hlen : record.length = p.coins),
    let input := (probProgramBits p ++ record).map some
    ∃ (t : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin (comp.states + 1))),
      BitMachineAfter comp.machine input t = some cfg ∧
      Turing.TM0.step comp.machine cfg = none ∧
      t ≤ clock ∧
      peakSpaceAfter comp.machine input t ≤ space ∧
      NatsOnTape cfg (runProb c p record).out

open scoped Classical in

/-- Requires the output law obtained by counting uniform coin records whose `tm0Final` tape
encodes each output list to equal `ProbLaw`. -/
def TM0LawPreserved {w L : ℕ} (comp : ProbTM0Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock : ℕ) : Prop :=
  ∀ ω : List ℕ,
    ((Finset.univ.filter fun r : Fin p.coins → Bool =>
        match tm0Final comp ((probProgramBits p ++ List.ofFn r).map some) clock with
        | some cfg => NatsOnTape cfg ω
        | none => False).card : ℝ) / (2 ^ p.coins : ℝ) = ProbLaw c p ω

/-- Stores a TM2 program over three optional-bit stacks, with finite label and internal-state
types determined by `V` and `S`. -/
structure ProbTM2Compiler where
  V : ℕ
  S : ℕ
  machine : Fin (V + 1) →
    Turing.TM2.Stmt (fun _ : Fin 3 => Option Bool) (Fin (V + 1)) (Fin (S + 1))

/-- Runs the TM2 machine for a specified number of steps from an initialization placing the
input on stack zero. Once the run returns `none`, later values remain `none`. -/
def tm2After (comp : ProbTM2Compiler) (input : List (Option Bool)) :
    ℕ → Option (Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (comp.V + 1)) (Fin (comp.S + 1)))
  | 0 => some (Turing.TM2.init (0 : Fin 3) input)
  | t + 1 =>
    match tm2After comp input t with
    | none => none
    | some cfg => Turing.TM2.step comp.machine cfg

/-- Measures a TM2 configuration's space by summing the lengths of all three stacks, including
blank symbols stored in them. -/
def tm2Space {V S : ℕ}
    (cfg : Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (V + 1)) (Fin (S + 1))) : ℕ :=
  ∑ k : Fin 3, (cfg.stk k).length

/-- Returns the last available TM2 configuration among times zero through `clock`, or `none` if
none is available. The selected configuration is not required to be halting by this
definition. -/
def tm2Final (comp : ProbTM2Compiler) (input : List (Option Bool)) (clock : ℕ) :
    Option (Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (comp.V + 1)) (Fin (comp.S + 1))) :=
  ((List.range (clock + 1)).filterMap (fun s => tm2After comp input s)).getLast?

/-- Requires every coin record of the prescribed length to yield a TM2 configuration with no
next label within the clock bound, with stack space bounded throughout the run. Stack zero
must match the encoded `runProb` output followed by blanks. -/
def TM2Compiled {w L : ℕ} (comp : ProbTM2Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock space : ℕ) : Prop :=
  ∀ (record : List Bool) (_hlen : record.length = p.coins),
    let input := (probProgramBits p ++ record).map some
    ∃ (t : ℕ) (cfg : Turing.TM2.Cfg (fun _ : Fin 3 => Option Bool) (Fin (comp.V + 1)) (Fin (comp.S + 1))),
      tm2After comp input t = some cfg ∧
      cfg.l = none ∧
      t ≤ clock ∧
      (∀ s ≤ t, match tm2After comp input s with
        | some c' => tm2Space c' ≤ space
        | none => True) ∧
      ∀ i : ℕ, (cfg.stk (0 : Fin 3)).getD i none =
        tapeAt ((runProb c p record).out.flatMap natBits) i

open scoped Classical in

/-- Requires the output law obtained by counting uniform coin records whose `tm2Final` stack
zero matches each encoded output list to equal `ProbLaw`. -/
def TM2LawPreserved {w L : ℕ} (comp : ProbTM2Compiler) (c : AccessContract L)
    (p : ProbProgram w L) (clock : ℕ) : Prop :=
  ∀ ω : List ℕ,
    ((Finset.univ.filter fun r : Fin p.coins → Bool =>
        match tm2Final comp ((probProgramBits p ++ List.ofFn r).map some) clock with
        | some cfg => ∀ i : ℕ, (cfg.stk (0 : Fin 3)).getD i none =
            tapeAt (ω.flatMap natBits) i
        | none => False).card : ℝ) / (2 ^ p.coins : ℝ) = ProbLaw c p ω

/-- States that every oracle instruction of a legal program under a well-formed access contract
has both a supplied flag and an available implementation. -/
def AccessRestrictionPreserved : Prop :=
  ∀ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L),
    c.WellFormed →
    p.LegalFor c →
    ∀ s ∈ p.steps, match s with
      | ProbInstr.oracle slot form _ _ => c.supplied slot form = true ∧ (c.impl slot form).isSome
      | _ => True

/-- Requires zero-coin legal programs computing modular exponentiation and greatest common
divisors, with TM0 output and law preservation under well-formed access contracts. Each
program's clock and space are bounded by one plus the total `natBits` lengths of its
numerical arguments. -/
def ShorPostprocessConsumer (comp0 : ProbTM0Compiler) : Prop :=
  (∀ (a e m : ℕ), ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      p.coins = 0 ∧ c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins → (runProb c p record).out = [a ^ e % m]) ∧
      clock ≤ 1 + (natBits a).length + (natBits e).length + (natBits m).length ∧
      space ≤ 1 + (natBits a).length + (natBits e).length + (natBits m).length) ∧
  (∀ (x y : ℕ), ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      p.coins = 0 ∧ c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins → (runProb c p record).out = [Nat.gcd x y]) ∧
      clock ≤ 1 + (natBits x).length + (natBits y).length ∧
      space ≤ 1 + (natBits x).length + (natBits y).length)

/-- Requires a legal program with TM0 output and law preservation whose output is `[0]`, or
`[1]` accompanied by existence of a Boolean solution to the given linear system modulo two.
Both clock and space are bounded by `1 + n * m + n + m`; the zero output requires no
inconsistency certificate. -/
def SimonPostprocessConsumer (comp0 : ProbTM0Compiler) : Prop :=
  ∀ (n m : ℕ) (A : Fin m → Fin n → Bool) (b : Fin m → Bool),
    ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins →
        match (runProb c p record).out with
        | [code] =>
            code = 0 ∨
            ∃ x : Fin n → Bool,
              code = 1 ∧
              (∀ i : Fin m,
                (List.ofFn fun j : Fin n => if A i j && x j then (1 : ℕ) else 0).sum % 2
                  = if b i then 1 else 0)
        | _ => False) ∧
      clock ≤ 1 + n * m + n + m ∧
      space ≤ 1 + n * m + n + m

/-- Requires a legal program with TM0 output and law preservation that outputs the integer sum
of `2^j` over the true input bits. The access contract must be well formed, and clock and
space are each bounded by `1 + n`. -/
def QFTPostprocessConsumer (comp0 : ProbTM0Compiler) : Prop :=
  ∀ (n : ℕ) (bits : Fin n → Bool),
    ∃ (w L : ℕ) (p : ProbProgram w L) (c : AccessContract L) (clock space : ℕ),
      c.WellFormed ∧ p.LegalFor c ∧
      TM0Compiled comp0 c p clock space ∧
      TM0LawPreserved comp0 c p clock ∧
      (∀ record, record.length = p.coins →
        (runProb c p record).out
          = [(List.ofFn fun j : Fin n => if bits j then 2 ^ j.val else 0).sum]) ∧
      clock ≤ 1 + n ∧
      space ≤ 1 + n

end

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
