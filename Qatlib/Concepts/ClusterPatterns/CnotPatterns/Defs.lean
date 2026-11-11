/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Cluster measurement patterns and their branch semantics

This module defines finite cluster measurement patterns, their adaptive angle rules, and the
matrix operations for loading an input, entangling it with a resource, measuring selected
qubits, applying output corrections, and discarding the measured register. The cluster
computation framework is motivated by [RaussendorfBriegel2000]. The measurement vectors used
here have amplitudes involving the real exponential `exp(alpha)`; the definitions impose neither
normalization of these vectors nor unitarity of a pattern's entangler.

Concrete patterns include a wire, a controlled-NOT layout, a six-vertex Euler chain, and a
four-vertex chain with two outputs. Dependency sets record classical control of angles and
corrections, while a determinism predicate requires a common isometry for all equally weighted
branches and participation of every measured vertex in the dependency graph.

## Main statements

* `MpPattern` packages entangling, angle, and correction data.
* `mpPatternKraus`, `mpPatternBranch`, and `mpPatternInstrument` give the operator and
  instrument semantics.
* `mpWirePattern`, `mpCnotPattern`, `mpEulerPattern`, and `mpTwoOutputPattern` specify the
  concrete layouts.
* `MpDependency`, `MpFlowCondition`, and `MpDeterministic` express classical dependencies, their
  order, and branch determinism.
* `mpBitTime_eq`, `mpPeakSpace_eq`, and `mpCommBits_eq` expose the associated resource counts.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000], *Quantum computing via measurements
  only*.
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns

open Complex
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The two-component measurement vector with amplitudes `1 / sqrt 2` and `(-1)^o * exp(alpha) /
sqrt 2`. The exponential has real argument, so the vector need not have unit norm. -/
noncomputable def mpSVector (α : ℝ) (o : Bool) : Bool → ℂ :=
  fun b =>
    (if b then if o then -Complex.exp (Complex.ofReal α) else Complex.exp (Complex.ofReal α)
      else 1) / Real.sqrt 2

/-- The outer-product operator `|mpSVector alpha o><mpSVector alpha o|`, indexed by `Fin 2`. Its
definition does not require the underlying vector to be normalized. -/
noncomputable def mpSBasisProjector (α : ℝ) (o : Bool) : Operator 2 :=
  Matrix.of fun i j =>
    mpSVector α o ((i : ℕ) = 1) * star (mpSVector α o ((j : ℕ) = 1))

/-- The Boolean parity of the outcomes indexed by `S`, true exactly when the number of true
outcomes is odd. -/
def mpParity {k : ℕ} (S : Finset (Fin k)) (s : Fin k → Bool) : Bool :=
  decide ((∑ i ∈ S, if s i then 1 else 0 : ℕ) % 2 = 1)

/-- The parity of an empty set of outcome indices is false. -/
@[simp] theorem mpParity_empty {k : ℕ} (s : Fin k → Bool) : mpParity ∅ s = false := by
  simp [mpParity]

/-- Data for a cluster measurement pattern with `n` input qubits, `w` measured qubits, and `m`
output qubits, including entangling, adaptive-angle, and Boolean correction rules. This
representation of the framework of [RaussendorfBriegel2000] requires `n <= w` but imposes no
matrix or normalization laws. -/
structure MpPattern (n w m : ℕ) where

  entangler : Matrix (Reg (w + m)) (Reg (w + m)) ℂ

  baseAngle : Fin w → ℝ

  angleSign : Fin w → Finset (Fin w)

  angleShift : Fin w → Finset (Fin w)

  xCorr : Fin m → (Fin w → Bool) → Bool

  zCorr : Fin m → (Fin w → Bool) → Bool

  nin : n ≤ w

/-- The base angle with its sign controlled by the parity of `angleSign j`, followed by a pi
shift controlled by the parity of `angleShift j`. -/
noncomputable def mpAdaptiveAngle {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool)
    (j : Fin w) : ℝ :=
  (if mpParity (P.angleSign j) s then -P.baseAngle j else P.baseAngle j)
    + Real.pi * (if mpParity (P.angleShift j) s then (1 : ℝ) else 0)

/-- The input-loading matrix that places the input on the first `n` coordinates and the resource
vector on the remaining coordinates. An entry vanishes unless the input coordinates agree. -/
noncomputable def mpLoadMatrix {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) : Matrix (Reg (w + m)) (Reg n) ℂ :=
  Matrix.of fun u y =>
    if ∀ i : Fin n, u (Fin.castLE (by have := P.nin; omega : n ≤ w + m) i) = y i then
      resource (fun k => u (Fin.cast (by have := P.nin; omega) (Fin.natAdd n k)))
    else 0

/-- The tensor product of the adaptive measurement outer products on the first `w` qubits and
the identity on the `m` outputs. No normalization assumption on the measurement vectors is
needed for this matrix definition. -/
noncomputable def mpProjector {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) :
    Matrix (Reg (w + m)) (Reg (w + m)) ℂ :=
  Matrix.of fun u u' =>
    (∏ j : Fin w,
        mpSVector (mpAdaptiveAngle P s j) (s j) (u (Fin.castLE (by omega : w ≤ w + m) j))
          * star (mpSVector (mpAdaptiveAngle P s j) (s j)
              (u' (Fin.castLE (by omega) j))))
      * (if ∀ k : Fin m, u (Fin.natAdd w k) = u' (Fin.natAdd w k) then (1 : ℂ) else 0)

/-- The output correction matrix that fixes measured coordinates and applies the pattern's `X`
and `Z` corrections to each output. Its entries apply the `Z` sign to the source output bits
before the `X` flips. -/
def mpCorrection {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) :
    Matrix (Reg (w + m)) (Reg (w + m)) ℂ :=
  Matrix.of fun u u' =>
    if ∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j)
        = u' (Fin.castLE (by omega) j) then
      if ∀ k : Fin m, u (Fin.natAdd w k) = (xor (P.xCorr k s) (u' (Fin.natAdd w k))) then
        ∏ k : Fin m, if P.zCorr k s && u' (Fin.natAdd w k) then (-1 : ℂ) else 1
      else 0
    else 0

/-- The matrix selecting the measured-register basis string `z` and encoding the remaining
output bits by `bitVecEquiv m`. -/
def mpReadout (w m : ℕ) (z : Fin w → Bool) : Matrix (Fin (2 ^ m)) (Reg (w + m)) ℂ :=
  Matrix.of fun xp u =>
    if (∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j) = z j)
        ∧ bitVecEquiv m (fun k => u (Fin.natAdd w k)) = xp then (1 : ℂ) else 0

/-- The matrix obtained by composing input loading, entangling, adaptive measurement, output
correction, and measured-register readout. The measurement outcome is `s`, while `z` indexes
the discarded register in the cluster-pattern semantics motivated by
[RaussendorfBriegel2000]. -/
noncomputable def mpPatternKraus {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s z : Fin w → Bool) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (Equiv.refl _) (bitVecEquiv n)
    (mpReadout w m z * mpCorrection P s * mpProjector P s * P.entangler * mpLoadMatrix P resource)

/-- The completely positive branch map for outcome string `s`, formed by summing conjugation by
`mpPatternKraus` over all discarded-register strings `z`. -/
noncomputable def mpPatternBranch {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s : Fin w → Bool) :
    Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ m) :=
  ∑ z : Fin w → Bool, conjBranch (mpPatternKraus P resource s z)

/-- The instrument whose outcome branches are `mpPatternBranch P resource`. Complete positivity
follows from the Kraus representation, while trace preservation of the total map is supplied
by `htotal`. -/
noncomputable def mpPatternInstrument {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n)))
    (htotal : ∀ A : Operator (2 ^ n),
      Matrix.trace (∑ s : Fin w → Bool, mpPatternBranch P resource s A) = Matrix.trace A) :
    Instrument (Fin w → Bool) (2 ^ n) (2 ^ m) :=
  Instrument.ofBranches (mpPatternBranch P resource)
    (fun s => CompletelyPositive.sum (s := Finset.univ)
      fun z _ => completelyPositive_conjBranch (mpPatternKraus P resource s z))
    htotal

/-- The three-vertex chain pattern with one input, two zero-angle measurements, and one output.
It uses complemented outcome bits for its output `X` and `Z` corrections in the cluster-wire
setting of [RaussendorfBriegel2000]. -/
noncomputable def mpWirePattern : MpPattern 1 2 1 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    ({(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩)} :
      Finset (Fin 3 × Fin 3))
  baseAngle := fun _ => 0
  angleSign := fun _ => ∅
  angleShift := fun _ => ∅
  xCorr := fun _ s => !s 1
  zCorr := fun _ s => !s 0
  nin := by omega

/-- The six-vertex, two-input, two-output pattern with four zero-angle measurements and the
specified outcome-dependent Pauli corrections. Its graph and correction data provide the
controlled-NOT pattern considered in the framework of [RaussendorfBriegel2000]. -/
noncomputable def mpCnotPattern : MpPattern 2 4 2 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    ({(⟨0, by omega⟩, ⟨2, by omega⟩), (⟨0, by omega⟩, ⟨3, by omega⟩),
      (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
      (⟨3, by omega⟩, ⟨4, by omega⟩)} : Finset (Fin 6 × Fin 6))
  baseAngle := fun _ => 0
  angleSign := fun _ => ∅
  angleShift := fun _ => ∅
  xCorr := fun k s => if (k : ℕ) = 0 then !s 3 else s 2
  zCorr := fun k s => if (k : ℕ) = 0 then !(xor (s 0) (s 1)) else !s 1
  nin := by omega

/-- The earlier measurement indices whose distance from `j` is odd, used to control the sign of
the Euler-chain angle at `j`. -/
def mpEulerSignSet (j : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter fun i => (i : ℕ) < (j : ℕ) ∧ ((j : ℕ) - (i : ℕ)) % 2 = 1

/-- The six-vertex chain with five measurements, base angles `-theta j`, alternating-parity sign
dependencies, and one corrected output. This is the concrete Euler-pattern data used for the
cluster computation setting of [RaussendorfBriegel2000]. -/
noncomputable def mpEulerPattern (θ : Fin 5 → ℝ) : MpPattern 1 5 1 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    (Finset.univ.filter fun p : Fin 6 × Fin 6 =>
      ∃ k : ℕ, k + 1 < 6 ∧ (p.1 : ℕ) = k ∧ (p.2 : ℕ) = k + 1)
  baseAngle := fun j => -θ j
  angleSign := fun j => mpEulerSignSet j
  angleShift := fun _ => ∅
  xCorr := fun _ s => xor (xor (s 0) (s 2)) (s 4)
  zCorr := fun _ s => xor (s 1) (s 3)
  nin := by omega

/-- The four-vertex chain pattern with one input, two zero-angle measurements, and two outputs.
Its corrections are `X^(s 1) Z^(s 0)` on the first output and `Z^(s 1)` on the second, in
the setting of [RaussendorfBriegel2000]. -/
noncomputable def mpTwoOutputPattern : MpPattern 1 2 2 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    ({(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
      (⟨2, by omega⟩, ⟨3, by omega⟩)} : Finset (Fin 4 × Fin 4))
  baseAngle := fun _ => 0
  angleSign := fun _ => ∅
  angleShift := fun _ => ∅
  xCorr := fun k s => if (k : ℕ) = 0 then s 1 else false
  zCorr := fun k s => if (k : ℕ) = 0 then s 0 else s 1
  nin := by omega

/-- The two-qubit matrix of a finite gate code, reindexed from Boolean registers to `Fin 4`
using `bitVecEquiv 2`. -/
noncomputable def mpFinGate (g : FiniteGateCode) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex (bitVecEquiv 2) (bitVecEquiv 2) (finiteCodeMatrix 2 g)

/-- The one-qubit matrix of a finite gate code, reindexed from Boolean registers to `Fin 2`
using `bitVecEquiv 1`. -/
noncomputable def mpFin1Gate (g : FiniteGateCode) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.reindex (bitVecEquiv 1) (bitVecEquiv 1) (finiteCodeMatrix 1 g)

/-- The `Fin 4` matrix obtained from the controlled-X finite gate code with control `c` and
target `t`. -/
noncomputable def mpFinCnot (c t : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  mpFinGate (FiniteGateCode.cx (c : ℕ) (t : ℕ))

/-- The two-qubit wire-swap permutation matrix, reindexed by `bitVecEquiv 2` on its rows and
columns. -/
def mpWireSwapMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex (bitVecEquiv 2) (bitVecEquiv 2)
    (permMatrix fun x : Reg 2 => fun i => if (i : ℕ) = 0 then x 1 else x 0)

/-- The directed nearest-neighbor edges of an `a` by `b` rectangular lattice in row-major order.
Each vertex is connected to its right and lower neighbors when they exist. -/
noncomputable def mpLatticeEdges (a b : ℕ) : Finset (Fin (a * b) × Fin (a * b)) :=
  Finset.univ.filter fun p =>
    ∃ i j : ℕ, i < a ∧ j < b ∧ (p.1 : ℕ) = i * b + j ∧
      (((p.2 : ℕ) = i * b + j + 1 ∧ j + 1 < b) ∨ ((p.2 : ℕ) = (i + 1) * b + j ∧ i + 1 < a))

/-- The source-pulse matrix for the rectangular-lattice edge set `mpLatticeEdges a b`. -/
noncomputable def mpLatticeEntangler (a b : ℕ) : Matrix (Reg (a * b)) (Reg (a * b)) ℂ :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse (mpLatticeEdges a b)

/-- The diagonal computational-basis projector selecting register strings whose bit at vertex
`v` equals `b`. -/
def mpVertexProjector (n : ℕ) (v : Fin n) (b : Bool) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if x v = b then (1 : ℂ) else 0

/-- The singleton edge set containing the directed edge from vertex zero to vertex one. -/
def mpEdge01 : Finset (Fin 2 × Fin 2) := {(⟨0, by omega⟩, ⟨1, by omega⟩)}

/-- The two-qubit vector supported on first bit `b`, with amplitude `bitPhase (!b && x 1) / 2`.
It records the unnormalized state associated with fixing that vertex outcome. -/
noncomputable def mpDeletionState (b : Bool) : QState (Reg 2) :=
  fun x => if x 0 = b then Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!b && x 1) / 2 else 0

/-- The Bell vector supported on strings with second bit equal to the first bit XOR `f1`, with
phase determined by `f2` times the second bit. Each nonzero amplitude has magnitude `1 /
sqrt 2`. -/
noncomputable def mpBellVector (f1 f2 : Bool) : QState (Reg 2) :=
  fun x =>
    if x 0 = false then
      (if x 1 = f1 then Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (f2 && f1) / Real.sqrt 2 else 0)
    else
      (if x 1 = !f1 then Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (f2 && !f1) / Real.sqrt 2 else 0)

/-- The one-qubit Pauli matrix `X^f2 Z^f1`, expressed by its bit-flip condition and
input-dependent sign. -/
def mpLoadPauli (f1 f2 : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    (if f2 then (if i ≠ j then (1 : ℂ) else 0) else (if i = j then (1 : ℂ) else 0))
      * (if (j : ℕ) = 1 ∧ f1 then (-1 : ℂ) else 1)

/-- The loading Kraus matrix equal to one half of the Pauli correction `mpLoadPauli f1 f2`. -/
noncomputable def mpLoadKraus (f1 f2 : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2) • mpLoadPauli f1 f2

/-- The set of outcome coordinates that can affect the Boolean function `f`. An index belongs
exactly when flipping that bit changes `f` for some outcome string. -/
noncomputable def mpSupportSet {w : ℕ} (f : (Fin w → Bool) → Bool) : Finset (Fin w) :=
  Finset.univ.filter fun i =>
    decide (∃ s : Fin w → Bool, f (Function.update s i (!(s i))) ≠ f s)

/-- The directed classical dependency set from measurement outcomes to adaptive angles and
output corrections. Angle edges use the declared parity sets, and correction edges use the
Boolean supports of the correction functions. -/
noncomputable def MpDependency {n w m : ℕ} (P : MpPattern n w m) :
    Finset (Fin (w + m) × Fin (w + m)) :=
  (Finset.univ : Finset (Fin w)).biUnion fun j =>
      ((P.angleSign j ∪ P.angleShift j).image fun i : Fin w =>
        (Fin.castLE (by omega : w ≤ w + m) i, Fin.castLE (by omega) j))
    ∪ (Finset.univ : Finset (Fin m)).biUnion fun k =>
      ((mpSupportSet (P.xCorr k) ∪ mpSupportSet (P.zCorr k)).image fun i : Fin w =>
        (Fin.castLE (by omega) i, Fin.natAdd w k))

/-- The condition that every classical dependency edge points from a smaller vertex index to a
larger one. -/
def MpFlowCondition {n w m : ℕ} (P : MpPattern n w m) : Prop :=
  ∀ p ∈ MpDependency P, (p.1 : ℕ) < (p.2 : ℕ)

/-- The pattern's bit-time count `2 * w + m` plus the number of classical dependency edges. -/
noncomputable def mpBitTime {n w m : ℕ} (P : MpPattern n w m) : ℕ :=
    2 * w + m + (MpDependency P).card

/-- The peak-space count given by the full number `w + m` of measured and output qubits. -/
def mpPeakSpace {n w m : ℕ} (P : MpPattern n w m) : ℕ := w + m

/-- The communication-bit count defined as the cardinality of the pattern's classical dependency
set. -/
noncomputable def mpCommBits {n w m : ℕ} (P : MpPattern n w m) : ℕ := (MpDependency P).card

/-- The condition that every outcome branch is `2^(-w)` times conjugation by one common
isometry, and every measured vertex is incident to a classical dependency edge. It
formalizes the branch-independence requirement used here for cluster patterns motivated by
[RaussendorfBriegel2000]. -/
def MpDeterministic {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) : Prop :=
  (∃ V : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ (s : Fin w → Bool) (ρ : Operator (2 ^ n)),
        ∑ z : Fin w → Bool,
            (mpPatternKraus P resource s z) * ρ
              * (mpPatternKraus P resource s z).conjTranspose
          = (1 / (2 : ℂ) ^ w) • (V * ρ * V.conjTranspose))
    ∧ ∀ j : Fin w, ∃ p, p ∈ MpDependency P ∧
      (p.1 = Fin.castLE (by omega : w ≤ w + m) j ∨ p.2 = Fin.castLE (by omega) j)

/-- The peak-space count of a pattern with `w` measured and `m` output qubits is `w + m`. -/
@[simp] theorem mpPeakSpace_eq {n w m : ℕ} (P : MpPattern n w m) :
    mpPeakSpace P = w + m := rfl

/-- The communication-bit count equals the number of edges in `MpDependency P`. -/
@[simp] theorem mpCommBits_eq {n w m : ℕ} (P : MpPattern n w m) :
    mpCommBits P = (MpDependency P).card := rfl

/-- The bit-time count equals `2 * w + m` plus the number of classical dependency edges. -/
@[simp] theorem mpBitTime_eq {n w m : ℕ} (P : MpPattern n w m) :
    mpBitTime P = 2 * w + m + (MpDependency P).card := rfl

/-- The angle rounded to the grid of spacing `2 * pi / 2^b` using `floor(x + 1/2)` on the
rescaled angle. -/
noncomputable def mpRoundedAngle (b : ℕ) (θ : ℝ) : ℝ :=
  2 * Real.pi * ((Int.floor (θ * (2 ^ b) / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ) / (2 ^ b)

end Qatlib.Concepts.ClusterPatterns.CnotPatterns
