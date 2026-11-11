/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

/-!
# CSS recovery and fault-tolerance data

This module defines Pauli labels, syndromes, recovery programs, orthonormal CSS encodings,
syndrome outcome masses, and the syndrome-projection recovery map. Predicates such as
`CorrectsUpTo`, `MinimumWeightSound`, and `LogicalReferencePreserved` state the distinct
correction properties used by later proofs. These definitions use the stabilizer framework of
[Gottesman1997].

The module also records code-family bounds, noisy syndrome weights, fault-set noise conditions,
gadget residuals, and resource expressions. `FtRealization` collects finite code, decoder,
gadget, noise, and budget parameters; the correctness properties are expressed separately.

## Main definitions

* `RecoveryProgram`: assigns a correction label and classical decoding time to each syndrome.
* `CssEncoding`: specifies an orthonormal basis spanning the CSS codespace.
* `recoveryChannel`: sums syndrome-projected and corrected operators.
* `LocalStochasticNoiseLaw` and `AdversarialFaultBudget`: specify fault-set laws.
* `GadgetSpec`: records gadget resources and fault-dependent residuals.
* `FtRealization`: collects finite fault-tolerance parameters.

## References

* [Gottesman, 1997][Gottesman1997]
-/

open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester

set_option autoImplicit false


namespace Qatlib.Concepts.CodingDecoding.CssTesters

open Matrix
open scoped Classical

variable {ι κX κZ : Type*} [Fintype ι] [Fintype κX] [Fintype κZ]
  [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]

/-- A pair of binary vectors specifying the X and Z components of a Pauli operator. -/
abbrev PauliLabel (ι : Type*) := (ι → ZMod 2) × (ι → ZMod 2)

/-- The pair of syndromes obtained by applying the X-check matrix to the Z label and the Z-check
matrix to the X label. -/
def pauliSyndrome (c : CssData ι κX κZ) (e : PauliLabel ι) : (κX → ZMod 2) × (κZ → ZMod 2) :=
  (c.hX *ᵥ e.2, c.hZ *ᵥ e.1)

/-- The Hamming distance between two syndrome pairs, summed over their X-check and Z-check
components. -/
def syndromeDist (η η' : (κX → ZMod 2) × (κZ → ZMod 2)) : ℕ :=
  bitWeight (η.1 + η'.1) + bitWeight (η.2 + η'.2)

/-- A Pauli label whose X and Z components lie in the row spaces of the corresponding check
matrices. -/
noncomputable def IsStabilizerLabel (c : CssData ι κX κZ) (e : PauliLabel ι) : Prop :=
  e.1 ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
    e.2 ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)

/-- A syndrome-dependent Pauli correction together with an assigned classical decoding time for
each syndrome. -/
structure RecoveryProgram (c : CssData ι κX κZ) where

  corr : (κX → ZMod 2) × (κZ → ZMod 2) → PauliLabel ι

  decodeTime : (κX → ZMod 2) × (κZ → ZMod 2) → ℕ

/-- The Pauli label remaining after adding the correction chosen from the observed syndrome to
the input error label. -/
def residualFromObserved {c : CssData ι κX κZ} (prog : RecoveryProgram c) (e : PauliLabel ι)
    (ηobs : (κX → ZMod 2) × (κZ → ZMod 2)) : PauliLabel ι :=
  (e.1 + (prog.corr ηobs).1, e.2 + (prog.corr ηobs).2)

/-- The residual Pauli label obtained when the recovery program receives the true syndrome. -/
def residualLabel {c : CssData ι κX κZ} (prog : RecoveryProgram c) (e : PauliLabel ι) :
    PauliLabel ι :=
  residualFromObserved prog e (pauliSyndrome c e)

/-- The property that every Pauli error of weight at most `t` leaves a stabilizer residual after
decoding its true syndrome. -/
def CorrectsUpTo {c : CssData ι κX κZ} (prog : RecoveryProgram c) (t : ℕ) : Prop :=
  ∀ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ t →
    IsStabilizerLabel c (residualLabel prog e)

/-- The property that errors of weight at most `t` leave stabilizer residuals whenever the
observed syndrome is within Hamming distance `s` of the true syndrome. -/
def CorrectsSingleShotNoisyUpTo {c : CssData ι κX κZ} (prog : RecoveryProgram c)
    (t s : ℕ) : Prop :=
  ∀ (e : PauliLabel ι) (ηobs : (κX → ZMod 2) × (κZ → ZMod 2)),
    pauliWeight e.1 e.2 ≤ t →
    syndromeDist (pauliSyndrome c e) ηobs ≤ s →
    IsStabilizerLabel c (residualFromObserved prog e ηobs)

/-- The property that a correction's weight is bounded by the weight of every error having the
supplied syndrome. -/
def MinimumWeightSound {c : CssData ι κX κZ} (prog : RecoveryProgram c) : Prop :=
  ∀ (η : (κX → ZMod 2) × (κZ → ZMod 2)) (e : PauliLabel ι),
    pauliSyndrome c e = η →
    pauliWeight (prog.corr η).1 (prog.corr η).2 ≤ pauliWeight e.1 e.2

/-- The complex coefficient inner product, conjugate-linear in the first argument. -/
noncomputable def coeffInner (u v : (ι → ZMod 2) → ℂ) : ℂ := ∑ i, star (u i) * v i

/-- An orthonormal basis of the CSS codespace indexed by binary strings of length `K`. -/
structure CssEncoding (c : CssData ι κX κZ) (K : ℕ) where

  enc : (Fin K → ZMod 2) → (ι → ZMod 2) → ℂ

  mem_codespace : ∀ b : Fin K → ZMod 2, enc b ∈ cssCodespace c

  orthonormal : ∀ b b' : Fin K → ZMod 2,
    coeffInner (enc b) (enc b') = if b = b' then 1 else 0

  spans : ∀ v : (ι → ZMod 2) → ℂ,
    v ∈ cssCodespace c → v ∈ Submodule.span ℂ (Set.range enc)

/-- The squared norm of a coefficient vector, defined as the sum of the squared complex norms of
its entries. -/
noncomputable def vecNormSq (ψ : (ι → ZMod 2) → ℂ) : ℝ := ∑ i, (ψ i).normSq

/-- The squared norm of the input vector after projection onto a specified CSS syndrome. -/
noncomputable def syndromeOutcomeMass (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (ψ : (ι → ZMod 2) → ℂ) : ℝ :=
  vecNormSq (cssSyndromeProjector c η *ᵥ ψ)

/-- The outer-product matrix of a coefficient vector, with entries `ψ i * star (ψ j)`. -/
noncomputable def densityOf (ψ : (ι → ZMod 2) → ℂ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  fun i j => ψ i * star (ψ j)

/-- The operator map that sums over syndrome projections followed by the program's Pauli
corrections. -/
noncomputable def recoveryChannel (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (ρ : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
    (fun P R => R * (P * ρ * P) * Matrix.conjTranspose R)
      (cssSyndromeProjector c η)
      (cssPauliX (prog.corr η).1 * cssPauliZ (prog.corr η).2)

/-- The property that the Pauli operator fixes every matrix whose columns lie in the CSS
codespace, for any finite reference index type. -/
noncomputable def LogicalReferencePreserved (c : CssData ι κX κZ) (e : PauliLabel ι) : Prop :=
  ∀ (ρ : Type) [Fintype ρ] (M : Matrix (ι → ZMod 2) ρ ℂ),
    (∀ r : ρ, (fun q => M q r) ∈ cssCodespace c) →
    (cssPauliX e.1 * cssPauliZ e.2) * M = M

/-- The gate count, measurement count, and classical decoding time assigned to a recovery. -/
structure RecoveryCost where

  gates : ℕ

  measurements : ℕ

  classicalTime : ℕ

/-- The total number of X and Z check indices, used as the syndrome measurement count. -/
def syndromeMeasurements (_c : CssData ι κX κZ) : ℕ := Fintype.card (κX ⊕ κZ)

/-- The sum of the Hamming weights of all X-check and Z-check rows, used as the syndrome
extraction gate count. -/
def syndromeExtractionGates (c : CssData ι κX κZ) : ℕ :=
  (∑ i : κX, bitWeight (c.hX i)) + (∑ j : κZ, bitWeight (c.hZ j))

/-- The Pauli weight of a correction label, used as its gate count. -/
def correctionGates (e : PauliLabel ι) : ℕ := pauliWeight e.1 e.2

/-- The recovery cost combining syndrome extraction gates, the chosen correction's weight, the
check count, and the assigned decoding time. -/
def recoveryCost (c : CssData ι κX κZ) (prog : RecoveryProgram c)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : RecoveryCost :=
  { gates := syndromeExtractionGates c + correctionGates (prog.corr η)
    measurements := syndromeMeasurements c
    classicalTime := prog.decodeTime η }

/-- The maximum assigned decoding time over all syndrome pairs. -/
def decodeTimeBound (c : CssData ι κX κZ) (prog : RecoveryProgram c) : ℕ :=
  Finset.univ.sup fun η : (κX → ZMod 2) × (κZ → ZMod 2) => prog.decodeTime η

/-- A record of the observed syndrome, applied Pauli label, and recovery cost. -/
structure RecoveryReceipt (c : CssData ι κX κZ) (prog : RecoveryProgram c) where

  η : (κX → ZMod 2) × (κZ → ZMod 2)

  applied : PauliLabel ι

  cost : RecoveryCost

/-- The property that a receipt records the true error syndrome, the program's correction for
that syndrome, and its assigned recovery cost. -/
def RecoveryReceipt.Realizes {c : CssData ι κX κZ} {prog : RecoveryProgram c}
    (r : RecoveryReceipt c prog) (e : PauliLabel ι) : Prop :=
  r.η = pauliSyndrome c e ∧ r.applied = prog.corr r.η ∧
    r.cost = recoveryCost c prog r.η

/-- A natural-number-indexed family of finite CSS codes with specified qubit counts and X-check
and Z-check counts. -/
structure CssFamily where

  N : ℕ → ℕ

  mX : ℕ → ℕ

  mZ : ℕ → ℕ

  code : (n : ℕ) → CssData (Fin (N n)) (Fin (mX n)) (Fin (mZ n))

/-- Uniform bounds on check weights and qubit incidences, together with a linear bound on the
total check count, at every positive family index. -/
def CssFamily.IsLdpc (f : CssFamily) (w inc a : ℕ) : Prop :=
  ∀ n, 0 < n →
    (f.code n).checkWeight ≤ w ∧ (f.code n).qubitIncidence ≤ inc ∧
      f.mX n + f.mZ n ≤ a * f.N n

/-- The property that each code at a positive family index has distance at least the prescribed
natural-number bound. -/
noncomputable def CssFamily.DistanceAtLeast (f : CssFamily) (d : ℕ → ℕ) : Prop :=
  ∀ n, 0 < n → (d n : ℕ∞) ≤ cssDistance (f.code n)

/-- The property that each code at a positive family index satisfies the prescribed CSS tester
soundness bound. -/
noncomputable def CssFamily.SoundnessAtLeast (f : CssFamily) (σ : ℕ → ℝ) : Prop :=
  ∀ n, 0 < n → cssHasSoundnessAtLeast (f.code n) (σ n)

/-- The existence of positive uniform rate and linear distance bounds for the family at every
positive index. -/
noncomputable def CssFamily.IsGood (f : CssFamily) : Prop :=
  ∃ (d : ℕ → ℕ) (C : ℕ) (r : ℚ), 0 < C ∧ 0 < r ∧
    f.DistanceAtLeast d ∧ (∀ n, 0 < n → f.N n ≤ C * d n) ∧
      (∀ n, 0 < n → r ≤ (f.code n).rate)

/-- The family with `n` qubits and one zero check of each type at index `n`. -/
def trivialFamily : CssFamily where
  N := fun n => n
  mX := fun _ => 1
  mZ := fun _ => 1
  code := fun n =>
    { hX := 0
      hZ := 0
      hcompat := by exact Matrix.zero_mul _ }

/-- The Bernoulli weight of an observed syndrome under independent flips of the true syndrome
bits with parameter `p`. -/
noncomputable def iidSyndromeLaw (c : CssData ι κX κZ)
    (ηtrue ηobs : (κX → ZMod 2) × (κZ → ZMod 2)) (p : ℝ) : ℝ :=
  p ^ syndromeDist ηtrue ηobs *
    (1 - p) ^ (syndromeMeasurements c - syndromeDist ηtrue ηobs)

/-- The sum of independent syndrome-noise weights over observations whose decoded residual is
not a stabilizer label. -/
noncomputable def noisyFailureMass {c : CssData ι κX κZ} (prog : RecoveryProgram c)
    (e : PauliLabel ι) (p : ℝ) : ℝ :=
  ∑ ηobs : (κX → ZMod 2) × (κZ → ZMod 2),
    if IsStabilizerLabel c (residualFromObserved prog e ηobs) then 0
    else iidSyndromeLaw c (pauliSyndrome c e) ηobs p

/-- A nonnegative normalized law on fault sets for which the mass of sets containing any fixed
subset `S` is at most `p ^ S.card`. -/
def LocalStochasticNoiseLaw {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (p : ℝ) : Prop :=
  (∀ F, 0 ≤ pp F) ∧ (∑ F ∈ Finset.univ, pp F = 1) ∧
    ∀ S ⊆ Finset.univ,
      ∑ F ∈ Finset.univ.filter (fun F => S ⊆ F), pp F ≤ p ^ S.card

/-- A nonnegative normalized law supported on fault sets of cardinality at most `a`. -/
def AdversarialFaultBudget {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (a : ℕ) : Prop :=
  (∀ F, 0 ≤ pp F) ∧ (∑ F ∈ Finset.univ, pp F = 1) ∧
    ∀ F, 0 < pp F → F.card ≤ a

/-- The total mass of fault sets whose cardinality exceeds the tolerance `t`. -/
noncomputable def gadgetFailureProb {ζ : ℕ} (pp : Finset (Fin ζ) → ℝ) (t : ℕ) : ℝ :=
  ∑ F ∈ Finset.univ.filter (fun F : Finset (Fin ζ) => t < F.card), pp F

/-- The kinds of gadgets: syndrome extraction rounds, gates, preparations, and measurements. -/
inductive GadgetKind where

  | syndromeRound

  | gate

  | prep

  | measure

/-- A gadget's kind, location count, space and time costs, ideal Pauli label, and residual label
for each fault set. -/
structure GadgetSpec (c : CssData ι κX κZ) where

  kind : GadgetKind

  locations : ℕ

  space : ℕ

  time : ℕ

  ideal : PauliLabel ι

  residual : Finset (Fin locations) → PauliLabel ι

/-- The property that the ideal label is a stabilizer label and equals the residual for the
empty fault set. -/
noncomputable def GadgetSpec.IsIdealCorrect {c : CssData ι κX κZ} (g : GadgetSpec c) : Prop :=
  IsStabilizerLabel c g.ideal ∧ g.residual ∅ = g.ideal

/-- The property that every fault set of size at most `t` produces a residual Pauli label of
weight at most `t`. -/
def GadgetSpec.IsFaultTolerantAt {c : CssData ι κX κZ} (g : GadgetSpec c) (t : ℕ) : Prop :=
  ∀ F : Finset (Fin g.locations), F.card ≤ t →
    pauliWeight (g.residual F).1 (g.residual F).2 ≤ t

/-- The product of a gadget's space and time costs. -/
def GadgetSpec.spaceTime {c : CssData ι κX κZ} (g : GadgetSpec c) : ℕ :=
  g.space * g.time

/-- The binomial failure-bound expression `choose locations (t + 1) * p ^ (t + 1)` for a gadget. -/
noncomputable def GadgetSpec.failureMass {c : CssData ι κX κZ} (g : GadgetSpec c)
    (t : ℕ) (p : ℝ) : ℝ :=
  (g.locations.choose (t + 1) : ℝ) * p ^ (t + 1)

/-- The sum of the individual gadget failure-bound expressions. -/
noncomputable def composedFailureMass {c : CssData ι κX κZ}
    (gs : List (GadgetSpec c)) (t : ℕ) (p : ℝ) : ℝ :=
  (gs.map fun g => g.failureMass t p).sum

/-- The common-location failure-bound expression obtained by multiplying the gadget count by
`choose ζ (t + 1) * p ^ (t + 1)`. -/
noncomputable def composedErrWindow {c : CssData ι κX κZ} (gs : List (GadgetSpec c))
    (ζ t : ℕ) (p : ℝ) : ℝ :=
  (gs.length : ℝ) * (ζ.choose (t + 1) : ℝ) * p ^ (t + 1)

/-- The sum of space times time over the gadget list. -/
def cumulativeSpaceTime {c : CssData ι κX κZ} (gs : List (GadgetSpec c)) : ℕ :=
  (gs.map fun g => g.space * g.time).sum

/-- The maximum gadget space cost, with value zero for an empty list. -/
def peakSpace {c : CssData ι κX κZ} (gs : List (GadgetSpec c)) : ℕ :=
  (gs.map fun g => g.space).foldr max 0

/-- A record of a finite CSS code, recovery program, gadget list, tolerance, location bound,
noise and error parameters, and resource budgets. -/
structure FtRealization where

  N : ℕ

  mX : ℕ

  mZ : ℕ

  code : CssData (Fin N) (Fin mX) (Fin mZ)

  prog : RecoveryProgram code

  t : ℕ

  ζ : ℕ

  gadgets : List (GadgetSpec code)

  pTh : ℝ

  ε : ℝ

  budget : ℕ

  peak : ℕ

end Qatlib.Concepts.CodingDecoding.CssTesters
