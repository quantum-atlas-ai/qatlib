/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Depth3Learn26 — source model

Arunachalam, Dutt, Gheorghiu, de Oliveira,
*Learning depth-3 circuits via quantum agnostic boosting*,
fixed arXiv:2509.14461v3 (2026-02-17).

This module fixes state and specification vocabulary; it proves no learning algorithm:

* `Cube n = Fin n → Bool` is the Boolean cube and `BoolFun n` a Boolean function on it.
* `QVec n` is an (unnormalised) `n`-qubit pure state in the computational basis.
* `phaseState f` is the phase state `|φ_f⟩ = 2^{-n/2} Σ_x (-1)^{f(x)} |x⟩` (Eq. (4), p.14).
* `parityFun s`, `parityState s` are the parity functions/phase states (Section 2.2, p.13).
* `classFidelity C ψ` is `F_C(|ψ⟩) = max_{c ∈ C} |⟨φ_c|ψ⟩|²` (Eq. (6) vicinity, p.14).
* `projState T ψ` is the projection `Λ_T |ψ⟩ = Σ_{i} ⟨χ_i|ψ⟩ |χ_i⟩` onto parities (Eq. (8)/(9), p.18).
* `Randomized α` models a randomised algorithm output distribution; `successMass` is the
  probability mass of a successful set of outputs, so that "with probability ≥ 1 - δ" is an
  honest probability statement rather than a bare existential.
* `WeakAgnosticLearner` records an output-existence promise and unverified resource labels.

Boundary: the model treats an `n`-qubit state as a finite vector of complex amplitudes and
resource labels as real numbers. `AlgorithmExecution` adds a conditional interpretation in
a supplied primitive step model. Its bounds count steps and sample charges of the same
word that produces the output. No implementation of the paper's learner, or main learning
or complexity theorem, is present. `weakAgnosticLearner_statement` is a specification only.
-/

set_option autoImplicit false

namespace Qatlib.Papers.Depth3Learn26.MainResults

noncomputable section

open scoped BigOperators

/-- The Boolean cube on `n` bits. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Boolean functions on the `n`-bit cube. -/
abbrev BoolFun (n : ℕ) := Cube n → Bool

/-- An (unnormalised) `n`-qubit pure state, as complex amplitudes on the computational basis. -/
abbrev QVec (n : ℕ) := Cube n → ℂ

/-- Dirac overlap `⟨ψ|φ⟩ = Σ_x conj(ψ x) * φ x`. -/
def qInner {n : ℕ} (ψ φ : QVec n) : ℂ := ∑ x, star (ψ x) * φ x

/-- Squared Hilbert-space norm `‖ψ‖² = Σ_x |ψ x|²`, a nonnegative real. -/
def qNormSq {n : ℕ} (ψ : QVec n) : ℝ := ∑ x, Complex.normSq (ψ x)

/-- A normalised (unit) state. -/
def Normalized {n : ℕ} (ψ : QVec n) : Prop := qNormSq ψ = 1

/-- Fidelity `|⟨ψ|φ⟩|²` between two states (the paper's `|⟨ψ|φ⟩|²`). -/
def fidelity {n : ℕ} (ψ φ : QVec n) : ℝ := Complex.normSq (qInner ψ φ)

/-- The sign `(-1)^b` as a complex number. -/
def signC (b : Bool) : ℂ := if b then -1 else 1

/-- Phase state of a Boolean function, Eq. (4), p.14:
`|φ_f⟩ = 2^{-n/2} Σ_x (-1)^{f(x)} |x⟩`. -/
def phaseState {n : ℕ} (f : BoolFun n) : QVec n :=
  fun x => signC (f x) / (Real.sqrt ((2 : ℝ) ^ n) : ℂ)

/-- Parity pairing `s · x = Σ_i s_i x_i` as a natural number (Section 2.1, p.13). -/
def parityDot {n : ℕ} (s x : Cube n) : ℕ :=
  ∑ i, (if s i then 1 else 0) * (if x i then 1 else 0)

/-- The parity function `χ_s(x) = (-1)^{s·x}` as a Boolean-valued function. -/
def parityFun {n : ℕ} (s : Cube n) : BoolFun n :=
  fun x => decide (parityDot s x % 2 = 1)

/-- The parity phase state `|χ_s⟩` (Section 2.2, p.13). -/
def parityState {n : ℕ} (s : Cube n) : QVec n := phaseState (parityFun s)

/-- A state is a parity state if it is some `|χ_s⟩`. -/
def IsParity {n : ℕ} (φ : QVec n) : Prop := ∃ s, φ = parityState s

/-- Class fidelity `F_C(|ψ⟩) = max_{c ∈ C} |⟨φ_c|ψ⟩|²` (Section 2.3, p.14). -/
def classFidelity {n : ℕ} (C : Set (BoolFun n)) (ψ : QVec n) : ℝ :=
  sSup ((fun f => fidelity ψ (phaseState f)) '' C)

/-- Membership in the unit complex ball `B_∞^k`: every coordinate has modulus in `(0,1]`
(Section 2.1, p.13). -/
def InBInf {k : ℕ} (β : Fin k → ℂ) : Prop := ∀ i, ‖β i‖ ∈ Set.Ioc (0 : ℝ) 1

/-- The linear combination `Σ_{i<k} β_i |χ_{χ_i}⟩` of parity states. -/
def linearCombination {n k : ℕ} (β : Fin k → ℂ) (χ : Fin k → Cube n) : QVec n :=
  fun x => ∑ i, β i * parityState (χ i) x

/-- Projection of `|ψ⟩` onto the span of the parity states indexed by a finite set `T`,
Eq. (8)/(9), p.18: `Λ_T|ψ⟩ = Σ_{s ∈ T} ⟨χ_s|ψ⟩ |χ_s⟩`. -/
def projState {n : ℕ} (T : Finset (Cube n)) (ψ : QVec n) : QVec n :=
  fun x => ∑ s ∈ T, qInner (parityState s) ψ * parityState s x

/-- Squared overlap of `|ψ⟩` with its own projection, the quantity
`|⟨ψ|(Λ_T|ψ⟩)|²` of Lemma 3.11, p.25. -/
def projFidelity {n : ℕ} (T : Finset (Cube n)) (ψ : QVec n) : ℝ :=
  fidelity ψ (projState T ψ)

/-- A randomised algorithm output, as a finitely supported probability distribution. -/
structure Randomized (α : Type) [Fintype α] where
  /-- Probability of each output. -/
  prob : α → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- Probabilities sum to one. -/
  sum_one : (∑ a, prob a) = 1

/-- Probability mass of the successful outputs of a randomised algorithm. -/
noncomputable def successMass {α : Type} [Fintype α] (r : Randomized α)
    (P : α → Prop) : ℝ := by
  classical
  exact ∑ a, if P a then r.prob a else 0

/-- Output-existence specification inspired by Definition 3.1 (p.17).
`samples` and `time` are unverified labels, independent of `guarantee`.
Use `weakAgnosticLearner_statement` to request an implementation contract.
The `guarantee` field is the probabilistic
promise: for every state with class fidelity at least `τ`, some output distribution over
parity indices puts mass at least `1 - δ` on indices whose parity state has fidelity at
least `η τ` with the input. -/
structure WeakAgnosticLearner (n : ℕ) (C : Set (BoolFun n)) (η : ℝ → ℝ) where
  /-- Unverified sample label. -/
  samples : ℝ
  /-- Unverified time label. -/
  time : ℝ
  /-- The agnostic promise of Definition 3.1. -/
  guarantee : ∀ (τ δ : ℝ), 0 < τ → τ ≤ 1 → 0 < δ → δ < 1 → ∀ ψ : QVec n,
    Normalized ψ → classFidelity C ψ ≥ τ →
      ∃ r : Randomized (Cube n),
        successMass r (fun s => η τ ≤ fidelity ψ (parityState s)) ≥ 1 - δ

/-- Squared Euclidean norm of a coefficient vector, `‖β‖₂²`. -/
def coeffNormSq {k : ℕ} (β : Fin k → ℂ) : ℝ := ∑ i, Complex.normSq (β i)

/-- A finite-seed output function with unverified resource labels.
`run` alone supplies no execution or runtime semantics; see `AlgorithmExecution`. -/
structure RandomizedAlgorithm (α : Type) where
  /-- The finite random seed type. -/
  seeds : Type
  /-- Fintype instance for the seed type. -/
  fintypeSeeds : Fintype seeds
  /-- Nonemptiness of the seed type. -/
  nonemptySeeds : Nonempty seeds
  /-- Unverified sample label. -/
  samples : ℝ
  /-- Unverified time label. -/
  time : ℝ
  /-- The output on a given seed. -/
  run : seeds → α

/-- Success probability of a finite-seed randomised algorithm: the fraction of seeds on
which the output satisfies `P`. -/
def successProb {Ω α : Type} [Fintype Ω] (run : Ω → α) (P : α → Prop) : ℝ := by
  classical
  exact (∑ ω, if P (run ω) then (1 : ℝ) else 0) / (Fintype.card Ω)

/-- Success probability of a `RandomizedAlgorithm`. -/
def algSuccess {α : Type} (A : RandomizedAlgorithm α) (P : α → Prop) : ℝ :=
  @successProb A.seeds α A.fintypeSeeds A.run P

/-- Conditional execution contract in a supplied primitive model. Initialization,
readout and each primitive's semantics and sample charge are assumptions of that
model, not a gate synthesis result. Every executed instruction costs one time unit.
Initialization, readout and word generation are excluded; total runtime claims
would also require their costs to be represented in the primitive model.
The same instruction word determines both the output and the resource bounds. -/
structure AlgorithmExecution {α : Type} (A : RandomizedAlgorithm α)
    (State Instruction : Type) (initial : A.seeds → State)
    (step : State → Instruction → State) (readout : State → α)
    (sampleCharge : Instruction → ℕ) where
  word : A.seeds → List Instruction
  output_eq : ∀ ω, A.run ω = readout ((word ω).foldl step (initial ω))
  time_bound : ∀ ω, ((word ω).length : ℝ) ≤ A.time
  samples_bound : ∀ ω, (((word ω).map sampleCharge).sum : ℝ) ≤ A.samples

/-- A nonempty executed word rules out a zero time label, conditional on the
primitive execution contract. -/
theorem AlgorithmExecution.time_pos {α : Type} {A : RandomizedAlgorithm α}
    {State Instruction : Type} {initial : A.seeds → State}
    {step : State → Instruction → State} {readout : State → α}
    {sampleCharge : Instruction → ℕ}
    (h : AlgorithmExecution A State Instruction initial step readout sampleCharge)
    (ω : A.seeds) (hne : h.word ω ≠ []) : 0 < A.time :=
  lt_of_lt_of_le (Nat.cast_pos.mpr (List.length_pos_iff.mpr hne)) (h.time_bound ω)

/-- **Statement only — not proved in Qatlib.**
A resource-supported version of the weak promise, relative to supplied primitive
semantics. For each admissible input it requests a finite-seed execution with
the stated success probability and budgets. No such execution is constructed here. -/
def weakAgnosticLearner_statement {n : ℕ} {C : Set (BoolFun n)} {η : ℝ → ℝ}
    (L : WeakAgnosticLearner n C η) (State Instruction : Type)
    (initial : QVec n → ℕ → State) (step : State → Instruction → State)
    (readout : State → Cube n) (sampleCharge : Instruction → ℕ) : Prop :=
  ∀ (τ δ : ℝ), 0 < τ → τ ≤ 1 → 0 < δ → δ < 1 → ∀ ψ : QVec n,
    Normalized ψ → τ ≤ classFidelity C ψ →
    ∃ (A : RandomizedAlgorithm (Cube n)) (seed : A.seeds → ℕ),
      Nonempty (AlgorithmExecution A State Instruction (fun ω => initial ψ (seed ω))
        step readout sampleCharge) ∧ A.time ≤ L.time ∧ A.samples ≤ L.samples ∧
      1 - δ ≤ algSuccess A (fun s => η τ ≤ fidelity ψ (parityState s))

/-- The paper's universal constant `C = (2/3)^{1/η₂ + 1}` from Theorem 3.2, p.17. -/
def boostingConstant (η2 : ℝ) : ℝ := Real.rpow (2 / 3) (1 / η2 + 1)

/-- The paper's `υ = η(C ε² / 16)` from Theorem 3.2, p.17. -/
def boostingUpsilon (η1 η2 ε : ℝ) : ℝ :=
  η1 * Real.rpow (boostingConstant η2 * ε ^ 2 / 16) η2

/-- Theorem 3.7's `ε'_s = (3/2)^{1/η₂+1} ε_s` (p.21). -/
def structureEpsPrime (η2 εs : ℝ) : ℝ := Real.rpow (3 / 2) (1 / η2 + 1) * εs

/-- Lemma 4.9's `s* = (s/τ)^{O(log log(s/τ)·log(1/τ))}`, with the constant set to one
(p.35). -/
def dnfStar (s τ : ℝ) : ℝ :=
  Real.rpow (s / τ) (Real.log (Real.log (s / τ)) * Real.log (1 / τ))

end

end Qatlib.Papers.Depth3Learn26.MainResults
