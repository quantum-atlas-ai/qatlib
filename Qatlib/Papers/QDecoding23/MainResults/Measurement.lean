/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QDecoding23.MainResults.Definitions
import QuantumInfo.Measurements.POVM
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option backward.isDefEq.respectTransparency false

/-!
# QDecoding23 — measurement, notation and state helpers

Source: Chailloux--Tillich, *The Quantum Decoding Problem*, fixed arXiv:2310.20651v1
(2023-10-31).

This module collects the small vocabulary shared by the claim files: the q-ary
`x^⊥` of Notation 1 (p.9), Born probabilities for effects/POVM outcomes, the binary
and q-ary noisy states of §3 / §4, and the embedding of a qubit into the 3-dimensional
space of Lemma 5.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QDecoding23.MainResults

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath.Reflection

/-! ## `x^⊥` (Notation 1, p.9) -/

/-- Notation 1, p.9: the q-ary `x^⊥ = (√((q-1)(1-x)) - √x)² / q`, which for `q = 2` gives
`(1 - 2√(x(1-x)))/2`. -/
def perpProb (q x : ℝ) : ℝ := (Real.sqrt ((q - 1) * (1 - x)) - Real.sqrt x) ^ 2 / q

/-! ## Born probabilities -/

/-- The Born probability `⟨ψ|A|ψ⟩` of an effect `A` on the pure state `ψ`, for an arbitrary
finite index type (used for the qubit and q-ary registers, which are not `FVec` types). -/
def probOf {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (ψ : QState I) : ℝ :=
  (Qatlib.Foundations.PureStateMath.Inner ψ (A *ᵥ ψ)).re

/-- The probability that the POVM `Λ` returns outcome `a` on the pure state `ψ`. -/
def probPOVM {X I : Type} [Fintype X] [Fintype I] [DecidableEq I] (Λ : POVM X I) (a : X)
    (ψ : QState I) : ℝ :=
  probOf (Λ.mats a).mat ψ

/-! ## Binary states of §3 -/

/-- §3 (p.8): the qubit state `|ψ_b^p⟩ = √(1-p)|b⟩ + √p|1-b⟩`. -/
def qubitNoisyState (p : ℝ) (b : Fin 2) : QState (Fin 2) :=
  fun i => if i = b then ((Real.sqrt (1 - p) : ℝ) : ℂ) else ((Real.sqrt p : ℝ) : ℂ)

/-- The complement of a bit. -/
def bitNot (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

/-- Embed a qubit state into the 3-dimensional space `span{|0⟩,|1⟩,|2⟩}` of Lemma 5 (p.23). -/
def embed2to3 (ψ : QState (Fin 2)) : QState (Fin 3) := ![ψ 0, ψ 1, 0]

/-- Lemma 5 (p.23): `α = √(ω^⊥/(ω')^⊥)`. -/
def lemma5Alpha (ω ω' : ℝ) : ℝ := Real.sqrt (perpProb 2 ω / perpProb 2 ω')

/-- Lemma 5 (p.23): `β = √(1 - α²)`. -/
def lemma5Beta (ω ω' : ℝ) : ℝ := Real.sqrt (1 - (lemma5Alpha ω ω') ^ 2)

/-! ## q-ary states of §4 -/

/-- §4 (p.29): the q-ary symmetric USD state
`|ψ_a⟩ = √(1-ω)|a⟩ + ∑_{b≠a} √(ω/(q-1))|b⟩`, indexed by the field elements. -/
def qaryUsdState {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (ω : ℝ) (a : 𝔽) :
    QState 𝔽 :=
  fun b => if b = a then ((Real.sqrt (1 - ω) : ℝ) : ℂ)
           else ((Real.sqrt (ω / ((Fintype.card 𝔽 : ℝ) - 1)) : ℝ) : ℂ)

/-- Definition 13 (p.15): the n-coordinate noisy codeword state
`|ψ_c⟩ = ∑_e √(P(e)) |c + e⟩`, with the q-ary symmetric channel `P(e) =
(ω/(q-1))^{|e|}(1-ω)^{n-|e|}`; here written as the product of per-coordinate amplitudes. -/
def tensorNoisyState {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ω : ℝ) (c : FVec 𝔽 n) : QState (FVec 𝔽 n) :=
  fun y => ∏ i : Fin n,
    (if y i = c i then ((Real.sqrt (1 - ω) : ℝ) : ℂ)
     else ((Real.sqrt (ω / ((Fintype.card 𝔽 : ℝ) - 1)) : ℝ) : ℂ))

/-- Proposition 17 (p.30): `u = √(ω^⊥ / ((1-ω^⊥)(q-1)))`. -/
def lemma17u (q ω : ℝ) : ℝ := Real.sqrt (perpProb q ω / ((1 - perpProb q ω) * (q - 1)))

end Qatlib.Papers.QDecoding23.MainResults
