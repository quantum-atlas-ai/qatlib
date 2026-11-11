/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Probability.ProbabilityMassFunction.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — source core model

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013), 22 pages.

This file records the elementary source objects reused by the paper layer:

* `sourceC` — the dispersiveness `C(U)` of Eq. (2), also Eq. (10)/(11),
  `C(U) = −log₂ max_{i,j} |Uᵢⱼ|²`.
* `sourceSignVec` — the normalised sign vector `|f⟩` of Eq. (4)/(5).
* `sourceAcceptance` — the algorithm's acceptance probability
  `p_U(f,g) = |⟨g| U |f⟩|²` of Eq. (6).
* `sourceUniformMean` — the average of `p_U` over independent uniform sign
  pairs (the left-hand expectation of Proposition II.1(i)).
* `SignPairLaw`, `sourceCorrelatedMass`, `sourceCorrelatedMean` — a finite
  probability-law interface on sign pairs, and the *concrete* Gaussian
  correlated law of Section II A: `v` is a real `2N`-dimensional standard
  Gaussian, `f(x) = sgn(Re v_x)`, `g(x) = sgn(Re((Uv)_x))`.

Boundary: only the source definitions needed to state the paper's results are
introduced. No claim is made here; each result lives in its own file. No Haar
measure on the unitary group is assumed: approximate designs are represented by
their twirl-difference residual (defined in `SourceDesign.lean`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace Model

/-- Source Eq. (2)/(10)/(11): the dispersiveness
`C(U) = −log₂ max_{i,j} |Uᵢⱼ|²` of a square complex matrix. -/
noncomputable def sourceC {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  - Real.logb 2 (sSup (Set.range fun p : Fin N × Fin N => ‖U p.1 p.2‖ ^ 2))

/-- Source Eq. (4)/(5): the normalised sign vector
`|f⟩ = 2^{-n/2} ∑ₓ (−1)^{f(x)} |x⟩`, written for `N = 2ⁿ` basis states.
It is a unit vector whenever `N > 0`. -/
noncomputable def sourceSignVec {N : ℕ} (f : Fin N → Bool) : Fin N → ℂ :=
  fun x => ((if f x then (-1 : ℂ) else 1) / (Real.sqrt (N : ℝ) : ℂ))

/-- Source Eq. (6): the acceptance probability `p_U(f,g) = |⟨g| U |f⟩|²`
of the quantum algorithm for `U`-circuit checking. -/
noncomputable def sourceAcceptance {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (f g : Fin N → Bool) : ℝ :=
  ‖∑ x : Fin N, star (sourceSignVec g x) * (∑ y : Fin N, U x y * sourceSignVec f y)‖ ^ 2

/-- The average of `p_U` over independent, uniformly random sign pairs
`f, g` — the expectation appearing in Proposition II.1, Eq. (7). -/
noncomputable def sourceUniformMean {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ((Fintype.card (Fin N → Bool) : ℝ))⁻¹ * ((Fintype.card (Fin N → Bool) : ℝ))⁻¹ *
    ∑ f : Fin N → Bool, ∑ g : Fin N → Bool, sourceAcceptance U f g

/-- A probability mass function on sign-vector pairs `(f, g) ∈ ({0,1}ⁿ)²`.
This is the finite model of *any* law on sign pairs, including the pushforward
of the Gaussian correlated law of Section II A. -/
structure SignPairLaw (N : ℕ) where
  /-- probability of the pair `(f, g)`. -/
  mass : (Fin N → Bool) → (Fin N → Bool) → ℝ
  mass_nonneg : ∀ f g, 0 ≤ mass f g
  total_mass : ∑ f : Fin N → Bool, ∑ g : Fin N → Bool, mass f g = 1

namespace SignPairLaw

/-- Expectation of the acceptance probability under a pair law. -/
noncomputable def expect {N : ℕ} (ℓ : SignPairLaw N)
    (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ f : Fin N → Bool, ∑ g : Fin N → Bool, ℓ.mass f g * sourceAcceptance U f g

end SignPairLaw

/-- The i.i.d. standard-real-normal measure on the `2N` real coordinates that
encode a complex vector `v ∈ ℂᴺ` (`Re v₀, Im v₀, Re v₁, Im v₁, …`). -/
noncomputable def sourceComplexNormalMeasure (N : ℕ) : Measure (Fin (2 * N) → ℝ) :=
  Measure.pi (fun _ : Fin (2 * N) => ProbabilityTheory.gaussianReal 0 1)

/-- Real part of the `x`-th encoded complex coordinate. -/
def sourceRealPart {N : ℕ} (v : Fin (2 * N) → ℝ) (x : Fin N) : ℝ :=
  v ⟨2 * x.val, by omega⟩

/-- Imaginary part of the `x`-th encoded complex coordinate. -/
def sourceImagPart {N : ℕ} (v : Fin (2 * N) → ℝ) (x : Fin N) : ℝ :=
  v ⟨2 * x.val + 1, by omega⟩

/-- The complex vector encoded by `2N` real Gaussian coordinates. -/
def sourceComplexVec {N : ℕ} (v : Fin (2 * N) → ℝ) : Fin N → ℂ :=
  fun x => (sourceRealPart v x : ℂ) + Complex.I * (sourceImagPart v x : ℂ)

/-- Matrix–vector product `(U v)ₓ = ∑ᵧ Uₓᵧ vᵧ` (Eq. (3)). -/
def sourceUApply {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) : Fin N → ℂ :=
  fun x => ∑ y : Fin N, U x y * v y

/-- The sign map `sgn` interpreted as a Boolean (`true` for `≥ 0`). -/
def sourceSignBool (r : ℝ) : Bool := decide (0 ≤ r)

/-- The event (in the Gaussian sample space) that the signs of
`(Re v₀, …, Re v_{N−1}, Re(Uv)₀, …, Re(Uv)_{N−1})` equal `(f, g)`. -/
def sourceCorrelatedSignSet {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (f g : Fin N → Bool) : Set (Fin (2 * N) → ℝ) :=
  {v | (∀ x : Fin N, sourceSignBool (sourceRealPart v x) = f x) ∧
       (∀ x : Fin N, sourceSignBool ((sourceUApply U (sourceComplexVec v) x).re) = g x)}

/-- The mass of `(f, g)` under the Gaussian correlated law of Section II A:
the pushforward, through the sign map, of the i.i.d. standard-normal measure on
`2N` real coordinates. -/
noncomputable def sourceCorrelatedMass {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ)
    (f g : Fin N → Bool) : ℝ :=
  (sourceComplexNormalMeasure N (sourceCorrelatedSignSet U f g)).toReal

/-- The expectation `E[p_U(f,g)]` when `f = sgn(Re v)` and
`g = sgn(Re(Uv))` for a complex standard Gaussian vector `v` — the
left-hand side of Proposition II.1, Eq. (8), and the quantity that Theorem V
estimates. -/
noncomputable def sourceCorrelatedMean {N : ℕ} (U : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ f : Fin N → Bool, ∑ g : Fin N → Bool,
    sourceCorrelatedMass U f g * sourceAcceptance U f g

end Model
end Qatlib.Papers.ExpSpeedup10.MainResults
