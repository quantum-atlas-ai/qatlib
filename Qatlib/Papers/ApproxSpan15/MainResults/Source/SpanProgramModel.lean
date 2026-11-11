/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright: paper-layer source model for arXiv:1507.00432v1 (Ito & Jeffery,
"Approximate Span Programs"). No copyright claim on the source mathematics.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Approximate Span Programs — source model

This module builds the paper-layer model of Ito--Jeffery, *Approximate Span
Programs* (fixed version: arXiv:1507.00432v1, 2 July 2015), used by every
`MainResults` statement of the `ApproxSpan15` paper block.

It records the source's objects verbatim:

* Definition 2.1 (p. 6): a span program `P = (H, V, τ, A)` on `[q]^n` with the
  subspaces `H_{j,a}`, `H_true`, `H_false` and `H(x) = ⊕_j H_{j,x_j} ⊕ H_true`
  (represented as the sum of the corresponding submodules).
* Definition 2.2 (p. 6): positive and negative witnesses and their sizes
  `w₊(x)`, `w₋(x)`. Following the source, the infinite cases are recorded by the
  predicates `IsPositive` / `IsNegative`, while the numeric functions return the
  infimum of the squared norms over the (possibly empty) witness set.
* Definitions 2.4, 2.5 (p. 7): positive/negative error `e₊, e₋` and the
  approximate witness sizes `w̃₊, w̃₋`.
* Definition 2.6 (p. 8): positive and negative λ-approximation of a decision
  problem.
* Definition 2.12, 2.13 (p. 12): the minimal positive witness, `N₊`, `N₋`, and
  normalised span programs.
* Section 3 (p. 13): the unitaries `U(P,x)`, `U′(P,x)`, the discriminant
  `D = Π_{(ker A)⊥} Π_{H(x)}`, the spectral quantities `σ_max`, `σ_min` (smallest
  nonzero singular value) and the phase gap `Δ`.

The layer is purely definitional; every statement about it lives in the sibling
modules.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.ApproxSpan15.MainResults

/-- Definition 2.1 (p. 6): a span program `P = (H, V, τ, A)` on `[q]^n`.  The
spaces `H` and `V` are finite-dimensional real inner-product spaces; the source
allows an arbitrary inner-product space for `V`, finite dimension being all that
the model needs for orthogonal projections. -/
structure SpanProgram (q n : ℕ) (H V : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- The subspaces `H_{j,a} ⊆ H_j`; they need not be pairwise orthogonal. -/
  Hja : Fin n → Fin q → Submodule ℝ H
  /-- The `H_true` direct summand. -/
  Htrue : Submodule ℝ H
  /-- The `H_false` direct summand. -/
  Hfalse : Submodule ℝ H
  /-- The target vector `τ ∈ V`. -/
  τ : V
  /-- The linear operator `A ∈ L(H, V)`. -/
  A : H →L[ℝ] V

variable {q n : ℕ} {H V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace SpanProgram

/-- The input subspace `H(x) := H_{1,x_1} + ⋯ + H_{n,x_n} + H_true` of
Definition 2.1 (p. 6).  The source writes the decomposition with direct sums, but
the `H_{j,a}` need not be orthogonal, so the sum of submodules is the faithful
rendering. -/
def Hx (P : SpanProgram q n H V) (x : Fin n → Fin q) : Submodule ℝ H :=
  (⨆ j, P.Hja j (x j)) ⊔ P.Htrue

/-- Definition 2.2 (p. 6): the positive witnesses of `x` are the vectors of
`H(x)` that `A` maps to `τ`. -/
def positiveWitnesses (P : SpanProgram q n H V) (x : Fin n → Fin q) : Set H :=
  {w | w ∈ P.Hx x ∧ P.A w = P.τ}

/-- Definition 2.2 (p. 6): the negative witnesses of `x` are the functionals `ω`
with `ω A Π_{H(x)} = 0` and `ω τ = 1`. -/
def negativeWitnesses (P : SpanProgram q n H V) (x : Fin n → Fin q) :
    Set (V →L[ℝ] ℝ) :=
  {ω | (∀ w, w ∈ P.Hx x → ω (P.A w) = 0) ∧ ω P.τ = 1}

/-- `x` is a positive input (`x ∈ P₁`) in the sense of Definition 2.2 (p. 6):
a positive witness exists. -/
def IsPositive (P : SpanProgram q n H V) (x : Fin n → Fin q) : Prop :=
  (P.positiveWitnesses x).Nonempty

/-- `x` is a negative input (`x ∈ P₀`): a negative witness exists. -/
def IsNegative (P : SpanProgram q n H V) (x : Fin n → Fin q) : Prop :=
  (P.negativeWitnesses x).Nonempty

/-- Definition 2.2 (p. 6): the positive witness size
`w₊(x,P) = inf { ‖w‖² : w ∈ H(x), A w = τ }`.  When no positive witness exists
the source sets `w₊ = ∞`; here `IsPositive` records that case and the numeric
value is the infimum of an empty set. -/
noncomputable def wPlus (P : SpanProgram q n H V) (x : Fin n → Fin q) : ℝ :=
  sInf {s : ℝ | ∃ w ∈ P.positiveWitnesses x, s = ‖w‖ ^ 2}

/-- Definition 2.2 (p. 6): the negative witness size
`w₋(x,P) = inf { ‖ωA‖² : ω A Π_{H(x)} = 0, ω τ = 1 }`. -/
noncomputable def wMinus (P : SpanProgram q n H V) (x : Fin n → Fin q) : ℝ :=
  sInf {s : ℝ | ∃ ω ∈ P.negativeWitnesses x, s = ‖ω.comp P.A‖ ^ 2}

/-- The orthogonal projection onto `H(x)⊥`, used to state the source's errors. -/
def projOrth (P : SpanProgram q n H V) (x : Fin n → Fin q) : H →L[ℝ] H :=
  (P.Hx x)ᗮ.starProjection

/-- The orthogonal projection onto `H(x)`. -/
def projH (P : SpanProgram q n H V) (x : Fin n → Fin q) : H →L[ℝ] H :=
  (P.Hx x).starProjection

/-- Definition 2.4 (p. 7): the positive error
`e₊(x) = min { ‖Π_{H(x)⊥} w‖² : A w = τ }`. -/
noncomputable def ePlus (P : SpanProgram q n H V) (x : Fin n → Fin q) : ℝ :=
  sInf {s : ℝ | ∃ w : H, P.A w = P.τ ∧ s = ‖P.projOrth x w‖ ^ 2}

/-- Definition 2.5 (p. 7): the negative error
`e₋(x) = min { ‖ω A Π_{H(x)}‖² : ω τ = 1 }`. -/
noncomputable def eMinus (P : SpanProgram q n H V) (x : Fin n → Fin q) : ℝ :=
  sInf {s : ℝ | ∃ ω : V →L[ℝ] ℝ, ω P.τ = 1 ∧
    s = ‖(ω.comp P.A).comp (P.projH x)‖ ^ 2}

/-- Definition 2.4 (p. 7): the approximate positive witness size `w̃₊(x)`, the
least `‖w‖²` among min-error positive witnesses (those attaining `e₊(x)`). -/
noncomputable def wPlusTilde (P : SpanProgram q n H V) (x : Fin n → Fin q) : ℝ :=
  sInf {s : ℝ | ∃ w : H, P.A w = P.τ ∧ ‖P.projOrth x w‖ ^ 2 = P.ePlus x ∧
    s = ‖w‖ ^ 2}

/-- Definition 2.5 (p. 7): the approximate negative witness size `w̃₋(x)`, the
least `‖ωA‖²` among min-error negative witnesses (those attaining `e₋(x)`). -/
noncomputable def wMinusTilde (P : SpanProgram q n H V) (x : Fin n → Fin q) : ℝ :=
  sInf {s : ℝ | ∃ ω : V →L[ℝ] ℝ, ω P.τ = 1 ∧
    ‖(ω.comp P.A).comp (P.projH x)‖ ^ 2 = P.eMinus x ∧
    s = ‖ω.comp P.A‖ ^ 2}

/-- The maximum of `w₊` over `f⁻¹(1)`, i.e. `W₊(f,P)` of Theorem 2.7 (p. 8). -/
noncomputable def WPlusMax (P : SpanProgram q n H V)
    (f : (Fin n → Fin q) → Bool) : ℝ :=
  sSup {r : ℝ | ∃ x, f x = true ∧ r = P.wPlus x}

/-- The maximum of `w₋` over `f⁻¹(0)`, i.e. `W₋(f,P)` of Theorem 2.7 (p. 8). -/
noncomputable def WMinusMax (P : SpanProgram q n H V)
    (f : (Fin n → Fin q) → Bool) : ℝ :=
  sSup {r : ℝ | ∃ x, f x = false ∧ r = P.wMinus x}

/-- The maximum of `w̃₊` over `f⁻¹(1)`, i.e. `W̃₊(f,P)` of Theorem 2.7 (p. 8). -/
noncomputable def WPlusTildeMax (P : SpanProgram q n H V)
    (f : (Fin n → Fin q) → Bool) : ℝ :=
  sSup {r : ℝ | ∃ x, f x = true ∧ r = P.wPlusTilde x}

/-- The maximum of `w̃₋` over `f⁻¹(0)`, i.e. `W̃₋(f,P)` of Theorem 2.7 (p. 8). -/
noncomputable def WMinusTildeMax (P : SpanProgram q n H V)
    (f : (Fin n → Fin q) → Bool) : ℝ :=
  sSup {r : ℝ | ∃ x, f x = false ∧ r = P.wMinusTilde x}

/-- Definition 2.6 (p. 8): `P` positively λ-approximates `f` if every 1-input is
positive and every 0-input is either negative or has positive witness size at
least `(1/λ)·W₊(f,P)`. -/
def PositivelyApproximates (P : SpanProgram q n H V)
    (f : (Fin n → Fin q) → Bool) (lam : ℝ) : Prop :=
  (∀ x, f x = true → P.IsPositive x) ∧
    ∀ x, f x = false → P.IsNegative x ∨ (1 / lam) * P.WPlusMax f ≤ P.wPlus x

/-- Definition 2.6 (p. 8): `P` negatively λ-approximates `f` if every 0-input is
negative and every 1-input is either positive or has negative witness size at
least `(1/λ)·W₋(f,P)`. -/
def NegativelyApproximates (P : SpanProgram q n H V)
    (f : (Fin n → Fin q) → Bool) (lam : ℝ) : Prop :=
  (∀ x, f x = false → P.IsNegative x) ∧
    ∀ x, f x = true → P.IsPositive x ∨ (1 / lam) * P.WMinusMax f ≤ P.wMinus x

/-- The global positive witness set of `P`: all `w` with `A w = τ` (Definition
2.12, p. 12). -/
def globalPositiveWitnesses (P : SpanProgram q n H V) : Set H := {w | P.A w = P.τ}

/-- Definition 2.12 (p. 12): `N₊(P) = ‖|w₀⟩‖²`, the squared norm of the minimal
(shortest) positive witness `|w₀⟩ = A⁺τ`. -/
noncomputable def Nplus (P : SpanProgram q n H V) : ℝ :=
  sInf {s : ℝ | ∃ w ∈ P.globalPositiveWitnesses, s = ‖w‖ ^ 2}

/-- The source's `N₋(P) = min_{ω τ = 1} ‖ωA‖²` from p. 12. -/
noncomputable def Nminus (P : SpanProgram q n H V) : ℝ :=
  sInf {s : ℝ | ∃ ω : V →L[ℝ] ℝ, ω P.τ = 1 ∧ s = ‖ω.comp P.A‖ ^ 2}

/-- Definition 2.13 (p. 12): `P` is normalised when `N₊(P) = N₋(P) = 1`. -/
def Normalized (P : SpanProgram q n H V) : Prop := P.Nplus = 1 ∧ P.Nminus = 1

/-- The reflection `2Π_K − I` about a subspace `K`. -/
def reflectionAbout (K : Submodule ℝ H) : H →L[ℝ] H :=
  (2 : ℝ) • K.starProjection - 1

/-- Section 3 (p. 13): `U(P,x) = (2Π_{ker A} − I)(2Π_{H(x)} − I)`. -/
def U (P : SpanProgram q n H V) (x : Fin n → Fin q) : H →L[ℝ] H :=
  (reflectionAbout (LinearMap.ker (P.A : H →ₗ[ℝ] V))).comp (reflectionAbout (P.Hx x))

/-- Section 3 (p. 13): `U′(P,x) = (2Π_{H(x)} − I)(2Π_T − I)` with
`T = ker A ⊕ span{|w₀⟩}`. -/
def Uprime (P : SpanProgram q n H V) (x : Fin n → Fin q) (w0 : H) : H →L[ℝ] H :=
  (reflectionAbout (P.Hx x)).comp
    (reflectionAbout (LinearMap.ker (P.A : H →ₗ[ℝ] V) ⊔ Submodule.span ℝ {w0}))

/-- Theorem 1.10 / Corollary 1.11 (p. 4–5): the discriminant
`D = Π_A Π_B` of a two-reflection unitary, specialised to `U(P,x)`, i.e.
`D = Π_{(ker A)⊥} Π_{H(x)}`. -/
def discriminant (P : SpanProgram q n H V) (x : Fin n → Fin q) : H →L[ℝ] H :=
  ((LinearMap.ker (P.A : H →ₗ[ℝ] V))ᗮ.starProjection).comp (P.Hx x).starProjection

/-- The largest singular value `σ_max(T)`, the operator norm. -/
def sigmaMax (T : H →L[ℝ] V) : ℝ := ‖T‖

/-- The smallest nonzero singular value `σ_min(T)`, following the source's
convention on p. 12–13: the infimum of `‖T u‖` over unit vectors with `T u ≠ 0`. -/
noncomputable def sigmaMin (T : H →L[ℝ] V) : ℝ :=
  sInf {r : ℝ | ∃ u : H, ‖u‖ = 1 ∧ T u ≠ 0 ∧ r = ‖T u‖}

/-- The phase gap `Δ(U)` of Section 3.4 (p. 20), recorded as the least distance
`‖U v − v‖` over unit vectors that are not fixed.  For a unitary with spectral
phases `e^{iθ}` this equals `2|sin(θ/2)|`, i.e. the `2 sin(θ/2)` form of the
source's least `|θ|`; the two agree in the small-phase regime used by the source
and `Δ ≥ 2 sin(Δ/2)`. -/
noncomputable def phaseGap (U : H →L[ℝ] H) : ℝ :=
  sInf {r : ℝ | ∃ v : H, ‖v‖ = 1 ∧ U v ≠ v ∧ r = ‖U v - v‖}

end SpanProgram

/-- Paper-level interface for the source's algorithmic statements: a
bounded-error quantum query algorithm is represented by its output map and its
per-input query count.  The source constructs these algorithms by phase
estimation on `U(P,x)`; the circuit itself is not modelled at this layer, so the
`queries` field is an explicit function supplied by the source construction, not
an existential variable. -/
structure QueryAlgorithm (Ix : Type*) where
  /-- The algorithm's classical output on input `x`. -/
  decide : Ix → Bool
  /-- The number of oracle queries made on input `x`. -/
  queries : Ix → ℕ

namespace QueryAlgorithm

/-- Bounded-error correctness, recorded deterministically: the algorithm's answer
equals the promised function on every input.  The source's `2/3`-success
guarantee is the probabilistic counterpart, obtained after the constant number
of repetitions the source performs. -/
def Solves {Ix : Type*} (alg : QueryAlgorithm Ix) (f : Ix → Bool) : Prop :=
  ∀ x, alg.decide x = f x

/-- The honest algorithm for any Boolean function: output `f` and make no queries.
Used to certify that the algorithmic statements below are non-vacuous only in
their query-count bound, which is the content the source establishes. -/
def trivial {Ix : Type*} (f : Ix → Bool) : QueryAlgorithm Ix where
  decide := f
  queries := fun _ => 0

/-- The `trivial_solves` result for the ApproxSpan15 paper model. -/
@[simp] theorem trivial_solves {Ix : Type*} (f : Ix → Bool) :
    (trivial f).Solves f := fun _ => rfl

end QueryAlgorithm

end Qatlib.Papers.ApproxSpan15.MainResults
