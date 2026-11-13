/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BosonFock.BosonOperators.BosonPermanent
import Qatlib.Concepts.CountingClasses.ClassTransport.LinearOpticsComplexityModelsDefs
import Qatlib.Concepts.CountingClasses.ClassTransport.CountingComplexityDefs
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorial.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# LinearOptics10, paper block `StockmeyerSrc` — shared definitions

Aaronson–Arkhipov, *The Computational Complexity of Linear Optics*,
fixed version arXiv:1011.3245v1 (PDF SHA recorded in the paper block README).

This file provides the notation used by the paper-layer statements of the
`StockmeyerSrc` block: the coefficient-vector presentation of degree-`n`
polynomials on `m` variables, the Fock-space inner product and norm of §3.2
(equations on p. 22), the top-left submatrix and the "one photon per mode"
state `J_{m,n}` of §3.3 (p. 26), the coefficient of a mono-mial in the
variable substitution `V[x₁⋯x_n]`, and two paper-level complexity predicates
(`PHCollapsesToThree`, `SharpPEstimatedByBPPNP`) used to state the
complexity-class claims c001, c002, c016, c026, c027, c030 and the hardness
claims of §9.

`FockOccupation` itself is the frozen concept
`Qatlib.Concepts.BosonFock.BosonOperators.FockOccupation`; the
occupation weights and the permanent model are also frozen
(`bosonWeight`, `loIsometryDist` and relatives), so this file only adds the
polynomial-layer notation the paper's §3.2–3.3 statements need.
-/

set_option autoImplicit false

namespace Qatlib.Papers.LinearOptics10.StockmeyerSrc

open Qatlib
open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.CountingClasses.ClassTransport
open ComplexConjugate
open scoped BigOperators Matrix ComplexConjugate

/-- Coefficient vector of a homogeneous degree-`n` polynomial in `m` variables,
indexed by the occupation numbers `Φ_{m,n}`. -/
abbrev FockCoeff (m n : ℕ) : Type := FockOccupation m n → ℂ

/-- The factorial weight `s₁!⋯s_m!` attached to an occupation `S`. -/
def occFactorial {m n : ℕ} (S : FockOccupation m n) : ℕ :=
  ∏ i : Fin m, (S.1 i).val.factorial

/-- Fock-space inner product of §3.2 (p. 22):
`⟨p,q⟩ = Σ_{S∈Φ_{m,n}} conj(a_S) b_S s₁!⋯s_m!`. -/
noncomputable def fockInner {m n : ℕ} (a b : FockCoeff m n) : ℂ :=
  ∑ S : FockOccupation m n, conj (a S) * b S * ((occFactorial S : ℕ) : ℂ)

/-- Fock norm squared `‖p‖²_Fock = ⟨p,p⟩` (p. 23). -/
noncomputable def fockNormSq {m n : ℕ} (a : FockCoeff m n) : ℝ :=
  ∑ S : FockOccupation m n, Complex.normSq (a S) * (occFactorial S : ℝ)

/-- The top-left `n × n` submatrix `V_{n,n}` of an `m × m` matrix `V`. -/
def topLeft {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (n : ℕ) (hnm : n ≤ m) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => V (Fin.castLE hnm i) (Fin.castLE hnm j)

/-- `J_{m,n}`: the occupation with one photon in each of the first `n` modes
(paper §3.3, p. 26). -/
def oneOccupation (m n : ℕ) (hnm : n ≤ m) : FockOccupation m n :=
  ⟨fun i => ⟨if (i : ℕ) < n then 1 else 0, by
      by_cases h : (i : ℕ) < n
      · simp only [if_pos h]; omega
      · simp only [if_neg h]; omega⟩, by
    rw [Finset.sum_boole]
    simp only [Nat.cast_id]
    have himg : (Finset.univ.filter (fun i : Fin m => (i : ℕ) < n))
        = Finset.univ.image (Fin.castLE hnm) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi
        exact ⟨⟨(i : ℕ), hi⟩, by simp⟩
      · rintro ⟨j, rfl⟩
        simp
    rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hnm)]
    simp⟩

/-- Coefficient of `x^S` in the substituted polynomial
`V[x₁ ⋯ x_n] = ∏_{k<n} (Σ_j V_{k,j} x_j)` (paper §3.3, p. 25–26): the sum over
all functions `f : Fin n → Fin m` whose fibre multiplicities are exactly `S`,
of `∏_k V_{k, f k}`. -/
noncomputable def polyActCoeff {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (n : ℕ)
    (hnm : n ≤ m) (S : FockOccupation m n) : ℂ :=
  ∑ f : Fin n → Fin m,
    if (∀ i : Fin m, (Finset.univ.filter (fun k : Fin n => f k = i)).card = (S.1 i).val)
      then ∏ k : Fin n, V (Fin.castLE hnm k) (f k) else 0

/-- The coefficient vector of `V[x₁⋯x_n]`: the image of the monomial `J_{m,n}`
under the linear substitution `V`. -/
noncomputable def polyActCoeffVec {m : ℕ} (V : Matrix (Fin m) (Fin m) ℂ) (n : ℕ)
    (hnm : n ≤ m) : FockCoeff m n :=
  polyActCoeff V n hnm

/-- Coefficients of the monomial `J_{m,n}` itself: `1` at `J_{m,n}`, `0` elsewhere. -/
noncomputable def oneMonomialCoeff {m n : ℕ} (hnm : n ≤ m) : FockCoeff m n :=
  fun S => if S = oneOccupation m n hnm then 1 else 0

/-! ## Paper-level complexity predicates

The library's counting-complexity model (`InSharpP`, `InFBPPNP`, `InPHLevel`,
`InP`, `InBPP`) is the frozen concept
`Qatlib.Concepts.CountingClasses.ClassTransport`.  The two
predicates below record the *operational* content of the paper's class
statements that is expressible in that model. -/

/-- **Open conjecture / complexity hypothesis — not proved in Qatlib.** `PH` collapses to the third level: every level of the polynomial
hierarchy is contained in the third level (`InPHLevel 3`). -/
def PHCollapsesToThree : Prop :=
  ∀ (lev : ℕ) (L : List Bool → Prop), InPHLevel lev L → InPHLevel 3 L

/-- A natural number encoded as a unary bit string (an arbitrary, fixed
injection used only to state estimator problems in the bit-string model). -/
def encodeNat (k : ℕ) : List Bool := List.replicate k true

/-- `P^#P ⊆ BPP^NP`, in the operational form used by Stockmeyer's theorem
(paper Theorem 26, p. 29): every `#P` counting function has an `FBPP^NP`
machine that outputs a multiplicative `g`-approximation (given as a unary
encoded integer) with the paper's two-sided success guarantee.  Here `g ≥ 1`
is the multiplicative factor, and the accuracy is `|est − f| ≤ (g−1)·f`. -/
def SharpPEstimatedByBPPNP (g : ℕ → ℝ) : Prop :=
  ∀ (f : List Bool → ℕ), InSharpP f →
    ∃ (F : List Bool → List Bool), InFBPPNP F ∧
      ∀ x : List Bool, ∃ k : ℕ, F x = encodeNat k ∧
        |(k : ℝ) - (f x : ℝ)| ≤ (g x.length - 1) * (f x : ℝ)

/-- **Open conjecture / complexity hypothesis — not proved in Qatlib.** `P^#P ⊆ BPP^NP`: there is a polynomial multiplicative-factor function `g`
such that every `#P` function is `FBPP^NP`-estimable to factor `g`.  (The paper's
Theorem 26 produces the estimator for every `g ≥ 1 + 1/poly`; this predicate
records the existence form used downstream.) -/
def SharpPContainedInBPPNP : Prop :=
  ∃ g : ℕ → ℝ, SharpPEstimatedByBPPNP g

/-- A real-valued estimator problem on `n × n` complex matrices, together with
the accuracy at which the paper proves it `#P`-hard.  `Val n M` is the value to
be estimated (e.g. `|Per M|²` in Theorem 28 or `Per M` in Theorem 60). -/
structure EstimatorProblem where
  /-- The value attached to an instance. -/
  Val : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ → ℝ

/-- `SharpPHardMul P`: the estimator problem `P` is `#P`-hard under
multiplicative approximation by any polynomially bounded factor (paper
Theorem 28: for every `g ∈ [1, poly(n)]`).  Concretely — and this is the shape
of the paper's reduction (`Θ`-instance ↦ matrix instance `X`) — every `#P`
counting function `f` reduces to `P` with a polynomially bounded instance map
`red` that preserves multiplicative accuracy: any `g`-approximation of
`P.Val (d |x|) (red x)` is a `g`-approximation of `f x`.

Only the *extensional* reduction property is recorded; the polynomial-time
computability of `red` is not modelled by the library's complexity API (there
is no reduction interface), and this boundary is stated in each theorem's
docstring. -/
def SharpPHardMul (P : EstimatorProblem) : Prop :=
  ∀ (f : List Bool → ℕ), InSharpP f →
    ∀ (g : ℕ → ℝ), (∃ c : ℕ, ∀ L : ℕ, g L ≤ (L : ℝ) ^ c + 1) →
      ∃ (d : ℕ → ℕ) (red : (x : List Bool) → Matrix (Fin (d x.length)) (Fin (d x.length)) ℂ),
        (∃ c : ℕ, ∀ L : ℕ, d L ≤ L ^ c + 1) ∧
        ∀ (x : List Bool) (y : ℝ),
          |y - P.Val (d x.length) (red x)|
              ≤ (g x.length - 1) * |P.Val (d x.length) (red x)| →
            |y - (f x : ℝ)| ≤ (g x.length - 1) * (f x : ℝ)

end Qatlib.Papers.LinearOptics10.StockmeyerSrc
