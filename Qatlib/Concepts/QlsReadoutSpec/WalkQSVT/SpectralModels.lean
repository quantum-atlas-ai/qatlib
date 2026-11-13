/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Spectral and compilation models for quantum walks

This module defines cyclic subspaces, reflected walks, residual vectors, and candidate spectral
branches and support operators. It also defines Pauli coefficient matrices, spectral Fourier
constructions, walk-call compilation, and four-level marking states. Related mathematical
background is given in [LowSu2026].

## Main statements

* `cyclic`: Span of the forward and adjoint orbits.
* `walk`: The reflected-unitary walk operator.
* `walkSupport`: Sum of embedded eigenvector and residual outer products.
* `compileWalk`: Expansion of walk calls into oracle calls and reflections.

## References

* [Low and Su, 2026][LowSu2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QlsReadoutSpec.Amplification

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The complex submodule spanned by all forward and adjoint iterates of `v` under `U`. -/
def cyclic {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (v : QState H) : Submodule ℂ (QState H) :=
  Submodule.span ℂ ({ψ | ∃ k : ℕ, ψ=U^k *ᵥ v} ∪ {ψ | ∃ k : ℕ, ψ=(Uᴴ)^k *ᵥ v})
/-- The reflected walk matrix `(2 • (G * Gᴴ) - 1) * U`. -/
def walk {H I : Type} [Fintype H] [Fintype I] [DecidableEq H]
    (G : Matrix H I ℂ) (U : Matrix H H ℂ) : Matrix H H ℂ := (2 • (G*Gᴴ)-1)*U
/-- The residual `U *ᵥ v - lam • v` scaled by the reciprocal square root of `1 - lam^2`. -/
def residual {H : Type} [Fintype H]
    (U : Matrix H H ℂ) (v : QState H) (lam : ℝ) : QState H :=
  (Real.sqrt (1-lam^2) : ℂ)⁻¹ • (U *ᵥ v-(lam : ℂ) • v)
/-- The candidate walk eigenvector formed from `v` and its residual with coefficient positive or
negative imaginary unit, scaled by the reciprocal square root of two. -/
def walkBranch {H : Type} [Fintype H] (U : Matrix H H ℂ)
    (v : QState H) (lam : ℝ) (neg : Bool) : QState H :=
  (Real.sqrt 2 : ℂ)⁻¹ • (v+(if neg then -Complex.I else Complex.I) • residual U v lam)
/-- The sum of pure densities of the embedded columns of `S`, together with their residual
densities when the corresponding eigenvalue magnitude is less than one. -/
def walkSupport {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    (U : Matrix H H ℂ) (G : Matrix H I ℂ) (S : Matrix I I ℂ) (lam : I → ℝ) : Matrix H H ℂ :=
  ∑ i, let v := G *ᵥ (fun j =>  S j i)
    pureDensity v + if abs (lam i) < 1 then pureDensity (residual U v (lam i)) else 0

/-- The complex two-by-two matrix with rows `(a + i b, d + i c)` and `(-d + i c, a - i b)` for
four real coefficients. -/
def pauliCoefficients (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ)+Complex.I*b, (d : ℂ)+Complex.I*c;
     -(d : ℂ)+Complex.I*c, (a : ℂ)-Complex.I*b]
/-- The finite cosine expansion with coefficients `a` and frequencies from zero through `n`. -/
def fourierCos (n : ℕ) (a : Fin (n+1) → ℝ) (θ : ℝ) : ℝ :=
  ∑ k, a k*Real.cos (k.val*θ)
/-- The finite sine expansion with coefficients `a` and frequencies from zero through `n`. -/
def fourierSin (n : ℕ) (a : Fin (n+1) → ℝ) (θ : ℝ) : ℝ :=
  ∑ k, a k*Real.sin (k.val*θ)
/-- The matrix obtained by conjugating the diagonal phases `exp (i * θ)` by `S` and its
conjugate transpose. -/
def spectralUnitary {H : Type} [Fintype H] [DecidableEq H]
    (S : Matrix H H ℂ) (θ : H → ℝ) : Matrix H H ℂ :=
  S*Matrix.diagonal (fun i =>  Complex.exp (Complex.I*θ i))*Sᴴ
/-- The matrix assembling phase-dependent Pauli coefficient blocks along the columns of `S`. -/
def spectralPauli {H : Type} [Fintype H]
    (S : Matrix H H ℂ) (θ : H → ℝ) (a b c d : ℝ → ℝ) :
    Matrix (Space H 2) (Space H 2) ℂ :=
  fun p q =>  ∑ i, S p.1 i*star (S q.1 i)*
    pauliCoefficients (a (θ i)) (b (θ i)) (c (θ i)) (d (θ i)) p.2 q.2

/-- The word obtained by replacing each walk call with an oracle call and controlled range
reflection, ordered according to the adjoint flag. -/
def compileWalk {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (C : Word H r) : Word H r :=
  C.flatMap (fun s =>  match s with
    | .known V =>  [.known V]
    | .call j T adj =>
      let R := controlled (2 • (G*Gᴴ)-1) T
      if adj then [.known R,.call j T true] else [.call j T false,.known R])

/-- The state assigning amplitude `φ / 2` uniformly across four marking labels. -/
def markingInput {H : Type} (φ : QState H) : QState (Space H 4) := fun p =>  φ p.1/2
/-- The four-label marking target with amplitude `φ / 2`, negated on odd labels when `neg` is
true. -/
def markingTarget {H : Type} (φ : QState H) (neg : Bool) : QState (Space H 4) :=
  fun p =>  φ p.1*(if neg && (p.2.val%2=1) then (-1/2 : ℂ) else 1/2)
/-- The state supported on marking label zero or two according to `neg`, with data amplitudes
`φ`. -/
def markedInput {H : Type} (φ : QState H) (neg : Bool) : QState (Space H 4) :=
  fun p =>  if p.2.val=(if neg then 2 else 0) then φ p.1 else 0
/-- The state placing `φ` times the two-level state `ξ` in the pair of marking labels selected
by `neg`. -/
def markedOutput {H : Type} (φ : QState H) (neg : Bool) (ξ : QState (Fin 2)) :
    QState (Space H 4) :=
  fun p =>  if p.2.val/2=(if neg then 1 else 0) then φ p.1*ξ ⟨p.2.val%2,by omega⟩ else 0

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
