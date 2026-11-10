/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.WalkQSVT.ApplicationModels
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option warningAsError false
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

def cyclic {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) (v : QState H) : Submodule ℂ (QState H) :=
  Submodule.span ℂ ({ψ | ∃ k : ℕ, ψ=U^k *ᵥ v} ∪ {ψ | ∃ k : ℕ, ψ=(Uᴴ)^k *ᵥ v})
def walk {H I : Type} [Fintype H] [Fintype I] [DecidableEq H]
    (G : Matrix H I ℂ) (U : Matrix H H ℂ) : Matrix H H ℂ := (2 • (G*Gᴴ)-1)*U
def residual {H : Type} [Fintype H]
    (U : Matrix H H ℂ) (v : QState H) (lam : ℝ) : QState H :=
  (Real.sqrt (1-lam^2) : ℂ)⁻¹ • (U *ᵥ v-(lam : ℂ) • v)
def walkBranch {H : Type} [Fintype H] (U : Matrix H H ℂ)
    (v : QState H) (lam : ℝ) (neg : Bool) : QState H :=
  (Real.sqrt 2 : ℂ)⁻¹ • (v+(if neg then -Complex.I else Complex.I) • residual U v lam)
def walkSupport {H I : Type} [Fintype H] [DecidableEq H] [Fintype I]
    (U : Matrix H H ℂ) (G : Matrix H I ℂ) (S : Matrix I I ℂ) (lam : I → ℝ) : Matrix H H ℂ :=
  ∑ i, let v := G *ᵥ (fun j =>  S j i)
    pureDensity v + if abs (lam i) < 1 then pureDensity (residual U v (lam i)) else 0

def pauliCoefficients (a b c d : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(a : ℂ)+Complex.I*b, (d : ℂ)+Complex.I*c;
     -(d : ℂ)+Complex.I*c, (a : ℂ)-Complex.I*b]
def fourierCos (n : ℕ) (a : Fin (n+1) → ℝ) (θ : ℝ) : ℝ :=
  ∑ k, a k*Real.cos (k.val*θ)
def fourierSin (n : ℕ) (a : Fin (n+1) → ℝ) (θ : ℝ) : ℝ :=
  ∑ k, a k*Real.sin (k.val*θ)
def spectralUnitary {H : Type} [Fintype H] [DecidableEq H]
    (S : Matrix H H ℂ) (θ : H → ℝ) : Matrix H H ℂ :=
  S*Matrix.diagonal (fun i =>  Complex.exp (Complex.I*θ i))*Sᴴ
def spectralPauli {H : Type} [Fintype H]
    (S : Matrix H H ℂ) (θ : H → ℝ) (a b c d : ℝ → ℝ) :
    Matrix (Space H 2) (Space H 2) ℂ :=
  fun p q =>  ∑ i, S p.1 i*star (S q.1 i)*
    pauliCoefficients (a (θ i)) (b (θ i)) (c (θ i)) (d (θ i)) p.2 q.2

def compileWalk {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] {r : ℕ}
    (G : Matrix H I ℂ) (C : Word H r) : Word H r :=
  C.flatMap (fun s =>  match s with
    | .known V =>  [.known V]
    | .call j T adj =>
      let R := controlled (2 • (G*Gᴴ)-1) T
      if adj then [.known R,.call j T true] else [.call j T false,.known R])

def markingInput {H : Type} (φ : QState H) : QState (Space H 4) := fun p =>  φ p.1/2
def markingTarget {H : Type} (φ : QState H) (neg : Bool) : QState (Space H 4) :=
  fun p =>  φ p.1*(if neg && (p.2.val%2=1) then (-1/2 : ℂ) else 1/2)
def markedInput {H : Type} (φ : QState H) (neg : Bool) : QState (Space H 4) :=
  fun p =>  if p.2.val=(if neg then 2 else 0) then φ p.1 else 0
def markedOutput {H : Type} (φ : QState H) (neg : Bool) (ξ : QState (Fin 2)) :
    QState (Space H 4) :=
  fun p =>  if p.2.val/2=(if neg then 1 else 0) then φ p.1*ξ ⟨p.2.val%2,by omega⟩ else 0

end Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
