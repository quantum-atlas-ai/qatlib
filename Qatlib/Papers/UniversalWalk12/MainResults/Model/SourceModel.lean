/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Complex.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Shared model of UniversalWalk12

Concrete definitions used to state the results of Childs--Gosset--Webb,
*Universal computation by multi-particle quantum walk*, fixed arXiv:1205.3782v2.

This file fixes the paper's displayed objects:
* the momentum window `R` (p.29),
* the single-particle wave packet `|ψ^j(0)⟩` and its approximation `|α^j(t)⟩`
  (Theorem 1, p.29),
* the two-particle window `F`, coefficients `a_xy` (eqs. (20)–(21), p.30),
* the packet amplitudes `χ_{z,k}` and `|ψ(0)⟩` (Theorem 2, p.30),
* the Fourier kernels `A`, `B` (eq. (49), p.62),
* the amplitude `⟨x,y|ψ_A(t)⟩` of eq. (47) (p.54),
* the projector mass `P₂` of eq. (50),
* amplitude-to-state assembly over an abstract Hilbert space.

The existence of the graph, its Hamiltonian and its scattering states is *not*
formalised: the claim files take the corresponding Hilbert space, Hamiltonian
and scattering data as hypotheses.  See the per-claim `sorry` notes.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Set MeasureTheory

namespace Qatlib.Papers.UniversalWalk12.MainResults.Model

/-! ## Index sets -/

/-- Vertices of the single-particle graph `G` of Figure 1: a finite core
`Fin m` (the graph `Ĝ`) together with the semi-infinite path vertices
`(x, q)`, `x : ℕ`, `q : Fin N`. -/
abbrev VPath (m N : ℕ) := (Fin m) ⊕ (ℕ × Fin N)

/-- Path vertex `(x, q)` as an index of `VPath`. -/
def pathIdx {m N : ℕ} (x : ℕ) (q : Fin N) : VPath m N := Sum.inr (x, q)

/-- Core vertex `c` as an index of `VPath`. -/
def coreIdx {m N : ℕ} (c : Fin m) : VPath m N := Sum.inl c

/-- The path neighbours of `(x, q)`: `(x+1,q)` and, for `x > 0`, `(x-1,q)`; the
vertex `x = 0` is attached to the core (handled by the coupling `coreCoup`). -/
def pathNeighbors {m N : ℕ} (x : ℕ) (q : Fin N) : Finset (VPath m N) :=
  insert (pathIdx (x + 1) q) (if x = 0 then ∅ else {pathIdx (x - 1) q})

/-- The two-particle path neighbours of `(x, y)` on `ℤ × ℤ` (eq. (12)). -/
def twoNeighbors (x y : ℤ) : Finset (ℤ × ℤ) :=
  {(x + 1, y), (x - 1, y), (x, y + 1), (x, y - 1)}

/-! ## The momentum window `R` (p.29) -/

/-- `R(l) = 1` on `{M+1, …, M+L}`, `0` otherwise (Theorem 1, p.29). -/
def windowR (M L : ℕ) (l : ℤ) : ℝ :=
  if l ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)) then 1 else 0

/-! ## Single-particle packet and approximation (Theorem 1) -/

/-- Amplitude `⟨x,q|ψ^j(0)⟩ = L^{-1/2} e^{-ikx} δ_{qj}` on `x ∈ {M+1,…,M+L}`
(Theorem 1, p.29), set to `0` for `x = 0`. -/
def singlePacketAmp {N : ℕ} (k : ℝ) (M L : ℕ) (j : Fin N) (x : ℕ) (q : Fin N) : ℂ :=
  (if 1 ≤ x then 1 else 0)
    * (((1 / Real.sqrt (L : ℝ) : ℝ) : ℂ) * Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))
        * (if q = j then 1 else 0))
      * ((windowR M L (x : ℤ) : ℝ) : ℂ)

/-- Amplitude `⟨x,q|α^j(t)⟩` of the approximation of Theorem 1 (p.29), with
`S(k)` the S-matrix. -/
def singleAlphaAmp {N : ℕ} (k : ℝ) (M L : ℕ) (t : ℝ)
    (S : Fin N → Fin N → ℂ) (j : Fin N) (x : ℕ) (q : Fin N) : ℂ :=
  (if 1 ≤ x then 1 else 0)
    * (((1 / Real.sqrt (L : ℝ) : ℝ) : ℂ)
        * Complex.exp (-(2 : ℂ) * Complex.I * (t : ℂ) * (Real.cos k : ℂ))
        * ((if q = j then 1 else 0) * Complex.exp (-Complex.I * (k : ℂ) * (x : ℂ))
              * ((windowR M L ((x : ℤ) - ⌊(2 : ℝ) * t * Real.sin k⌋) : ℝ) : ℂ)
            + S q j * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))
              * ((windowR M L (-(x : ℤ) - ⌊(2 : ℝ) * t * Real.sin k⌋) : ℝ) : ℂ)))

/-! ## Two-particle objects (Theorem 2, Lemmas 4–7) -/

/-- The window `F(u,v,t)` of Theorem 2 (p.30). -/
def twoF (M L : ℕ) (t : ℝ) (u v : ℤ) : ℝ :=
  if (u - 2 * ⌊t⌋ ∈ Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)))
      ∧ (v + 2 * ⌊t / Real.sqrt 2⌋ ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)))
    then 1 else 0

/-- Coefficient `a_xy(t)` of eq. (21) (p.30) for `x ≤ y`.  The integer `σ ∈ {1,-1}`
encodes the `±` of the (anti)symmetrisation. -/
def twoAlphaCoeff (M L : ℕ) (t θ : ℝ) (σ : ℤ) (x y : ℤ) : ℂ :=
  ((1 / (Real.sqrt 2 * (L : ℝ)) : ℝ) : ℂ) * Complex.exp (-(Real.sqrt 2 : ℂ) * Complex.I * (t : ℂ))
    * (Complex.exp (-Complex.I * (Real.pi : ℂ) * (x : ℂ) / 2)
          * Complex.exp (Complex.I * (Real.pi : ℂ) * (y : ℂ) / 4) * ((twoF M L t x y : ℝ) : ℂ)
        + (σ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
          * Complex.exp (Complex.I * (Real.pi : ℂ) * (x : ℂ) / 4)
          * Complex.exp (-Complex.I * (Real.pi : ℂ) * (y : ℂ) / 2) * ((twoF M L t y x : ℝ) : ℂ))

/-- Coefficient `a_xy(t)` of eqs. (20)–(21) for all `x, y`, with
`a_xy = σ a_yx` for `x ≠ y`. -/
def twoAlphaAmp (M L : ℕ) (t θ : ℝ) (σ : ℤ) (x y : ℤ) : ℂ :=
  if x ≤ y then twoAlphaCoeff M L t θ σ x y else (σ : ℂ) * twoAlphaCoeff M L t θ σ y x

/-- Amplitude `⟨x|χ_{z,k}⟩ = L^{-1/2} e^{ikx}` on the block `{z-L, …, z-1}`
(Theorem 2, p.30). -/
def chiAmp (z : ℤ) (k : ℝ) (L : ℕ) (x : ℤ) : ℂ :=
  if x ∈ Finset.Icc (z - (L : ℤ)) (z - 1) then
    ((1 / Real.sqrt (L : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))
  else 0

/-- Amplitude `⟨x,y|ψ(0)⟩` of the symmetrised initial state of Theorem 2 (p.30). -/
def psiTwo0Amp (M L : ℕ) (σ : ℤ) (x y : ℤ) : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ)
    * (chiAmp (-(M : ℤ)) (-(Real.pi / 2)) L x * chiAmp ((M : ℤ) + (L : ℤ) + 1) (Real.pi / 4) L y
        + (σ : ℂ) * chiAmp ((M : ℤ) + (L : ℤ) + 1) (Real.pi / 4) L x
          * chiAmp (-(M : ℤ)) (-(Real.pi / 2)) L y)

/-- The Fourier kernel `A(φ₁,φ₂)` of eq. (49) (p.62). -/
def AmpA (M L : ℕ) (φ1 φ2 : ℝ) : ℂ :=
  ((1 / (L : ℝ) : ℝ) : ℂ)
    * ∑ x ∈ Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)),
      ∑ y ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)),
        Complex.exp (Complex.I * (φ1 : ℂ) * (((x + y : ℤ) : ℂ)) / 2)
          * Complex.exp (Complex.I * (φ2 : ℂ) * (((x - y : ℤ) : ℂ)))

/-- The Fourier kernel `B(φ₁,φ₂,k)` of eq. (49) (p.62). -/
def AmpB (M L : ℕ) (φ1 φ2 k : ℝ) : ℂ :=
  ((1 / (L : ℝ) : ℝ) : ℂ)
    * ∑ x ∈ Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)),
      ∑ y ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)),
        Complex.exp (Complex.I * (φ1 : ℂ) * (((x + y : ℤ) : ℂ)) / 2)
          * Complex.exp (Complex.I * (((φ2 : ℂ) + 2 * (k : ℂ))) * (((y - x : ℤ) : ℂ)))

/-- The real-valued Lebesgue integral over a set, `∫_{s} f dφ`. -/
def setIntegralR (s : Set ℝ) (f : ℝ → ℝ) : ℝ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict s) f

/-- The Lebesgue integral over a set, `∫_{s} f dφ` with respect to `volume`. -/
def setIntegral (s : Set ℝ) (f : ℝ → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict s) f

/-- Amplitude `⟨x,y|ψ_A(t)⟩` of eq. (47) (p.54), given the two-particle
scattering amplitude `scAmp p₁ p₂ x y = ⟨x,y|sc(p₁;p₂)⟩±`. -/
def psiAAmp (M L : ℕ) (ε t : ℝ) (scAmp : ℝ → ℝ → ℤ → ℤ → ℂ) (x y : ℤ) : ℂ :=
  setIntegral (Icc (-ε) ε) fun φ1 =>
    setIntegral (Icc (-ε) ε) fun φ2 =>
      ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ)
        * Complex.exp (-(4 : ℂ) * Complex.I * (t : ℂ)
            * ((Real.cos (Real.pi / 4 + φ1 / 2) : ℝ) : ℂ)
            * ((Real.cos (3 * Real.pi / 8 + φ2 / 2) : ℝ) : ℂ))
        * AmpA M L φ1 φ2 * scAmp (Real.pi / 4 + φ1) (3 * Real.pi / 8 + φ2) x y

/-- The double integral of Lemma 6 (p.64): `∬_{Dπ} A(φ₁,φ₂) e^{-iφ₁ a} e^{-2iφ₂ b} dφ₁dφ₂/(4π²)`. -/
def lemmaSixIntegral (M L : ℕ) (a b : ℝ) : ℂ :=
  setIntegral (Icc (-Real.pi) Real.pi) fun φ1 =>
    setIntegral (Icc (-Real.pi) Real.pi) fun φ2 =>
      ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) * AmpA M L φ1 φ2
        * Complex.exp (-Complex.I * (φ1 : ℂ) * (a : ℂ))
        * Complex.exp (-(2 : ℂ) * Complex.I * (φ2 : ℂ) * (b : ℂ))

/-- The projector mass `P₂` of eq. (50): `∑_{|x-y| < C} |amp(x,y)|²`. -/
def offWindowMass (C : ℕ) (amp : ℤ → ℤ → ℂ) : ℝ :=
  ∑' (x : ℤ), ∑' (y : ℤ), if Int.natAbs (x - y) < C then ‖amp x y‖ ^ 2 else 0

/-! ## Assembly of a state from amplitudes over position kets -/

/-- Assemble a single-particle state `∑_{x,q} φ(x,q) |x,q⟩`. -/
def singleState {E : Type*} [AddCommMonoid E] [Module ℂ E] [TopologicalSpace E]
    {m N : ℕ} (ket : VPath m N → E) (φ : ℕ → Fin N → ℂ) : E :=
  ∑' (x : ℕ) (q : Fin N), φ x q • ket (pathIdx x q)

/-- Assemble a two-particle state `∑_{x,y} φ(x,y) |x,y⟩`. -/
def twoState {E : Type*} [AddCommMonoid E] [Module ℂ E] [TopologicalSpace E]
    (ket : ℤ × ℤ → E) (φ : ℤ → ℤ → ℂ) : E :=
  ∑' (x : ℤ) (y : ℤ), φ x y • ket (x, y)

end Qatlib.Papers.UniversalWalk12.MainResults.Model
