/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Qatlib.Concepts.LchsSimulation.TimeLchs

set_option backward.isDefEq.respectTransparency false

/-!
# LinNonunitary25 — paper-layer definitions

Low--Somma, *Optimal quantum simulation of linear non-unitary dynamics*,
fixed arXiv:2508.19238v2 (PDF: `assets/2508.19238.pdf`).

This file fixes the paper's own objects so that every active claim can be stated
with the paper's notation:

* `paperEvolution L H z s t` is the time-ordered exponential
  `U(t;z) = T exp(-i ∫_s^t (z L(u) + H(u)) du)` of Lemma 3/Lemma 4, expressed
  through the shared frozen Dyson-series implementation.
* `lchsOperator` is the truncated LCHS `O_R(t)` of Eq. (7).
* `f1`, `f2`, `f2shift` are the entire approximations of Lemma 5, Lemma 6 and
  Corollary 7; `hatF1`, `hatF2` are the corresponding Fourier kernels
  (`hatF2` uses the general complex argument so that the shifted-contour
  integrals of Lemma 8 and the trapezoid analysis of Lemma 12 can be stated).
* `erfc` is the complementary error function `erfc x = 2/√π ∫_x^∞ e^{-t²} dt`,
  which is not part of Mathlib and is therefore defined here explicitly.
* `alphaR`, `alphaInfty`, `alphaRh` are the block-encoding normalization factors
  `α_{f̂,R}`, `α_{f̂}` and `α_{f̂,R,h}` of Eq. (10)--(12).

The `QuantumAlgorithm` import provides the shared `orderedEvolution` and its
entirety/stability lemmas; no proof is imported at this layer.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.LinNonunitary25.MainResults

open Qatlib.Concepts.TimeEvolution

/-- Paper's time-ordered exponential `U(t;z) = T e^{-i ∫_s^t (z L(u)+H(u)) du}`
(Eq. (7) and Lemma 3).  The shared `orderedEvolution A s t` solves
`d/dt U = -A(t)U`, so the generator is `i (z L + H)`. -/
noncomputable def paperEvolution {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (z : ℂ) (s t : ℝ) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • (z • L u + H u)) s t

/-- The truncated LCHS `O_R(t)` of Eq. (7), with integration over real `k`. -/
noncomputable def lchsOperator {I : Type} [Fintype I] [DecidableEq I]
    (fhat : ℝ → ℂ) (L H : ℝ → Matrix I I ℂ) (R t : ℝ) : Matrix I I ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
    ∫ k in (-R)..R, fhat k • paperEvolution L H (k : ℂ) 0 t

/-- Complementary error function `erfc x = 2/√π ∫_x^∞ e^{-t²} dt`. -/
noncomputable def erfc (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in Set.Ici x, Real.exp (-(t ^ 2))

/-- Lemma 5, Eq. (42): `f₁(x;γ) = ½ e^{-x} erfc(1/(2γ) - γx)`. -/
noncomputable def f1 (x γ : ℝ) : ℝ :=
  (1 / 2) * Real.exp (-x) * erfc (1 / (2 * γ) - γ * x)

/-- Lemma 6, Eq. (49): `f₂(x;γ) = f₁(x;γ) + f₁(-x;γ)`. -/
noncomputable def f2 (x γ : ℝ) : ℝ :=
  f1 x γ + f1 (-x) γ

/-- Corollary 7, Eq. (56) (position space): `f₂(x;γ,c) = e^c f₂(x+c;γ)`. -/
noncomputable def f2shift (x γ c : ℝ) : ℝ :=
  Real.exp c * f2 (x + c) γ

/-- Lemma 5, Eq. (43): the Fourier kernel `f̂₁(k;γ)`. -/
noncomputable def hatF1 (z : ℂ) (γ : ℝ) : ℂ :=
  ((1 : ℂ) / (Real.sqrt (2 * Real.pi) * (1 - Complex.I * z))) *
    Complex.exp (-((z ^ 2 + 1) / (4 * (γ : ℂ) ^ 2)))

/-- Lemma 6/Corollary 7 kernel `f̂₂(z;γ,c)` with a general complex argument
(Eq. (50) for `c = 0`, Eq. (56) for general `c`). -/
noncomputable def hatF2 (z : ℂ) (γ c : ℝ) : ℂ :=
  (Real.sqrt (2 / Real.pi) : ℂ) * Complex.exp ((c : ℂ) - Complex.I * z * (c : ℂ)) /
    (1 + z ^ 2) * Complex.exp (-((z ^ 2 + 1) / (4 * (γ : ℂ) ^ 2)))

/-- The `c = 0` kernel of Lemma 6 (Eq. (50)). -/
noncomputable def hatF2Zero (k : ℝ) (γ : ℝ) : ℂ := hatF2 (k : ℂ) γ 0

/-- The standard Fourier transform used in the paper:
`F[f](k) = (2π)^{-1/2} ∫ f(x) e^{-ikx} dx`. -/
noncomputable def fourierTrafo (f : ℝ → ℂ) (k : ℝ) : ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
    ∫ x : ℝ, f x * Complex.exp (-(Complex.I * (k : ℂ) * (x : ℂ)))

/-- Lemma 5 auxiliary: `g₂(k;γ) = (1+k²)^{-1/2} e^{-(k²+1)/(8γ²)}` (up to the
constant `(2/π)^{1/4}`, absorbed into the normalization; see Lemma 19/Lemma 21). -/
noncomputable def g2 (k γ : ℝ) : ℝ :=
  (1 / Real.sqrt (1 + k ^ 2)) * Real.exp (-(k ^ 2 + 1) / (8 * γ ^ 2))

/-- `α_{f̂}`: the full-line block-encoding normalization of Eq. (10). -/
noncomputable def alphaInfty (fhat : ℝ → ℂ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ k : ℝ, ‖fhat k‖

/-- `α_{f̂,R}`: the truncated normalization of Eq. (10). -/
noncomputable def alphaR (fhat : ℝ → ℂ) (R : ℝ) : ℝ :=
  (1 / Real.sqrt (2 * Real.pi)) * ∫ k in (-R)..R, ‖fhat k‖

/-- `α_{f̂,R,h}`: the uniform-quadrature normalization of Eq. (11). -/
noncomputable def alphaRh (fhat : ℝ → ℂ) (h : ℝ) (J : ℕ) : ℝ :=
  (h / Real.sqrt (2 * Real.pi)) *
    ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), ‖fhat ((j : ℝ) * h)‖

/-- `α_{f̂₂} = e^c erfc(1/(2γ))`, the closed form of Theorem 2/Corollary 7. -/
noncomputable def alphaF2Infty (γ c : ℝ) : ℝ :=
  Real.exp c * erfc (1 / (2 * γ))

/-- The finite uniform quadrature `I_{R,γ,c,h}(t)` of Eq. (11) with `R/h = J`
and `U(k) = U(t;k)`. -/
noncomputable def uniformQuadrature {I : Type} [Fintype I] [DecidableEq I]
    (fhat : ℝ → ℂ) (U : ℝ → Matrix I I ℂ) (h : ℝ) (J : ℕ) : Matrix I I ℂ :=
  ((h / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
    ∑ j ∈ Finset.Icc (-(J : ℤ)) (J : ℤ), fhat ((j : ℝ) * h) • U ((j : ℝ) * h)

/-- The doubly infinite quadrature `I_{∞,γ,c,h}(t)` of Lemma 11. -/
noncomputable def infiniteQuadrature {I : Type} [Fintype I] [DecidableEq I]
    (fhat : ℝ → ℂ) (U : ℝ → Matrix I I ℂ) (h : ℝ) : Matrix I I ℂ :=
  ((h / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
    ∑' j : ℤ, fhat ((j : ℝ) * h) • U ((j : ℝ) * h)

/-- The selector `Sel = ∑_j |j⟩⟨j| ⊗ U(t; hj)` of Theorem 4/Lemma 16, with the
index `a : Fin (2J+1)` read as `j = a - J`. -/
noncomputable def timeEvolutionSelector {I : Type} [Fintype I] [DecidableEq I]
    (L H : ℝ → Matrix I I ℂ) (t h : ℝ) (J : ℕ) :
    Matrix (Fin (2 * J + 1) × I) (Fin (2 * J + 1) × I) ℂ :=
  fun (a, i) (b, j) =>
    if a = b then paperEvolution L H (((a.val : ℝ) - (J : ℝ)) * h : ℂ) 0 t i j else 0

/-- The multiplexed block-encoding target of Lemma 18, Eq. (117): the block for
index `j` is `(hj L + H)/(R α_L + α_H)`. -/
noncomputable def multiplexedTarget {I : Type} [Fintype I] [DecidableEq I]
    (L H : Matrix I I ℂ) (αL αH R : ℝ) (M : ℕ) :
    Matrix (Fin (2 * M + 1) × I) (Fin (2 * M + 1) × I) ℂ :=
  fun (a, i) (b, j) =>
    if a = b then
      (((R * αL + αH)⁻¹ : ℝ) : ℂ) * (((((a.val : ℝ) - (M : ℝ)) : ℝ) : ℂ) • L + H) i j
    else 0

/-- Standard block-encoding relation (Definition 1): the ancilla-zero block of
`U` equals `M / α`. -/
def BlockEncodes {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (U : Matrix (A ⊕ B) (A ⊕ B) ℂ) (M : Matrix A A ℂ) (α : ℝ) : Prop :=
  (Matrix.of (fun i j : A => U (Sum.inl i) (Sum.inl j))) = ((α⁻¹ : ℝ) : ℂ) • M

/-- Abstract query/gate cost ledger for the circuit lemmas of Section 5. -/
structure CostedCircuit where
  queries : ℕ
  twoQubitGates : ℕ

/-- The kernel superposition `|ψ_{R,h,γ}⟩` of Lemma 19, Eq. (132). -/
noncomputable def kernelState (γ c h : ℝ) (J : ℕ) : EuclideanSpace ℂ (Fin (2 * J + 1)) :=
  WithLp.toLp 2 (fun a : Fin (2 * J + 1) =>
    let k : ℝ := ((a.val : ℝ) - (J : ℝ)) * h
    let A : ℝ := ∑ b : Fin (2 * J + 1),
      ‖hatF2 ((((b.val : ℝ) - (J : ℝ)) * h : ℝ) : ℂ) γ c‖
    ((Real.sqrt ‖hatF2 (k : ℂ) γ c‖ / Real.sqrt A : ℝ) : ℂ))

/-- The conjugate kernel superposition `|ψ̄_{R,h,γ}⟩` of Lemma 19, Eq. (132). -/
noncomputable def kernelStateBar (γ c h : ℝ) (J : ℕ) : EuclideanSpace ℂ (Fin (2 * J + 1)) :=
  WithLp.toLp 2 (fun a : Fin (2 * J + 1) =>
    let k : ℝ := ((a.val : ℝ) - (J : ℝ)) * h
    let A : ℝ := ∑ b : Fin (2 * J + 1),
      ‖hatF2 ((((b.val : ℝ) - (J : ℝ)) * h : ℝ) : ℂ) γ c‖
    ((Real.sqrt ‖hatF2 (k : ℂ) γ c‖ / Real.sqrt A : ℝ) : ℂ) *
      Complex.exp (-(Complex.I * (h : ℂ) * (c : ℂ))))

/-- The `L¹` norm `‖L‖_{L¹} = ∫_0^t ‖L(s)‖ ds` attached to a time-dependent
matrix field, as used in Theorems 1--4 and Lemmas 12--13. -/
noncomputable def l1Norm {I : Type} [Fintype I] [DecidableEq I]
    (L : ℝ → Matrix I I ℂ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, ‖L s‖

/-- The full-line LCHS `O_{∞,γ,c}(t)` obtained by integrating `f̂` over all of
`ℝ` (the limit `R → ∞` of `lchsOperator`). -/
noncomputable def lchsOperatorInfty {I : Type} [Fintype I] [DecidableEq I]
    (fhat : ℝ → ℂ) (L H : ℝ → Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  ((1 / Real.sqrt (2 * Real.pi) : ℝ) : ℂ) •
    ∫ k : ℝ, fhat k • paperEvolution L H (k : ℂ) 0 t

/-- The heat semigroup `e^{-tL}` generated by a PSD matrix `L`, expressed via the
shared time-ordered exponential with constant generator `L`. -/
noncomputable def heatFlow {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  orderedEvolution (fun _ => L) 0 t

/-- The (unnormalized) state `e^{-tL}|φ⟩` of Theorem 5, Eq. (162). -/
noncomputable def heatState {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (t : ℝ) (φ : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (heatFlow L t *ᵥ (φ : I → ℂ))

/-- The normalized target state `|ψ_{N,K}⟩ = e^{-tL}|φ⟩ / ‖e^{-tL}|φ⟩‖` of
Theorem 5, Eq. (162). -/
noncomputable def normalizedHeatState {I : Type} [Fintype I] [DecidableEq I]
    (L : Matrix I I ℂ) (t : ℝ) (φ : EuclideanSpace ℂ I) : EuclideanSpace ℂ I :=
  (‖heatState L t φ‖)⁻¹ • heatState L t φ

end Qatlib.Papers.LinNonunitary25.MainResults
