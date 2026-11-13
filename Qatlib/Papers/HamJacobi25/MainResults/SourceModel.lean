/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Matrix.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# HamJacobi25 — source model for the vanishing-viscosity paper

Fixed source: Marco Cirant and Alessandro Goffi, *Convergence rates for the vanishing
viscosity approximation of Hamilton-Jacobi equations: the convex case*,
arXiv:2502.15495v2 (22 Jul 2025). PDF on file, SHA-256
`082f88f2e23fcc5faf82c2b9d822c8dfbe265b3603105971a53e9a646bdf6554`.

This module provides the analytic vocabulary shared by all claim files of the
`MainResults` block.  The spatial variable lives in `Point n = Fin n → ℝ`, the
universal cover of the torus `T^n`; all solution predicates carry 1-periodicity in
every coordinate, and the unit cube `torusCube n = [0,1]^n` is the integration
domain standing for `T^n`.  Spatial derivatives are honest Fréchet derivatives
(`fderiv`, `iteratedFDeriv`), the time derivative is the one-variable `deriv`, and
Lebesgue integrals are `∫ … in torusCube n` and `∫ … in Set.Icc a b`.

The predicates below encode the paper's hypotheses without weakening them:
`UniformlyConvex` is (H) of p.2, `StrictlyConvexSuperquadratic` is (H_γ) of p.2,
`SolvesViscousEquation` is (1), `SolvesFirstOrderViscosity` is the test-function
definition of the viscosity solution of (2), `SolvesAdjoint` is the fundamental
solution of (6) issued from `δ_x`, and the two `Solves…Conservation` predicates are
the parabolic and hyperbolic systems (13) and (14) of p.9.  Upper `L^∞`/`L¹L^∞`
constants use `sSup` of ranges and coincide with the paper's norms on continuous
periodic data.

The elementary lemmas at the end are proved outright.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HamJacobi25.MainResults.SourceModel

open scoped BigOperators
open MeasureTheory

/-- A point of the universal cover `ℝ^n` of the torus `T^n`. -/
abbrev Point (n : ℕ) := Fin n → ℝ

/-- The `i`-th standard basis vector. -/
def basisVec {n : ℕ} (i : Fin n) : Point n := Pi.single i 1

/-- Squared Euclidean norm, written as a finite sum to avoid norm-side goals. -/
def normSq {n : ℕ} (x : Point n) : ℝ := ∑ i, x i ^ 2

/-- `i`-th spatial partial derivative of `u` at `x`. -/
def gradCoord {n : ℕ} (u : Point n → ℝ) (x : Point n) (i : Fin n) : ℝ :=
  fderiv ℝ u x (basisVec i)

/-- Full spatial gradient of `u` at `x`, as a vector. -/
def gradFun {n : ℕ} (u : Point n → ℝ) (x : Point n) : Point n :=
  fun i => gradCoord u x i

/-- Second mixed derivative `∂_i∂_j u` at `x`, via the second iterated Fréchet derivative. -/
def hessCoord {n : ℕ} (u : Point n → ℝ) (x : Point n) (i j : Fin n) : ℝ :=
  (iteratedFDeriv ℝ 2 u x) (fun k : Fin 2 => if k = 0 then basisVec i else basisVec j)

/-- The Hessian quadratic form `D²u(x)(v,v)`. -/
def hessForm {n : ℕ} (u : Point n → ℝ) (x uu vv : Point n) : ℝ :=
  (iteratedFDeriv ℝ 2 u x) (fun k : Fin 2 => if k = 0 then uu else vv)

/-- Laplacian `Δu(x) = ∑ᵢ ∂ᵢ∂ᵢu(x)`. -/
def laplacian {n : ℕ} (u : Point n → ℝ) (x : Point n) : ℝ :=
  ∑ i, hessCoord u x i i

/-- Squared Euclidean norm of the gradient. -/
def gradNormSq {n : ℕ} (u : Point n → ℝ) (x : Point n) : ℝ :=
  ∑ i, (gradCoord u x i) ^ 2

/-- Euclidean norm of the gradient. -/
def gradNorm {n : ℕ} (u : Point n → ℝ) (x : Point n) : ℝ :=
  Real.sqrt (gradNormSq u x)

/-- Squared Frobenius norm of the Hessian, `|D²u(x)|²`. -/
def hessNormSq {n : ℕ} (u : Point n → ℝ) (x : Point n) : ℝ :=
  ∑ i, ∑ j, (hessCoord u x i j) ^ 2

/-- Divergence of a time-dependent vector field, `∑ᵢ ∂ᵢvᵢ(x)`. -/
def divergence {n : ℕ} (v : Point n → Point n) (x : Point n) : ℝ :=
  ∑ i, gradCoord (fun y => v y i) x i

/-- Time derivative of `t ↦ u(t,x)` at `t`. -/
def timeDeriv {n : ℕ} (u : ℝ → Point n → ℝ) (t : ℝ) (x : Point n) : ℝ :=
  deriv (fun s => u s x) t

/-- The unit cube `[0,1]^n`, standing for `T^n` in Lebesgue integrals. -/
def torusCube (n : ℕ) : Set (Point n) := Set.Icc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))

/-- Spatial 1-periodicity in every coordinate. -/
def periodicOnTorus {n : ℕ} (u : Point n → ℝ) : Prop :=
  ∀ x i, u (Function.update x i (x i + 1)) = u x

/-- Integral over the torus `T^n`. -/
def spatialIntegral {n : ℕ} (F : Point n → ℝ) : ℝ :=
  ∫ x in torusCube n, F x

/-- Sup norm of a spatial function. -/
def linfNorm {n : ℕ} (u : Point n → ℝ) : ℝ := sSup (Set.range u)

/-- Sup norm of the positive part. -/
def posPartLinf {n : ℕ} (u : Point n → ℝ) : ℝ :=
  sSup (Set.range (fun x => max (u x) 0))

/-- `L¹_t L^∞_x` norm of the positive part on `Q_T`. -/
def l1tLinfx {n : ℕ} (T : ℝ) (f : ℝ → Point n → ℝ) : ℝ :=
  ∫ t in Set.Icc 0 T, posPartLinf (f t)

/-- `L^∞(0,T; L²(T^n))` norm of `t ↦ Dg(t)`. -/
def linfL2Grad {n : ℕ} (T : ℝ) (g : ℝ → Point n → ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => Set.indicator (Set.Icc 0 T)
    (fun t => Real.sqrt (∫ x in torusCube n, gradNormSq (g t) x)) t))

/-- `L²(Q_T)` norm of a scalar field on the space-time cylinder. -/
def l2QNorm {n : ℕ} (T : ℝ) (g : ℝ → Point n → ℝ) : ℝ :=
  Real.sqrt (∫ t in Set.Icc 0 T, ∫ x in torusCube n, g t x ^ 2)

/-- `L²(Q_T)` norm of a vector-valued field. -/
def l2QNormVec {n : ℕ} (T : ℝ) (g : ℝ → Point n → Point n) : ℝ :=
  Real.sqrt (∫ t in Set.Icc 0 T, ∫ x in torusCube n, ∑ i, (g t x i) ^ 2)

/-- Parabolic distance `|x-y| + |t-s|^{1/2}`. -/
def parabolicDist {n : ℕ} (z w : ℝ × Point n) : ℝ :=
  Real.sqrt (normSq (z.2 - w.2)) + Real.sqrt |z.1 - w.1|

/-- Hölder regularity of exponent `α` with respect to the parabolic metric. -/
def HolderParabolic {n : ℕ} (g : ℝ × Point n → ℝ) (α C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ z w, |g z - g w| ≤ C * (parabolicDist z w) ^ α

/-- The classical parabolic Hölder class `C^{2+α,1+α/2}(T^n × [0,T])`. -/
def ParabolicHolderClass {n : ℕ} (u : ℝ → Point n → ℝ) (α : ℝ) : Prop :=
  ContDiff ℝ 2 (fun z : ℝ × Point n => u z.1 z.2) ∧
  ∃ C, 0 ≤ C ∧
    (∀ i, HolderParabolic (fun z : ℝ × Point n => gradCoord (u z.1) z.2 i) α C) ∧
    (∀ i j, HolderParabolic (fun z : ℝ × Point n => hessCoord (u z.1) z.2 i j) α C) ∧
    HolderParabolic (fun z : ℝ × Point n => timeDeriv u z.1 z.2) (α / 2) C

/-- Hypothesis (H), p.2: `H ∈ C²` and `θ I ≤ D²H(p) ≤ Θ I` for all `p`. -/
def UniformlyConvex {n : ℕ} (H : Point n → ℝ) (θ Θ : ℝ) : Prop :=
  ContDiff ℝ 2 H ∧ 0 < θ ∧ θ ≤ Θ ∧
    ∀ p (v : Point n), θ * normSq v ≤ hessForm H p v v ∧ hessForm H p v v ≤ Θ * normSq v

/-- Hypothesis (H_γ), p.2: superquadratic strict convexity,
`Tr(D²H(p)M²) ≥ θ|M|²|p|^{γ-2}`, with the local upper bound `D²H ≤ Θ_R I` on balls. -/
def StrictlyConvexSuperquadratic {n : ℕ} (H : Point n → ℝ) (θ Θ γ : ℝ) : Prop :=
  ContDiff ℝ 2 H ∧ 2 < γ ∧ 0 < θ ∧ θ < Θ ∧
    (∀ p (M : Matrix (Fin n) (Fin n) ℝ),
      θ * (normSq p) ^ ((γ - 2) / 2) * (∑ i, ∑ j, M i j ^ 2) ≤
        ∑ k, hessForm H p (M.mulVec (basisVec k)) (M.mulVec (basisVec k))) ∧
    (∀ R : ℝ, 0 < R → ∃ ΘR : ℝ, 0 < ΘR ∧ ∀ p, normSq p ≤ R ^ 2 →
      ∀ v, hessForm H p v v ≤ ΘR * normSq v)

/-- Standing regularity: `u_T ∈ C²` and `f ∈ C²` (the paper assumes the parabolic
Hölder versions `C^{2,α}` and `C^{2+α,1+α/2}`, which imply these). -/
def SourceRegularity {n : ℕ} (uT : Point n → ℝ) (f : ℝ → Point n → ℝ) : Prop :=
  ContDiff ℝ 2 uT ∧ ContDiff ℝ 2 (fun z : ℝ × Point n => f z.1 z.2)

/-- `uε` is the classical solution of (1) with viscosity `ε`. -/
def SolvesViscousEquation {n : ℕ} (T ε : ℝ) (H : Point n → ℝ)
    (f : ℝ → Point n → ℝ) (uT : Point n → ℝ) (uε : ℝ → Point n → ℝ) : Prop :=
  ContDiff ℝ 2 (fun z : ℝ × Point n => uε z.1 z.2) ∧
  (∀ t x, 0 < t → t < T →
    -timeDeriv uε t x - ε * laplacian (uε t) x + H (gradFun (uε t) x) = f t x) ∧
  (∀ x, uε T x = uT x) ∧ (∀ t, periodicOnTorus (uε t))

/-- Viscosity subsolution test-function condition for (2). -/
def IsViscositySubsolution {n : ℕ} (T : ℝ) (H : Point n → ℝ)
    (f : ℝ → Point n → ℝ) (u : ℝ → Point n → ℝ) : Prop :=
  ∀ (φ : ℝ → Point n → ℝ) (t : ℝ) (x : Point n),
    ContDiff ℝ 2 (fun z : ℝ × Point n => φ z.1 z.2) →
    0 < t → t < T →
    (∀ w : ℝ × Point n, 0 < w.1 → w.1 < T →
      u w.1 w.2 - φ w.1 w.2 ≤ u t x - φ t x) →
    -timeDeriv φ t x + H (gradFun (φ t) x) ≤ f t x

/-- Viscosity supersolution test-function condition for (2). -/
def IsViscositySupersolution {n : ℕ} (T : ℝ) (H : Point n → ℝ)
    (f : ℝ → Point n → ℝ) (u : ℝ → Point n → ℝ) : Prop :=
  ∀ (φ : ℝ → Point n → ℝ) (t : ℝ) (x : Point n),
    ContDiff ℝ 2 (fun z : ℝ × Point n => φ z.1 z.2) →
    0 < t → t < T →
    (∀ w : ℝ × Point n, 0 < w.1 → w.1 < T →
      u t x - φ t x ≤ u w.1 w.2 - φ w.1 w.2) →
    f t x ≤ -timeDeriv φ t x + H (gradFun (φ t) x)

/-- `u` is the viscosity solution of the first-order equation (2). -/
def SolvesFirstOrderViscosity {n : ℕ} (T : ℝ) (H : Point n → ℝ)
    (f : ℝ → Point n → ℝ) (uT : Point n → ℝ) (u : ℝ → Point n → ℝ) : Prop :=
  IsViscositySubsolution T H f u ∧ IsViscositySupersolution T H f u ∧
  (∀ x, u T x = uT x) ∧ (∀ t, periodicOnTorus (u t))

/-- `D_p H(p)` as a vector, built from the Fréchet derivative of `H`. -/
def hamiltonianGradient {n : ℕ} (H : Point n → ℝ) (p : Point n) : Point n :=
  gradFun H p

/-- `ρ` is the fundamental solution of the adjoint (Fokker–Planck) equation (6)
issued from `δ_x` at time `τ`, with drift `b`: nonnegative, unit mass after `τ`,
and pointwise solution of the equation on `Q_{τ,T}`. -/
def SolvesAdjoint {n : ℕ} (T ε : ℝ) (b : ℝ → Point n → Point n)
    (τ : ℝ) (_x : Point n) (ρ : ℝ → Point n → ℝ) : Prop :=
  (∀ t y, 0 ≤ ρ t y) ∧
  (∀ t, τ < t → t ≤ T → (∫ y in torusCube n, ρ t y) = 1) ∧
  (∀ t y, τ < t → t < T →
    timeDeriv ρ t y - ε * laplacian (ρ t) y
      + divergence (fun z i => b t z i * ρ t z) y = 0) ∧
  (∀ t, periodicOnTorus (ρ t))

/-- The quasilinear parabolic system (13) of p.9. -/
def SolvesParabolicConservation {n : ℕ} (T ε : ℝ) (H : Point n → ℝ)
    (p0 : Fin n → Point n → ℝ) (pε : ℝ → Point n → Point n) : Prop :=
  (∀ i t x, 0 < t → t < T →
    deriv (fun s => pε s x i) t
      + gradCoord (fun y => H (fun j => pε t y j)) x i
      = ε * laplacian (fun y => pε t y i) x) ∧
  (∀ i x, pε 0 x i = p0 i x)

/-- The hyperbolic conservation-law system (14) of p.9. -/
def SolvesHyperbolicConservation {n : ℕ} (T : ℝ) (H : Point n → ℝ)
    (p0 : Fin n → Point n → ℝ) (p : ℝ → Point n → Point n) : Prop :=
  (∀ i t x, 0 < t → t < T →
    deriv (fun s => p s x i) t
      + gradCoord (fun y => H (fun j => p t y j)) x i = 0) ∧
  (∀ i x, p 0 x i = p0 i x)

/-! ## Projections of the solution predicates (proved) -/

/-- The PDE in (1), extracted from `SolvesViscousEquation`. -/
theorem SolvesViscousEquation.equation {n : ℕ} {T ε : ℝ} {H : Point n → ℝ}
    {f : ℝ → Point n → ℝ} {uT : Point n → ℝ} {uε : ℝ → Point n → ℝ}
    (h : SolvesViscousEquation T ε H f uT uε) {t : ℝ} {x : Point n}
    (ht : 0 < t) (htT : t < T) :
    -timeDeriv uε t x - ε * laplacian (uε t) x + H (gradFun (uε t) x) = f t x :=
  h.2.1 t x ht htT

/-- The terminal condition of (1). -/
theorem SolvesViscousEquation.terminal {n : ℕ} {T ε : ℝ} {H : Point n → ℝ}
    {f : ℝ → Point n → ℝ} {uT : Point n → ℝ} {uε : ℝ → Point n → ℝ}
    (h : SolvesViscousEquation T ε H f uT uε) (x : Point n) : uε T x = uT x :=
  h.2.2.1 x

/-- The terminal condition of (2), extracted from `SolvesFirstOrderViscosity`. -/
theorem SolvesFirstOrderViscosity.terminal {n : ℕ} {T : ℝ} {H : Point n → ℝ}
    {f : ℝ → Point n → ℝ} {uT : Point n → ℝ} {u : ℝ → Point n → ℝ}
    (h : SolvesFirstOrderViscosity T H f uT u) (x : Point n) : u T x = uT x :=
  h.2.2.1 x

/-- Conservation of mass for the adjoint density (6). -/
theorem SolvesAdjoint.mass {n : ℕ} {T ε : ℝ} {b : ℝ → Point n → Point n}
    {τ : ℝ} {x : Point n} {ρ : ℝ → Point n → ℝ}
    (h : SolvesAdjoint T ε b τ x ρ) {t : ℝ} (ht : τ < t) (htT : t ≤ T) :
    (∫ y in torusCube n, ρ t y) = 1 :=
  h.2.1 t ht htT

/-! ## Elementary facts (proved) -/

/-- The squared Euclidean norm is nonnegative. -/
theorem normSq_nonneg {n : ℕ} (x : Point n) : 0 ≤ normSq x := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

/-- The squared gradient norm is nonnegative. -/
theorem gradNormSq_nonneg {n : ℕ} (u : Point n → ℝ) (x : Point n) : 0 ≤ gradNormSq u x := by
  unfold gradNormSq
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (gradCoord u x i))

/-- The gradient norm is nonnegative. -/
theorem gradNorm_nonneg {n : ℕ} (u : Point n → ℝ) (x : Point n) : 0 ≤ gradNorm u x :=
  Real.sqrt_nonneg _

/-- The squared Hessian norm is nonnegative. -/
theorem hessNormSq_nonneg {n : ℕ} (u : Point n → ℝ) (x : Point n) : 0 ≤ hessNormSq u x := by
  unfold hessNormSq
  exact Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => sq_nonneg (hessCoord u x i j)))

/-- The positive part of a real-valued function is nonnegative. -/
theorem posPart_nonneg {n : ℕ} (u : Point n → ℝ) (x : Point n) : 0 ≤ max (u x) 0 :=
  le_max_right _ _

/-- The parabolic distance is nonnegative. -/
theorem parabolicDist_nonneg {n : ℕ} (z w : ℝ × Point n) : 0 ≤ parabolicDist z w := by
  unfold parabolicDist
  exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Qatlib.Papers.HamJacobi25.MainResults.SourceModel
