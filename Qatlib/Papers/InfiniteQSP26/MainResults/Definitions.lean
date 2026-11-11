/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Qatlib.Concepts.LaurentPolys.FiniteBitCost.FiniteQSPDefs

set_option backward.isDefEq.respectTransparency false

/-!
# InfiniteQSP26 — paper-layer model

Fixed source: arXiv:2407.05634v3 (2026-03-04), M. Alexis, L. Lin, G. Mnatasyan,
C. Thiele and J. Wang, *Infinite quantum signal processing for arbitrary Szegő
functions*, CPAM 79(1) 123–174.  Page and equation numbers below refer to the
fixed v3 PDF.

This file sets up the paper's vocabulary in the paper layer:

* `CircleT` — the unit circle `𝕋`, represented as `UnitAddCircle` (`ℝ / ℤ`);
  `fourier n x` is `z^n` and `fourierCoeff u n` is the `n`-th Fourier
  coefficient of `u` (Mathlib's normalized Haar measure).
* `InP` — the phase sequence space `P` of sequences with
  `ψ_k ∈ [-π/2, π/2]` (§1.1, p.2).
* `uEntry`, `imU`, `qspOperator` — the QSP recursion Eq. (2), using the frozen
  finite model `rhwQSPBridgeOperator` which is exactly Eq. (2).
* `SzegoFunction`, `szegoNorm`, `InSη` — the Szegő class `S` and the stability
  subclasses `S_η` of Eqs. (5), (6), (9), pp.3–4.
* `PlancherelIdentity`, `IsIQSPL2Solution` — the nonlinear Plancherel identity
  Eq. (7) and the `L²` convergence criterion Eq. (8), p.3.
* `starFun`, `MemH2D`, `MemH2DStar`, `MemZkH2`, `IsOuterStar`, `InB` — the
  Hardy-space vocabulary of §2.1–2.3, pp.6–10, in the Fourier-support form
  (Paley–Wiener characterization) used by the paper's arguments.
* `pairMul`, `InHGe`, `InHLe` — the pair multiplication Eq. (24) and the
  factor classes `H_{≥k}`, `H_{≤k}` of §2.2.
* `hankelMatrix`, `idPlusMk`, `annulus`, `rCoeff`, `cCoeff`, `dftCoeff`,
  `Gfun`, `Ghat` — the objects of §5, pp.33–38.

The analytic existence/uniqueness content (Hardy spaces, outer functions,
unbounded self-adjoint operators, Riemann–Hilbert factorization) is *not*
available in the repository; the predicates below are the paper's definitions
in terms of Fourier support and the concrete finite-QSP model, and the results
that depend on the missing analytic theory are marked `sorry` in the claim
files with a handover note.
-/

open scoped BigOperators
open MeasureTheory Filter Topology Matrix

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.InfiniteQSP26.MainResults

/-- The paper's unit circle `𝕋`, represented as `ℝ / ℤ`. -/
abbrev CircleT : Type := UnitAddCircle

/-- The holomorphic reflection `f*(z) = f(z⁻¹)` on `𝕋` (§2.1 Eq. (14)): on the
period-one circle this is `starFun f x = f (-x)`. -/
def starFun (f : CircleT → ℂ) : CircleT → ℂ := fun x => f (-x)

/-! ### Phase sequences and the QSP recursion (Eqs. (1)–(2), p.2) -/

/-- `(1,1)` entry `u_d(x,Ψ)` of the QSP operator `U_d(x,Ψ)` of Eq. (2). -/
noncomputable def uEntry (Ψ : ℕ → ℝ) (x : ℝ) (d : ℕ) : ℂ :=
  (Qatlib.Concepts.LaurentPolys.FiniteBitCost.rhwQSPBridgeOperator Ψ x d) false false

/-- `Im[u_d(x,Ψ)]`, the real function encoded by a phase sequence (§1.1, p.2). -/
noncomputable def imU (Ψ : ℕ → ℝ) (x : ℝ) (d : ℕ) : ℝ := (uEntry Ψ x d).im

/-- The phase space `P`: `ψ_k ∈ [-π/2, π/2]` for all `k` (§1.1, p.2). -/
def InP (Ψ : ℕ → ℝ) : Prop := ∀ k, Ψ k ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- The nonlinear Fourier coefficient `F_k = i tan ψ_{|k|}` of Eq. (26), p.9. -/
noncomputable def phaseCoeff (Ψ : ℕ → ℝ) (k : ℤ) : ℂ :=
  Complex.I * (Real.tan (Ψ k.natAbs) : ℂ)

/-! ### Szegő class and norms (Eqs. (5), (6), (9), pp.3–4) -/

/-- Chebyshev polynomial of the first kind `T_n(x) = cos(n arccos x)` on `[-1,1]`. -/
noncomputable def cheb (n : ℕ) (x : ℝ) : ℝ := Real.cos (n * Real.arccos x)

/-- The Szegő norm of Eq. (6), p.3:
`‖f‖_S = sqrt ((1/π) ∫₀¹ |f(x)|² / sqrt(1-x²) dx)`. -/
noncomputable def szegoNorm (f : ℝ → ℝ) : ℝ :=
  Real.sqrt ((1 / Real.pi) * ∫ x in (0 : ℝ)..1, (f x) ^ 2 / Real.sqrt (1 - x ^ 2))

/-- The Szegő condition of Eq. (5), p.3: the log-integral is finite and bounded
below, together with `|f| ≤ 1` on `[-1,1]`. -/
def SzegoFunction (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 1) ∧
    IntervalIntegrable
      (fun x => Real.log (1 - (f x) ^ 2) / Real.sqrt (1 - x ^ 2)) volume 0 1 ∧
    ∃ M : ℝ, M < ∫ x in (0 : ℝ)..1, Real.log (1 - (f x) ^ 2) / Real.sqrt (1 - x ^ 2)

/-- The stability subclass `S_η` of Eq. (9), p.4: `f ∈ S` and `‖f‖_∞ ≤ 1 - η`. -/
def InSη (η : ℝ) (f : ℝ → ℝ) : Prop :=
  SzegoFunction f ∧ ∀ x ∈ Set.Icc (-1 : ℝ) 1, |f x| ≤ 1 - η

/-- The nonlinear Plancherel identity Eq. (7), p.3. -/
def PlancherelIdentity (f : ℝ → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  (-(2 / Real.pi) * ∫ x in (0 : ℝ)..1, Real.log (|1 - (f x) ^ 2|) / Real.sqrt (1 - x ^ 2)
    = ∑' k : ℤ, Real.log (1 + Real.tan (Ψ k.natAbs) ^ 2))

/-- The assertion that `Ψ` is the iQSP solution of `f`: `Ψ ∈ P`, `Im[u_d] → f`
in Szegő norm (Eq. (8)) and the nonlinear Plancherel identity (Eq. (7)) holds. -/
def IsIQSPL2Solution (f : ℝ → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  InP Ψ ∧
    Tendsto (fun d => szegoNorm (fun x => imU Ψ x d - f x)) Filter.atTop (nhds 0) ∧
    PlancherelIdentity f Ψ

/-! ### Hardy spaces and outer functions (§2.1, pp.6–8) -/

/-- Membership in `H²(D)` in the Fourier-support form: all negative Fourier
coefficients vanish (Paley–Wiener; equivalent to the boundary values of a
holomorphic `H²` function, §2.1 p.6). -/
def MemH2D (g : CircleT → ℂ) : Prop := ∀ n : ℤ, n < 0 → fourierCoeff g n = 0

/-- Membership in `H²(D*)`: all positive Fourier coefficients vanish (§2.1). -/
def MemH2DStar (g : CircleT → ℂ) : Prop := ∀ n : ℤ, 0 < n → fourierCoeff g n = 0

/-- Membership in `z^k H²(D)`: Fourier support in `[k, ∞)` (§3.3 Eq. (46)). -/
def MemZkH2 (k : ℕ) (g : CircleT → ℂ) : Prop := ∀ n : ℤ, n < (k : ℤ) → fourierCoeff g n = 0

/-- `a*` is outer with `a*(0) > 0` (§2.3, p.10), in the working Fourier-support
form used by the paper: analytic in `D*`, pointwise nonzero, positive value at
the origin `a*(0) = a(1)`. -/
def IsOuterStar (g : CircleT → ℂ) : Prop :=
  MemH2DStar g ∧ (∀ x, g x ≠ 0) ∧ 0 < (g 0).re

/-- The set `B` of §2.3, p.10: measurable pairs `(a,b)` on `𝕋` with
`a a* + b b* = 1` a.e. and `a*` outer with `a*(0) > 0`. -/
def InB (a b : CircleT → ℂ) : Prop :=
  (∀ x, a x * starFun a x + b x * starFun b x = 1) ∧ IsOuterStar a

/-- The pair multiplication Eq. (24), p.8:
`(a,b)(c,d) = (ac - b d*, ad + b c*)`. -/
def pairMul (p q : (CircleT → ℂ) × (CircleT → ℂ)) : (CircleT → ℂ) × (CircleT → ℂ) :=
  (fun z => p.1 z * q.1 z - p.2 z * starFun q.2 z,
   fun z => p.1 z * q.2 z + p.2 z * starFun q.1 z)

/-- The factor class `H_{≥k}` of §2.2 (p.8): `a ∈ H²(D*)`,
`b ∈ z^k H²(D)`, and `a a* + b b* = 1`. -/
def InHGe (k : ℤ) (p : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  MemH2DStar p.1 ∧ (∀ n : ℤ, n < k → fourierCoeff p.2 n = 0) ∧
    (∀ x, p.1 x * starFun p.1 x + p.2 x * starFun p.2 x = 1)

/-- The factor class `H_{≤k}` of §2.2: `(a, b) ∈ H_{≤k}` iff
`(a, b*) ∈ H_{≥-k}`. -/
def InHLe (k : ℤ) (p : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  InHGe (-k) (p.1, starFun p.2)

/-- `(a,b)` is the NLFT of the sequence `F` (§2.2, Eq. (25) and the surrounding
discussion): `(a,b) ∈ B`, both `a` and `b` are the boundary values of an
`H²(D*)`/`H²(D)`-type pair, and the pair is the two-sided ordered product.
The analytic product convergence is recorded as the pair being the limit in
the claim files; here we keep the membership shape used by the statements. -/
def IsNLFT (F : ℤ → ℂ) (a b : CircleT → ℂ) : Prop :=
  (∀ x, starFun b x = -b x) ∧
    (∀ n : ℤ, fourierCoeff b n = phaseCoeff (fun k => Real.arctan ((F (k : ℤ)).im)) n) ∧
    (∀ x, a x * starFun a x + b x * starFun b x = 1)

/-! ### Annulus and Section 5 objects (pp.33–38) -/

/-- The annulus `A_r = {z : r⁻¹ < |z| < r}` of Eq. (103), p.33. -/
def annulus (r : ℝ) : Set ℂ := {z : ℂ | r⁻¹ < ‖z‖ ∧ ‖z‖ < r}

/-- The radius `r > 1` of Eq. (102): `r^{2d} = (1-η)⁻¹`. -/
noncomputable def radiusOf (d : ℕ) (η : ℝ) : ℝ :=
  Real.rpow (1 - η) (-(1 / (2 * (d : ℝ))))

/-- The Fourier coefficient `r_j` of `log sqrt(1 - |b|²)`, Eq. (109) area, p.34. -/
noncomputable def rCoeff (b : CircleT → ℂ) (j : ℤ) : ℂ :=
  fourierCoeff (fun x => (Real.log (Real.sqrt (1 - ‖b x‖ ^ 2)) : ℂ)) j

/-- The discrete Fourier coefficient `r̂_j` of the Weiss algorithm (§5.1, p.34). -/
noncomputable def dftCoeff (N : ℕ) (u : CircleT → ℂ) (j : ℤ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ l ∈ Finset.range N,
    u ((l : ℝ) / (N : ℝ)) * Complex.exp (-(2 * Real.pi * Complex.I * (j : ℂ) * (l : ℂ) / (N : ℂ)))

/-- `r̂_j` for `log sqrt(1 - |b|²)` (§5.1, p.34). -/
noncomputable def rHat (b : CircleT → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  dftCoeff N (fun x => (Real.log (Real.sqrt (1 - ‖b x‖ ^ 2)) : ℂ)) j

/-- The Fourier coefficient `c_j` of `b a⁻¹` (Eq. (119), p.36). -/
noncomputable def cCoeff (a b : CircleT → ℂ) (j : ℤ) : ℂ :=
  fourierCoeff (fun x => b x / a x) j

/-- The discrete Fourier coefficient `c'_j` of `b a⁻¹` (Eq. (119), p.36). -/
noncomputable def cPrime (a b : CircleT → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  dftCoeff N (fun x => b x / a x) j

/-- The approximation `ĉ_j` computed from `â = e^{Ĝ}` (Eq. (124), p.36). -/
noncomputable def cHat (aHat b : CircleT → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  dftCoeff N (fun x => b x / aHat x) j

/-- `G(z) = 2 Σ_{ℓ≥1} r_{-ℓ} z^{-ℓ} + r_0` of Eq. (111), p.35. -/
noncomputable def Gfun (b : CircleT → ℂ) (x : CircleT) : ℂ :=
  (2 : ℂ) * ∑' l : ℕ, rCoeff b (-((l : ℤ) + 1)) * fourier (-((l : ℤ) + 1)) x
    + rCoeff b 0

/-- `Ĝ(z) = 2 Σ_{ℓ=1}^{N/2} r̂_{-ℓ} z^{-ℓ} + r̂_0` of Eq. (111), p.35. -/
noncomputable def Ghat (b : CircleT → ℂ) (N : ℕ) (x : CircleT) : ℂ :=
  (2 : ℂ) * ∑ l ∈ Finset.range (N / 2),
      rHat b N (-((l : ℤ) + 1)) * fourier (-((l : ℤ) + 1)) x
    + rHat b N 0

/-- The Hankel matrix `Ξ_k` of Eq. (50), p.15: the `(i,j)` entry is `c_{i+j+k}`
when `i+j+k ≤ d` and zero otherwise. -/
noncomputable def hankelMatrix (c : ℤ → ℂ) (k d : ℕ) :
    Matrix (Fin (d - k + 1)) (Fin (d - k + 1)) ℂ :=
  fun i j => if (i : ℕ) + (j : ℕ) + k ≤ d then c (((i : ℕ) + (j : ℕ) + k : ℕ) : ℤ) else 0

/-- The block matrix `Id + M_k = [[I, -Ξ_k], [-Ξ_k, I]]` of Eq. (50), p.15. -/
noncomputable def idPlusMk (c : ℤ → ℂ) (k d : ℕ) :
    Matrix (Fin (d - k + 1) ⊕ Fin (d - k + 1)) (Fin (d - k + 1) ⊕ Fin (d - k + 1)) ℂ :=
  Matrix.fromBlocks (1 : Matrix (Fin (d - k + 1)) (Fin (d - k + 1)) ℂ)
    (-(hankelMatrix c k d)) (-(hankelMatrix c k d))
    (1 : Matrix (Fin (d - k + 1)) (Fin (d - k + 1)) ℂ)

/-- The `L∞` norm `‖F‖_∞ = sup_k |F_k|` of a two-sided sequence. -/
noncomputable def linfNormSeq (F : ℤ → ℂ) : ℝ := ⨆ k : ℤ, ‖F k‖

/-- The `L²(𝕋)` norm of a circle function. -/
noncomputable def l2TNorm (u : CircleT → ℂ) : ℝ :=
  Real.sqrt (∫ x in (0 : ℝ)..1, ‖u (x : CircleT)‖ ^ 2)

/-- `‖b/a‖_{L²(𝕋)}`, the right-hand side of the Lipschitz estimates (10), (85). -/
noncomputable def bOverAL2 (p : (CircleT → ℂ) × (CircleT → ℂ)) : ℝ :=
  l2TNorm (fun x => p.2 x / p.1 x)


/-! ### Auxiliary vocabulary shared by the claim files -/

/-- The point of `𝕋 ⊂ ℂ` corresponding to `x : UnitAddCircle`. -/
noncomputable def circlePt (x : CircleT) : ℂ := (AddCircle.toCircle x : Circle)

/-- The first standard basis vector `e₀` of the function pair space used in
Eq. (47) and Eq. (51). -/
def e0Pair : (CircleT → ℂ) × (CircleT → ℂ) := (fun _ => 1, fun _ => 0)

/-- The Riesz projection `P_D` onto nonnegative frequencies (§2.1, p.7). -/
noncomputable def projD (u : CircleT → ℂ) : CircleT → ℂ :=
  fun x => ∑' n : ℤ, if 0 ≤ n then fourierCoeff u n * fourier n x else 0

/-- The complementary projection `P_{D*}` onto nonpositive frequencies (§2.1). -/
noncomputable def projDStar (u : CircleT → ℂ) : CircleT → ℂ :=
  fun x => ∑' n : ℤ, if n ≤ 0 then fourierCoeff u n * fourier n x else 0

/-- The `L²(𝕋) × L²(𝕋)` inner product used in §4.1, Eq. (57). -/
noncomputable def l2Inner (p q : (CircleT → ℂ) × (CircleT → ℂ)) : ℂ :=
  ∫ x in (0 : ℝ)..1, p.1 x * star (q.1 x) + p.2 x * star (q.2 x)

/-- The `L²` norm of a pair, induced by Eq. (57). -/
noncomputable def pairNorm (p : (CircleT → ℂ) × (CircleT → ℂ)) : ℝ :=
  Real.sqrt (l2Inner p p).re

/-- Pointwise truncation `a_η` of `a` used in Eq. (59): keep `|a| > η`, otherwise
scale down to modulus `η`. -/
noncomputable def aEta (a : CircleT → ℂ) (η : ℝ) : CircleT → ℂ :=
  fun x => if a x = 0 then 0 else a x * ((min 1 (η / ‖a x‖) : ℝ) : ℂ)

/-- The operator `M_k` of Eq. (47) applied to `(A,B)`, written as
`(Id + M_k)(A,B)`. -/
noncomputable def hkOperator (a b : CircleT → ℂ) (k : ℕ)
    (p : (CircleT → ℂ) × (CircleT → ℂ)) : (CircleT → ℂ) × (CircleT → ℂ) :=
  (fun x => p.1 x + projDStar (fun y => starFun (fun z => b z / a z) y * p.2 y) x,
   fun x => p.2 x - fourier (k : ℤ) x *
     projD (fun y => fourier (-(k : ℤ)) y * (b y / a y) * p.1 y) x)

/-- The exact linear system (47) `(Id + M_k)(A_k,B_k) = e₀`. -/
def SatisfiesSystem (a b : CircleT → ℂ) (k : ℕ)
    (p : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  hkOperator a b k p = e0Pair

/-- The weak-limit system of Lemma 16, Eq. (97): `M_k` is the `η → 0` weak
limit of Eq. (98). -/
def SatisfiesWeakSystem (a b : CircleT → ℂ) (k : ℕ)
    (p : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  (∀ q : (CircleT → ℂ) × (CircleT → ℂ),
    Tendsto (fun η => l2Inner (hkOperator (aEta a η) b k p) q)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (l2Inner (hkOperator a b k p) q))) ∧
  SatisfiesSystem a b k p

/-- `(A_k,B_k) ∈ H_k = H²(D*) × z^k H²(D)` of Eq. (46). -/
def HkSpace (k : ℕ) (p : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  MemH2DStar p.1 ∧ MemZkH2 k p.2

/-- The constant Fourier coefficient (value at `z = 1` of the analytic extension). -/
noncomputable def constantTerm (g : CircleT → ℂ) : ℂ := fourierCoeff g 0

/-- `F_k = (B_k z^{-k})(0) / A_k^*(0)` of Lemma 6/16, Eq. (44)/(52). -/
noncomputable def FkOf (Ak Bk : CircleT → ℂ) (k : ℕ) : ℂ :=
  constantTerm (fun x => Bk x * fourier (-(k : ℤ)) x) / starFun Ak 0

/-- `ψ_k = arctan(-i F_k)` of Eq. (52); `-i F_k` is real for the paper's data. -/
noncomputable def psiOf (F : ℂ) : ℝ := Real.arctan (-(Complex.I * F)).re

/-- `ψ` is the `k`-th phase factor of `f`: it is the `k`-th entry of the unique
iQSP solution sequence of `f` (Theorem 1 / Lemma 16). -/
def IsPhaseFactorOf (f : ℝ → ℝ) (k : ℕ) (ψ : ℝ) : Prop :=
  ∃ Ψ : ℕ → ℝ, IsIQSPL2Solution f Ψ ∧ Ψ k = ψ

/-- The QSP correspondence Eq. (29)/(31): `b(e^{2iθ}) = i f(cos θ)` on the
upper semicircle, together with `(a,b) ∈ B`. -/
def IsQSPPair (f : ℝ → ℝ) (a b : CircleT → ℂ) : Prop :=
  InB a b ∧
    ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      b ((θ / Real.pi : ℝ) : CircleT) = Complex.I * (f (Real.cos θ) : ℂ)

/-- `(A,B)` is the solution of Eq. (41) `(Id + M)(A,B) = (1,0)`. -/
def IsABSolution (a b : CircleT → ℂ) (A B : CircleT → ℂ) : Prop :=
  SatisfiesSystem a b 0 (A, B)

/-- Weak convergence of pairs against all test pairs (Eq. (58)). -/
def WeakTendsto (F : ℝ → (CircleT → ℂ) × (CircleT → ℂ))
    (q : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  ∀ h : (CircleT → ℂ) × (CircleT → ℂ),
    Tendsto (fun η => l2Inner (F η) h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (l2Inner q h))

/-- The operator of Eq. (58) under truncation `η`. -/
noncomputable def lawsonOp (a b : CircleT → ℂ) (η : ℝ)
    (p : (CircleT → ℂ) × (CircleT → ℂ)) : (CircleT → ℂ) × (CircleT → ℂ) :=
  (projDStar (fun x => starFun b x / starFun (aEta a η) x * p.2 x),
   -(projD (fun x => b x / aEta a η x * p.1 x)))

/-- The limiting operator of Eq. (60)/(62). -/
noncomputable def lawsonOp0 (a b : CircleT → ℂ)
    (p : (CircleT → ℂ) × (CircleT → ℂ)) : (CircleT → ℂ) × (CircleT → ℂ) :=
  (projDStar (fun x => starFun b x / starFun a x * p.2 x),
   -(projD (fun x => b x / a x * p.1 x)))

/-- The domain `D = a H²(D*) × a* H²(D)` of Eq. (56). -/
def Dset (a : CircleT → ℂ) : Set ((CircleT → ℂ) × (CircleT → ℂ)) :=
  {p | ∃ h : (CircleT → ℂ) × (CircleT → ℂ),
    p.1 = (fun x => a x * h.1 x) ∧ p.2 = (fun x => starFun a x * h.2 x)}

/-- The weak-convergence domain `E` of Eq. (58). -/
def Eset (a b : CircleT → ℂ) : Set ((CircleT → ℂ) × (CircleT → ℂ)) :=
  {p | ∃ q, WeakTendsto (fun η => lawsonOp a b η p) q}

/-- A partially defined operator on pairs (§4.1). -/
structure DenselyDefinedOperator where
  domain : Set ((CircleT → ℂ) × (CircleT → ℂ))
  toFun : (CircleT → ℂ) × (CircleT → ℂ) → (CircleT → ℂ) × (CircleT → ℂ)

/-- Density of the domain: the `D` in [25, Definition 13.1]. -/
def HasDenseDomain (T : DenselyDefinedOperator) : Prop := Dense T.domain

/-- The adjoint domain condition of [25, Definition 13.1]. -/
def InAdjointDomain (T : DenselyDefinedOperator)
    (g : (CircleT → ℂ) × (CircleT → ℂ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ T.domain, ‖l2Inner (T.toFun h) g‖ ≤ C * pairNorm h

/-- Self-adjointness of a densely defined operator [25, Definition 13.3]: symmetry
on the domain plus `D(M*) ⊆ D(M)`. -/
def IsSelfAdjointOp (T : DenselyDefinedOperator) : Prop :=
  (∀ f ∈ T.domain, ∀ g ∈ T.domain, l2Inner (T.toFun f) g = l2Inner f (T.toFun g)) ∧
  (∀ g, InAdjointDomain T g → g ∈ T.domain)

/-- The unbounded operator `M` of Eq. (62) (with the integer `n` of Lemma 10). -/
noncomputable def unboundedM (a b : CircleT → ℂ) (n : ℤ) : DenselyDefinedOperator :=
  { domain := Dset a
    toFun := fun p => lawsonOp0 a b
      (fun x => fourier n x * p.1 x, fun x => fourier n x * p.2 x) }

/-- `(Id + M)` and `(Id - M)` as endomaps of pair space. -/
def idPlusM (a b : CircleT → ℂ) (p : (CircleT → ℂ) × (CircleT → ℂ)) := hkOperator a b 0 p
def idMinusM (a b : CircleT → ℂ) (p : (CircleT → ℂ) × (CircleT → ℂ)) : (CircleT → ℂ) × (CircleT → ℂ) :=
  (fun x => p.1 x - projDStar (fun y => starFun (fun z => b z / a z) y * p.2 y) x,
   fun x => p.2 x + projD (fun y => (b y / a y) * p.1 y) x)

/-- The `L² × L²` norm of a pair (same as `pairNorm`, named for §4.3). -/
noncomputable def pairL2 (p : (CircleT → ℂ) × (CircleT → ℂ)) : ℝ := pairNorm p

/-- The paper's standing annulus data of §5.1: `b` is a pure imaginary Laurent
polynomial of degree `d`, `b(z) = b(z⁻¹)`, and `|b| ≤ 1 - η` on `𝕋`. -/
structure AnnulusData (η : ℝ) where
  d : ℕ
  b : ℂ → ℂ
  a : ℂ → ℂ
  eta_pos : 0 < η
  eta_lt_half : η < 1 / 2
  norm_le : ∀ z : ℂ, ‖z‖ = 1 → ‖b z‖ ≤ 1 - η
  laurent : ∀ z : ℂ, z ≠ 0 → b z = b z⁻¹
  pureImaginary : ∀ z : ℂ, ‖z‖ = 1 → b z = -star (b z)
  a_ne_zero : ∀ z : ℂ, z ∈ annulus (radiusOf d η) → a z ≠ 0

/-- The analytic extension of `log (1 - |b|²)` to the plane, using the Laurent
structure `|b(z)|² = b(z) b(z⁻¹)` of §5.1, Eq. (105). -/
noncomputable def logOneMinusModSq (b : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.log (1 - b z * b z⁻¹)

/-- `r_j` of `log sqrt(1-|b|²)` for a complex-plane profile `b`. -/
noncomputable def rCoeffOn (b : ℂ → ℂ) (j : ℤ) : ℂ :=
  rCoeff (fun x => b (circlePt x)) j

/-- `r̂_j` of `log sqrt(1-|b|²)` for a complex-plane profile `b`. -/
noncomputable def rHatOn (b : ℂ → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  rHat (fun x => b (circlePt x)) N j

/-- `G(z)` of Eq. (111) for a complex-plane profile `b`. -/
noncomputable def GfunOn (b : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ) * ∑' l : ℕ, rCoeffOn b (-((l : ℤ) + 1)) * z ^ (-((l : ℤ) + 1)) + rCoeffOn b 0

/-- `Ĝ(z)` of Eq. (111) for a complex-plane profile `b`. -/
noncomputable def GhatOn (b : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (2 : ℂ) * ∑ l ∈ Finset.range (N / 2),
      rHatOn b N (-((l : ℤ) + 1)) * z ^ (-((l : ℤ) + 1)) + rHatOn b N 0

/-- `c_j` of `b a⁻¹` for complex-plane profiles. -/
noncomputable def cCoeffOn (a b : ℂ → ℂ) (j : ℤ) : ℂ :=
  fourierCoeff (fun x => b (circlePt x) / a (circlePt x)) j

/-- `c'_j` of `b a⁻¹` (discrete Fourier coefficient, Eq. (119)). -/
noncomputable def cPrimeOn (a b : ℂ → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  dftCoeff N (fun x => b (circlePt x) / a (circlePt x)) j

/-- `ĉ_j` from `â = e^{Ĝ}` (§5.1, Eq. (124)). -/
noncomputable def cHatOn (aHat b : ℂ → ℂ) (N : ℕ) (j : ℤ) : ℂ :=
  dftCoeff N (fun x => b (circlePt x) / aHat (circlePt x)) j

/-- Uniform norm on `𝕋` of a circle function. -/
noncomputable def linfOnT (u : CircleT → ℂ) : ℝ := ⨆ x : CircleT, ‖u x‖

/-- The exponential approximation `â = e^{Ĝ}`. -/
noncomputable def aHatExp (b : ℂ → ℂ) (N : ℕ) : ℂ → ℂ :=
  fun z => Complex.exp (GhatOn b N z)

/-- `f` is a (real even) polynomial of degree at most `2d`, represented in the
Chebyshev basis. -/
def IsEvenChebyshevPolynomial (f : ℝ → ℝ) (d : ℕ) : Prop :=
  ∃ c : ℕ → ℝ, (∀ k, d < k → c k = 0) ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, f x = ∑' k, c k * cheb (2 * k) x)

/-- The `N`-point Riemann–Hilbert–Weiss output for `f` (Theorem 8): the phase
factors produced from the truncated Hankel systems built from the discrete
coefficients `ĉ`. -/
def IsRHWOutput (f : ℝ → ℝ) (η : ℝ) (d N : ℕ) (ψhat : ℕ → ℝ) : Prop :=
  IsEvenChebyshevPolynomial f d ∧ 0 < η ∧ 0 < N ∧
  ∃ b : ℂ → ℂ, ∃ aHat : ℂ → ℂ, aHat = aHatExp b N ∧
    ∃ Ak Bk : ℕ → CircleT → ℂ,
      (∀ k ≤ d, HkSpace k (Ak k, Bk k)) ∧
      (∀ k ≤ d, ψhat k = psiOf (FkOf (Ak k) (Bk k) k))

end Qatlib.Papers.InfiniteQSP26.MainResults
