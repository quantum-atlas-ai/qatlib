/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# DQI source model

Fixed paper version: arXiv:2408.08292v5, *Optimization by Decoded Quantum
Interferometry* (Jordan--Shutty--Wootters--Zalcman--Schmidhuber--King--Isakov--
Khattar--Babbush).  PDF SHA-256
`6357170bb5566b483f72cc95316490cbc7ea8b81678279f3c0836df3929a1b62`.

This module fixes the notation shared by the paper-layer statements: Hamming
shells, the syndrome map `Bᵀ`, the maximum-LINSAT objective, the elementary
symmetric polynomials appearing in the DQI amplitude, the tridiagonal matrices
`A^(m,ℓ,d)`, `Ā^(m,ℓ)`, `M^(m,ℓ)` and `E^(m,ℓ,𝓕)`, and the finite expectation
values obtained from the ideal and imperfect DQI states.

The Hilbert-space model is the syndrome-basis model of §8.2: the ideal
unnormalised state is the vector over `𝔽^n` with amplitude
`∑_k w_k / √(p^{n-k} C(m,k)) ∑_{|y|=k} g̃(y)` on `Bᵀ y`, and the computational
basis distribution is the Hadamard transform of that vector.  All sums are
finite sums; all expectations are finite sums divided by the state norm.
-/

open scoped BigOperators
open Finset

namespace Qatlib.Papers.DQIOptim24.MainResults.Source

noncomputable section
set_option autoImplicit false

/-! ## Hamming shells and the syndrome map -/

/-- Hamming weight on `𝔽^m` (the number of nonzero coordinates). -/
def weight {𝔽 : Type*} [Zero 𝔽] [DecidableEq 𝔽] [Fintype 𝔽] {m : ℕ} (y : Fin m → 𝔽) : ℕ :=
  hammingNorm y

/-- The Hamming shell of weight `k`: all `y ∈ 𝔽^m` with `|y| = k`. -/
def shell (𝔽 : Type*) [Zero 𝔽] [DecidableEq 𝔽] [Fintype 𝔽] (m k : ℕ) :
    Finset (Fin m → 𝔽) :=
  Finset.univ.filter (fun y => weight y = k)

/-- The syndrome `Bᵀ y`. -/
def syndrome {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (y : Fin m → 𝔽) : Fin n → 𝔽 :=
  Matrix.mulVec B.transpose y

/-- The syndrome map `y ↦ Bᵀ y` as a linear map. -/
def syndromeLin {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) :
    (Fin m → 𝔽) →ₗ[𝔽] (Fin n → 𝔽) :=
  Matrix.mulVecLin B.transpose

/-- `d` is the minimum distance of the code `C^⊥ = ker Bᵀ`. -/
def IsMinDistance {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (d : ℕ) : Prop :=
  (∀ y : Fin m → 𝔽, y ≠ 0 → syndrome B y = 0 → d ≤ weight y) ∧
    (∃ y : Fin m → 𝔽, y ≠ 0 ∧ syndrome B y = 0 ∧ weight y = d)

/-! ## Characters and the max-LINSAT / max-XORSAT objective -/

/-- The sign character `(-1)^a` of `𝔽₂`, as a real number. -/
def sign2 (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- The same sign character as a complex number. -/
def sign2C (a : ZMod 2) : ℂ := if a = 0 then 1 else -1

/-- Inner product over `𝔽₂`. -/
def dot2 {m : ℕ} (u v : Fin m → ZMod 2) : ZMod 2 := ∑ i, u i * v i

/-- The max-XORSAT objective `∑_i (-1)^{v_i + b_i·x}`, as a real number. -/
def xorsatObjective {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (x : Fin n → ZMod 2) : ℝ :=
  ∑ i : Fin m, sign2 (v i + ∑ j, B i j * x j)

/-- The max-XORSAT number of satisfied constraints, as a natural number. -/
def xorsatSatisfied {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (x : Fin n → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => (v i + ∑ j, B i j * x j) = 0)).card

/-- The max-LINSAT objective `∑_i f_i(b_i·x)` over a field `𝔽`. -/
def linsatObjective {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (f : Fin m → 𝔽 → ℤ) (x : Fin n → 𝔽) : ℤ :=
  ∑ i : Fin m, f i (∑ j, B i j * x j)

/-- The `k`-th elementary symmetric polynomial evaluated at `x`. -/
def esymmVal {R : Type*} [CommRing R] {m : ℕ} (k : ℕ) (x : Fin m → R) : R :=
  ∑ s ∈ Finset.univ.powersetCard k, ∏ i ∈ s, x i

/-! ## The DQI amplitude and its finite expectation values -/

/-- The unnormalised DQI amplitude `P(f(x))` on `x ∈ 𝔽^n`, in the decomposition
of Lemma 9.2 with weights `w`: `∑_k w_k P^{(k)}(f_1,…,f_m) / √(p^{n-k} C(m,k))`. -/
def dqiAmplitude {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (f : Fin m → 𝔽 → ℤ) (L : ℕ)
    (w : Fin (L + 1) → ℝ) (x : Fin n → 𝔽) : ℂ :=
  ∑ k : Fin (L + 1),
    (w k : ℂ) * ((esymmVal (R := ℂ) k.val (fun i : Fin m =>
      ((f i (∑ j, B i j * x j) : ℤ) : ℂ))) /
      (((Real.sqrt (((Fintype.card 𝔽 : ℝ) ^ (n - k.val)) *
        (Nat.choose m k.val : ℝ))) : ℝ) : ℂ))

/-- Expected number of satisfied constraints for the ideal DQI state, eq. (76)
with the Born rule `|P(f(x))|² / ‖P(f)‖²`. -/
def expectedSatisfied {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (f : Fin m → 𝔽 → ℤ) {L : ℕ}
    (w : Fin (L + 1) → ℝ) : ℝ :=
  (∑ x : Fin n → 𝔽,
      ((linsatObjective B f x : ℤ) : ℝ) * Complex.normSq (dqiAmplitude B f L w x)) /
    (∑ x : Fin n → 𝔽, Complex.normSq (dqiAmplitude B f L w x))

/-! ## Dirac notation and the syndrome-basis DQI states -/

/-- The computational basis vector `|z⟩` of `ℂ^ι`. -/
def ket {ι : Type*} [DecidableEq ι] (z : ι) : ι → ℂ :=
  fun z' => if z' = z then 1 else 0

/-- The sesquilinear inner product `⟨f|g⟩ = ∑_z f(z) conj(g(z))`. -/
def inner {ι : Type*} [Fintype ι] (f g : ι → ℂ) : ℂ :=
  ∑ z, f z * starRingEnd ℂ (g z)

/-- The squared norm induced by `inner`. -/
def normSqFn {ι : Type*} [Fintype ι] (f : ι → ℂ) : ℝ := (inner f f).re

/-- The unnormalised ideal DQI state `|P̃(f)⟩` in the syndrome basis, eq. (66),
with symbol weights `g` (`g y = ∏_i g̃_i(y_i)`, `|g y| = 1`). -/
def idealState {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (g : (Fin m → 𝔽) → ℂ) {L : ℕ}
    (w : Fin (L + 1) → ℝ) : (Fin n → 𝔽) → ℂ :=
  ∑ k : Fin (L + 1), ∑ y ∈ shell 𝔽 m k.val,
    ((((w k) / Real.sqrt (Nat.choose m k.val : ℝ) : ℝ) : ℂ) * g y) • ket (syndrome B y)

/-! ## Matrices from §9 and §10 -/

/-- The `(ℓ+1) × (ℓ+1)` symmetric tridiagonal matrix `A^(m,ℓ,d)` of eq. (70)/(111).
Diagonal entry `k d`; off-diagonal entry between `k` and `k+1` is
`√((k+1)(m-k))`. -/
def tridiagonal (m L : ℕ) (d : ℝ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun k k' =>
    if k = k' then (k.val : ℝ) * d
    else if k.val + 1 = k'.val then Real.sqrt (((k.val : ℝ) + 1) * ((m : ℝ) - k.val))
    else if k'.val + 1 = k.val then Real.sqrt (((k'.val : ℝ) + 1) * ((m : ℝ) - k'.val))
    else 0

/-- The parameter `d = (p-2r)/√(r(p-r))` of Lemma 9.2. -/
def dOfPR (p r : ℕ) : ℝ :=
  (((p : ℝ) - 2 * (r : ℝ)) / Real.sqrt ((r : ℝ) * ((p : ℝ) - (r : ℝ))))

/-- The matrix `A^(m,ℓ,d)` with `d` determined by `p` and `r` (eq. (70)). -/
def Amat (m L p r : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  tridiagonal m L (dOfPR p r)

/-- Real quadratic form `wᵀ A w`. -/
def quadForm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → ℝ) : ℝ :=
  ∑ k, w k * ∑ k', A k k' * w k'

/-- Complex Hermitian form `w† A w` for a real matrix `A`. -/
def cQuadForm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (w : Fin N → ℂ) : ℂ :=
  ∑ k, starRingEnd ℂ (w k) * ∑ k', (A k k' : ℂ) * w k'

/-- `IsOptimalWeights B f w`: `w` maximises the expected number of satisfied
constraints among all nonzero weight vectors. -/
def IsOptimalWeights {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) 𝔽) (f : Fin m → 𝔽 → ℤ) {L : ℕ}
    (w : Fin (L + 1) → ℝ) : Prop :=
  w ≠ 0 ∧ ∀ w' : Fin (L + 1) → ℝ, w' ≠ 0 →
    expectedSatisfied B f w' ≤ expectedSatisfied B f w

/-! ## Eigenvalue predicates -/

/-- `A λ v`: `v` is an eigenvector of `A` with eigenvalue `λ`. -/
def IsEigenpair {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ)
    (v : Fin N → ℝ) : Prop :=
  v ≠ 0 ∧ Matrix.mulVec A v = lam • v

/-- `λ` is the maximum eigenvalue of `A`. -/
def IsMaxEigenvalue {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ) : Prop :=
  (∃ v : Fin N → ℝ, IsEigenpair A lam v) ∧
    ∀ μ : ℝ, (∃ v : Fin N → ℝ, IsEigenpair A μ v) → μ ≤ lam

/-- The asymptotic optimal fraction of Theorem 4.1, eq. (9)/(139). -/
def optimalFraction (μ ρ : ℝ) : ℝ :=
  if ρ ≤ 1 - μ then
    (Real.sqrt (μ * (1 - ρ)) + Real.sqrt (ρ * (1 - μ))) ^ 2
  else 1

/-! ## The binary matrices `M`, `Ā`, `E` and the decoder model -/

/-- The pair set `S^{(i)}_{k,k'}` of eq. (148). -/
def pairSet {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2)) (i : Fin m) (k k' : ℕ) :
    Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  ((shell (ZMod 2) m k) ×ˢ (shell (ZMod 2) m k')).filter
    (fun p => syndrome B (p.1 + p.2 + Pi.single i 1) = 0)

/-- The matrix `M^(m,ℓ)` of Lemma 10.1, eq. (145). -/
def Mmatrix {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ y ∈ shell (ZMod 2) m k.val, ∑ y' ∈ shell (ZMod 2) m k'.val,
        sign2 (dot2 v (y + y')) *
          (if syndrome B y = syndrome B y' then 1 else 0)

/-- The matrix `Ā^(m,ℓ)` of Lemma 10.2, eq. (147), for the ideal (perfect)
decoder. -/
def AbarMatrix {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (v : Fin m → ZMod 2) (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m, ∑ p ∈ pairSet B i k.val k'.val,
        sign2 (v i + dot2 v (p.1 + p.2))

/-- Errors correctly recovered by the single-valued decoder on the weight-`k`
shell. -/
def decodedShell {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) : Finset (Fin m → ZMod 2) :=
  (shell (ZMod 2) m k).filter (fun y => decode (syndrome B y) = y)

/-- Errors misidentified by the decoder on the weight-`k` shell, `F_k`. -/
def failedShell {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) : Finset (Fin m → ZMod 2) :=
  shell (ZMod 2) m k \ decodedShell B decode k

/-- The decoder failure fraction `ε_k = |F_k| / C(m,k)`. -/
def epsAt {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (k : ℕ) : ℝ :=
  ((failedShell B decode k).card : ℝ) / (Nat.choose m k : ℝ)

/-- `ε = max_{0 ≤ k ≤ ℓ} ε_k`. -/
def epsMax {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (L : ℕ) : ℝ :=
  sSup (Set.range (fun k : Fin (L + 1) => epsAt B decode k.val))

/-- The pair set `S^{(i,D)}_{k,k'}` of eq. (178). -/
def pairSetD {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (i : Fin m) (k k' : ℕ) :
    Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  ((decodedShell B decode k) ×ˢ (decodedShell B decode k')).filter
    (fun p => syndrome B (p.1 + p.2 + Pi.single i 1) = 0)

/-- The matrix `Ā^(m,ℓ,𝒟)` of Lemma 10.5, eq. (177). -/
def AbarMatrixD {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (v : Fin m → ZMod 2)
    (L : ℕ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m, ∑ p ∈ pairSetD B decode i k.val k'.val,
        sign2 (v i + dot2 v (p.1 + p.2))

/-- The error pair set `T^{(i,𝓕)}_{k,k'}` of eq. (182). -/
def errorPairSet {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (i : Fin m) (k k' : ℕ) :
    Finset ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
  (((shell (ZMod 2) m k) ×ˢ (failedShell B decode k')) ∪
    ((failedShell B decode k) ×ˢ (shell (ZMod 2) m k'))).filter
    (fun p => p.1 + p.2 + Pi.single i 1 = 0)

/-- The error matrix `E^(m,ℓ,𝓕)` of eq. (181). -/
def Ematrix {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (L : ℕ) :
    Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun k k' =>
    (1 / Real.sqrt ((Nat.choose m k.val : ℝ) * (Nat.choose m k'.val : ℝ))) *
      ∑ i : Fin m, ((errorPairSet B decode i k.val k'.val).card : ℝ)

/-- Euclidean (`l²`) norm on `ℝ^N`, used to state the spectral-norm bound of
Lemma 10.7. -/
def l2norm {N : ℕ} (v : Fin N → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2)

/-- `OperatorBound E c`: the spectral norm of `E` is at most `c`, i.e.
`‖E v‖₂ ≤ c ‖v‖₂` for every `v`. -/
def OperatorBound {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) : Prop :=
  ∀ v : Fin N → ℝ, l2norm (Matrix.mulVec E v) ≤ c * l2norm v

/-- The `q`-ary tridiagonal matrix `A^(q)` of Theorem 15.4, eq. (268). -/
def tridiagonalQ (Q : ℝ) (L : ℕ) (d : ℝ) : Matrix (Fin (L + 1)) (Fin (L + 1)) ℝ :=
  fun k k' =>
    if k = k' then (k.val : ℝ) * d
    else if k.val + 1 = k'.val then Real.sqrt (((k.val : ℝ) + 1) * (Q - k.val))
    else if k'.val + 1 = k.val then Real.sqrt (((k'.val : ℝ) + 1) * (Q - k'.val))
    else 0

/-- The parameter `d = (q-2r)/√(r(q^m-r))` of Theorem 15.4. -/
def dOfQR (q m r : ℕ) : ℝ :=
  (((q : ℝ) - 2 * (r : ℝ)) /
    Real.sqrt ((r : ℝ) * (((q : ℝ) ^ m) - (r : ℝ))))

/-- The unnormalised imperfect DQI state `|P̃_𝒟(f)⟩` of eq. (171): only the
correctly decoded errors `D_k` are kept. -/
def imperfectState {m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod 2))
    (decode : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (v : Fin m → ZMod 2)
    {L : ℕ} (w : Fin (L + 1) → ℝ) : (Fin n → ZMod 2) → ℂ :=
  ∑ k : Fin (L + 1), ∑ y ∈ decodedShell B decode k.val,
    ((((w k) / Real.sqrt (Nat.choose m k.val : ℝ) : ℝ) : ℂ) * sign2C (dot2 v y)) •
      ket (syndrome B y)

/-! ## Entropy and the classical-comparison boundary -/

/-- Binary entropy in bits, `H₂(p) = -p log₂ p - (1-p) log₂ (1-p)`. -/
def binaryEntropy (p : ℝ) : ℝ :=
  - p * Real.log p / Real.log 2 - (1 - p) * Real.log (1 - p) / Real.log 2

/-- The branch of `H₂⁻¹` on `[0, 1/2]`, defined as the supremum of the
`s ≤ 1/2` with `H₂(s) ≥ y`. -/
def binaryEntropyInv (y : ℝ) : ℝ :=
  sSup {s : ℝ | s ∈ Set.Icc 0 (1 / 2) ∧ y ≤ binaryEntropy s}

/-- Recorded §12 / Table 1 satisfaction fractions on the 31,216-variable,
50,000-constraint max-XORSAT instance: DQI+BP at least `0.831`, simulated
annealing at 8 s on one core `0.764`, tailored classical algorithm `0.88`. -/
def tableDQIBP : ℚ := 831 / 1000
def tableSA8s : ℚ := 764 / 1000
def tableTailored : ℚ := 88 / 100

end

end Qatlib.Papers.DQIOptim24.MainResults.Source
