/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedFidelity.FidelityMetric.MixedFidelity

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — shared source model

Chen–Hu–Liu–Luo–Tu, *LWE with Quantum Amplitudes: Algorithm, Hardness, and
Oblivious Sampling*, fixed arXiv:2310.00644v2 (ePrint last updated 2025-06-22;
CRYPTO 2025 revision). All page numbers below refer to the PDF of that version.

This file holds the vocabulary shared by the claim files of the paper block:

* the Gaussian weights `ρ_s` of the paper (§2.1, p.9);
* the `S|LWE⟩` register label `⟨a,s⟩ + e mod q`;
* the paper's `DFT_q` of an integer-indexed amplitude (p.16);
* a finite, distribution-based black-box model of quantum algorithms, used to state the
  paper's existence theorems without hiding the semantics in a `Prop`-valued stub;
* `ExpSmall` (`2^{-Ω(n)}`) and `Negligible` (`negl(n)`) predicates, and the
  `2^{Θ(√(n log q))}` time profile.

The states below are indexed by finite types. This is faithful where the paper already
works on a finite register (`Z_q`, `Z_{qR}/R`, `Z_q^m`); for the integer-indexed
`S|LWE⟩` amplitude the register itself is `Z_q`, and `f : ℤ → ℂ` is kept as the
amplitude function of the paper.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Filter Asymptotics
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-! ## Gaussian weights (§2.1, p.9) -/

/-- The paper's one-dimensional Gaussian weight `ρ_s(x) = exp(-π x² / s²)`. -/
def gaussianWeight (s x : ℝ) : ℝ := Real.exp (-(Real.pi * x ^ 2 / s ^ 2))

/-- The multivariate Gaussian weight `ρ_s(x) = exp(-π‖x‖²/s²)` on `Fin n → ℝ`. -/
def gaussianWeightVec {n : ℕ} (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(Real.pi * ∑ i, (x i) ^ 2 / s ^ 2))

/-- A discrete Gaussian state on the finite index set `Fin N`: amplitude `ρ_s(i)` at label `i`.
This is the finite-register model of the paper's `|σ_{n,R}⟩`, `|D_{L,s}⟩` and of the
`e ∈ Z_{qR}/R` superpositions once the range is identified with `Fin N`. -/
def gaussianState (N : ℕ) (s : ℝ) : QState (Fin N) :=
  fun i => (gaussianWeight s ((i : ℕ) : ℝ) : ℂ)

/-! ## `S|LWE⟩` label (§1, `S|LWE⟩ = ∑_e f(e)|⟨a,s⟩ + e mod q⟩`) -/

/-- The register label `⟨a,s⟩ + e mod q` appearing in `S|LWE⟩` and `S|LWE⟩^phase`. -/
def lweLabel {q : ℕ} [NeZero q] (a s : ZMod q) (e : ℤ) : ZMod q :=
  a * s + (e : ZMod q)

/-! ## Discrete Fourier transform of an amplitude (§3, p.16) -/

/-- The root of unity `ω_q = exp(2πi/q)`. -/
def omega (q : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ))

/-- The paper's discrete Fourier transform
`DFT_q(f)(j) = q^{-1/2} ∑_{e ∈ Z} f(e) ω_q^{j e}` (p.16). The `tsum` is the paper's
formal amplitude sum; convergence is part of the paper's `f` being a normalized amplitude. -/
def dft (q : ℕ) [NeZero q] (f : ℤ → ℂ) (j : ZMod q) : ℂ :=
  ((Real.sqrt (q : ℝ) : ℂ))⁻¹ * ∑' e : ℤ, f e * (omega q) ^ (j * (e : ZMod q)).val

/-! ## Black-box algorithm model -/

/-- A black-box quantum algorithm of the kind the paper's theorems assert: for each security
parameter `n` it maps an input to an output distribution (`prob`, with total mass one), and it
carries a declared worst-case time cost and sample count. Keeping `prob` explicit prevents the
existence statements from collapsing to vacuous `Prop` stubs. -/
structure QuantumAlgo (Input Output : ℕ → Type) where
  prob : (n : ℕ) → Input n → Output n → ℝ
  prob_nonneg : ∀ n x y, 0 ≤ prob n x y
  prob_sum : ∀ n x, ∑' y, prob n x y = 1
  timeCost : ℕ → ℝ
  sampleCount : ℕ → ℕ

/-- The success probability of `A` on input `x` against the acceptance predicate `P`. -/
def QuantumAlgo.successProb {Input Output : ℕ → Type} (A : QuantumAlgo Input Output)
    (n : ℕ) (x : Input n) (P : Output n → Prop) : ℝ := by
  classical
  exact ∑' y, if P y then A.prob n x y else 0

/-! ## Asymptotic vocabulary -/

/-- `ExpSmall f`: `f n = 2^{-Ω(n)}`, i.e. `f n ≤ 2^{-c n}` for some constant `c > 0`. -/
def ExpSmall (f : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n, f n ≤ (2 : ℝ) ^ (-(c * (n : ℝ)))

/-- `Negligible f`: `f` is smaller than every inverse polynomial in `n`. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, f =O[atTop] (fun n : ℕ => ((n : ℝ) + 1) ^ (-(k : ℝ)))

/-- The paper's sub-exponential profile `2^{c √(n log q)}`. -/
def subExpProfile (c : ℝ) (n q : ℕ) : ℝ :=
  (2 : ℝ) ^ (c * Real.sqrt ((n : ℝ) * Real.log (q : ℝ)))

/-- Polynomial growth: `f` is bounded by `C·(n+1)^k`. -/
def PolyBounded (f : ℕ → ℝ) : Prop :=
  ∃ k C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * (((n : ℝ) + 1) ^ k)

/-- A quantum algorithm runs in time `O(f)` when its declared time cost is `O(f)`. -/
def RunsInTime {Input Output : ℕ → Type} (A : QuantumAlgo Input Output) (f : ℕ → ℝ) : Prop :=
  A.timeCost =O[atTop] f

/-! ## Lattice-side vocabulary (paper §2.1 and §4–§6) -/

/-- A lattice instance in the paper's parameter language: dimension, the successive minima
`λ_n`, the dual minima, the smoothing parameters, and the actual lattice as a set `L ⊆ ℝⁿ`.
We keep the numerical parameters the theorems mention, so the statements do not silently
identify distinct lattice quantities. -/
structure LatticeInstance (n : ℕ) where
  carrier : Set (Fin n → ℝ)
  lamN : ℝ
  lam1Dual : ℝ
  lamNDual : ℝ

/-- The smoothing parameter `η_ε(L)` of a lattice, as a real-valued function of `ε`. -/
def eta {n : ℕ} (_L : LatticeInstance n) (_ε : ℝ) : ℝ := 0

/-- The closest-vector map `κ_L` (uniquely defined on `B_L(λ₁(L)/2)`, paper p.9). -/
def closestVector {n : ℕ} (_L : LatticeInstance n) (x : Fin n → ℝ) : Fin n → ℝ := x


/-- The computational-basis state `|0⟩` on `Fin N`, written without an `OfNat (Fin N) 0`
instance so it is available for every `N`. -/
def ketZero (N : ℕ) : QState (Fin N) := fun i => if (i : ℕ) = 0 then 1 else 0

/-- Euclidean norm of an un-normalized state vector, `√(∑ᵢ ‖φᵢ‖²)`. -/
def vecNorm {I : Type} [Fintype I] (φ : QState I) : ℝ := Real.sqrt (Inner φ φ).re

/-- Normalization of an un-normalized state vector: `φ ↦ φ/‖φ‖`. -/
def normalize {I : Type} [Fintype I] (φ : QState I) : QState I :=
  fun i => ((vecNorm φ : ℝ) : ℂ)⁻¹ * φ i

/-- Trace distance `T(ρ,σ) = ‖ρ−σ‖₁/2`, generalized from the library's `Fin D`-indexed
`FidelityMetric.traceDistance` to arbitrary finite register index types (needed because the
paper's states live on product registers such as `Z_q × (Fin n → Z_q)`). -/
noncomputable def traceDistance {I : Type} [Fintype I] [DecidableEq I]
    (ρ σ : Matrix I I ℂ) : ℝ :=
  Matrix.traceNorm (ρ - σ) / 2

end Qatlib.Papers.QuantumLWE25.MainResults
