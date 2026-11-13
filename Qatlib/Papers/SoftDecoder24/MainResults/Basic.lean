/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# SoftDecoder24 — shared source model

Chailloux–Tillich, *Quantum advantage from soft decoders*, fixed arXiv:2411.12553v2
(9 March 2026).  Everything in this file records the paper-layer vocabulary that the
claim modules in `QuantumAlgorithmDev.Papers.SoftDecoder24.MainResults.*` share:

* characters of `ZMod q` and of `(ZMod q)^n` (Definition 2, p.9–10),
* the normalized Fourier transform `F̂(y) = q^{-n/2} Σ_x χ_y(x) F(x)` (Definition 3, p.10),
* convolution `(f ⋆ g)(x) = Σ_y f(y) g(x - y)` (Section 2.1, p.9),
* codes, dual codes and cosets (Definitions 4–5, p.12), syndromes (Problem 3, p.6),
* the restricted distribution `u_p^{H,s}` (Definition 1, p.6) and trace distance (p.9),
* legacy cost annotations and explicit contracts for externally supplied executions.

The result modules prove character, selective Fourier-transform, and fourth-moment
identities. They construct no decoder, preparation circuit, or sampler and prove no
running-time transformation. The legacy records alone are not implementations.

The paper works over the finite field `F_q`.  All identities used in the paper hold
verbatim for the ring `ZMod q` (with `q ≠ 0`), so the model is stated there; where the
paper really needs a field (Reed–Solomon codes, polynomial evaluation) the claim modules
carry the explicit `q` prime hypothesis.  This is a harmless generalisation and is recorded
per theorem in the accompanying docstrings.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open scoped Classical
open Finset

namespace Qatlib.Papers.SoftDecoder24.MainResults.Basic

variable {q : ℕ}

/-! ## Characters (Definition 2, p.9–10) -/

/-- The additive character `χ_y(x) = exp (2 π i x y / q)` of `ZMod q`
(Definition 2, p.9; for prime `q` this is the paper's `e^{2πi x y/q}`). -/
def char [NeZero q] (y x : ZMod q) : ℂ := ZMod.stdAddChar (x * y)

/-- The vector character `χ_y(x) = ∏ᵢ χ_{yᵢ}(xᵢ)` on `(ZMod q)^n` (Definition 2, p.10). -/
def vchar [NeZero q] {n : ℕ} (y x : Fin n → ZMod q) : ℂ := ∏ i, char (y i) (x i)

/-- The Euclidean inner product `x · y = Σᵢ xᵢ yᵢ` on `(ZMod q)^n`. -/
def dot [NeZero q] {n : ℕ} (x y : Fin n → ZMod q) : ZMod q := ∑ i, x i * y i

/-- `dot` is additive in its first argument. -/
theorem dot_add [NeZero q] {n : ℕ} (a b c : Fin n → ZMod q) :
    dot (a + b) c = dot a c + dot b c := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- `dot` is homogeneous in its first argument. -/
theorem dot_smul [NeZero q] {n : ℕ} (a : ZMod q) (y c : Fin n → ZMod q) :
    dot (a • y) c = a * dot y c := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-! ## Fourier transform (Definition 3, p.10) -/

/-- The normalisation `q^{-n/2}`, written as `(√q)^{-n}`. -/
def dftNorm (q : ℕ) : ℂ := ((Real.sqrt (q : ℝ) : ℝ) : ℂ)⁻¹

/-- The normalized Fourier transform `F̂(y) = q^{-n/2} Σ_x χ_y(x) F(x)` on `(ZMod q)^n`
(Definition 3, p.10). -/
def dft [NeZero q] {n : ℕ} (F : (Fin n → ZMod q) → ℂ) (y : Fin n → ZMod q) : ℂ :=
  (dftNorm q) ^ n * ∑ x, vchar y x * F x

/-- The one-dimensional normalized Fourier transform `f̂(y) = q^{-1/2} Σ_x χ_y(x) f(x)`
(Definition 3, p.10 with `n = 1`); this is the transform used in Section 3.5. -/
def dft1 [NeZero q] (f : ZMod q → ℂ) (y : ZMod q) : ℂ :=
  dftNorm q * ∑ x, char y x * f x

/-- The conjugate character `χ̄_y(x)`; equals `conj (χ_y(x))` because characters take
values on the unit circle (Remark after Proposition 2, p.10). -/
def cchar [NeZero q] (y x : ZMod q) : ℂ := ZMod.stdAddChar (-(x * y))

/-! ## Convolution (Section 2.1, p.9) -/

/-- Convolution `(f ⋆ g)(x) = Σ_y f(y) g(x - y)` (Section 2.1, p.9). -/
def conv {G : Type*} [AddGroup G] [Fintype G] (f g : G → ℂ) (x : G) : ℂ :=
  ∑ y, f y * g (x - y)

/-! ## Codes, cosets and syndromes (Section 2.3, p.12; Problem 3, p.6) -/

/-- The dual code `C^⊥ = {y : y·c = 0 for all c ∈ C}` (Section 1.1, p.2). -/
def dual [NeZero q] {n : ℕ} (C : Submodule (ZMod q) (Fin n → ZMod q)) :
    Submodule (ZMod q) (Fin n → ZMod q) where
  carrier := {y | ∀ c ∈ C, dot y c = 0}
  zero_mem' := by
    intro c _
    simp [dot]
  add_mem' := by
    intro a b ha hb c hc
    rw [dot_add, ha c hc, hb c hc, add_zero]
  smul_mem' := by
    intro a y hy c hc
    rw [dot_smul, hy c hc, mul_zero]

/-- The finite carrier of a code, as a `Finset`. -/
def codeSum [NeZero q] {n : ℕ} (C : Submodule (ZMod q) (Fin n → ZMod q)) :
    Finset (Fin n → ZMod q) := by
  classical
  exact Finset.univ.filter (fun c => c ∈ C)

/-- The syndrome `H xᵀ` of a word `x` (Problem 3, p.6). -/
def syndrome [NeZero q] {m n : ℕ} (H : Fin m → Fin n → ZMod q) (x : Fin n → ZMod q) :
    Fin m → ZMod q :=
  fun i => ∑ j, H i j * x j

/-- The coset `C_s = {y : H yᵀ = sᵀ}` (Definition 5, p.12), as a set. -/
def coset [NeZero q] {m n : ℕ} (H : Fin m → Fin n → ZMod q) (s : Fin m → ZMod q) :
    Set (Fin n → ZMod q) :=
  {y | syndrome H y = s}

/-- The coset `-v + C^⊥` appearing in Proposition 3 and Theorem 6 (p.11, p.18). -/
def dualCoset [NeZero q] {n : ℕ} (C : Submodule (ZMod q) (Fin n → ZMod q))
    (v : Fin n → ZMod q) : Finset (Fin n → ZMod q) := by
  classical
  exact Finset.univ.filter (fun y => y + v ∈ dual C)

/-! ## Distributions and distances (Definition 1, p.6; Section 2.1, p.9) -/

/-- The restricted distribution `u_p^{H,s}` of Definition 1 (p.6): `p` conditioned on the
coset `H xᵀ = sᵀ`, with the null-function convention when the conditioning event has zero
mass. -/
def condProb [NeZero q] {m n : ℕ} (H : Fin m → Fin n → ZMod q)
    (p : (Fin n → ZMod q) → ℝ) (s : Fin m → ZMod q) (x : Fin n → ZMod q) : ℝ := by
  classical
  exact if x ∈ coset H s then
    p x / ∑ y, if y ∈ coset H s then p y else 0
  else 0

/-- Trace distance `Δ(p, r) = ½ Σ_x |p(x) - r(x)|` (Section 2.1, p.9). -/
def traceDist {ι : Type*} [Fintype ι] (p r : ι → ℝ) : ℝ :=
  1 / 2 * ∑ x, |p x - r x|

/-! ## The state `|U_v^F⟩` and its norm (Proposition 6, p.15)

The amplitudes of `Σ_{c∈C, e∈F_q^n} F(e) χ_c(v) |c + e⟩` on the basis vector `x` are
`Σ_{c∈C} F(x - c) χ_c(v)`; this is the function `periodicAmp` below. -/

/-- Amplitudes of the periodic state `|U_v^F⟩ = Σ_{c∈C,e} F(e) χ_c(v) |c + e⟩`
(Proposition 6, p.15). -/
def periodicAmp [NeZero q] {n : ℕ} (C : Submodule (ZMod q) (Fin n → ZMod q))
    (F : (Fin n → ZMod q) → ℂ) (v x : Fin n → ZMod q) : ℂ :=
  ∑ c ∈ codeSum C, F (x - c) * vchar c v

/-- `Z_v^F = ‖|U_v^F⟩‖²` (Proposition 6, p.15). -/
def Zv [NeZero q] {n : ℕ} (C : Submodule (ZMod q) (Fin n → ZMod q))
    (F : (Fin n → ZMod q) → ℂ) (v : Fin n → ZMod q) : ℝ :=
  ∑ x, ‖periodicAmp C F v x‖ ^ 2

/-! ## Algorithmic vocabulary

The records in this section preserve the paper's vocabulary. Their cost fields are
independent annotations, not certified runtimes. No algorithmic existence theorem is
proved here. `ExecutesDecoder`, `PreparesState`, and `SamplesCosets` below express
additional input contracts against a supplied backend and a counted operation word.
These contracts are assumptions to any future reduction, not constructed algorithms. -/

/-- An abstract polynomial running-time bound in the field size `q`. -/
def PolyTime (cost : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ q, cost q ≤ c * (q + 2) ^ c

/-- A recovery map with an unverified cost annotation (Problem 3, p.6).
Use `ExecutesDecoder` to require a backend execution at that cost. -/
structure SyndromeDecoder (q n m : ℕ) [NeZero q] where
  /-- The parity-check matrix. -/
  H : Fin m → Fin n → ZMod q
  /-- The recovery map on syndromes. -/
  dec : (Fin m → ZMod q) → (Fin n → ZMod q)
  /-- Unverified cost annotation. -/
  cost : ℕ

/-- Success probability `P_dec = Σ_{e ∈ Good} p(e)` of a decoder, where `Good` is the set
of errors on which `dec (H eᵀ) = e` (Definition 6, p.12). -/
def SyndromeDecoder.successProb {q n m : ℕ} [NeZero q] (A : SyndromeDecoder q n m)
    (p : (Fin n → ZMod q) → ℝ) : ℝ :=
  ∑ e, if A.dec (syndrome A.H e) = e then p e else 0

/-- The decoding set `D` of a decoder (Definition 6 / Theorem 6 proof, p.18). -/
def SyndromeDecoder.decodeSet {q n m : ℕ} [NeZero q] (A : SyndromeDecoder q n m) :
    Finset (Fin n → ZMod q) :=
  Finset.univ.filter (fun e => A.dec (syndrome A.H e) = e)

/-- Legacy cost annotation for preparing `F`; contains no preparation witness.
Use `PreparesState` as an explicit backend contract. -/
structure StatePrep (q n : ℕ) [NeZero q] (F : (Fin n → ZMod q) → ℂ) where
  /-- Unverified cost annotation. -/
  cost : ℕ

/-- Proposed output masses and an independent cost annotation (Problem 4, p.6).
Normalization and a sampling execution require the additional `SamplesCosets` contract. -/
structure CosetSampler (q k n : ℕ) [NeZero q] where
  /-- The output distribution for each syndrome. -/
  out : (Fin k → ZMod q) → (Fin n → ZMod q) → ℝ
  /-- Unverified cost annotation. -/
  cost : ℕ

/-- An external execution model. Its primitive semantics and primitive costs must be
justified by the caller. This declaration supplies no implementation of those primitives. -/
structure ExecutionBackend (Input Output : Type) where
  Op : Type
  State : Type
  initial : Input → State
  step : Op → State → State
  read : State → Output
  charge : Op → ℕ

/-- Interpret the complete operation word, in order. -/
def ExecutionBackend.run {I O : Type} (B : ExecutionBackend I O)
    (word : List B.Op) (input : I) : O :=
  B.read (word.foldl (fun state op => B.step op state) (B.initial input))

/-- Total cost derived from the actual word, relative to the backend's primitive charges. -/
def ExecutionBackend.work {I O : Type} (B : ExecutionBackend I O)
    (word : List B.Op) : ℕ :=
  (word.map B.charge).sum

/-- Composition adds the charges of the two executed operation words. -/
theorem ExecutionBackend.work_append {I O : Type} (B : ExecutionBackend I O)
    (first second : List B.Op) :
    B.work (first ++ second) = B.work first + B.work second := by
  simp [ExecutionBackend.work, List.sum_append]

/-- Explicit decoder input contract: one word implements recovery on every syndrome,
and the declared cost equals the sum of charges for that word. -/
def ExecutesDecoder {q n m : ℕ} [NeZero q] (A : SyndromeDecoder q n m)
    (B : ExecutionBackend (Fin m → ZMod q) (Fin n → ZMod q))
    (word : List B.Op) : Prop :=
  (∀ s, B.run word s = A.dec s) ∧ A.cost = B.work word

/-- External coherent-preparation semantics, with charges for primitive operations.
The caller must justify `prepares` using a quantum execution model. -/
structure PreparationBackend (q n : ℕ) [NeZero q] where
  Op : Type
  prepares : List Op → ((Fin n → ZMod q) → ℂ) → Prop
  charge : Op → ℕ

/-- Explicit preparation input contract. Preparation is assumed for the very word
whose primitive charges sum to the legacy cost; it is not inferred from that cost. -/
def PreparesState {q n : ℕ} [NeZero q] {F : (Fin n → ZMod q) → ℂ}
    (A : StatePrep q n F) (B : PreparationBackend q n) (word : List B.Op) : Prop :=
  B.prepares word F ∧ A.cost = (word.map B.charge).sum

/-- Sampling contract using a uniform finite seed. The output law is derived from
execution on each seed, so it is normalized when `seeds > 0`. Random-seed generation
must be included in the supplied backend's charged primitive model. -/
def SamplesCosets {q k n : ℕ} [NeZero q] (A : CosetSampler q k n)
    (seeds : ℕ)
    (B : ExecutionBackend ((Fin k → ZMod q) × Fin seeds) (Fin n → ZMod q))
    (word : List B.Op) : Prop :=
  0 < seeds ∧ A.cost = B.work word ∧
    ∀ s x, A.out s x =
      (∑ seed : Fin seeds, if B.run word (s, seed) = x then (1 : ℝ) else 0) / seeds

end Qatlib.Papers.SoftDecoder24.MainResults.Basic
