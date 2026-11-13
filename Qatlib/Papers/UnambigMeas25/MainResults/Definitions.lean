/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper-layer definitions for Buzet--Chailloux,
"Fine-Grained Unambiguous Measurements",
arXiv:2510.07298v2 (2025).

The file fixes the finite model used by every claim statement:

* the vector space `F₂ⁿ`, its inner product and the phase `(−1)^z` (§2);
* the shift and phase operators `X_b`, `Z_b` and the quantum Fourier
  transform `H^{⊗n}` (Definitions 7–8, §2.1);
* fine-grained unambiguous measurements (POVM families indexed by parity
  outcomes `(k, H, y)`, Definitions 12–14, §2.3);
* the measurement quality `ρ(S, {F})` for a cost function `C`
  (Definition 15) and symmetric state sets (Definition 16).

All objects are concrete matrices and functions.  Claims whose full paper
proof needs external machinery are stated in corrected or auxiliary scope
directly in the claim files.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace Qatlib.Papers.UnambigMeas25.MainResults

/-! ## The vector space `F₂ⁿ` -/

/-- Binary vectors `x ∈ F₂ⁿ` (paper §2, Notations). -/
abbrev F2Vec (n : ℕ) := Fin n → ZMod 2

/-- The canonical inner product `x · y = Σ_i x_i y_i` in `F₂ⁿ` (§2). -/
def dotF2 {n : ℕ} (x y : F2Vec n) : ZMod 2 := ∑ i, x i * y i

/-- The phase `(−1)^z ∈ ℂ` for `z ∈ F₂`. -/
def phase (z : ZMod 2) : ℂ := if z = 0 then 1 else -1

/-- The phase of `0` is `1`. -/
lemma phase_zero : phase 0 = 1 := rfl

/-- The phase of `1` is `-1`. -/
lemma phase_one : phase 1 = -1 := rfl

/-- Doubling is trivial in `F₂ⁿ`. -/
lemma addSelf_zero {n : ℕ} (v : F2Vec n) : v + v = 0 := by
  have h01 : ∀ z : ZMod 2, z + z = 0 := by
    intro z
    fin_cases z <;> rfl
  funext i
  exact h01 (v i)

/-! ## Shift and phase operators, and the Fourier transform -/

/-- The shift operator `X_b` (Definition 7): `X_b |x⟩ = |x + b⟩`. -/
def shiftX {n : ℕ} (b : F2Vec n) : Matrix (F2Vec n) (F2Vec n) ℂ :=
  fun x y => if x = y + b then 1 else 0

/-- The phase operator `Z_b` (Definition 7): `Z_b |x⟩ = (−1)^{x·b} |x⟩`. -/
def phaseZ {n : ℕ} (b : F2Vec n) : Matrix (F2Vec n) (F2Vec n) ℂ :=
  fun x y => if x = y then phase (dotF2 x b) else 0

/-- The quantum Fourier transform over `F₂ⁿ`, i.e. `H^{⊗n}` (§2.1):
entries `2^{−n/2} (−1)^{x·y}`. -/
noncomputable def qftMat (n : ℕ) : Matrix (F2Vec n) (F2Vec n) ℂ :=
  fun x y => ((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 x y)

/-- The Fourier-transformed ket `|x̂⟩ = H^{⊗n} |x⟩` (Definition 8). -/
noncomputable def hatKet {n : ℕ} (x : F2Vec n) : F2Vec n → ℂ := qftMat n *ᵥ Pi.single x 1

/-! ## Fine-grained unambiguous measurements -/

/-- Index set of fine-grained outcomes (Definition 12): triples
`(k, H, y)` with `H ∈ F₂^{k×n}` and `y ∈ F₂^k`. -/
structure Idx (n : ℕ) where
  /-- Number of parities learned. -/
  k : Fin (n + 1)
  /-- The parity matrix `H`. -/
  H : Matrix (Fin k) (Fin n) (ZMod 2)
  /-- The parity values `y`. -/
  y : Fin k → ZMod 2
  deriving Fintype

/-- The outcome `(H, y)` is correct on `x`, i.e. `H x = y`. -/
def Idx.holds {n : ℕ} (idx : Idx n) (x : F2Vec n) : Prop :=
  ∀ i, (∑ j, idx.H i j * x j) = idx.y i

/-- Euclidean inner product `⟨u|v⟩ = Σ conj(u_i) v_i`. -/
def innerVec {n : ℕ} (u v : F2Vec n → ℂ) : ℂ := ∑ i, starRingEnd ℂ (u i) * v i

/-- Positive semidefiniteness for complex matrices: self-adjoint with
nonnegative real quadratic form. -/
def IsPSD {n : ℕ} (M : Matrix (F2Vec n) (F2Vec n) ℂ) : Prop :=
  M = Mᴴ ∧ ∀ u : F2Vec n → ℂ, 0 ≤ (innerVec u (M *ᵥ u)).re

/-- `F` is a POVM over the index set `Idx n`: every element is positive
semidefinite and the elements sum to the identity. -/
def IsPOVMOverIdx {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ) : Prop :=
  (∀ idx, IsPSD (F idx)) ∧
    ∀ x y : F2Vec n, ∑ idx, F idx x y = (if x = y then 1 else 0)

/-- The fine-grained unambiguity condition (Definition 13): outcome
`(H, y)` never fires on `|ψ_x⟩⟨ψ_x|` unless `H x = y`. -/
def IsUnambiguous {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ)
    (ψ : F2Vec n → F2Vec n → ℂ) : Prop :=
  ∀ idx : Idx n, ∀ x : F2Vec n, ¬ idx.holds x →
    innerVec (ψ x) (F idx *ᵥ ψ x) = 0

/-- `Γ(S)`: the fine-grained unambiguous measurements on `S`
(Definition 14). -/
def IsFGUM {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ)
    (ψ : F2Vec n → F2Vec n → ℂ) : Prop :=
  IsPOVMOverIdx F ∧ IsUnambiguous F ψ

/-- The measurement quality `ρ(S, {F})` for cost function `C`
(Definition 15): the expected `C(k)`-weighted outcome mass. -/
noncomputable def rhoOf {n : ℕ} (C : Fin (n + 1) → ℝ)
    (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ) (ψ : F2Vec n → F2Vec n → ℂ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ x, ∑ idx, C idx.k * (innerVec (ψ x) (F idx *ᵥ ψ x)).re

/-- Symmetric state sets (Definition 16): `|ψ_x⟩ = X_x |ψ_0⟩`. -/
def IsSymmetricSet {n : ℕ} (ψ : F2Vec n → F2Vec n → ℂ) : Prop :=
  ∀ x : F2Vec n, ψ x = shiftX x *ᵥ ψ 0

/-- Fourier coefficients `α̂_i = ⟨î|ψ_0⟩` (§2.3). -/
noncomputable def fourierCoeff {n : ℕ} (ψ0 : F2Vec n → ℂ) (i : F2Vec n) : ℂ :=
  innerVec (fun j => ((Real.sqrt 2)⁻¹ ^ n : ℝ) * phase (dotF2 i j)) ψ0

/-- Symmetrized measurements (Definition 17): `X_a F_{H,y} X_a =
F_{H, y + H a}` for all `a`. -/
def IsSymmetrized {n : ℕ} (F : Idx n → Matrix (F2Vec n) (F2Vec n) ℂ) : Prop :=
  ∀ idx : Idx n, ∀ a : F2Vec n, ∀ i j : F2Vec n,
    (shiftX a * F idx * shiftX a) i j = F ⟨idx.k, idx.H, fun r => idx.y r + ∑ s, idx.H r s * a s⟩ i j

end Qatlib.Papers.UnambigMeas25.MainResults
