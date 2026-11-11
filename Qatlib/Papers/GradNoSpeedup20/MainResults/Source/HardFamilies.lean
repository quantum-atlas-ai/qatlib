/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi

set_option backward.isDefEq.respectTransparency false

/-!
# GradNoSpeedup20 — hard function families and shared vocabulary

Source: *No quantum speedup over gradient descent for non-smooth convex optimization*,
arXiv:2010.01801 (fixed version 2010.01801v2, 2020).

This module fixes the paper's objects once, so that the result modules of
`GradNoSpeedup20.MainResults` can state each claim against a single set of
definitions that match the paper's notation:

* `fz`  — Definition 6, eq. (12): the classical hard family `fz(x) = max_i z_i x_i`.
* `xStarOfZ` — eq. (13): the minimiser `-1/√n · Σ_i z_i e_i` of `fz` on the unit ball.
* `gV`, `fV` — Definition 11, eq. (16): `g_V^(i)(x) = ⟨v_i,x⟩ + (k-i)γ‖x‖`
  and `f_V(x) = max_i g_V^(i)(x)`.
* `fVtrunc` — eq. (44): `max_{i≤t} g_V^(i)`.
* `pV`, `fVWall`, `fVWallTrunc` — eqs. (34), (43), (44): the wall-function family.
* `IsSubgradientAt`, `IsOrthonormalTuple`, `IsSignVector` — the paper's side notions.
* `HaarOrthonormalLaw`, `HaarTailLaw`, `HaarUnitLaw`, `HaarOrthComplementLaw`
  — the randomness models ("chosen uniformly at random") used by the
  probabilistic lemmas, stated as rotation-invariance of the law.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ENNReal
open Finset MeasureTheory

namespace Qatlib.Papers.GradNoSpeedup20.MainResults.Source

/-- The ambient Hilbert space `ℝ^n` of the paper (standard `ℓ²` norm and inner product). -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

instance {n : ℕ} : MeasurableSpace (Vec n) := borel (Vec n)

/-- Package a coordinate function as an element of `ℝ^n`. -/
def ofFn {n : ℕ} (f : Fin n → ℝ) : Vec n := WithLp.toLp 2 f

/-- The packaged vector evaluates to the original coordinate function. -/
@[simp] theorem ofFn_apply {n : ℕ} (f : Fin n → ℝ) (i : Fin n) : (ofFn f) i = f i := rfl

/-- Definition 6 / eq. (12): for `z ∈ ℝ^n` the function
`f_z(x₁,…,xₙ) = max_{i∈[n]} z_i x_i`.  The paper uses `z ∈ {−1,+1}^n`
(`IsSignVector`); we keep the ambient type real. -/
def fz {n : ℕ} [NeZero n] (z : Fin n → ℝ) (x : Vec n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => z i * x i)

/-- A sign vector: every coordinate is `+1` or `−1` (paper: `z ∈ {−1,+1}^n`). -/
def IsSignVector {n : ℕ} (z : Fin n → ℝ) : Prop := ∀ i, z i = 1 ∨ z i = -1

/-- Eq. (13): the minimiser `x* = −1/√n · Σ_i z_i e_i` of `fz` on the unit ball. -/
def xStarOfZ {n : ℕ} [NeZero n] (z : Fin n → ℝ) : Vec n :=
  ofFn (fun i => -(z i) / Real.sqrt (n : ℝ))

/-- Definition 11 / eq. (16): `g_V^(i)(x) = ⟨v_i, x⟩ + (k−i)γ‖x‖`, with the paper's
one-based index `i ∈ [k]` represented by `(i : ℕ) + 1`. -/
def gV {n k : ℕ} (v : Fin k → Vec n) (γ : ℝ) (i : Fin k) (x : Vec n) : ℝ :=
  inner ℝ (v i) x + ((k : ℝ) - ((i : ℕ) + 1 : ℝ)) * γ * ‖x‖

/-- Definition 11 / eq. (16): `f_V(x) = max_{i∈[k]} g_V^(i)(x)`. -/
def fV {n k : ℕ} [NeZero k] (v : Fin k → Vec n) (γ : ℝ) (x : Vec n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => gV v γ i x)

/-- Eq. (44): the prefix maximum `f_V^(t)(x) = max_{i∈[t]} g_V^(i)(x)`, for `1 ≤ t ≤ k`. -/
def fVtrunc {n k : ℕ} [NeZero k] (v : Fin k → Vec n) (γ : ℝ) (t : ℕ) [NeZero t] (htk : t ≤ k)
    (x : Vec n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin t => gV v γ ⟨j.val, lt_of_lt_of_le j.isLt htk⟩ x)

/-- Eq. (34): the wall-family core `p_V(x) = max_{i∈[k]} (⟨v_i,x⟩ − iγ)`,
one-based `i`. -/
def pV {n k : ℕ} [NeZero k] (v : Fin k → Vec n) (γ : ℝ) (x : Vec n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ (v i) x - ((i : ℕ) + 1 : ℝ) * γ)

/-- Eq. (44): the prefix core `p_V^(t)(x) = max_{i∈[t]} (⟨v_i,x⟩ − iγ)`. -/
def pVtrunc {n k : ℕ} [NeZero k] (v : Fin k → Vec n) (γ : ℝ) (t : ℕ) [NeZero t] (htk : t ≤ k)
    (x : Vec n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin t => inner ℝ (v (⟨j.val, lt_of_lt_of_le j.isLt htk⟩)) x
      - ((j.val + 1 : ℕ) : ℝ) * γ)

/-- Eq. (43): the wall family `f_V(x) = max{p_V(x), W_V(x)}`, where `W` is the wall
function of eq. (41).  The wall function itself is supplied as a parameter; the
probabilistic statements below do not need its internal definition. -/
def fVWall {n} (v : Fin 1 → Vec n) (W : Vec n → ℝ) (x : Vec n) : ℝ := max (pV v 0 x) (W x)

/-- A subgradient of `f` at `x` (paper's `∂f(x)`): `g` with the first-order inequality
`f(y) ≥ f(x) + ⟨g, y − x⟩` for every `y`. -/
def IsSubgradientAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x g : E) : Prop :=
  ∀ y : E, f x + inner ℝ g (y - x) ≤ f y

/-- An orthonormal `k`-tuple (Definition 11: `∀i,j ⟨v_i,v_j⟩ = δ_{ij}`). -/
def IsOrthonormalTuple {n k : ℕ} (v : Fin k → Vec n) : Prop :=
  ∀ i j, inner ℝ (v i) (v j) = if i = j then 1 else 0

/-! ## Randomness models

The paper samples orthonormal tuples and unit vectors "uniformly at random"
(Haar measure).  We record only the properties that the proofs use: probability
one, orthonormality, and invariance under the unitary group (with a fixed prefix
in the tail case). -/

/-- A Haar-random orthonormal `k`-tuple law on `ℝ^n`. -/
def HaarOrthonormalLaw {n k : ℕ} (P : Measure (Fin k → Vec n)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ᵐ v ∂P, IsOrthonormalTuple v) ∧
  (∀ U : Vec n ≃ₗᵢ[ℝ] Vec n,
      Measure.map (fun v : Fin k → Vec n => fun i => U (v i)) P = P)

/-- A Haar-random completion of a fixed prefix of length `t`: the first `t`
vectors are fixed pointwise, the remainder is Haar-uniform in the complement, and
the law is invariant under unitaries fixing that prefix. -/
def HaarTailLaw {n k : ℕ} (v : Fin k → Vec n) (t : ℕ) (P : Measure (Fin k → Vec n)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ᵐ w ∂P, IsOrthonormalTuple w ∧ ∀ i : Fin k, (i : ℕ) < t → w i = v i) ∧
  (∀ U : Vec n ≃ₗᵢ[ℝ] Vec n, (∀ i : Fin k, (i : ℕ) < t → U (v i) = v i) →
      Measure.map (fun w : Fin k → Vec n => fun i => U (w i)) P = P)

/-- A Haar-random unit vector law on `ℝ^n`. -/
def HaarUnitLaw {n : ℕ} (P : Measure (Vec n)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ᵐ v ∂P, ‖v‖ = 1) ∧
  (∀ U : Vec n ≃ₗᵢ[ℝ] Vec n, Measure.map U P = P)

/-- A Haar-random unit vector in the orthogonal complement of a fixed orthonormal
prefix `v : Fin k → Vec n`. -/
def HaarOrthComplementLaw {n k : ℕ} (v : Fin k → Vec n) (P : Measure (Vec n)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ᵐ w ∂P, ‖w‖ = 1 ∧ ∀ i : Fin k, inner ℝ (v i) w = 0) ∧
  (∀ U : Vec n ≃ₗᵢ[ℝ] Vec n, (∀ i : Fin k, U (v i) = v i) →
      Measure.map U P = P)

end Qatlib.Papers.GradNoSpeedup20.MainResults.Source
