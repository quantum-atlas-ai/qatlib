/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatticeFilter21.MainResults.Model.SourceModel
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.UnitaryGroup

set_option backward.isDefEq.respectTransparency false

/-!
# Distribution, Gram–Schmidt and filtering-state vocabulary for `LatticeFilter21`

Fixed source version: arXiv:2108.11015.

This module supplies the objects that the paper's lemmas quantify over:

* the bounded-uniform and interval-uniform amplitudes of Corollaries 9/36 and
  Theorems 13/46;
* the Born weights and finite probabilities used by Lemmas 22, 23, 34, 42 and
  Corollary 24 (finite uniform measure over `y` and over the measurement
  outcomes, with the outcome weights `1 - |⟨ψ_y|ψ_x⟩|²` and `|⟨ψ_y|ψ_x⟩|²`);
* the Gram–Schmidt vocabulary of Section 4 (`gsNorm`, column vectors,
  circulant matrices);
* the filtering state after the `m` unitaries `U_i` of Algorithm 2, i.e. the
  tensor product of the normalised Gram–Schmidt coefficients, and the bad mass
  `∑_{s ∈ Bad_u} |w_s|²` of Lemmas 35 and 43.
-/

namespace Qatlib.Papers.LatticeFilter21.MainResults

open scoped BigOperators
open Finset

set_option autoImplicit false

/-! ## Amplitude distributions -/

/-- The bounded-uniform amplitude `f(x) = 1/√(2B+1)` on `[-B,B] ∩ Z`, zero
elsewhere (Corollary 9, Corollary 36, Theorem 10). -/
noncomputable def boundedUniformAmplitude (q B : ℕ) [NeZero q] : Zq q → ℂ :=
  fun x =>
    if |ZMod.valMinAbs x| ≤ (B : ℤ) then (((Real.sqrt ((2 * B + 1 : ℕ) : ℝ)) : ℝ) : ℂ)⁻¹
    else 0

/-- The uniform amplitude on the prefix `[0, q-c) ∩ Z` (Theorems 13 and 46). -/
noncomputable def prefixUniformAmplitude (q k : ℕ) [NeZero q] : Zq q → ℂ :=
  fun x => if x.val < k then (((Real.sqrt (k : ℝ)) : ℝ) : ℂ)⁻¹ else 0

/-- "The state `∑_e f(e)|e⟩` is efficiently constructible" (Theorem 8, 12, 32,
45): the one-register state with amplitudes `f` is constructible in
polynomial time with negligible error. -/
def AmplitudeConstructible (q : ℕ → ℕ) [∀ n, NeZero (q n)]
    (f : ∀ n, Zq (q n) → ℂ) : Prop :=
  ConstructibleInPolyTime (fun _ : ℕ => Unit) (fun n => Zq (q n))
    (fun n _ x => f n x)

/-- The inverse-polynomial EDCP success schedule `1/((n+1)(q+1))` used by the
EDCP statements; it is bounded below by an inverse polynomial in `n log q`, as
in Definition 11. -/
noncomputable def edcpSchedule (q : ℕ → ℕ) : ℕ → ℝ :=
  fun n => (((n : ℝ) + 1) * ((q n : ℝ) + 1))⁻¹

/-! ## Born weights and finite probabilities -/

/-- The state `|ψ_v⟩ = ∑_e g(e)|v+e⟩` of Eq. (6), where `g` is the amplitude
in the error register (in the paper `g = f̂`). -/
noncomputable def psiVec {q : ℕ} (g : Zq q → ℂ) (v : Zq q) : QState (Zq q) :=
  fun w => g (w - v)

/-- The Hilbert inner product of two finite amplitude functions. -/
noncomputable def stateInner {ι : Type} [Fintype ι] (φ ψ : QState ι) : ℂ :=
  ∑ i, starRingEnd ℂ (φ i) * ψ i

/-- The squared norm of a finite amplitude function. -/
noncomputable def stateNormSq {ι : Type} [Fintype ι] (φ : QState ι) : ℝ :=
  (stateInner φ φ).re

/-- The norm of a finite amplitude function. -/
noncomputable def stateNorm {ι : Type} [Fintype ι] (φ : QState ι) : ℝ :=
  Real.sqrt (stateNormSq φ)

/-- The Born weight of the outcome `0` when measuring `U_y|ψ_x⟩` in the
computational basis: `|⟨ψ_y|ψ_x⟩|²`. -/
noncomputable def zeroOutcomeWeight {q : ℕ} [NeZero q] (g : Zq q → ℂ) (x y : Zq q) : ℝ :=
  ‖stateInner (psiVec g y) (psiVec g x)‖ ^ 2

/-- The Born weight of a non-zero outcome, `1 - |⟨ψ_y|ψ_x⟩|²`. -/
noncomputable def nonzeroOutcomeWeight {q : ℕ} [NeZero q] (g : Zq q → ℂ) (x y : Zq q) : ℝ :=
  1 - zeroOutcomeWeight g x y

/-- The probability of a non-zero outcome averaged over uniform `y`, i.e. the
left-hand side of Lemma 22. -/
noncomputable def avgNonzeroWeight {q : ℕ} [NeZero q] (g : Zq q → ℂ) (x : Zq q) : ℝ :=
  ((q : ℝ))⁻¹ * ∑ y : Zq q, nonzeroOutcomeWeight g x y

/-- The joint weight of a set `S` of coordinates producing non-zero outcomes
and its complement producing zeros, for fixed `x` and `y` (Lemma 23). -/
noncomputable def jointMeasure {m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (x y : Fin m → Zq q) (S : Finset (Fin m)) : ℝ :=
  (∏ i ∈ S, nonzeroOutcomeWeight g (x i) (y i)) *
    (∏ i ∈ Finset.univ \ S, zeroOutcomeWeight g (x i) (y i))

/-- The probability, over uniform `y` and the measurement outcomes, that at
least `t` of the `m` outcomes are non-zero (Lemma 23). -/
noncomputable def probCountAtLeast {m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (x : Fin m → Zq q) (t : ℝ) : ℝ :=
  ((q : ℝ) ^ m)⁻¹ *
    ∑ y : Fin m → Zq q, ∑ S ∈ Finset.univ.powerset,
      if t ≤ (S.card : ℝ) then jointMeasure g x y S else 0

/-- The probability, over uniform `y` and all measurement outcomes, that for
every `u` at least `t` of the `m` coordinates are non-zero (Corollary 24).  The
outcomes for different `u` are conditioned independently on the shared `y`, as
in the paper's union-bound reading. -/
noncomputable def probAllCountAtLeast {n m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (A : Matrix (Fin m) (Fin n) (Zq q)) (t : ℝ) : ℝ :=
  ((q : ℝ) ^ m)⁻¹ *
    ∑ y : Fin m → Zq q, ∑ S : (Fin n → Zq q) → Finset (Fin m),
      if ∀ u, t ≤ ((S u).card : ℝ) then
        ∏ u, jointMeasure g (A.mulVec u) y (S u)
      else 0

/-- Uniform probability over a pair `(A, y_1,…,y_m)`, used to state "for an
overwhelming fraction of all `A,y`" (Lemmas 35 and 43). -/
noncomputable def probOverSetup {n m q : ℕ} [NeZero q]
    (P : Matrix (Fin m) (Fin n) (Zq q) → (Fin m → Zq q) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun p : Matrix (Fin m) (Fin n) (Zq q) × (Fin m → Zq q) =>
      P p.1 p.2)).card : ℝ) /
    (Fintype.card (Matrix (Fin m) (Fin n) (Zq q)) * Fintype.card (Fin m → Zq q) : ℝ)

/-! ## Gram–Schmidt vocabulary of Section 4 -/

/-- The length of the `i`-th Gram–Schmidt vector of the ordered list `b`. -/
noncomputable def gsNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (b : Fin k → E) (i : Fin k) : ℝ :=
  ‖InnerProductSpace.gramSchmidt ℝ b i‖

/-- The `j`-th column of a real matrix, as a Euclidean vector. -/
noncomputable def colVec {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => C i j)

/-- The length of the Gram–Schmidt vector attached to the `k`-th column of `C`
(the paper's `‖GS(C)_{k-1}‖₂`). -/
noncomputable def gsColumnNorm {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : ℝ :=
  gsNorm (fun j : Fin n => colVec C j) k

/-- A real circulant matrix with first row `c`; `C i j = c (i - j)`. -/
noncomputable def circulantMatrix {q : ℕ} (c : Zq q → ℝ) : Matrix (Zq q) (Zq q) ℝ :=
  fun i j => c (i - j)

/-- The Euclidean-space view of an amplitude function, used to apply Mathlib's
Gram–Schmidt procedure. -/
noncomputable def euclidOf {ι : Type*} (φ : ι → ℂ) : EuclideanSpace ℂ ι :=
  (WithLp.equiv 2 (ι → ℂ)).symm φ

/-- The normalised `j`-th Gram–Schmidt vector of the list `t ↦ |ψ_{y+t}⟩`,
where `t` ranges over `Fin q` through the ring isomorphism `Fin q ≃+* Z_q`. -/
noncomputable def ngsVec {q : ℕ} [NeZero q] (g : Zq q → ℂ) (v : Zq q) (j : Fin q) :
    QState (Zq q) :=
  fun i =>
    let b : EuclideanSpace ℂ (Zq q) :=
      InnerProductSpace.gramSchmidt ℂ
        (fun t : Fin q => euclidOf (psiVec g (v + (ZMod.finEquiv q t)))) j
    (stateNorm (fun k => b k))⁻¹ * b i

/-- The amplitude of the outcome `s` after applying the filtering unitaries
`U_i` (Algorithm 2/3) to the `m` registers of `|φ_x⟩`, where `x i = (uᵀA)_i`.
It is the product of the Gram–Schmidt coefficients. -/
noncomputable def filteredAmplitude {m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (y x : Fin m → Zq q) (s : Fin m → Zq q) : ℂ :=
  ∏ i, stateInner (ngsVec g (y i) ((ZMod.finEquiv q).symm (s i))) (psiVec g (x i))

/-- The filtering state on the outcome register. -/
noncomputable def filteredState {m q : ℕ} [NeZero q] (g : Zq q → ℂ)
    (y x : Fin m → Zq q) : QState (Fin m → Zq q) :=
  fun s => filteredAmplitude g y x s

/-- The coordinates on which the measured outcome `s` certifies the sample
`x i = (uᵀA)_i`, i.e. `s i = x i - y i`. -/
def certifyingCoords {m q : ℕ} (x y s : Fin m → Zq q) : Finset (Fin m) :=
  Finset.univ.filter (fun i => s i = x i - y i)

/-- The set of coordinates `C` determines the secret `u` when no other secret
agrees with `u` on all rows of `C`. -/
def DeterminesSecret {n m q : ℕ} (A : Matrix (Fin m) (Fin n) (Zq q))
    (C : Finset (Fin m)) (u : Fin n → Zq q) : Prop :=
  ∀ u' : Fin n → Zq q, (∀ i ∈ C, A.mulVec u' i = A.mulVec u i) → u' = u

/-- The bad mass `∑_{s ∈ Bad_u} |w_s|²` of Lemma 35/43: the mass of outcomes
whose certifying coordinates do not determine `u`. -/
noncomputable def badMass {n m q : ℕ} [NeZero q] (A : Matrix (Fin m) (Fin n) (Zq q))
    (y : Fin m → Zq q) (φ : QState (Fin m → Zq q)) (u : Fin n → Zq q) : ℝ := by
  classical
  exact ∑ s, if DeterminesSecret A (certifyingCoords (A.mulVec u) y s) u then 0 else ‖φ s‖ ^ 2

/-! ## Two-level gates (Proposition 15) -/

/-- The entrywise max norm, used to measure the approximation in
Proposition 15. -/
noncomputable def maxNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) : ℝ := by
  classical
  by_cases h : Nonempty ι
  · letI := h
    exact Finset.univ.sup' Finset.univ_nonempty (fun i : ι =>
      Finset.univ.sup' Finset.univ_nonempty (fun j : ι => ‖A i j‖))
  · exact 0

/-- A two-level unitary: unitary and differing from the identity in rank at
most two. -/
def IsTwoLevelGate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup ι ℂ ∧ (U - 1).rank ≤ 2

/-- The ordered product of a finite family of matrices (matrix multiplication is
not commutative, so `Finset.prod` is unavailable). -/
noncomputable def matProd {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (V : Fin k → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (List.ofFn V).prod

/-- `G` is universal for two-level gates: every two-level gate is a finite
product of elements of `G` and their inverses. -/
def UniversalTwoLevel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Set (Matrix ι ι ℂ)) : Prop :=
  ∀ U : Matrix ι ι ℂ, IsTwoLevelGate U →
    ∃ (k : ℕ) (V : Fin k → Matrix ι ι ℂ),
      (∀ i, V i ∈ G ∨ (V i)⁻¹ ∈ G) ∧ matProd V = U

end Qatlib.Papers.LatticeFilter21.MainResults
