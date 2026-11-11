/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Paper-layer objects for Chen--Childs--Hung,
"Quantum algorithm for multivariate polynomial interpolation",
fixed at arXiv:1701.03990v2 (19 Jan 2018).

This module fixes the mathematical vocabulary of the paper:

* the monomial index set `J` of degree-`≤ d` monomials in `n` variables,
  realized as the symmetric power `Sym (Fin (n+1)) d` via the homogenization
  `(x_1,...,x_n) ↦ (x_1/x_{n+1},...,x_n/x_{n+1})` of §3.3 observation (1)
  and eq. (25)-(27), with `#J = C(n+d,d)`;
* the Veronese set `X'_{n,d}` (eq. (27)), the query range `R_k = Z(K^{nk},K^k)`
  of §3.1, its cone `R'_k` (eq. (27)) and the "nonzero coordinates" variant
  `R''_k` of Lemma 3.11;
* the Zariski closure / Krull dimension used for the paper's `dim R_k` (§2.2,
  §3.3), the fundamental domain and dual lattice of §2.1, the success ratio
  `m(R_k ∩ S)/m(S)` of eq. (19)/(24), the finite-field success `|R_k|/q^J`
  of §3.2.1, and the explicit `k_C(n,d)` of eq. (31).

No assertions of the paper are proved here; this file only provides the
objects and elementary bookkeeping (`card_monomialIndex`, monotonicity of
`imageSet`), so that every claim file can state the source result over the
same objects.
-/
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory

namespace Qatlib.Papers.MultivInterp17.MainResults.Model

/-! ## Monomials, Veronese set and the query ranges `R_k`, `R'_k`, `R''_k` -/

/-- The monomial index set `J` of degree-`≤ d` monomials in `n` variables,
realized as degree-`d` monomials in `n+1` variables (`Sym (Fin (n+1)) d`).
This is the homogenization of §3.3 observation (1); its cardinality is
`C(n+d,d)` (see `card_monomialIndex`). -/
abbrev MonomialIndex (n d : ℕ) := Sym (Fin (n + 1)) d

/-- Evaluation of the degree-`d` monomial with exponent multiset `m` at a point
`v ∈ K^{n+1}`: the product of `v i` over the entries `i` of `m`. With the
homogenizing coordinate `v 0 = 1`, this is `x^j` for the exponent vector `j`
of §2.1. -/
def monomialEval {K : Type*} [CommMonoid K] {n d : ℕ}
    (v : Fin (n + 1) → K) (m : MonomialIndex n d) : K :=
  (Sym.map v m : Multiset K).prod

/-- The affine point `(1, x_1, …, x_n) ∈ K^{n+1}` used to homogenize `x ∈ K^n`
(§3.3 observation (1)). -/
def homogPoint {K : Type*} [One K] {n : ℕ} (x : Fin n → K) : Fin (n + 1) → K :=
  Fin.cons (1 : K) x

/-- The Veronese set `X'_{n,d}` of eq. (27): all degree-`d` monomial evaluation
vectors of points in `K^{n+1}`. -/
def veroneseSet (K : Type*) [CommMonoid K] (n d : ℕ) : Set (MonomialIndex n d → K) :=
  Set.range (fun v : Fin (n + 1) → K => fun m => monomialEval v m)

/-- `R'_k` of eq. (27): vectors that are sums of `k` Veronese points with
coefficients in `K`. -/
def secantSet (K : Type*) [CommSemiring K] (n d k : ℕ) : Set (MonomialIndex n d → K) :=
  {w | ∃ (c : Fin k → K) (v : Fin k → Fin (n + 1) → K),
      w = fun m => ∑ i, c i * monomialEval (v i) m}

/-- `R''_k` of Lemma 3.11: sums of `k` Veronese points all of whose coordinates
are nonzero. -/
def reorderSet (K : Type*) [CommSemiring K] (n d k : ℕ) : Set (MonomialIndex n d → K) :=
  {w | ∃ (c : Fin k → K) (v : Fin k → Fin (n + 1) → K),
      (∀ i j, v i j ≠ 0) ∧ w = fun m => ∑ i, c i * monomialEval (v i) m}

/-- `R_k = Z(K^{nk}, K^k)` of §3.1: the image of the query map
`Z(x,y)_j = ∑_i y_i x_i^j`, written with the homogenized point `(1, x_i)`. -/
def imageSet (K : Type*) [CommSemiring K] (n d k : ℕ) : Set (MonomialIndex n d → K) :=
  {w | ∃ (c : Fin k → K) (v : Fin k → Fin n → K),
      w = fun m => ∑ i, c i * monomialEval (homogPoint (v i)) m}

/-- The paper's `J = C(n+d,d)`, the number of monomials of degree at most `d`
in `n` variables (§2.1, §3.3). -/
def monomialCount (n d : ℕ) : ℕ := (n + d).choose d

/-- `#J = C(n+d,d)` (the stars-and-bars count behind eq. (25)-(27)). -/
theorem card_monomialIndex (n d : ℕ) :
    Fintype.card (MonomialIndex n d) = monomialCount n d := by
  rw [monomialCount, Sym.card_sym_eq_choose, Fintype.card_fin]
  congr 1
  omega

/-! ## Zariski closure and algebraic dimension

The paper's `dim R_k` is the dimension of the Zariski closure of a
constructible set (§2.2, §3.3). We formalize the closure as the zero locus of
the vanishing ideal inside `MvPolynomial (MonomialIndex n d) K`, and the
dimension as the Krull dimension of the coordinate ring. For constructible
sets over an algebraically closed field this agrees with the paper's notion,
and over `ℝ` it is the dimension of the Zariski closure of the semialgebraic
set. -/

/-- The vanishing ideal of a set of coefficient vectors. -/
def vanishingIdeal (K : Type*) [CommRing K] {σ : Type*} (S : Set (σ → K)) :
    Ideal (MvPolynomial σ K) where
  carrier := {f | ∀ x ∈ S, MvPolynomial.eval x f = 0}
  zero_mem' := by intro x _; simp
  add_mem' := by
    intro f g hf hg x hx
    simp only [Set.mem_setOf_eq] at hf hg ⊢
    rw [map_add, hf x hx, hg x hx, add_zero]
  smul_mem' := by
    intro a f hf x hx
    simp only [Set.mem_setOf_eq] at hf ⊢
    rw [Algebra.smul_def, map_mul, hf x hx, mul_zero]

/-- The Zariski closure of `S`, i.e. the common zero locus of its vanishing
ideal. -/
def zariskiClosure (K : Type*) [CommRing K] {σ : Type*} (S : Set (σ → K)) :
    Set (σ → K) :=
  {x | ∀ f ∈ vanishingIdeal K S, MvPolynomial.eval x f = 0}

/-- The algebraic dimension of `S`: the Krull dimension of the coordinate ring
of its Zariski closure. This is the paper's `dim R_k` (§2.2, §3.3). -/
def algDim (K : Type*) [CommRing K] {σ : Type*} (S : Set (σ → K)) : WithBot ℕ∞ :=
  ringKrullDim (MvPolynomial σ K ⧸ vanishingIdeal K S)

/-- `S` is a linear subspace of `K^σ`. Used for Palatini's Lemma 3.4
(`R'_{k+1}` is linear). -/
def IsLinearSubspace (K : Type*) [Field K] {σ : Type*} (S : Set (σ → K)) : Prop :=
  ∃ W : Submodule K (σ → K), (W : Set (σ → K)) = S

/-! ## Lattices, fundamental domains and the dual lattice (§2.1) -/

/-- `S` is a fundamental domain for the additive subgroup `Λ`: every point has
a unique decomposition `x = λ + s` with `λ ∈ Λ`, `s ∈ S` (§2.1). -/
def IsFundamentalDomain {V : Type*} [AddCommGroup V] (Λ : AddSubgroup V)
    (S : Set V) : Prop :=
  ∀ x : V, ∃! lam : V, lam ∈ (Λ : Set V) ∧ x - lam ∈ S

/-- A fundamental domain centred at zero (§2.1), as used in Lemma 3.3: the
fundamental domain contains the origin. -/
def IsCenteredFundamentalDomain {V : Type*} [AddCommGroup V] (Λ : AddSubgroup V)
    (S : Set V) : Prop :=
  IsFundamentalDomain Λ S ∧ (0 : V) ∈ S

/-- The analytic dual lattice of `Λ` in `ℝ^σ`: all `f` with `f · λ ∈ ℤ` for
every `λ ∈ Λ` (§2.1, dual lattice `Λ̃`). -/
def dualLattice {σ : Type*} [Fintype σ] (Λ : AddSubgroup (σ → ℝ)) :
    AddSubgroup (σ → ℝ) where
  carrier := {f | ∀ lam ∈ (Λ : Set (σ → ℝ)), ∃ k : ℤ, ∑ i, f i * lam i = (k : ℝ)}
  zero_mem' := by
    intro lam _
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    intro f g hf hg lam hlam
    obtain ⟨kf, hkf⟩ := hf lam hlam
    obtain ⟨kg, hkg⟩ := hg lam hlam
    refine ⟨kf + kg, ?_⟩
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, hkf, hkg]
    push_cast
    ring
  neg_mem' := by
    intro f hf lam hlam
    obtain ⟨k, hk⟩ := hf lam hlam
    refine ⟨-k, ?_⟩
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, hk]
    push_cast
    ring

/-- A lattice in the sense of §2.1: a discrete additive subgroup. -/
def IsLattice {V : Type*} [AddCommGroup V] [TopologicalSpace V]
    (Λ : AddSubgroup V) : Prop :=
  DiscreteTopology Λ

/-! ## Success probabilities -/

/-- The success ratio `m(R ∩ S)/m(S)` of eq. (19)/(24), for a measure `μ` on
the ambient coefficient space. -/
def successRatio {V : Type*} [MeasurableSpace V] (μ : Measure V)
    (R S : Set V) : ℝ≥0∞ :=
  μ (R ∩ S) / μ S

/-- The finite-field success probability `|R_k|/q^J` of §3.2.1 (eq. (10)). -/
def finiteFieldSuccess (F : Type*) [Field F] [Fintype F] (n d k : ℕ) : ℚ :=
  (Nat.card ↥(imageSet F n d k) : ℚ) / (Fintype.card F : ℚ) ^ monomialCount n d

/-! ## The threshold parameters `k_C`, `k_Fq`, `k_R`, `r_{n,d}` -/

/-- `k_C(n,d)` of eq. (31): the number of queries of the complex algorithm.
`⌈C/(n+1)⌉` is written `(C + n)/(n+1)` for `C = C(n+d,d)`. -/
def kC (n d : ℕ) : ℕ :=
  if d = 2 ∧ 2 ≤ n then n + 1
  else if (n, d) = (4, 3) ∨ (n, d) = (2, 4) ∨ (n, d) = (3, 4) ∨ (n, d) = (4, 4) then
    (monomialCount n d + n) / (n + 1) + 1
  else (monomialCount n d + n) / (n + 1)

/-- The finite-field query bound `d/(n+d) · C(n+d,d)`, equal to
`C(n+d-1,d-1)` by Corollary 3.12/3.13. -/
def finiteQueryBound (n d : ℕ) : ℕ := (n + d - 1).choose (d - 1)

/-- `IsFiniteThreshold kFq` says `kFq n d` is the least number of queries such
that the finite-field success probability `|R_k|/q^J` tends to 1 as
`q → ∞` (§3.3, p.9). -/
def IsFiniteThreshold (kFq : ℕ → ℕ → ℕ) : Prop :=
  ∀ n d k,
    (∀ ε : ℚ, 0 < ε → ∃ Q : ℕ, ∀ (F : Type*) [Field F] [Fintype F],
        Q ≤ Fintype.card F → 1 - ε ≤ finiteFieldSuccess F n d k)
      ↔ kFq n d ≤ k

/-- `IsRealThreshold kR` says `kR n d` is the least number of queries such
that the real-field success ratio `m(R_k ∩ S)/m(S)` equals 1 for some
centred fundamental domain `S` (§3.3, p.9). -/
def IsRealThreshold (kR : ℕ → ℕ → ℕ) : Prop :=
  ∀ n d k,
    (∃ (Λ : AddSubgroup (MonomialIndex n d → ℝ)) (S : Set (MonomialIndex n d → ℝ)),
        IsCenteredFundamentalDomain Λ S ∧
        successRatio (volume : Measure (MonomialIndex n d → ℝ))
          (imageSet ℝ n d k) S = 1)
      ↔ kR n d ≤ k

/-- `IsReorderThreshold r` says `r n d` is the least `k` such that the
"nonzero coordinate" range `R''_k` covers all but an `O(q^{J-1})` part of
`F_q^J` (Lemma 3.11, p.11). -/
def IsReorderThreshold (r : ℕ → ℕ → ℕ) : Prop :=
  ∀ n d, 1 ≤ n → 1 ≤ d → ∀ k,
    (∃ C : ℕ, ∀ (F : Type*) [Field F] [Fintype F],
        (Fintype.card F) ^ monomialCount n d
            - C * (Fintype.card F) ^ (monomialCount n d - 1)
          ≤ Nat.card ↥(reorderSet F n d k))
      ↔ r n d ≤ k

/-! ## Fourier states for the lattice lemmas (§3.2.2, Lemma 3.1-3.2) -/

/-- The Fourier phase `e(c·z) = exp(i 2π c·z)` of §3.2.2. -/
def fourierPhase {σ : Type*} [Fintype σ] (c z : σ → ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi) * ((∑ i, c i * z i : ℝ) : ℂ))

/-- The Fourier coefficient `F(I_S)(c) = ∫_S d^n z e(c·z)` of Lemma 3.1. -/
def fourierCoeff {σ : Type*} [Fintype σ] (S : Set (σ → ℝ)) (c : σ → ℝ) : ℂ :=
  ∫ z in S, fourierPhase c z ∂volume

/-- The normalized state `|c̃⟩ = (1/√m(S)) ∫_S d^n z e(c·z)|z⟩` of Lemma 3.1;
as a function of the position `z` it is `z ↦ e(c·z)/√m(S)`. -/
def basisState {σ : Type*} [Fintype σ] (S : Set (σ → ℝ)) (c : σ → ℝ) :
    (σ → ℝ) → ℂ :=
  fun z => fourierPhase c z / (Real.sqrt (volume S).toReal : ℂ)

/-- `{|c̃⟩ : c ∈ Λ}` is a complete orthonormal basis over the support `S`
(Lemma 3.2): orthonormality `⟨c̃'|c̃⟩ = δ_{c,c'}` on `S`, plus the statement
that a function orthogonal to every basis state vanishes on `S`. -/
def IsCompleteBasis {σ : Type*} [Fintype σ] (S : Set (σ → ℝ))
    (Λ : AddSubgroup (σ → ℝ)) : Prop :=
  (∀ c ∈ (Λ : Set (σ → ℝ)), ∀ c' ∈ (Λ : Set (σ → ℝ)),
      ∫ z in S, basisState S c' z * star (basisState S c z) ∂volume
        = if c = c' then 1 else 0) ∧
  (∀ f : (σ → ℝ) → ℂ,
      (∀ c ∈ (Λ : Set (σ → ℝ)),
          ∫ z in S, star (basisState S c z) * f z ∂volume = 0) →
      ∀ z ∈ S, f z = 0)

end Qatlib.Papers.MultivInterp17.MainResults.Model
