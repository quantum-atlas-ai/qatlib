/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section


/-!
# BddDegreeCSP15 — shared source model (Block `FourierTools`)

Fixed source: arXiv:1505.03424v2 (Barak, Moitra, O'Donnell, Raghavendra,
Regev, Steurer, Trevisan, Vijayaraghavan, Witmer, Wright), "Beating the
random assignment on constraint satisfaction problems of bounded degree",
11 Aug 2015.

This module fixes the vocabulary shared by the claim modules of paper
`BddDegreeCSP15` .  It lives in the `FourierTools` block because source Lemma 2.2 (the
discrete-derivative variance lower bound, `SourceLemma22`) is its first
consumer:

* the sign embedding `{±1} ⊆ ℝ`, the sign cube, uniform average/variance;
* the discrete partial derivative, first-order Fourier coefficient and
  influence (source §2);
* multilinear Boolean polynomials of bounded degree;
* the paper-level randomized-algorithm interface `RandomizedAlgorithm`
  with success probability and polynomial cost bound — a semantic record
  with **no uniformity or computability constraint** (the legacy
  statements quantify over it existentially after the instance, so it
  cannot express the source's algorithmic content; a limitation of this model);
* Max-kXOR instances with their advantage polynomial and value, and
  triangle-free (source Definition 2.1) CSP instances with value, random
  value `μ` and advantage.
-/

set_option autoImplicit false

namespace Qatlib.Papers.BddDegreeCSP15.FourierTools

open scoped BigOperators

/-! ## Sign cube and uniform statistics -/

/-- `false ↦ −1`, `true ↦ +1`: the embedding of `Bool` into `{±1} ⊆ ℝ`. -/
def signOfBool (b : Bool) : ℝ := if b then 1 else -1

/-- The `true` sign is `+1`. -/
@[simp] theorem signOfBool_true : signOfBool true = 1 := rfl

/-- The `false` sign is `−1`. -/
@[simp] theorem signOfBool_false : signOfBool false = -1 := rfl

/-- Every sign squares to one. -/
theorem signOfBool_sq (b : Bool) : signOfBool b ^ 2 = 1 := by
  cases b <;> norm_num [signOfBool]

/-- Every sign has absolute value one. -/
theorem signOfBool_abs (b : Bool) : |signOfBool b| = 1 := by
  cases b <;> norm_num [signOfBool]

/-- No sign is zero. -/
theorem signOfBool_ne_zero (b : Bool) : signOfBool b ≠ 0 := by
  cases b <;> norm_num [signOfBool]

/-- Negating a bit negates its sign. -/
theorem signOfBool_not (b : Bool) : signOfBool (!b) = -signOfBool b := by
  cases b <;> norm_num [signOfBool]

/-- The sign cube `{±1}^n`, encoded as Boolean strings. -/
abbrev SignCube (n : ℕ) := Fin n → Bool

/-- Uniform average over a finite type. -/
noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / (Fintype.card α : ℝ)

/-- Uniform variance `Var[f(x)]` over a finite type. -/
noncomputable def variance {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  avg (fun x => (f x - avg f) ^ 2)

/-- The uniform average is the sum divided by the cardinality. -/
@[simp] theorem avg_def {α : Type*} [Fintype α] (f : α → ℝ) :
    avg f = (∑ x, f x) / (Fintype.card α : ℝ) := rfl

/-- The uniform variance is the average squared deviation. -/
@[simp] theorem variance_def {α : Type*} [Fintype α] (f : α → ℝ) :
    variance f = avg (fun x => (f x - avg f) ^ 2) := rfl

/-! ## Coordinate updates and discrete derivatives -/

/-- Overwrite coordinate `i` of `x` with `b`, keeping all other coordinates. -/
def setCoord {n : ℕ} (x : SignCube n) (i : Fin n) (b : Bool) : SignCube n :=
  Function.update x i b

/-- Overwriting coordinate `i` with `b` really yields `b` at `i`. -/
@[simp] theorem setCoord_self {n : ℕ} (x : SignCube n) (i : Fin n) (b : Bool) :
    setCoord x i b i = b := by
  simp [setCoord]

/-- Overwriting coordinate `i` leaves all other coordinates unchanged. -/
theorem setCoord_ne {n : ℕ} (x : SignCube n) (i j : Fin n) (b : Bool) (h : j ≠ i) :
    setCoord x i b j = x j := by
  simp [setCoord, h]

/-- `setCoord` is `Function.update`. -/
theorem setCoord_eq_update {n : ℕ} (x : SignCube n) (i : Fin n) (b : Bool) :
    setCoord x i b = Function.update x i b := rfl

/-- Overwriting a coordinate with its own value leaves the string unchanged. -/
theorem setCoord_same {n : ℕ} (x : SignCube n) (i : Fin n) : setCoord x i (x i) = x := by
  rw [setCoord_eq_update, Function.update_eq_self]

/-- Partial derivative `∂ᵢP(x) = (P(x', +1) − P(x', −1)) / 2` (source §2). -/
noncomputable def deriv {n : ℕ} (P : SignCube n → ℝ) (i : Fin n) (x : SignCube n) : ℝ :=
  (P (setCoord x i true) - P (setCoord x i false)) / 2

/-- First-order Fourier coefficient `ĝ({i}) = E[g(x)·x_i]` (source §2). -/
noncomputable def fourierSingleton {n : ℕ} (g : SignCube n → ℝ) (i : Fin n) : ℝ :=
  avg (fun x => g x * signOfBool (x i))

/-- `Influence_i[g] = E[(∂ᵢg)²]` (source §2). -/
noncomputable def influence {n : ℕ} (g : SignCube n → ℝ) (i : Fin n) : ℝ :=
  avg (fun x => (deriv g i x) ^ 2)

/-! ## Multilinear Boolean polynomials -/

/-- A multilinear Boolean polynomial of degree at most `k` on `{±1}^N`, represented by its
monomial coefficients. `degree_le` says every nonzero monomial involves at most `k` variables. -/
structure BoolPoly (N k : ℕ) where
  coeff : Finset (Fin N) → ℝ
  degree_le : ∀ S, coeff S ≠ 0 → S.card ≤ k

namespace BoolPoly

variable {N k : ℕ}

/-- Evaluation of a multilinear polynomial on an assignment (monomial expansion). -/
noncomputable def eval (p : BoolPoly N k) (x : SignCube N) : ℝ :=
  ∑ S : Finset (Fin N), (p.coeff S * ∏ i ∈ S, signOfBool (x i))

/-- First-order Fourier coefficient `ĝ({i})`, i.e. the coefficient of `x_i`. -/
def linearCoeff (p : BoolPoly N k) (i : Fin N) : ℝ := p.coeff {i}

/-- The `L¹` mass of the first-order Fourier coefficients `Σ_i |ĝ({i})|` (source Lemma 4.3). -/
noncomputable def linearMass (p : BoolPoly N k) : ℝ :=
  ∑ i : Fin N, |p.linearCoeff i|

/-- Number of nonzero monomials of `p` (the source's `m` in Theorem 4.2). -/
noncomputable def monomialCount (p : BoolPoly N k) : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin N) => p.coeff S ≠ 0)).card

end BoolPoly

/-! ## Paper-level algorithm interfaces -/

/-- A randomized algorithm: for each random string of `randBits` fair coin flips it outputs an
assignment, together with the cost of that run.  Model boundary:
this is a paper-level interface with no uniformity or computability constraint — the legacy
statements quantify over it existentially *after* the instance, so it cannot express the
source's algorithmic content. -/
structure RandomizedAlgorithm (N : ℕ) where
  randBits : ℕ
  run : (Fin randBits → Bool) → SignCube N
  cost : (Fin randBits → Bool) → ℕ

/-- Success probability of a randomized algorithm for a decidable goal `good`: the fraction of
random strings producing an assignment that satisfies `good`. -/
noncomputable def successProb {N : ℕ} (alg : RandomizedAlgorithm N) (good : SignCube N → Bool) :
    ℝ :=
  (∑ r : Fin alg.randBits → Bool, if good (alg.run r) then (1 : ℝ) else 0)
    / (Fintype.card (Fin alg.randBits → Bool) : ℝ)

/-- `PolyTimeBound m n k alg`: each run costs at most a polynomial in `m`, `n`, `exp k`
(the source's `poly(m, n, exp(k))`): `∃ C, cost r ≤ C · (m + n + 1 + 2^k)^C`. -/
def PolyTimeBound {N : ℕ} (m n k : ℕ) (alg : RandomizedAlgorithm N) : Prop :=
  ∃ C : ℕ, ∀ r : Fin alg.randBits → Bool, alg.cost r ≤ C * (m + n + 1 + 2 ^ k) ^ C

/-! ## CSP instance models -/

/-- A Max-`k`XOR instance of `m` constraints on `n` variables, degree at most `D`: each
constraint `ℓ` is a signed parity `b_ℓ · ∏_{j∈S_ℓ} x_j = 1` with `b_ℓ ∈ {±1}`, `|S_ℓ| = k`. -/
structure MaxKXORInstance (n k : ℕ) where
  m : ℕ
  scope : Fin m → Finset (Fin n)
  sign : Fin m → ℝ
  arity : ∀ ℓ, (scope ℓ).card = k
  sign_unit : ∀ ℓ, |sign ℓ| = 1
  D : ℕ
  degree_le : ∀ i : Fin n, (Finset.univ.filter (fun ℓ => i ∈ scope ℓ)).card ≤ D

namespace MaxKXORInstance

variable {n k : ℕ}

/-- Advantage polynomial `P(x) = (1/(2m)) Σ_ℓ b_ℓ ∏_{j∈S_ℓ} x_j` (source §4). -/
noncomputable def advantage (I : MaxKXORInstance n k) (x : SignCube n) : ℝ :=
  (1 / (2 * (I.m : ℝ))) *
    ∑ ℓ : Fin I.m, (I.sign ℓ * ∏ j ∈ I.scope ℓ, signOfBool (x j))

/-- Fraction of constraints satisfied by `x`: `val(x) = 1/2 + P(x)` for Max-kXOR
(source §2, §4). -/
noncomputable def val (I : MaxKXORInstance n k) (x : SignCube n) : ℝ :=
  1 / 2 + I.advantage x

end MaxKXORInstance

/-- A constraint: a scope and a `{0,1}`-valued predicate on assignments. -/
structure Constraint (n : ℕ) where
  scope : Finset (Fin n)
  pred : SignCube n → ℝ
  pred01 : ∀ x, pred x = 0 ∨ pred x = 1

/-- Definition 2.1 (triangle-free): any two distinct scopes meet in at most one variable, and
there are no three distinct constraints whose scopes pairwise intersect. -/
def TriangleFreeScopes {n m : ℕ} (scope : Fin m → Finset (Fin n)) : Prop :=
  (∀ a b : Fin m, a ≠ b → (scope a ∩ scope b).card ≤ 1) ∧
  (¬ ∃ a b c : Fin m, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (scope a ∩ scope b).Nonempty ∧ (scope b ∩ scope c).Nonempty ∧
      (scope a ∩ scope c).Nonempty)

/-- A triangle-free (Definition 2.1), degree-`D`, arity-`[2,k]` CSP instance of `m` constraints
on `n` variables. -/
structure CSPInstance (n k : ℕ) where
  m : ℕ
  constraints : Fin m → Constraint n
  arity_lower : ∀ ℓ, 2 ≤ (constraints ℓ).scope.card
  arity_upper : ∀ ℓ, (constraints ℓ).scope.card ≤ k
  D : ℕ
  degree_le : ∀ i : Fin n,
    (Finset.univ.filter (fun ℓ => i ∈ (constraints ℓ).scope)).card ≤ D
  triangle_free : TriangleFreeScopes (fun ℓ => (constraints ℓ).scope)

namespace CSPInstance

variable {n k : ℕ}

/-- Fraction of constraints satisfied by `x` (source §1). -/
noncomputable def val (I : CSPInstance n k) (x : SignCube n) : ℝ :=
  (1 / (I.m : ℝ)) * ∑ ℓ : Fin I.m, (I.constraints ℓ).pred x

/-- `μ`, the expected fraction of constraints satisfied by a uniformly random assignment (§1). -/
noncomputable def mu (I : CSPInstance n k) : ℝ := avg (fun x => I.val x)

/-- Advantage `P(x) = val(x) − μ` over the random assignment (source §2). -/
noncomputable def advantage (I : CSPInstance n k) (x : SignCube n) : ℝ := I.val x - I.mu

end CSPInstance

end Qatlib.Papers.BddDegreeCSP15.FourierTools
