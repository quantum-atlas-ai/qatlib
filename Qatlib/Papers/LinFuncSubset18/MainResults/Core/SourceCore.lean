/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# LinFuncSubset18 — shared paper-layer vocabulary

Ivanyos--Prakash--Santha, *On learning linear functions from subset and its
applications in quantum computing*, fixed version arXiv:1806.09660v1 (25 June 2018).

This module fixes the objects used by the paper-layer statements of the
`MainResults` block:

* `AffineDistribution` — Definition 1.1, an `(A, ℓ)`-distribution on `F^n`:
  a probability mass function supported on `ℓ(u) ∈ A` and constant on every
  level set of the linear form `ℓ`.
* `linearPoly` — the linear form `ℓ` viewed as a degree-one multivariate
  polynomial, used for the divisibility hypothesis of Lemma 2.4 / 3.1.
* `IsScalarMultiple` — "a non-zero constant multiple of `ℓ`", the output
  convention of `LFS` (Definition 1.2).
* `RandomizedProcedure` — the resource ledger used to state the paper's
  "there is a randomized / quantum algorithm with sample complexity ... and
  running time ..." theorems. For the quantum statements of Sections 4--5 the
  seed space models the measurement-outcome randomness and the paper's quantum
  primitives (QFT, the `(V,V^⊥)`-measurement) are granted; the `time` ledger
  counts elementary operations in the paper's cost model. This is an interface
  for the source theorems, not a gate-level complexity model.
* `sampleBudget`, `runtimeBudget` — the concrete `(n+d)^{O(d)}` and
  `poly(log q, (n+d)^d)` templates appearing in Theorems 1.3 / 3.2.

All objects are paper-local: nothing here is added to the shared
Foundations/Concepts layer.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

-- Paper-layer statements quantify over arbitrary finite fields; all
-- decidability below is classical and only used to write probability sums.
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.LinFuncSubset18.MainResults.Core

/-! ## §1. Linear forms as multivariate polynomials -/

section LinearForm

variable {F : Type*} [Field F] {n : ℕ}

/-- The linear form `ℓ : F^n → F` as the degree-one polynomial
`∑ᵢ ℓ(eᵢ) · Xᵢ` in `F[X₀,…,Xₙ₋₁]`. Used to state "`g` is divisible by
`ℓ(x) − α`" literally as a divisibility in `MvPolynomial (Fin n) F`. -/
def linearPoly (ℓ : (Fin n → F) →ₗ[F] F) : MvPolynomial (Fin n) F :=
  ∑ i : Fin n, MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i

/-- Evaluation of `linearPoly ℓ` is `ℓ` itself (arXiv:1806.09660v1,
Definition 1.1 / Section 3, pages 6--9: the polynomial `ℓ(x) − α`). -/
lemma eval_linearPoly (ℓ : (Fin n → F) →ₗ[F] F) (u : Fin n → F) :
    MvPolynomial.eval u (linearPoly ℓ) = ℓ u := by
  have hu : u = ∑ i : Fin n, u i • (Pi.single i (1 : F)) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  have hmap : ℓ (∑ i : Fin n, u i • (Pi.single i (1 : F))) =
      ∑ i : Fin n, u i * ℓ (Pi.single i (1 : F)) := by
    rw [map_sum]
    simp [map_smul, smul_eq_mul]
  calc
    MvPolynomial.eval u (linearPoly ℓ) = ∑ i : Fin n, ℓ (Pi.single i 1) * u i := by
      simp [linearPoly, map_sum]
    _ = ∑ i : Fin n, u i * ℓ (Pi.single i 1) := by
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    _ = ℓ u := by
      conv_rhs => rw [hu]
      rw [hmap]

/-- `ℓ'` is a non-zero constant multiple of `ℓ` (Definition 1.2's output
convention: "a non zero constant multiple of `ℓ`"). -/
def IsScalarMultiple (ℓ' ℓ : (Fin n → F) →ₗ[F] F) : Prop :=
  ∃ c : F, c ≠ 0 ∧ ℓ' = c • ℓ

/-- Boolean (classically decided) version of `IsScalarMultiple`, used as the
success predicate of the randomized procedures below. -/
def isScalarMultipleBool (ℓ' ℓ : (Fin n → F) →ₗ[F] F) : Bool :=
  if IsScalarMultiple ℓ' ℓ then true else false

end LinearForm

/-! ## §2. `(A, ℓ)`-distributions (Definition 1.1) -/

/-- Definition 1.1: an `(A, ℓ)`-distribution on `F^n`. The paper's definition
requires the `ℓ`-image of the distribution to be contained in `A` and the mass
to be `ℓ`-symmetric; `total` records that it is a probability distribution. -/
structure AffineDistribution {F : Type*} [Field F] [Fintype F]
    (n : ℕ) (A : Finset F) (ℓ : (Fin n → F) →ₗ[F] F) where
  /-- Probability mass of a sample point. -/
  prob : (Fin n → F) → ℝ
  nonneg : ∀ u, 0 ≤ prob u
  total : ∑ u : Fin n → F, prob u = 1
  /-- The support is contained in the `ℓ`-preimage of `A`. -/
  support_mem : ∀ u, prob u ≠ 0 → ℓ u ∈ A
  /-- Masses only depend on the value of `ℓ`. -/
  symmetric : ∀ u v, ℓ u = ℓ v → prob u = prob v

/-- The mass attached to a level set `ℓ(u) = α`. -/
def levelMass {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (p : (Fin n → F) → ℝ) (ℓ : (Fin n → F) →ₗ[F] F) (α : F) : ℝ :=
  ∑ u : Fin n → F, if ℓ u = α then p u else 0

/-- The most likely value `α_p = argmax_{α ∈ A} Pr[ℓ(u) = α]` from Section 3,
chosen noncomputably (ties broken arbitrarily by the choice operator). -/
def mostLikelyValue {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (A : Finset F) (p : (Fin n → F) → ℝ) (ℓ : (Fin n → F) →ₗ[F] F)
    (hA : A.Nonempty) : F :=
  (A.exists_max_image (fun α => levelMass p ℓ α) hA).choose

/-- The most likely value lies in `A` (arXiv:1806.09660v1, Section 3, page 9:
`α_p ∈ A` for the `(A,ℓ)`-distribution). -/
lemma mostLikelyValue_mem {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (A : Finset F) (p : (Fin n → F) → ℝ) (ℓ : (Fin n → F) →ₗ[F] F)
    (hA : A.Nonempty) : mostLikelyValue A p ℓ hA ∈ A :=
  ((A.exists_max_image (fun α => levelMass p ℓ α) hA).choose_spec).1

/-- Maximality of `α_p` over `A` (arXiv:1806.09660v1, Section 3, page 9: the
definition of `α_p = argmax_{α ∈ A} Pr[ℓ(u) = α]`). -/
lemma mostLikelyValue_max {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (A : Finset F) (p : (Fin n → F) → ℝ) (ℓ : (Fin n → F) →ₗ[F] F)
    (hA : A.Nonempty) {α : F} (hα : α ∈ A) :
    levelMass p ℓ α ≤ levelMass p ℓ (mostLikelyValue A p ℓ hA) :=
  ((A.exists_max_image (fun α => levelMass p ℓ α) hA).choose_spec).2 α hα

/-- Law of an `N`-tuple of independent samples from `p`. -/
def sampleMass {F : Type*} [Field F] [Fintype F] {n N : ℕ}
    (p : (Fin n → F) → ℝ) (xs : Fin N → Fin n → F) : ℝ :=
  ∏ i : Fin N, p (xs i)

/-- Probability of a Boolean event on an `N`-tuple of independent samples. -/
def tupleProb {F : Type*} [Field F] [Fintype F] {n N : ℕ}
    (p : (Fin n → F) → ℝ) (good : (Fin N → Fin n → F) → Bool) : ℝ :=
  ∑ xs : Fin N → Fin n → F, if good xs then sampleMass p xs else 0

/-! ## §3. Randomized procedures and their resource templates -/

/-- A randomized procedure described by a finite seed space and an explicit
per-input time ledger. For a quantum algorithm the seed represents the joint
outcome of all measurements (the classical input/output behaviour); the
paper's unitary primitives are taken as granted. -/
structure RandomizedProcedure (Input Output : Type*) where
  seed : Type*
  fintypeSeed : Fintype seed
  nonemptySeed : Nonempty seed
  decidableEqSeed : DecidableEq seed
  run : seed → Input → Output
  time : Input → ℕ

attribute [instance] RandomizedProcedure.fintypeSeed
  RandomizedProcedure.nonemptySeed RandomizedProcedure.decidableEqSeed

/-- Success probability of `alg` on inputs distributed as `law`, for the
Boolean predicate `good` on outputs: average over the uniform seed and the
input law. -/
def successProb {Input Output : Type*} [Fintype Input]
    (alg : RandomizedProcedure Input Output) (law : Input → ℝ)
    (good : Output → Bool) : ℝ :=
  (∑ s : alg.seed, ∑ x : Input, if good (alg.run s x) then law x else 0) /
    (Fintype.card alg.seed : ℝ)

/-- Probability that an event `E` on the input holds, averaged over the
uniform seed and the input law; used for "the procedure accepts" events. -/
def eventProb {Input Output : Type*} [Fintype Input]
    (alg : RandomizedProcedure Input Output) (law : Input → ℝ)
    (E : Input → Bool) : ℝ :=
  (∑ _s : alg.seed, ∑ x : Input, if E x then law x else 0) /
    (Fintype.card alg.seed : ℝ)

/-- Output law of a randomized procedure on a finite input law. -/
def outputLaw {Input Output : Type*} [Fintype Input] [Fintype Output]
    [DecidableEq Output] (alg : RandomizedProcedure Input Output)
    (law : Input → ℝ) (v : Output) : ℝ :=
  (∑ s : alg.seed, ∑ x : Input, if alg.run s x = v then law x else 0) /
    (Fintype.card alg.seed : ℝ)

/-- Acceptance-conditioned output law: distribution of `run s x` conditioned on
the acceptance event `accept x`. Used in Proposition 5.5, where only retained
samples are required to follow an `(A, ℓ)`-distribution. -/
def conditionedOutputLaw {Input Output : Type*} [Fintype Input] [Fintype Output]
    [DecidableEq Output] (alg : RandomizedProcedure Input Output)
    (law : Input → ℝ) (E : Input → Bool) (v : Output) : ℝ :=
  (∑ s : alg.seed, ∑ x : Input, if E x && (alg.run s x = v) then law x else 0) /
    (∑ _s : alg.seed, ∑ x : Input, if E x then law x else 0)

/-- The `(n+d)^{O(d)}` sample count template: `(n+d)^{d·k}`. -/
def sampleBudget (n d k : ℕ) : ℕ := (n + d) ^ (d * k)

/-- The `poly(log q, (n+d)^d)` time template with degree `k`:
`C · (⌊log₂ q⌋+1)^k · ((n+d)^d)^k`. -/
def runtimeBudget (q n d k C : ℕ) : ℕ :=
  C * (Nat.log 2 q + 1) ^ k * ((n + d) ^ d) ^ k

/-- The `poly(n, log q)` time template of Corollary 3.3. -/
def polyTimeBudget (q n k C : ℕ) : ℕ := C * (n + 1) ^ k * (Nat.log 2 q + 1) ^ k

end Qatlib.Papers.LinFuncSubset18.MainResults.Core
