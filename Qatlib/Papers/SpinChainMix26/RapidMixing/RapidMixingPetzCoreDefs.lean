/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Cut-based Petz heat-bath definitions

This module defines finite-chain configurations, site cuts, Gibbs operators, and the
partial-trace Petz heat-bath map for the formalization of [Kim2026]. The equivalence
`PetzCut.matrixEquiv` places the complementary factor before the block factor, while
`petzGenerator` and `petzOpenGenerator` sum the corresponding updates.

It also supplies the matrix-exponential representation `superExp`, marginal masses,
product-state predicates, influence constants, and `mixingTime`. Chain records encode Hermitian
operators and local norm data, with an explicit decomposition and entrywise support condition in
`BoundedRangeChain`.

## Main definitions

* `petzHeatBath`: the cut-based partial-trace recovery map.
* `aEta` and `gammaOf`: the influence constant and associated rate expression.
* `mixingTime`: the infimum of nonnegative uniform mixing times.

## References

* [Kim, 2026][Kim2026]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs

open Qatlib Matrix
open scoped Kronecker

set_option autoImplicit false

/-- Views a square operator as a complex function on pairs of matrix indices. -/
def vecOp {D : ℕ} (A : Operator D) : Fin D × Fin D → ℂ := fun p => A p.1 p.2

/-- Turns a complex function on pairs of indices into a square operator. -/
def unvecOp {D : ℕ} (v : Fin D × Fin D → ℂ) : Operator D := fun i j => v (i, j)

/-- The matrix whose column at each index pair is the vectorization of the map applied to the
corresponding matrix unit. -/
noncomputable def superMatrix {D : ℕ} (L : Operator D → Operator D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun p q => L (fun i j => if (i, j) = q then 1 else 0) p.1 p.2

/-- Applies the matrix exponential of `(t : ℂ) • superMatrix L` to the vectorized input and
converts it back to an operator. -/
noncomputable def superExp {D : ℕ} (L : Operator D → Operator D) (t : ℝ) :
    Operator D → Operator D :=
  fun ρ => unvecOp (NormedSpace.exp ((t : ℂ) • superMatrix L) *ᵥ vecOp ρ)

/-- The unnormalized Gibbs operator `exp ((-β : ℂ) • H)`. -/
noncomputable def gibbsUnnormalized {D : ℕ} (β : ℝ) (H : Operator D) : Operator D :=
  NormedSpace.exp ((-β : ℂ) • H)

/-- The unnormalized Gibbs operator scaled by the inverse of its complex trace. -/
noncomputable def gibbsState {D : ℕ} (β : ℝ) (H : Operator D) : Operator D :=
  (Matrix.trace (gibbsUnnormalized β H))⁻¹ • gibbsUnnormalized β H

/-- Half the Schatten one-norm of the difference of two operators. -/
noncomputable def halfTraceDistance {D : ℕ} (ρ σ : Operator D) : ℝ :=
  (1 / 2 : ℝ) * SchattenOne (ρ - σ)

/-- The operator obtained by applying `Real.sqrt` through real continuous functional calculus. -/
noncomputable def hermSqrt {D : ℕ} (M : Operator D) : Operator D := cfc Real.sqrt M

/-- The operator obtained by applying `x ↦ (Real.sqrt x)⁻¹` through real continuous functional
calculus. -/
noncomputable def hermInvSqrt {D : ℕ} (M : Operator D) : Operator D :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) M

/-- A configuration assigning one of `d` basis values to each of `n` sites. -/
abbrev SiteConfig (n d : ℕ) := Fin n → Fin d

/-- A finite-type equivalence between site configurations and basis indices in `Fin (d ^ n)`. -/
noncomputable def configEquiv (n d : ℕ) : SiteConfig n d ≃ Fin (d ^ n) :=
  (Fintype.equivFin (SiteConfig n d)).trans
    (finCongr (by simp [SiteConfig, Fintype.card_fin]))

/-- A site equivalence splitting `n` sites into a complementary component of size `n - b` and a
block component of size `b`. -/
structure PetzCut (n b : ℕ) where
  siteSplit : Fin n ≃ (Fin (n - b) ⊕ Fin b)

/-- The basis-index equivalence induced by a Petz cut, with the complementary factor first and
the block factor second. -/
noncomputable def PetzCut.matrixEquiv {n b d : ℕ} (c : PetzCut n b) :
    Fin (d ^ n) ≃ (Fin (d ^ (n - b)) × Fin (d ^ b)) :=
  (configEquiv n d).symm.trans <|
    (c.siteSplit.arrowCongr (Equiv.refl (Fin d))).trans <|
      (Equiv.sumArrowEquivProdArrow (Fin (n - b)) (Fin b) (Fin d)).trans <|
        (Equiv.prodCongr (configEquiv (n - b) d) (configEquiv b d))

/-- The condition that the block component of a cut contains exactly the sites satisfying
`(i.val + n - s) % n < ℓ`. -/
def IsCyclicBlockCut {n ℓ : ℕ} (s : ℕ) (c : PetzCut n ℓ) : Prop :=
  ∀ i : Fin n, (∃ k : Fin ℓ, c.siteSplit i = Sum.inr k) ↔ (i.val + n - s) % n < ℓ

/-- The sites whose one-based indices lie between the integer start `s` and `s + ℓ - 1`. -/
def openBlock (n ℓ : ℕ) (s : ℤ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun j => (s : ℤ) ≤ (j.val + 1 : ℤ) ∧ (j.val + 1 : ℤ) ≤ s + (ℓ : ℤ) - 1)

/-- The integer interval of open-chain block starts from `2 - ℓ` to `n`, inclusive. -/
noncomputable def openBlockStarts (n ℓ : ℕ) : Finset ℤ := Finset.Icc (2 - (ℓ : ℤ)) (n : ℤ)

/-- The condition that a cut's block component agrees with the specified one-based open interval
starting at `s`. -/
def IsOpenBlockCut {n b : ℕ} (s : ℤ) (c : PetzCut n b) : Prop :=
  ∀ i : Fin n, (∃ k : Fin b, c.siteSplit i = Sum.inr k) ↔
    (s : ℤ) ≤ (i.val + 1 : ℤ) ∧ (i.val + 1 : ℤ) ≤ s + (b : ℤ) - 1 ∧ (i.val + 1 : ℤ) ≤ (n : ℤ)

/-- The Petz heat-bath map formed by taking the complementary partial trace, conjugating by its
reference inverse square root, tensoring with the block identity, and conjugating by the
full reference square root. -/
noncomputable def petzHeatBath {n ℓ d : ℕ} (c : PetzCut n ℓ) (σ : Operator (d ^ n)) :
    Operator (d ^ n) → Operator (d ^ n) := fun ρ =>
  let e := c.matrixEquiv (d := d)
  let τ := PartialTrace (Matrix.reindex e e ρ)
  let σA := PartialTrace (Matrix.reindex e e σ)
  let X := hermInvSqrt σA * τ * hermInvSqrt σA
  let middle : Matrix (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) ℂ :=
    X ⊗ₖ (1 : Operator (d ^ ℓ))
  hermSqrt σ * Matrix.reindex e.symm e.symm middle * hermSqrt σ

/-- The finite set of sites satisfying the cyclic block condition `(i.val + n - s) % n < ℓ`. -/
def cyclicBlock (n ℓ s : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => (i.val + n - s) % n < ℓ))

/-- The sum of rates `1 / ℓ` over periodic block starts whose blocks contain the selected site. -/
noncomputable def siteUpdateRate (n ℓ i : ℕ) : ℝ :=
  ∑ s ∈ Finset.range n, if (i + n - s) % n < ℓ then (1 / ℓ : ℝ) else 0

/-- The sum of rates `1 / ℓ` over the allowed open-chain starts whose intervals contain the
selected one-based site. -/
noncomputable def openSiteUpdateRate (n ℓ i : ℕ) : ℝ :=
  ∑ s ∈ openBlockStarts n ℓ,
    if (s : ℤ) ≤ i ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1 then (1 / ℓ : ℝ) else 0

/-- The sum of periodic Petz heat-bath updates minus the input, scaled by `1 / ℓ`. -/
noncomputable def petzGenerator {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) : Operator (d ^ n) → Operator (d ^ n) := fun ρ =>
  ((1 : ℂ) / ℓ) • ∑ s : Fin n, (petzHeatBath (cuts s) σ ρ - ρ)

/-- The sum of Petz heat-bath updates over open-chain block starts minus the input, scaled by `1
/ ℓ`. -/
noncomputable def petzOpenGenerator {n ℓ d : ℕ}
    (cuts : ∀ s : ℤ, PetzCut n ((openBlock n ℓ s).card)) (σ : Operator (d ^ n)) :
    Operator (d ^ n) → Operator (d ^ n) := fun ρ =>
  ((1 : ℂ) / ℓ) • ∑ s ∈ openBlockStarts n ℓ,
    (petzHeatBath (cuts s) σ ρ - ρ)

/-- The full-chain reset map `ρ ↦ (1 / n) • ((trace ρ) • σ - ρ)`. -/
noncomputable def fullChainResetGenerator {D : ℕ} (n : ℕ) (σ : Operator D) :
    Operator D → Operator D := fun ρ =>
  ((1 : ℂ) / n) • ((Matrix.trace ρ) • σ - ρ)

/-- A sequence of nonnegative real influence values indexed by natural numbers. -/
structure InfluenceProfile where
  eta : ℕ → ℝ
  nonneg : ∀ r, 0 ≤ eta r

/-- Twice the infinite sum of the influence profile over positive distances. -/
noncomputable def aEta (η : InfluenceProfile) : ℝ := 2 * ∑' r : ℕ, η.eta (r + 1)

/-- The proposed contraction rate `1 - aEta η / ℓ` for a block length `ℓ`. -/
noncomputable def gammaOf (η : InfluenceProfile) (ℓ : ℕ) : ℝ := 1 - aEta η / ℓ

/-- The configuration-indexed tensor product whose entries are products of the corresponding
single-site operator entries. -/
noncomputable def tensorProductConfig {n d : ℕ} (ρ : Fin n → Operator d) :
    Matrix (SiteConfig n d) (SiteConfig n d) ℂ :=
  fun g h => ∏ i : Fin n, ρ i (g i) (h i)

/-- The tensor product of site operators reindexed into `Operator (d ^ n)` through
`configEquiv`. -/
noncomputable def tensorProductOp {n d : ℕ} (ρ : Fin n → Operator d) : Operator (d ^ n) :=
  Matrix.reindex (configEquiv n d) (configEquiv n d) (tensorProductConfig ρ)

/-- The condition that an operator is a tensor product of single-site density operators. -/
def IsProductState {n d : ℕ} (ρ : Operator (d ^ n)) : Prop :=
  ∃ single : Fin n → Operator d, ρ = tensorProductOp single ∧ ∀ i, IsDensityOperator (single i)

/-- The basis-zero matrix unit, defined entrywise by requiring both indices to have value zero. -/
def pureZero (d : ℕ) : Operator d := fun i j => if i.val = 0 ∧ j.val = 0 then (1 : ℂ) else 0

/-- The single-site mass `exp (-t)` at the initial value plus the uniform contribution `(1 - exp
(-t)) / d`. -/
noncomputable def siteOutputMass (d : ℕ) (t : ℝ) (init out : ℕ) : ℝ :=
  Real.exp (-t) * (if out = init then (1 : ℝ) else 0) + (1 - Real.exp (-t)) * (1 / d : ℝ)

/-- The sum of real diagonal entries over configurations with the prescribed value at the
selected site. -/
noncomputable def siteMarginalMass {n d : ℕ} (ρ : Operator (d ^ n)) (i : Fin n)
    (out : Fin d) : ℝ :=
  ∑ g : SiteConfig n d, if g i = out then (ρ (configEquiv n d g) (configEquiv n d g)).re else 0

/-- The exponential weight `Real.exp (-t)` assigned to an untouched site. -/
noncomputable def untouchedMass (t : ℝ) : ℝ := Real.exp (-t)

/-- The logarithmic constant `(1 / 2) * log (16 * ℓ / (3 * (1 - 1 / d) ^ 2))`. -/
noncomputable def lowerBoundConst (ℓ d : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (16 * ℓ / (3 * (1 - 1 / (d : ℝ)) ^ 2))

/-- The infimum of nonnegative times at which every density input evolves within half trace
distance `ε` of `σ`. -/
noncomputable def mixingTime {D : ℕ} (L : Operator D → Operator D) (σ : Operator D)
    (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ ρ : Operator D,
    IsDensityOperator ρ → halfTraceDistance (superExp L t ρ) σ ≤ ε}

/-- A natural interaction range together with a real interaction-strength parameter. -/
structure RangeStrength where
  range : ℕ
  strength : ℝ

/-- The entrywise condition that an operator vanishes between configurations differing at any
site outside `S`. -/
def SupportedOn {n d : ℕ} (S : Finset (Fin n)) (A : Operator (d ^ n)) : Prop :=
  ∀ g h : SiteConfig n d, (∃ j : Fin n, j ∉ S ∧ g j ≠ h j) →
    A (configEquiv n d g) (configEquiv n d h) = 0

/-- The finite cyclic interval of sites satisfying `(j.val + n - i.val) % n < R`. -/
def intervalSites (n R : ℕ) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin n => (j.val + n - i.val) % n < R))

/-- A Hermitian Hamiltonian decomposed into site-indexed terms satisfying the specified support
and spectral-norm bounds. -/
structure BoundedRangeChain (n d : ℕ) (rs : RangeStrength) where
  H : Operator (d ^ n)
  hermitian : H.IsHermitian
  terms : Fin n → Operator (d ^ n)
  term_support : ∀ i : Fin n, SupportedOn (intervalSites n rs.range i) (terms i)
  term_norm : ∀ i : Fin n, OperatorSpectralNorm (terms i) ≤ rs.strength
  hamiltonian : H = ∑ i : Fin n, terms i

/-- A Hermitian chain operator together with `n` two-site operators of spectral norm at most
one. -/
structure PeriodicChain (n d : ℕ) where
  H : Operator (d ^ n)
  hermitian : H.IsHermitian
  term : Fin n → Operator (d * d)
  term_norm : ∀ i, OperatorSpectralNorm (term i) ≤ 1

/-- A Hermitian chain operator together with `n - 1` two-site operators of spectral norm at most
one. -/
structure OpenChain (n d : ℕ) where
  H : Operator (d ^ n)
  hermitian : H.IsHermitian
  term : Fin (n - 1) → Operator (d * d)
  term_norm : ∀ i, OperatorSpectralNorm (term i) ≤ 1

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
