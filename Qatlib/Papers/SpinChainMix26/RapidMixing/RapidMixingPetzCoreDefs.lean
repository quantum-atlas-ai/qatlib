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
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs

open Qatlib Matrix
open scoped Kronecker

set_option autoImplicit false

def vecOp {D : ℕ} (A : Operator D) : Fin D × Fin D → ℂ := fun p => A p.1 p.2

def unvecOp {D : ℕ} (v : Fin D × Fin D → ℂ) : Operator D := fun i j => v (i, j)

noncomputable def superMatrix {D : ℕ} (L : Operator D → Operator D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  fun p q => L (fun i j => if (i, j) = q then 1 else 0) p.1 p.2

noncomputable def superExp {D : ℕ} (L : Operator D → Operator D) (t : ℝ) :
    Operator D → Operator D :=
  fun ρ => unvecOp (NormedSpace.exp ((t : ℂ) • superMatrix L) *ᵥ vecOp ρ)

noncomputable def gibbsUnnormalized {D : ℕ} (β : ℝ) (H : Operator D) : Operator D :=
  NormedSpace.exp ((-β : ℂ) • H)

noncomputable def gibbsState {D : ℕ} (β : ℝ) (H : Operator D) : Operator D :=
  (Matrix.trace (gibbsUnnormalized β H))⁻¹ • gibbsUnnormalized β H

noncomputable def halfTraceDistance {D : ℕ} (ρ σ : Operator D) : ℝ :=
  (1 / 2 : ℝ) * SchattenOne (ρ - σ)

noncomputable def hermSqrt {D : ℕ} (M : Operator D) : Operator D := cfc Real.sqrt M

noncomputable def hermInvSqrt {D : ℕ} (M : Operator D) : Operator D :=
  cfc (fun x : ℝ => (Real.sqrt x)⁻¹) M

abbrev SiteConfig (n d : ℕ) := Fin n → Fin d

noncomputable def configEquiv (n d : ℕ) : SiteConfig n d ≃ Fin (d ^ n) :=
  (Fintype.equivFin (SiteConfig n d)).trans
    (finCongr (by simp [SiteConfig, Fintype.card_fin]))

structure PetzCut (n b : ℕ) where
  siteSplit : Fin n ≃ (Fin (n - b) ⊕ Fin b)

noncomputable def PetzCut.matrixEquiv {n b d : ℕ} (c : PetzCut n b) :
    Fin (d ^ n) ≃ (Fin (d ^ (n - b)) × Fin (d ^ b)) :=
  (configEquiv n d).symm.trans <|
    (c.siteSplit.arrowCongr (Equiv.refl (Fin d))).trans <|
      (Equiv.sumArrowEquivProdArrow (Fin (n - b)) (Fin b) (Fin d)).trans <|
        (Equiv.prodCongr (configEquiv (n - b) d) (configEquiv b d))

def IsCyclicBlockCut {n ℓ : ℕ} (s : ℕ) (c : PetzCut n ℓ) : Prop :=
  ∀ i : Fin n, (∃ k : Fin ℓ, c.siteSplit i = Sum.inr k) ↔ (i.val + n - s) % n < ℓ

def openBlock (n ℓ : ℕ) (s : ℤ) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter
    (fun j => (s : ℤ) ≤ (j.val + 1 : ℤ) ∧ (j.val + 1 : ℤ) ≤ s + (ℓ : ℤ) - 1)

noncomputable def openBlockStarts (n ℓ : ℕ) : Finset ℤ := Finset.Icc (2 - (ℓ : ℤ)) (n : ℤ)

def IsOpenBlockCut {n b : ℕ} (s : ℤ) (c : PetzCut n b) : Prop :=
  ∀ i : Fin n, (∃ k : Fin b, c.siteSplit i = Sum.inr k) ↔
    (s : ℤ) ≤ (i.val + 1 : ℤ) ∧ (i.val + 1 : ℤ) ≤ s + (b : ℤ) - 1 ∧ (i.val + 1 : ℤ) ≤ (n : ℤ)

noncomputable def petzHeatBath {n ℓ d : ℕ} (c : PetzCut n ℓ) (σ : Operator (d ^ n)) :
    Operator (d ^ n) → Operator (d ^ n) := fun ρ =>
  let e := c.matrixEquiv (d := d)
  let τ := PartialTrace (Matrix.reindex e e ρ)
  let σA := PartialTrace (Matrix.reindex e e σ)
  let X := hermInvSqrt σA * τ * hermInvSqrt σA
  let middle : Matrix (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) ℂ :=
    X ⊗ₖ (1 : Operator (d ^ ℓ))
  hermSqrt σ * Matrix.reindex e.symm e.symm middle * hermSqrt σ

def cyclicBlock (n ℓ s : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => (i.val + n - s) % n < ℓ))

noncomputable def siteUpdateRate (n ℓ i : ℕ) : ℝ :=
  ∑ s ∈ Finset.range n, if (i + n - s) % n < ℓ then (1 / ℓ : ℝ) else 0

noncomputable def openSiteUpdateRate (n ℓ i : ℕ) : ℝ :=
  ∑ s ∈ openBlockStarts n ℓ,
    if (s : ℤ) ≤ i ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1 then (1 / ℓ : ℝ) else 0

noncomputable def petzGenerator {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) : Operator (d ^ n) → Operator (d ^ n) := fun ρ =>
  ((1 : ℂ) / ℓ) • ∑ s : Fin n, (petzHeatBath (cuts s) σ ρ - ρ)

noncomputable def petzOpenGenerator {n ℓ d : ℕ}
    (cuts : ∀ s : ℤ, PetzCut n ((openBlock n ℓ s).card)) (σ : Operator (d ^ n)) :
    Operator (d ^ n) → Operator (d ^ n) := fun ρ =>
  ((1 : ℂ) / ℓ) • ∑ s ∈ openBlockStarts n ℓ,
    (petzHeatBath (cuts s) σ ρ - ρ)

noncomputable def fullChainResetGenerator {D : ℕ} (n : ℕ) (σ : Operator D) :
    Operator D → Operator D := fun ρ =>
  ((1 : ℂ) / n) • ((Matrix.trace ρ) • σ - ρ)

structure InfluenceProfile where
  eta : ℕ → ℝ
  nonneg : ∀ r, 0 ≤ eta r

noncomputable def aEta (η : InfluenceProfile) : ℝ := 2 * ∑' r : ℕ, η.eta (r + 1)

noncomputable def gammaOf (η : InfluenceProfile) (ℓ : ℕ) : ℝ := 1 - aEta η / ℓ

noncomputable def tensorProductConfig {n d : ℕ} (ρ : Fin n → Operator d) :
    Matrix (SiteConfig n d) (SiteConfig n d) ℂ :=
  fun g h => ∏ i : Fin n, ρ i (g i) (h i)

noncomputable def tensorProductOp {n d : ℕ} (ρ : Fin n → Operator d) : Operator (d ^ n) :=
  Matrix.reindex (configEquiv n d) (configEquiv n d) (tensorProductConfig ρ)

def IsProductState {n d : ℕ} (ρ : Operator (d ^ n)) : Prop :=
  ∃ single : Fin n → Operator d, ρ = tensorProductOp single ∧ ∀ i, IsDensityOperator (single i)

def pureZero (d : ℕ) : Operator d := fun i j => if i.val = 0 ∧ j.val = 0 then (1 : ℂ) else 0

noncomputable def siteOutputMass (d : ℕ) (t : ℝ) (init out : ℕ) : ℝ :=
  Real.exp (-t) * (if out = init then (1 : ℝ) else 0) + (1 - Real.exp (-t)) * (1 / d : ℝ)

noncomputable def siteMarginalMass {n d : ℕ} (ρ : Operator (d ^ n)) (i : Fin n)
    (out : Fin d) : ℝ :=
  ∑ g : SiteConfig n d, if g i = out then (ρ (configEquiv n d g) (configEquiv n d g)).re else 0

noncomputable def untouchedMass (t : ℝ) : ℝ := Real.exp (-t)

noncomputable def lowerBoundConst (ℓ d : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (16 * ℓ / (3 * (1 - 1 / (d : ℝ)) ^ 2))

noncomputable def mixingTime {D : ℕ} (L : Operator D → Operator D) (σ : Operator D)
    (ε : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ ρ : Operator D,
    IsDensityOperator ρ → halfTraceDistance (superExp L t ρ) σ ≤ ε}

structure RangeStrength where
  range : ℕ
  strength : ℝ

def SupportedOn {n d : ℕ} (S : Finset (Fin n)) (A : Operator (d ^ n)) : Prop :=
  ∀ g h : SiteConfig n d, (∃ j : Fin n, j ∉ S ∧ g j ≠ h j) →
    A (configEquiv n d g) (configEquiv n d h) = 0

def intervalSites (n R : ℕ) (i : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter (fun j : Fin n => (j.val + n - i.val) % n < R))

structure BoundedRangeChain (n d : ℕ) (rs : RangeStrength) where
  H : Operator (d ^ n)
  hermitian : H.IsHermitian
  terms : Fin n → Operator (d ^ n)
  term_support : ∀ i : Fin n, SupportedOn (intervalSites n rs.range i) (terms i)
  term_norm : ∀ i : Fin n, OperatorSpectralNorm (terms i) ≤ rs.strength
  hamiltonian : H = ∑ i : Fin n, terms i

structure PeriodicChain (n d : ℕ) where
  H : Operator (d ^ n)
  hermitian : H.IsHermitian
  term : Fin n → Operator (d * d)
  term_norm : ∀ i, OperatorSpectralNorm (term i) ≤ 1

structure OpenChain (n d : ℕ) where
  H : Operator (d ^ n)
  hermitian : H.IsHermitian
  term : Fin (n - 1) → Operator (d * d)
  term_norm : ∀ i, OperatorSpectralNorm (term i) ≤ 1

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
