/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.NullAlgebra
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Clebsch helicity, phase charges and vortex sums

[Kedia2018SuperfluidHelicity], Sections II–V,
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
Cartesian second-order jets encode commuting mixed partials of smooth scalar
potentials. The resulting curl and divergence identities explain the exact-form
mechanism behind single-valued Clebsch helicity. They are local identities: the
divergence theorem, decay or boundary conditions, singular vortex cores and the
Gross–Pitaevskii evolution are additional analytic requirements. The finite vortex
sum below takes linking and writhe as real input data; it does not construct Gauss
integrals or prove a continuum limit. Phase-charge cancellation uses the explicit
Madelung relation with nonzero mass and does not assert classical helicity conservation.
The Cartesian operations are from
`Qatlib.Papers.KnottedLight08.HopfField.dot3` and
`Qatlib.Papers.KnottedLight08.HopfField.cross3`.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.VanishCharge

open Qatlib.Papers.KnottedLight08.HopfField
open scoped BigOperators

/-- Symmetry of the Hessian is the commuting-mixed-partials hypothesis. -/
def SymmetricJet (H : Fin 3 → Fin 3 → ℝ) : Prop := ∀ i j, H i j = H j i

/-- Curl of a Cartesian Jacobian whose first index is the differentiation direction. -/
def curlJet (J : Fin 3 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![J 1 2 - J 2 1, J 2 0 - J 0 2, J 0 1 - J 1 0]

/-- The velocity associated with scalar Clebsch potentials is dφ + α dβ. -/
def clebschVelocity (alpha : ℝ) (dphi dbeta : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun j => dphi j + alpha * dbeta j

/-- The product rule gives this Jacobian for a Clebsch velocity. -/
def clebschJacobian (alpha : ℝ) (dalpha dbeta : Fin 3 → ℝ)
    (hphi hbeta : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => hphi i j + dalpha i * dbeta j + alpha * hbeta i j

/-- Commuting mixed partials imply curl(dφ + α dβ) = dα × dβ. -/
theorem clebsch_curl (alpha : ℝ) (dalpha dbeta : Fin 3 → ℝ)
    (hphi hbeta : Fin 3 → Fin 3 → ℝ)
    (hp : SymmetricJet hphi) (hb : SymmetricJet hbeta) :
    curlJet (clebschJacobian alpha dalpha dbeta hphi hbeta) =
      cross3 dalpha dbeta := by
  funext j
  fin_cases j <;> simp [curlJet, clebschJacobian, cross3,
    hp 1 0, hp 2 0, hp 2 1, hb 1 0, hb 2 0, hb 2 1]

/-- The helicity density of a Clebsch velocity is the scalar triple product of its potentials. -/
theorem clebsch_helicity (alpha : ℝ) (dphi dalpha dbeta : Fin 3 → ℝ) :
    dot3 (clebschVelocity alpha dphi dbeta) (cross3 dalpha dbeta) =
      dot3 dphi (cross3 dalpha dbeta) := by
  simp [dot3, clebschVelocity, cross3]
  ring

/-- A Clebsch velocity without the exact potential term has zero helicity density. -/
theorem simple_clebsch_helicity_zero (alpha : ℝ) (dalpha dbeta : Fin 3 → ℝ) :
    dot3 (clebschVelocity alpha 0 dbeta) (cross3 dalpha dbeta) = 0 := by
  rw [clebsch_helicity]
  simp [dot3]

/-- The product rule for the vorticity dα × dβ, represented by second-order jets. -/
def vorticityJacobian (dalpha dbeta : Fin 3 → ℝ)
    (halpha hbeta : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => cross3 (halpha i) dbeta j + cross3 dalpha (hbeta i) j

/-- Cartesian divergence is the trace of the derivative matrix. -/
def divergenceJet (J : Fin 3 → Fin 3 → ℝ) : ℝ := J 0 0 + J 1 1 + J 2 2

/-- The cross product of two gradients is divergence free when their Hessians are symmetric. -/
theorem vorticity_divergence_zero (dalpha dbeta : Fin 3 → ℝ)
    (halpha hbeta : Fin 3 → Fin 3 → ℝ)
    (ha : SymmetricJet halpha) (hb : SymmetricJet hbeta) :
    divergenceJet (vorticityJacobian dalpha dbeta halpha hbeta) = 0 := by
  simp [divergenceJet, vorticityJacobian, cross3,
    ha 1 0, ha 2 0, ha 2 1, hb 1 0, hb 2 0, hb 2 1]
  ring

/-- The boundary flux φ(dα × dβ) has this product-rule derivative. -/
def helicityFluxJacobian (phi : ℝ) (dphi dalpha dbeta : Fin 3 → ℝ)
    (halpha hbeta : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => dphi i * cross3 dalpha dbeta j +
    phi * vorticityJacobian dalpha dbeta halpha hbeta i j

/-- Local exact-form identity: Clebsch helicity equals divergence of the boundary flux. -/
theorem helicity_is_divergence (phi alpha : ℝ) (dphi dalpha dbeta : Fin 3 → ℝ)
    (halpha hbeta : Fin 3 → Fin 3 → ℝ)
    (ha : SymmetricJet halpha) (hb : SymmetricJet hbeta) :
    dot3 (clebschVelocity alpha dphi dbeta) (cross3 dalpha dbeta) =
      divergenceJet (helicityFluxJacobian phi dphi dalpha dbeta halpha hbeta) := by
  rw [clebsch_helicity]
  have hz := vorticity_divergence_zero dalpha dbeta halpha hbeta ha hb
  simp only [divergenceJet] at hz
  simp only [divergenceJet, helicityFluxJacobian, dot3]
  linear_combination -phi * hz

/-- The Euler contribution to the relabeling charge density. -/
def eulerCharge (u tangent : Fin 3 → ℝ) : ℝ := dot3 u tangent

/-- The phase contribution uses the same relabeling tangent and opposite normalization. -/
noncomputable def phaseCharge (mass : ℝ) (dphase tangent : Fin 3 → ℝ) : ℝ :=
  -(dot3 dphase tangent / mass)

/-- The Madelung velocity makes the Euler and phase relabeling charges cancel exactly. -/
theorem madelung_charge_cancels (mass : ℝ) (hm : mass ≠ 0)
    (dphase tangent : Fin 3 → ℝ) :
    eulerCharge (fun j => dphase j / mass) tangent +
      phaseCharge mass dphase tangent = 0 := by
  simp only [eulerCharge, phaseCharge, dot3]
  field_simp [hm]
  ring

/-- The pair contribution to centerline helicity, with the diagonal explicitly removed. -/
noncomputable def linkingPart {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kappa : ι → ℝ) (link : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else kappa i * kappa j * link i j

/-- The self contribution weights each writhe by squared circulation. -/
noncomputable def writhePart {ι : Type*} [Fintype ι] (kappa writhe : ι → ℝ) : ℝ :=
  ∑ i, kappa i ^ 2 * writhe i

/-- Centerline helicity separates distinct-line linking from self writhe. -/
noncomputable def centerlineHelicity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kappa : ι → ℝ) (link : ι → ι → ℝ) (writhe : ι → ℝ) : ℝ :=
  linkingPart kappa link + writhePart kappa writhe

/-- Rescaling all circulations scales centerline helicity quadratically. -/
theorem centerline_scaling {ι : Type*} [Fintype ι] [DecidableEq ι]
    (scale : ℝ) (kappa : ι → ℝ) (link : ι → ι → ℝ) (writhe : ι → ℝ) :
    centerlineHelicity (fun i => scale * kappa i) link writhe =
      scale ^ 2 * centerlineHelicity kappa link writhe := by
  simp only [centerlineHelicity, linkingPart, writhePart, mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Adding twist restores the framed self contribution, without assuming a topology theorem. -/
theorem framed_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kappa : ι → ℝ) (link : ι → ι → ℝ) (writhe twist : ι → ℝ) :
    centerlineHelicity kappa link (fun i => writhe i + twist i) =
      centerlineHelicity kappa link writhe + writhePart kappa twist := by
  simp [centerlineHelicity, writhePart, mul_add, Finset.sum_add_distrib, add_assoc]

/-- For equal circulations and common writhe, the normalized self term is exactly writhe/N. -/
theorem uniform_writhe_suppression (n : ℕ) (hn : n ≠ 0) (kappa writhe : ℝ)
    (hk : kappa ≠ 0) :
    writhePart (fun _ : Fin n => kappa) (fun _ => writhe) /
      ((n : ℝ) * kappa) ^ 2 = writhe / (n : ℝ) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [writhePart, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [hnR, hk]

end Qatlib.Papers.SuperfluidHel18.VanishCharge
