/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma2 — overlap lower bound for two PEPS ground-state projectors

Schwarz--Cubitt--Temme--Verstraete--Pérez-García,
*Preparing topological PEPS on a quantum computer*, fixed arXiv:1211.4050v1 (16 Nov 2012),
PRA 88, 032321 (2013). Source location: Lemma 2 (p. 3, right column) with the proof
Eqs. (4)--(7) on p. 4, left column.

Lemma 2 (paper): the overlap `d_min` between the ground-state projectors `P_t` and `P_{t+1}`
of two partial PEPS parent Hamiltonians is lower bounded by
`d_min ≥ κ(A^{t+1}|_{S_G})^{-2}`, where `κ = σ_max/σ_min` is the condition number of the
tensor `A^{t+1}` restricted to the `G`-symmetric subspace `S_G`.

Formalisation boundary. The infinite-dimensional PEPS construction and the parent Hamiltonians
are not re-built here. Following the paper, `A := A^{t+1}|_{S_G}` is taken as a positive
self-adjoint operator on the finite-dimensional complex space `V = S_G` (the paper uses that
`A` is positive-semidefinite after polar decomposition and invertible on `S_G`). The paper's
step (4)--(6) reduces the state overlap `d_min = min_ψ max_φ |⟨ψ|φ⟩|²` to the per-state ratio
`|⟨ψ|A|ψ⟩|² / ⟨ψ|A²|ψ⟩` obtained by choosing `φ = Aψ / sqrt(⟨ψ|A²|ψ⟩)` (Eq. (5)); that ratio is
`imageOverlap` below, and `dMinImage` is its infimum over unit `ψ`. The variational
characterisation of the extreme eigenvalues (Eq. (7), "by the variational characterisation of
eigenvalues") is `sigmaMin A = ⨅ Rayleigh quotient` and `σ_max = ‖A‖` (for a positive operator
the operator norm is the largest eigenvalue). Both give the paper's `κ = ‖A‖ / sigmaMin A`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TopoPEPS12.MainResults

open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [Nontrivial V]

/-- Paper Eq. (6), p. 4: the squared overlap between the old ground state `ψ` and its
normalised image `A ψ / ‖A ψ‖`, namely `|⟨ψ|A|ψ⟩|² / ⟨ψ|A²|ψ⟩`. For a self-adjoint `A` the
denominator `⟨ψ|A²|ψ⟩` equals `‖A ψ‖²`, which is the form used here. -/
def imageOverlap (A : V →L[ℂ] V) (ψ : V) : ℝ :=
  (A.reApplyInnerSelf ψ) ^ 2 / ‖A ψ‖ ^ 2

/-- Paper Lemma 2, Eq. (6): `d_min` is bounded below by the infimum over unit old states of the
per-state image overlap `imageOverlap A ψ`. -/
def dMinImage (A : V →L[ℂ] V) : ℝ :=
  ⨅ ψ : {ψ : V // ‖ψ‖ = 1}, imageOverlap A ψ

/-- The infimum defining `sigmaMin` is attained over the nonempty set of nonzero vectors. -/
theorem sigmaMin_nonempty : Nonempty {ψ : V // ψ ≠ 0} := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact ⟨⟨x, hx⟩⟩

/-- A nontrivial space has a nonempty subtype of nonzero vectors. -/
instance sigmaNonzeroNonempty : Nonempty {ψ : V // ψ ≠ 0} := sigmaMin_nonempty

/-- The unit sphere of a nontrivial normed space is nonempty. -/
theorem unitSphere_nonempty : Nonempty {ψ : V // ‖ψ‖ = 1} := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  refine ⟨⟨(‖x‖ : ℂ)⁻¹ • x, ?_⟩⟩
  rw [norm_smul]
  have hcoe : ‖((‖x‖ : ℂ)⁻¹)‖ = ‖x‖⁻¹ := by
    rw [← Complex.ofReal_inv]
    simp
  rw [hcoe, inv_mul_cancel₀ hxnorm]

/-- A nontrivial complex normed space has a nonempty unit sphere. -/
instance unitSphereNonemptyInst : Nonempty {ψ : V // ‖ψ‖ = 1} := unitSphere_nonempty

/-- Paper Eq. (7): `σ_min(A|_{S_G})` is the infimum of the Rayleigh quotient over nonzero
vectors, i.e. the smallest eigenvalue via the variational characterisation. -/
def sigmaMin (A : V →L[ℂ] V) : ℝ :=
  ⨅ ψ : {ψ : V // ψ ≠ 0}, A.rayleighQuotient ψ

/-- The Rayleigh quotients are bounded below by `-‖A‖`, so the defining infimum exists. -/
theorem bddBelow_rayleigh (A : V →L[ℂ] V) :
    BddBelow (Set.range fun ψ : {ψ : V // ψ ≠ 0} => A.rayleighQuotient ψ) := by
  refine ⟨-‖A‖, ?_⟩
  rintro _ ⟨ψ, rfl⟩
  exact neg_le_of_abs_le (A.rayleighQuotient_le_norm ψ)

/-- `sigmaMin A ≤` every Rayleigh quotient. -/
theorem sigmaMin_le_rayleigh (A : V →L[ℂ] V) (ψ : {ψ : V // ψ ≠ 0}) :
    sigmaMin A ≤ A.rayleighQuotient ψ :=
  ciInf_le (bddBelow_rayleigh A) ψ

/-- For a positive operator the defining infimum is nonnegative. -/
theorem sigmaMin_nonneg (A : V →L[ℂ] V) (hA : A.IsPositive) : 0 ≤ sigmaMin A := by
  apply le_ciInf
  intro ψ
  rw [ContinuousLinearMap.rayleighQuotient]
  exact div_nonneg (hA.2 ψ) (by positivity)

/-- Paper Eq. (7), first inequality: for every unit vector `ψ` the per-state image overlap is at
least `(σ_min/σ_max)²`, with `σ_min = sigmaMin A` and `σ_max = ‖A‖`. -/
theorem imageOverlap_ge (A : V →L[ℂ] V) (hA : A.IsPositive)
    (hinj : ∀ ψ, ψ ≠ 0 → A ψ ≠ 0) (ψ : V) (hψ : ‖ψ‖ = 1) :
    (sigmaMin A / ‖A‖) ^ 2 ≤ imageOverlap A ψ := by
  have hψne : ψ ≠ 0 := by
    intro h; rw [h, norm_zero] at hψ; norm_num at hψ
  -- variational lower bound `sigmaMin ≤ ⟪Aψ,ψ⟫`
  have hRge : sigmaMin A ≤ A.reApplyInnerSelf ψ := by
    have h := sigmaMin_le_rayleigh A ⟨ψ, hψne⟩
    rw [ContinuousLinearMap.rayleighQuotient, le_div_iff₀ (by positivity : (0 : ℝ) < ‖ψ‖ ^ 2)]
      at h
    simpa [hψ] using h
  have hRnonneg : 0 ≤ A.reApplyInnerSelf ψ := hA.2 ψ
  have ha0 : 0 ≤ sigmaMin A := sigmaMin_nonneg A hA
  -- operator-norm upper bound `‖A ψ‖ ≤ ‖A‖`
  have hden : ‖A ψ‖ ≤ ‖A‖ := by
    have := ContinuousLinearMap.le_opNorm A ψ
    simpa [hψ] using this
  have hdenpos : 0 < ‖A ψ‖ := norm_pos_iff.mpr (hinj ψ hψne)
  -- square both sides
  have hnum : (sigmaMin A) ^ 2 ≤ (A.reApplyInnerSelf ψ) ^ 2 :=
    pow_le_pow_left₀ ha0 hRge 2
  have hden2 : ‖A ψ‖ ^ 2 ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ hdenpos.le hden 2
  have hApos : (0 : ℝ) < ‖A‖ :=
    lt_of_le_of_ne (norm_nonneg A) (Ne.symm (norm_ne_zero_iff.mpr (by
      rintro rfl
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      exact hinj x hx (by simp))))
  have key : (sigmaMin A) ^ 2 / ‖A‖ ^ 2 ≤ (A.reApplyInnerSelf ψ) ^ 2 / ‖A ψ‖ ^ 2 := by
    gcongr
  calc (sigmaMin A / ‖A‖) ^ 2 = (sigmaMin A) ^ 2 / ‖A‖ ^ 2 := by rw [div_pow]
    _ ≤ (A.reApplyInnerSelf ψ) ^ 2 / ‖A ψ‖ ^ 2 := key

/-- The condition number `κ(A|_{S_G}) = σ_max/σ_min` of the paper (p. 3, Lemma 2). -/
def spectralConditionNumber (A : V →L[ℂ] V) : ℝ := ‖A‖ / sigmaMin A

/-- **Paper Lemma 2** (p. 3, right column; proof Eqs. (4)--(7), p. 4). For a positive
self-adjoint operator `A` on the symmetric subspace which is invertible there, the minimal
overlap between the old and new ground-state projectors is at least `κ^{-2}`, where
`κ = σ_max(A|_{S_G}) / σ_min(A|_{S_G})`.

This is the paper's stated `κ^{-2}` bound. The displayed chain (7) actually yields the stronger
`κ^{-1}` (the paper writes `σ_min(√A)²/σ_max(√A)² = σ_min(A)/σ_max(A)`); `κ^{-2}` follows since
`κ ≥ 1`. We prove the displayed `κ^{-2}` bound directly. -/
theorem lemma2_overlap_lower_bound (A : V →L[ℂ] V) (hA : A.IsPositive)
    (hinj : ∀ ψ, ψ ≠ 0 → A ψ ≠ 0) :
    (spectralConditionNumber A)⁻¹ ^ 2 ≤ dMinImage A := by
  apply le_ciInf
  intro ψ
  have hstate := imageOverlap_ge A hA hinj (ψ : V) ψ.2
  -- rewrite `(κ)⁻¹ = σ_min/σ_max`
  have hκ : (spectralConditionNumber A)⁻¹ = sigmaMin A / ‖A‖ := by
    rw [spectralConditionNumber, inv_div]
  rw [hκ]
  exact hstate

end Qatlib.Papers.TopoPEPS12.MainResults
