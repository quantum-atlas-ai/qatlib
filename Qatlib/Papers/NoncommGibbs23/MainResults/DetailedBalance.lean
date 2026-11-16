/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommGibbs23.MainResults.Model

@[expose] public section


/-!
# NoncommGibbs23, Section II: detailed balance and fixed points

Paper: arXiv:2311.09207v2 (14 Oct 2025), Chen–Kastoryano–Gilyén,
*An efficient and exact noncommutative quantum Gibbs sampler*.

This module contains:

* Proposition II.1, p. 8: ρ-detailed balance plus trace preservation implies
  `L[ρ] = 0` (proved).
* Proposition II.2, p. 10: coefficient skew-symmetry implies energy-domain
  detailed balance for the transition part (proved).
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Qatlib.Papers.NoncommGibbs23.MainResults

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

variable {D : ℕ}

/-! ## Proposition II.1: fixed point from ρ-detailed balance -/

/-- Cancellation of an explicit square-root pair around a conjugated matrix. -/
theorem mul_conj_cancel {r rInv X : Operator D} (hrr : r * rInv = 1)
    (hrr' : rInv * r = 1) : r * (rInv * X * rInv) * r = X := by
  calc r * (rInv * X * rInv) * r
      = (r * rInv) * X * (rInv * r) := by noncomm_ring
    _ = 1 * X * 1 := by rw [hrr, hrr']
    _ = X := by rw [Matrix.one_mul, Matrix.mul_one]

/-- **Proposition II.1** (p. 8). If a super-operator `L` is ρ-detailed balanced
(`L† = Γ_ρ^{-1} ∘ L ∘ Γ_ρ`) and trace preserving (`L†[I] = 0`), then the Gibbs state
is a fixed point: `L[ρ] = 0`.

Proof: evaluate detailed balance at `X = I`.  Since `Γ_ρ[I] = ρ`, this gives
`L†[I] = ρ^{-1/2} L[ρ] ρ^{-1/2}`, hence `ρ^{-1/2}L[ρ]ρ^{-1/2}=0`.  Conjugating by
`ρ^{1/2}` on both sides recovers `L[ρ]=0`. -/
theorem propositionII1_fixedPoint {ρ r rInv : Operator D} {T Tdag : SuperOp D}
    (hdb : IsRhoDetailedBalanced ρ r rInv T Tdag) (hT : Tdag 1 = 0) : T ρ = 0 := by
  obtain ⟨hrr, hrr', hsq, hform⟩ := hdb
  have h1 : rInv * T ρ * rInv = 0 := by
    have h := hform 1
    rw [hT] at h
    simpa [gammaRho, Matrix.mul_one, hsq] using h.symm
  calc T ρ = r * (rInv * T ρ * rInv) * r := by rw [mul_conj_cancel hrr hrr']
    _ = 0 := by rw [h1, Matrix.mul_zero, Matrix.zero_mul]

/-! ## Proposition II.2: energy-domain detailed balance -/

variable {ι : Type*}

/-- Product of half-exponentials is the exponential of the sum. -/
theorem exp_half_add (β ν μ : ℝ) :
    ((Real.exp (β * ν / 2) : ℝ) : ℂ) * ((Real.exp (β * μ / 2) : ℝ) : ℂ)
      = ((Real.exp (β * (ν + μ) / 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  congr 1
  ring_nf

/-- The modular eigen-relation for the adjoint jump: if `rInv A r = E • A` and
`r, rInv` are Hermitian, then `r A† rInv = E • A†` for real `E`. -/
theorem r_conj_adjoint {r rInv : Operator D} (hrm : rᴴ = r) (hrinv : rInvᴴ = rInv)
    {A : ι → Operator D} {E : ι → ℂ} (hE : ∀ i, star (E i) = E i)
    (hmod : ∀ i, rInv * A i * r = E i • A i)
    (i : ι) : r * (A i)ᴴ * rInv = E i • (A i)ᴴ := by
  have h := congrArg (fun M => Mᴴ) (hmod i)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hrm, hrinv] at h
  rw [hE i] at h
  simpa only [Matrix.mul_assoc] using h

/-- **Proposition II.2** (p. 10). Suppose the jump family has real Bohr frequencies,
`A_{star i}=A_i†`, `ν_{star i}=-ν_i`, and the modular eigen-relation
`rInv A_i r = e^{βν_i/2} A_i`.  If the coefficient matrix satisfies the
skew-symmetry `α_{ij}e^{β(ν_i+ν_j)/2}=α_{star j,star i}` and the Hermiticity
`α*_{ij}=α_{ji}`, then the transition part is energy-domain ρ-detailed balanced:
`Γ_ρ^{-1} T Γ_ρ = T†` when the modular factors are instantiated as the
square root of the state and its inverse. The algebraic identity itself needs
neither the inverse equations nor a specified state. -/
theorem propositionII2_energyDomainDB [Fintype ι] {β : ℝ} {r rInv : Operator D}
    (d : BohrJumpData D ι)
    (hrm : rᴴ = r) (hrinv : rInvᴴ = rInv)
    (hmod : BohrModularEigen β r rInv d)
    (hskew : BohrSkewSymmetry β d) (hherm : BohrCoeffHermitian d) :
    ∀ X, rInv * transitionSuper d (gammaRho r X) * rInv = transitionAdjoint d X := by
  intro X
  have hskew' : ∀ i j,
      d.α i j * (((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) *
        ((Real.exp (β * d.ν j / 2) : ℝ) : ℂ)) = d.α (d.star j) (d.star i) := by
    intro i j
    rw [exp_half_add]
    exact hskew i j
  have hcoef : ∀ i j,
      rInv * (d.α i j • (d.A i * (r * X * r) * (d.A j)ᴴ)) * rInv
        = (d.α i j * (((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) *
            ((Real.exp (β * d.ν j / 2) : ℝ) : ℂ))) • (d.A i * X * (d.A j)ᴴ) := by
    intro i j
    calc rInv * (d.α i j • (d.A i * (r * X * r) * (d.A j)ᴴ)) * rInv
        = d.α i j • (rInv * (d.A i * (r * X * r) * (d.A j)ᴴ) * rInv) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = d.α i j • (((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) •
            (((Real.exp (β * d.ν j / 2) : ℝ) : ℂ) • (d.A i * X * (d.A j)ᴴ))) := by
          rw [show rInv * (d.A i * (r * X * r) * (d.A j)ᴴ) * rInv
                = (rInv * d.A i * r) * X * (r * (d.A j)ᴴ * rInv) by noncomm_ring]
          rw [hmod i, r_conj_adjoint hrm hrinv
            (fun i => by simp only [Complex.star_def, Complex.conj_ofReal]) hmod j]
          rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (d.α i j * (((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) *
            ((Real.exp (β * d.ν j / 2) : ℝ) : ℂ))) • (d.A i * X * (d.A j)ᴴ) := by
          rw [smul_smul, smul_smul]
          congr 1
          ring
  have hsum : rInv * transitionSuper d (gammaRho r X) * rInv
      = ∑ i, ∑ j, (d.α i j * (((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) *
            ((Real.exp (β * d.ν j / 2) : ℝ) : ℂ))) • (d.A i * X * (d.A j)ᴴ) := by
    rw [transitionSuper, gammaRho]
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hcoef i j))
  have hAi : ∀ i, d.A i = (d.A (d.star i))ᴴ := by
    intro i
    have h := d.A_star (d.star i)
    rwa [d.star_invol i] at h
  have hrelabel : (∑ i, ∑ j, d.α (d.star j) (d.star i) • (d.A i * X * (d.A j)ᴴ))
      = ∑ p, ∑ q, d.α q p • ((d.A p)ᴴ * X * d.A q) := by
    have hstep : (∑ i, ∑ j, d.α (d.star j) (d.star i) • (d.A i * X * (d.A j)ᴴ))
        = ∑ i, ∑ j, d.α (d.star j) (d.star i) •
            ((d.A (d.star i))ᴴ * X * d.A (d.star j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hAi i, ← d.A_star j]
    rw [hstep]
    let e : ι ≃ ι :=
      { toFun := d.star
        invFun := d.star
        left_inv := d.star_invol
        right_inv := d.star_invol }
    refine Fintype.sum_equiv e _ _
      (fun i => Fintype.sum_equiv e _ _ (fun j => rfl))
  calc rInv * transitionSuper d (gammaRho r X) * rInv
      = ∑ i, ∑ j, (d.α i j * (((Real.exp (β * d.ν i / 2) : ℝ) : ℂ) *
            ((Real.exp (β * d.ν j / 2) : ℝ) : ℂ))) • (d.A i * X * (d.A j)ᴴ) := hsum
    _ = ∑ i, ∑ j, d.α (d.star j) (d.star i) • (d.A i * X * (d.A j)ᴴ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hskew' i j]
    _ = ∑ p, ∑ q, d.α q p • ((d.A p)ᴴ * X * d.A q) := hrelabel
    _ = transitionAdjoint d X := by
        rw [transitionAdjoint]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        rw [← hherm p q]


end Qatlib.Papers.NoncommGibbs23.MainResults
