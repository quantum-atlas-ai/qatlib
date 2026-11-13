/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoncommGibbs23.MainResults.Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

set_option backward.isDefEq.respectTransparency false

/-!
# Prescribing the Coherent Term for Exact Noncommutative Gibbs Detailed Balance

This module formalizes Section II (Lemma II.1 and Corollary II.1) of Chen, Kastoryano,
and Gilyen on prescribing the Bohr-frequency coherent Hamiltonian term
`B = (i / 2) ∑_ν tanh(β ν / 4) R_ν` so that the coherent-plus-decay super-operator
`S[X] = -i [B, X] - (1 / 2) {R, X}` satisfies exact KMS `ρ`-detailed balance
`Γ_ρ⁻¹ ∘ S ∘ Γ_ρ = S†`, and combining it with any `ρ`-detailed-balanced dissipative
transition part preserves `ρ`-detailed balance.

## Main definitions

* `coherentSuper`, `coherentSuperDag`: coherent commutator `-i [B, ·]` and its adjoint `+i [B, ·]`.
* `decaySuperFrom`, `combinedSuper`, `combinedSuperDag`: anticommutator decay and combined super-operators.
* `totalR`, `coherentB`, `bohrLindbladianAdjoint`: total jump operator, Bohr coherent solution, and Lindbladian adjoint.

## Main statements

* `lemmaII1_coherentTerm`: Lemma II.1, exact `ρ`-detailed balance of the coherent-plus-decay super-operator.
* `corollaryII1_prescribe`: Corollary II.1, closure of `ρ`-detailed balance under adding a transition part.

## References

* [Chen, Kastoryano, and Gilyen, 2023][ChenKastoryanoGilyen2023], Section II, Lemma II.1 and Corollary II.1, pp. 8--9.
-/

set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators

variable {D : ℕ}

/-- The coherent term `-i[B,·]` (Definition II.1, p. 8). -/
noncomputable def coherentSuper (B : Operator D) (X : Operator D) : Operator D :=
  commutatorSuper B X

/-- The Hilbert–Schmidt adjoint of the coherent term, `+i[B,·]` when `B` is Hermitian. -/
noncomputable def coherentSuperDag (B : Operator D) (X : Operator D) : Operator D :=
  Complex.I • (B * X - X * B)

/-- The decay term `-½{R,·}`. -/
noncomputable def decaySuperFrom (Rtot : Operator D) (X : Operator D) : Operator D :=
  (-(1 / 2 : ℂ)) • (Rtot * X + X * Rtot)

/-- `S[X] = -i[B,X] - ½{R,X}`. -/
noncomputable def combinedSuper (B Rtot : Operator D) (X : Operator D) : Operator D :=
  coherentSuper B X + decaySuperFrom Rtot X

/-- `S†[X] = +i[B,X] - ½{R,X}`. -/
noncomputable def combinedSuperDag (B Rtot : Operator D) (X : Operator D) : Operator D :=
  coherentSuperDag B X + decaySuperFrom Rtot X

/-- The total jump operator `R = Σ_ν R_ν` of Lemma II.1. -/
noncomputable def totalR {ι : Type*} [Fintype ι] (R : ι → Operator D) : Operator D :=
  ∑ i, R i

/-- The Bohr-frequency coherent solution `B = (i/2) Σ_ν tanh(βν/4) R_ν`
(Lemma II.1, p. 9). -/
noncomputable def coherentB {ι : Type*} [Fintype ι] (β : ℝ) (ν : ι → ℝ)
    (R : ι → Operator D) : Operator D :=
  ∑ i, ((Complex.I / 2) * ((Real.tanh (β * ν i / 4) : ℝ) : ℂ)) • R i

/-- The Hilbert–Schmidt adjoint of `bohrLindbladian d B`: the transition adjoint,
the same decay term, and the adjoint commutator term. -/
noncomputable def bohrLindbladianAdjoint {ι : Type*} [Fintype ι]
    (d : BohrJumpData D ι) (B : Operator D) (X : Operator D) : Operator D :=
  coherentSuperDag B X + transitionAdjoint d X + decaySuper d X

private lemma coherent_coefficients (u : ℝ) :
    (Real.tanh u - 1) / 2 * Real.exp (2 * u) = -(Real.tanh u + 1) / 2 ∧
    -(Real.tanh u + 1) / 2 * Real.exp (-(2 * u)) = (Real.tanh u - 1) / 2 := by
  have he : Real.exp u ≠ 0 := Real.exp_ne_zero u
  have hd : Real.exp u + (Real.exp u)⁻¹ ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos u) (inv_pos.mpr (Real.exp_pos u)))
  simp only [Real.tanh_eq, two_mul, Real.exp_add, Real.exp_neg]
  constructor <;> field_simp [he, hd] <;> ring

private lemma combinedSuper_coherentB {ι : Type*} [Fintype ι]
    (β : ℝ) (ν : ι → ℝ) (R : ι → Operator D) (X : Operator D) :
    combinedSuper (coherentB β ν R) (totalR R) X =
      ∑ i, ((((Real.tanh (β * ν i / 4) - 1) / 2 : ℝ) : ℂ) • (R i * X) +
        ((-(Real.tanh (β * ν i / 4) + 1) / 2 : ℝ) : ℂ) • (X * R i)) := by
  simp only [combinedSuper, coherentSuper, commutatorSuper, decaySuperFrom, coherentB,
    totalR, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_sub, smul_add, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

private lemma combinedSuperDag_coherentB {ι : Type*} [Fintype ι]
    (β : ℝ) (ν : ι → ℝ) (R : ι → Operator D) (X : Operator D) :
    combinedSuperDag (coherentB β ν R) (totalR R) X =
      ∑ i, (((-(Real.tanh (β * ν i / 4) + 1) / 2 : ℝ) : ℂ) • (R i * X) +
        (((Real.tanh (β * ν i / 4) - 1) / 2 : ℝ) : ℂ) • (X * R i)) := by
  simp only [combinedSuperDag, coherentSuperDag, decaySuperFrom, coherentB,
    totalR, Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    smul_sub, smul_add, Finset.smul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

-- Lemma II.1: the coherent solution is ρ-detailed balanced

/-- **Lemma II.1** (p. 9). For a full-rank Gibbs state `ρ ∝ exp(-βH)` and a
self-adjoint jump family `R_ν` with Bohr frequencies `ν`, the coherent term
`B = (i/2) Σ_ν tanh(βν/4) R_ν` makes
`S[X] = -i[B,X] - ½{Σ_ν R_ν, X}` exactly ρ-detailed balanced:
`Γ_ρ^{-1} S Γ_ρ = S†`. -/
theorem lemmaII1_coherentTerm {ι : Type*} [Fintype ι] {β : ℝ} {ρ r rInv : Operator D}
    (R : ι → Operator D) (ν : ι → ℝ) (star : ι → ι)
    (hstar : Function.Involutive star)
    (hR : ∀ i, R (star i) = (R i)ᴴ)
    (hν : ∀ i, ν (star i) = -ν i)
    (hrr : r * rInv = 1) (hrr' : rInv * r = 1) (hρ : r * r = ρ)
    (hrm : rᴴ = r) (hrinv : rInvᴴ = rInv)
    (hmod : ∀ i, rInv * R i * r =
      ((Real.exp (β * ν i / 2) : ℝ) : ℂ) • R i) :
    ∀ X : Operator D,
      rInv * combinedSuper (coherentB β ν R) (totalR R) (gammaRho r X) * rInv
        = combinedSuperDag (coherentB β ν R) (totalR R) X := by
  have hmodInv (i : ι) : r * R i * rInv =
      ((Real.exp (-(β * ν i / 2)) : ℝ) : ℂ) • R i := by
    have hi : R i = ((Real.exp (β * ν i / 2) : ℝ) : ℂ) • (r * R i * rInv) := by
      calc
        R i = r * (rInv * R i * r) * rInv := by
          calc
            R i = (r * rInv) * R i * (r * rInv) := by rw [hrr, one_mul, mul_one]
            _ = _ := by simp only [mul_assoc]
        _ = _ := by rw [hmod i, Matrix.mul_smul, Matrix.smul_mul]
    have he : ((Real.exp (-(β * ν i / 2)) : ℝ) : ℂ) *
        ((Real.exp (β * ν i / 2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]
      rfl
    calc
      r * R i * rInv = (1 : ℂ) • (r * R i * rInv) := (one_smul _ _).symm
      _ = _ := by
        simpa only [smul_smul, he, one_smul] using
          (congrArg (((Real.exp (-(β * ν i / 2)) : ℝ) : ℂ) • ·) hi).symm
  have hB_herm : (coherentB β ν R)ᴴ = coherentB β ν R := by
    unfold coherentB
    rw [Matrix.conjTranspose_sum]
    calc
      _ = ∑ i, ((Complex.I / 2) * ((Real.tanh (β * ν (star i) / 4) : ℝ) : ℂ)) •
          R (star i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Matrix.conjTranspose_smul, ← hR i, hν i]
        rw [mul_neg, neg_div, Real.tanh_neg, Complex.ofReal_neg]
        simp only [star_mul, star_div₀, star_ofNat, Complex.star_def, Complex.conj_I,
          Complex.conj_ofReal, neg_div, mul_neg]
        congr 1
        ring
      _ = _ := Equiv.sum_comp (hstar.toPerm star)
        (fun i => ((Complex.I / 2) * ((Real.tanh (β * ν i / 4) : ℝ) : ℂ)) • R i)
  have hρ_herm : ρᴴ = ρ := by
    rw [← hρ, Matrix.conjTranspose_mul, hrm]
  have hrinv_id : rInvᴴ = rInv := hrinv
  intro X
  calc
    rInv * combinedSuper (coherentB β ν R) (totalR R) (gammaRho r X) * rInv =
        rInvᴴ * combinedSuper (coherentB β ν R) (totalR R) (gammaRho r X) * rInvᴴ +
          (ρᴴ - ρ) := by rw [hrinv_id, hρ_herm, sub_self, add_zero]
    _ = combinedSuperDag (coherentB β ν R) (totalR R) X + (ρᴴ - ρ) := by
      rw [hrinv_id, combinedSuper_coherentB, combinedSuperDag_coherentB]
      congr 1
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      have hleft : rInv * (R i * gammaRho r X) * rInv =
          ((Real.exp (β * ν i / 2) : ℝ) : ℂ) • (R i * X) := by
        calc
          _ = (rInv * R i * r) * X * (r * rInv) := by
            simp only [gammaRho, mul_assoc]
          _ = _ := by rw [hmod i, hrr, mul_one, Matrix.smul_mul]
      have hright : rInv * (gammaRho r X * R i) * rInv =
          ((Real.exp (-(β * ν i / 2)) : ℝ) : ℂ) • (X * R i) := by
        calc
          _ = (rInv * r) * X * (r * R i * rInv) := by
            simp only [gammaRho, mul_assoc]
          _ = _ := by rw [hrr', one_mul, hmodInv i, Matrix.mul_smul]
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.smul_mul, hleft, hright, smul_smul, smul_smul]
      have hc := coherent_coefficients (β * ν i / 4)
      have hu : 2 * (β * ν i / 4) = β * ν i / 2 := by ring
      rw [hu] at hc
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hc.1, hc.2]
    _ = combinedSuperDag (coherentB β ν R)ᴴ (totalR R) X := by
      rw [hB_herm, hρ_herm, sub_self, add_zero]
    _ = combinedSuperDag (coherentB β ν R) (totalR R) X := by rw [hB_herm]

-- Corollary II.1: adding a ρ-detailed-balanced transition part

/-- **Corollary II.1** (p. 9). If a purely dissipative transition part `T` and the
coherent-plus-decay part `S` are both ρ-detailed balanced (with their Hilbert–Schmidt
adjoints), then so is their sum `S + T`. -/
theorem corollaryII1_prescribe {ρ r rInv : Operator D}
    {T Tdag S Sdag : SuperOp D}
    (hT : IsRhoDetailedBalanced ρ r rInv T Tdag)
    (hS : IsRhoDetailedBalanced ρ r rInv S Sdag) :
    IsRhoDetailedBalanced ρ r rInv (fun X => S X + T X) (fun X => Sdag X + Tdag X) := by
  obtain ⟨hrr, hrr', hsq, hTform⟩ := hT
  obtain ⟨_, _, _, hSform⟩ := hS
  refine ⟨hrr, hrr', hsq, ?_⟩
  intro X
  show Sdag X + Tdag X = rInv * (S (gammaRho r X) + T (gammaRho r X)) * rInv
  rw [hSform X, hTform X, Matrix.mul_add, Matrix.add_mul]

end Qatlib.Papers.NoncommGibbs23.MainResults
