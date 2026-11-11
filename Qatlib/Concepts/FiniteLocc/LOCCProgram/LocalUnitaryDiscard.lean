/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.LocalCapability

/-!
# Local unitaries and partial trace

This module proves that unitary conjugation on the second subsystem leaves the first reduced
operator unchanged. It develops the finite matrix contractions needed for this identity and then
transfers the result to outer products of pure states, as in the reduced-state formalism of
[NielsenChuang2010].

## Main statements

* `sum_contract_conj`: contract a coefficient array using unitary column orthogonality.
* `partialTrace_conj_tensorRight`: discard a unitary conjugation on the second subsystem.
* `partialTrace_outerProduct_apply_tensorRight`: obtain the corresponding pure-state marginal
  identity.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.FiniteLocc.LOCCProgram

open Matrix
open scoped Matrix.Norms.L2Operator

variable {D E : ℕ}

/-- An off-diagonal entry of the identity matrix is zero. -/
private theorem one_apply_zero {i p : Fin D} (h : p ≠ i) : (1 : Matrix (Fin D) (Fin D) ℂ) i p = 0 := by
  rw [Matrix.one_apply, if_neg (Ne.symm h)]

/-- Every diagonal entry of the identity matrix is one. -/
private theorem one_apply_one (i : Fin D) : (1 : Matrix (Fin D) (Fin D) ℂ) i i = 1 := by
  rw [Matrix.one_apply, if_pos rfl]

/-- A unitary matrix multiplied on the left by its conjugate transpose gives the identity. -/
private theorem conjTranspose_mul_eq (V : Matrix (Fin E) (Fin E) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ) : Vᴴ * V = 1 := by
  have hstar : star V * V = 1 := (Matrix.mem_unitaryGroup_iff').mp hV
  rwa [Matrix.star_eq_conjTranspose] at hstar

/-- Summing a column of a unitary matrix against the conjugate of another column gives the
corresponding Kronecker delta. -/
theorem sum_mul_conj_mul_eq (V : Matrix (Fin E) (Fin E) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ) (d e : Fin E) :
    (∑ a : Fin E, (V a d) * (starRingEnd ℂ) (V a e)) = if e = d then 1 else 0 := by
  have hentry : (Vᴴ * V) e d = ∑ a : Fin E, (starRingEnd ℂ (V a e)) * V a d := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
  calc (∑ a : Fin E, (V a d) * (starRingEnd ℂ) (V a e))
      = ∑ a : Fin E, (starRingEnd ℂ (V a e)) * V a d :=
        Finset.sum_congr rfl fun a _ => mul_comm _ _
    _ = (Vᴴ * V) e d := hentry.symm
    _ = (1 : Matrix (Fin E) (Fin E) ℂ) e d := by rw [conjTranspose_mul_eq V hV]
    _ = if e = d then 1 else 0 := Matrix.one_apply (i := e) (j := d)

/-- Contracting a two-index coefficient array against a unitary matrix and its conjugate reduces
to the sum of diagonal coefficients. -/
theorem sum_contract_conj (V : Matrix (Fin E) (Fin E) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ) (c : Fin E → Fin E → ℂ) :
    ((∑ a : Fin E, (∑ q : Fin E, (∑ l : Fin E, (c q l) * (V a q) * (starRingEnd ℂ (V a l)))))) = ∑ q : Fin E, c q q := by
  classical

  have hswap1 : ((∑ a : Fin E, (∑ q : Fin E, (∑ l : Fin E, (c q l) * (V a q) * (starRingEnd ℂ (V a l)))))) = ((∑ q : Fin E, (∑ a : Fin E, (∑ l : Fin E, (c q l) * (V a q) * (starRingEnd ℂ (V a l)))))) := by
    exact Finset.sum_comm
  have hswap2 : ((∑ q : Fin E, (∑ a : Fin E, (∑ l : Fin E, (c q l) * (V a q) * (starRingEnd ℂ (V a l)))))) = ((∑ q : Fin E, (∑ l : Fin E, (∑ a : Fin E, (c q l) * (V a q) * (starRingEnd ℂ (V a l)))))) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    exact Finset.sum_comm
  have hpull : ((∑ q : Fin E, (∑ l : Fin E, (∑ a : Fin E, (c q l) * (V a q) * (starRingEnd ℂ (V a l)))))) = ((∑ q : Fin E, (∑ l : Fin E, (c q l) * (∑ a : Fin E, (V a q) * (starRingEnd ℂ (V a l)))))) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  have horth : ((∑ q : Fin E, (∑ l : Fin E, (c q l) * (∑ a : Fin E, (V a q) * (starRingEnd ℂ (V a l)))))) = ((∑ q : Fin E, (∑ l : Fin E, (c q l) * (if l = q then 1 else 0)))) := by
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_mul_conj_mul_eq V hV]
  have hdiag : ((∑ q : Fin E, (∑ l : Fin E, (c q l) * (if l = q then 1 else 0)))) = ∑ q : Fin E, c q q := by
    refine Finset.sum_congr rfl fun q _ => ?_
    calc (∑ l : Fin E, (c q l) * (if l = q then 1 else 0))
        = (c q q) * (if q = q then 1 else 0) :=
          Fintype.sum_eq_single q fun l hl => by rw [if_neg hl, mul_zero]
      _ = c q q := by simp
  exact ((hswap1.trans hswap2).trans hpull).trans (horth.trans hdiag)

/-- A diagonal reference block entry after second-subsystem conjugation expands as the displayed
double sum over the second input indices. -/
theorem conj_tensorRight_apply (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (V : Matrix (Fin E) (Fin E) ℂ) (i j : Fin D) (a : Fin E) :
    (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V * ρ * (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V)ᴴ) (i, a) (j, a) = (∑ q : Fin E, (∑ l : Fin E, (V a q) * ρ (i, q) (j, l) * (starRingEnd ℂ (V a l)))) := by
  classical

  have hrow : ∀ k : Fin D × Fin E, (∑ p : Fin D, (∑ q : Fin E, ((1 : Matrix (Fin D) (Fin D) ℂ) i p * V a q) * ρ (p, q) k)) = (∑ q : Fin E, (V a q) * ρ (i, q) k) := by
    intro k
    have hfac : ∀ p : Fin D, (∑ q : Fin E, ((1 : Matrix (Fin D) (Fin D) ℂ) i p * V a q) * ρ (p, q) k) = (1 : Matrix (Fin D) (Fin D) ℂ) i p * (∑ q : Fin E, (V a q) * ρ (p, q) k) := by
      intro p
      nth_rewrite 1 [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [Finset.sum_congr rfl fun p _ => hfac p,
      Fintype.sum_eq_single i fun p hp => by rw [one_apply_zero hp, zero_mul], one_apply_one, one_mul]

  have hone : ∀ (l : Fin E) (k : Fin D), (1 : Matrix (Fin D) (Fin D) ℂ) j k * V a l = if j = k then V a l else 0 := by
    intro l k
    by_cases h : j = k <;> simp [Matrix.one_apply, h]
  have hcol : ∀ l : Fin E, (∑ k : Fin D, (∑ q : Fin E, (V a q) * ρ (i, q) (k, l)) * (starRingEnd ℂ ((1 : Matrix (Fin D) (Fin D) ℂ) j k * V a l))) = (∑ q : Fin E, (V a q) * ρ (i, q) (j, l)) * (starRingEnd ℂ (V a l)) := by
    intro l
    have hz : ∀ k : Fin D, k ≠ j → (∑ q : Fin E, (V a q) * ρ (i, q) (k, l)) * (starRingEnd ℂ ((1 : Matrix (Fin D) (Fin D) ℂ) j k * V a l)) = 0 := by
      intro k hk
      rw [hone l k, if_neg (Ne.symm hk), map_zero, mul_zero]
    refine (Fintype.sum_eq_single j hz).trans ?_
    rw [hone l j, if_pos rfl]

  have hexpand : (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V * ρ * (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V)ᴴ) (i, a) (j, a) = (∑ k : Fin D, (∑ l : Fin E, (∑ p : Fin D, (∑ q : Fin E, ((1 : Matrix (Fin D) (Fin D) ℂ) i p * V a q) * ρ (p, q) (k, l))) * (starRingEnd ℂ ((1 : Matrix (Fin D) (Fin D) ℂ) j k * V a l)))) := by
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, tensorGate_apply,
      Matrix.conjTranspose_apply, RCLike.star_def]

  have hrowsum : (∑ k : Fin D, (∑ l : Fin E, (∑ p : Fin D, (∑ q : Fin E, ((1 : Matrix (Fin D) (Fin D) ℂ) i p * V a q) * ρ (p, q) (k, l))) * (starRingEnd ℂ ((1 : Matrix (Fin D) (Fin D) ℂ) j k * V a l)))) = (∑ l : Fin E, (∑ q : Fin E, (V a q) * ρ (i, q) (j, l)) * (starRingEnd ℂ (V a l))) := by
    nth_rewrite 1 [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact (Finset.sum_congr rfl fun k _ =>
      congrArg (fun z : ℂ => z * (starRingEnd ℂ ((1 : Matrix (Fin D) (Fin D) ℂ) j k * V a l))) (hrow (k, l))).trans (hcol l)

  have hfactor : (∑ l : Fin E, (∑ q : Fin E, (V a q) * ρ (i, q) (j, l)) * (starRingEnd ℂ (V a l))) = (∑ l : Fin E, (∑ q : Fin E, (V a q) * ρ (i, q) (j, l) * (starRingEnd ℂ (V a l)))) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    nth_rewrite 1 [Finset.sum_mul]
    rfl
  have hswap : (∑ l : Fin E, (∑ q : Fin E, (V a q) * ρ (i, q) (j, l) * (starRingEnd ℂ (V a l)))) = (∑ q : Fin E, (∑ l : Fin E, (V a q) * ρ (i, q) (j, l) * (starRingEnd ℂ (V a l)))) := by
    nth_rewrite 1 [Finset.sum_comm]
    rfl
  exact ((hexpand.trans hrowsum).trans hfactor).trans hswap

/-- Conjugation by a unitary on the second subsystem leaves the first reduced operator
unchanged. -/
theorem partialTrace_conj_tensorRight (ρ : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ)
    (V : Matrix (Fin E) (Fin E) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ) :
    PartialTrace (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V * ρ * (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V)ᴴ) = PartialTrace ρ := by
  classical
  ext i j
  simp only [PartialTrace]

  have hentry : (∑ a : Fin E, (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V * ρ * (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V)ᴴ) (i, a) (j, a)) = (∑ a : Fin E, (∑ q : Fin E, (∑ l : Fin E, (ρ (i, q) (j, l)) * (V a q) * (starRingEnd ℂ (V a l))))) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [conj_tensorRight_apply ρ V i j a]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun l _ => by ring
  have hcontract : (∑ a : Fin E, (∑ q : Fin E, (∑ l : Fin E, (ρ (i, q) (j, l)) * (V a q) * (starRingEnd ℂ (V a l))))) = ∑ l : Fin E, ρ (i, l) (j, l) := by
    exact sum_contract_conj V hV fun q l => ρ (i, q) (j, l)
  exact hentry.trans hcontract

/-- Each entry of the outer product of a gate-transformed vector equals the corresponding entry
of the conjugated input outer product. -/
theorem outerProduct_applyGate_mul_conjTranspose
    (U : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) (ψ : QState (Fin D × Fin E))
    (i j : Fin D × Fin E) :
    outerProduct (ApplyGate U ψ) i j = (U * (outerProduct ψ) * Uᴴ) i j := by
  classical
  have hstep : ∀ p : Fin D × Fin E, (∑ k, U i k * ψ k) * (((starRingEnd ℂ) (U j p)) * ((starRingEnd ℂ) (ψ p))) = (∑ k, U i k * (ψ k * ((starRingEnd ℂ) (ψ p)))) * ((starRingEnd ℂ) (U j p)) := by
    intro p
    have h1 : (∑ k, U i k * ψ k) * (((starRingEnd ℂ) (U j p)) * ((starRingEnd ℂ) (ψ p))) = ∑ k, (U i k * ψ k) * (((starRingEnd ℂ) (U j p)) * ((starRingEnd ℂ) (ψ p))) := by
      exact Finset.sum_mul (Finset.univ : Finset (Fin D × Fin E)) (fun k => U i k * ψ k)
        ((starRingEnd ℂ (U j p)) * (starRingEnd ℂ (ψ p)))
    have h2 : ∑ k, (U i k * ψ k) * (((starRingEnd ℂ) (U j p)) * ((starRingEnd ℂ) (ψ p))) = ∑ k, (U i k * (ψ k * ((starRingEnd ℂ) (ψ p)))) * ((starRingEnd ℂ) (U j p)) := by
      exact Finset.sum_congr rfl fun k _ => by ring
    have h3 : ∑ k, (U i k * (ψ k * ((starRingEnd ℂ) (ψ p)))) * ((starRingEnd ℂ) (U j p)) = (∑ k, U i k * (ψ k * ((starRingEnd ℂ) (ψ p)))) * ((starRingEnd ℂ) (U j p)) := by
      exact (Finset.sum_mul (Finset.univ : Finset (Fin D × Fin E))
        (fun k => U i k * (ψ k * (starRingEnd ℂ (ψ p)))) (starRingEnd ℂ (U j p))).symm
    exact h1.trans (h2.trans h3)
  simp only [outerProduct_apply, ApplyGate, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum, map_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => hstep p

/-- Applying a unitary to the second factor of a bipartite pure state leaves its first reduced
operator unchanged. -/
theorem partialTrace_outerProduct_apply_tensorRight (ψ : QState (Fin D × Fin E))
    (V : Matrix (Fin E) (Fin E) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin E) ℂ) :
    PartialTrace (outerProduct (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ)) = PartialTrace (outerProduct ψ) := by
  have hmat : outerProduct (ApplyGate (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ) = TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V * (outerProduct ψ) * (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V)ᴴ :=
    funext fun p => funext fun q =>
      outerProduct_applyGate_mul_conjTranspose (TensorGate (1 : Matrix (Fin D) (Fin D) ℂ) V) ψ p q
  rw [hmat, ← partialTrace_conj_tensorRight (outerProduct ψ) V hV]

end Qatlib.Concepts.FiniteLocc.LOCCProgram
