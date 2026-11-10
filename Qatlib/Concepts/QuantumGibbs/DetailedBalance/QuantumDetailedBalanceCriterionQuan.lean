/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceCriterionStat
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceFixedPointQuan
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection


namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
set_option maxRecDepth 4096

private theorem ketbra_mul {D : ℕ} (u v a b : QState (Fin D)) :
    ketbra u v * ketbra a b = Qatlib.Foundations.PureStateMath.Inner v a • ketbra u b := by
  ext i j
  simp only [Matrix.mul_apply, ketbra, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem ketbra_star {D : ℕ} (u v : QState (Fin D)) : (ketbra u v)ᴴ = ketbra v u := by
  ext i j
  simp [ketbra, Matrix.conjTranspose_apply, mul_comm]

private theorem trace_ketbra {D : ℕ} (u v : QState (Fin D)) : Matrix.trace (ketbra u v) = Qatlib.Foundations.PureStateMath.Inner v u := by
  simp only [Matrix.trace, Matrix.diag_apply, ketbra, Matrix.of_apply,
      Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem ketbra_action {D : ℕ} (u v x : QState (Fin D)) : ketbra u v *ᵥ x = Qatlib.Foundations.PureStateMath.Inner v x • u := by
  ext i
  simp only [ketbra, Matrix.of_apply, Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Inner, Pi.star_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem realMatrixSmul {D : ℕ} (r : ℝ) (A : Operator D) : r • A = (r : ℂ) • A := by
  ext i j
  simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  rfl

private noncomputable def basisDiag {D : ℕ} (psi : Fin D → QState (Fin D)) (a : Fin D → ℝ) : Operator D :=
  ∑ i, (a i : ℂ) • ketbra (psi i) (psi i)

private theorem basisDiag_mul {D : ℕ} (psi : Fin D → QState (Fin D))
    (horth : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (psi i) (psi j) = if i = j then 1 else 0)
    (a b : Fin D → ℝ) : basisDiag psi a * basisDiag psi b = basisDiag psi (fun i => a i * b i) := by
  simp only [basisDiag, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    ketbra_mul, smul_smul, horth]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite, ite_smul, Complex.ofReal_mul, smul_smul, mul_comm]
  ext k l
  simp only [Matrix.smul_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  change Complex.ofReal (a i * b i) * ketbra (psi i) (psi i) k l =
    (Complex.ofReal (a i) * Complex.ofReal (b i)) * ketbra (psi i) (psi i) k l
  rw [Complex.ofReal_mul]

private theorem basisDiag_left {D : ℕ} (psi : Fin D → QState (Fin D))
    (horth : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (psi i) (psi j) = if i = j then 1 else 0)
    (a : Fin D → ℝ) (n m : Fin D) :
    basisDiag psi a * ketbra (psi n) (psi m) = (a n : ℂ) • ketbra (psi n) (psi m) := by
  simp only [basisDiag, Matrix.sum_mul, Matrix.smul_mul, ketbra_mul, horth, smul_smul]
  simp [mul_ite, ite_smul]

private theorem basisDiag_right {D : ℕ} (psi : Fin D → QState (Fin D))
    (horth : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (psi i) (psi j) = if i = j then 1 else 0)
    (a : Fin D → ℝ) (n m : Fin D) :
    ketbra (psi n) (psi m) * basisDiag psi a = (a m : ℂ) • ketbra (psi n) (psi m) := by
  simp only [basisDiag, Matrix.mul_sum, Matrix.mul_smul, ketbra_mul, horth, smul_smul]
  simp [mul_ite, ite_smul]

private theorem basisDiag_psd {D : ℕ} (psi : Fin D → QState (Fin D))
    (a : Fin D → ℝ) (ha : ∀ i, 0 ≤ a i) : (basisDiag psi a).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  have hk : (ketbra (psi i) (psi i)).PosSemidef := by
    exact outerProduct_posSemidef (psi i)
  exact hk.smul (by exact_mod_cast ha i)

private theorem basis_density {D : ℕ} (psi : Fin D → QState (Fin D))
    (horth : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (psi i) (psi j) = if i = j then 1 else 0)
    (p : Fin D → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    IsDensityOperator (gibbsBasis psi p) := by
  have he : gibbsBasis psi p = basisDiag psi p := by
    unfold gibbsBasis basisDiag
    apply Finset.sum_congr rfl
    intro i _
    exact realMatrixSmul (p i) (ketbra (psi i) (psi i))
  rw [he]
  refine ⟨basisDiag_psd psi p hp, ?_⟩
  simp only [basisDiag, Matrix.trace_sum, Matrix.trace_smul, trace_ketbra, horth,
    if_true, smul_eq_mul, mul_one, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

private theorem basis_sqrt {D : ℕ} (psi : Fin D → QState (Fin D))
    (horth : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (psi i) (psi j) = if i = j then 1 else 0)
    (p : Fin D → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    densSqrt (gibbsBasis psi p) = basisDiag psi (fun i => Real.sqrt (p i)) := by
  have hs := basis_density psi horth p hp hsum
  have hpos : 0 ≤ gibbsBasis psi p := Matrix.nonneg_iff_posSemidef.mpr hs.1
  have hsq : basisDiag psi (fun i => Real.sqrt (p i)) * basisDiag psi (fun i => Real.sqrt (p i)) =
      gibbsBasis psi p := by
    rw [basisDiag_mul psi horth]
    simp only [Real.mul_self_sqrt (hp _), basisDiag, gibbsBasis]
    apply Finset.sum_congr rfl
    intro i _
    exact (realMatrixSmul (p i) (ketbra (psi i) (psi i))).symm
  unfold densSqrt
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt _ hpos]
  exact CFC.sqrt_unique hsq (Matrix.nonneg_iff_posSemidef.mpr
    (basisDiag_psd psi _ (fun i => Real.sqrt_nonneg (p i))))

private theorem basis_sandwich {D : ℕ} (psi : Fin D → QState (Fin D))
    (horth : ∀ i j, Qatlib.Foundations.PureStateMath.Inner (psi i) (psi j) = if i = j then 1 else 0)
    (p : Fin D → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (n m : Fin D) :
    densSqrt (gibbsBasis psi p) * ketbra (psi n) (psi m) * densSqrt (gibbsBasis psi p) =
      (Real.sqrt (p n * p m) : ℂ) • ketbra (psi n) (psi m) := by
  rw [basis_sqrt psi horth p hp hsum, basisDiag_left psi horth, Matrix.smul_mul,
    basisDiag_right psi horth, smul_smul, ← Complex.ofReal_mul, ← Real.sqrt_mul (hp n)]

private theorem trace_ketbra_mul {D : ℕ} (u v : QState (Fin D)) (A : Operator D) :
    Matrix.trace (ketbra u v * A) = braKetElem A v u := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, ketbra, Matrix.of_apply,
    braKetElem, Qatlib.Foundations.PureStateMath.Inner, dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem trace_mul_ketbra {D : ℕ} (u v : QState (Fin D)) (A : Operator D) :
    Matrix.trace (A * ketbra u v) = braKetElem A v u := by
  rw [Matrix.trace_mul_comm, trace_ketbra_mul]

private theorem basis_expansion {D : ℕ} (psi : Fin D → QState (Fin D))
    (hcomplete : ∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (psi i) x • psi i = x)
    (A : Operator D) : A = ∑ n, ∑ m, braKetElem A (psi n) (psi m) • ketbra (psi n) (psi m) := by
  symm
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, ketbra_action, smul_smul, braKetElem]
  rw [Finset.sum_comm]
  calc
    _ = ∑ m, Qatlib.Foundations.PureStateMath.Inner (psi m) x • (∑ n, Qatlib.Foundations.PureStateMath.Inner (psi n) (A *ᵥ psi m) • psi n) := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro n _
      rw [mul_comm]
    _ = ∑ m, Qatlib.Foundations.PureStateMath.Inner (psi m) x • (A *ᵥ psi m) := by simp_rw [hcomplete]
    _ = A *ᵥ (∑ m, Qatlib.Foundations.PureStateMath.Inner (psi m) x • psi m) := by
      rw [Matrix.mulVec_sum]
      simp only [Matrix.mulVec_smul]
    _ = A *ᵥ x := by rw [hcomplete]

private theorem channel_star {D : ℕ} (T : QuantumChannel D D) (A : Operator D) :
    T.map Aᴴ = (T.map A)ᴴ := by
  letI : CStarAlgebra (Operator D) := {}
  let P : Operator D →ₚ[ℂ] Operator D := PositiveLinearMap.mk₀ T.map
    (fun X hX => Matrix.nonneg_iff_posSemidef.mpr
      (T.completelyPositive.positive (Matrix.nonneg_iff_posSemidef.mp hX)))
  exact map_star P A

private theorem balance_extension {D : ℕ} (T : Operator D →ₗ[ℂ] Operator D)
    (S : Operator D) (psi : Fin D → QState (Fin D))
    (hcomplete : ∀ x : QState (Fin D), ∑ i, Qatlib.Foundations.PureStateMath.Inner (psi i) x • psi i = x)
    (hbalanced : ∀ a b n m, Matrix.trace ((ketbra (psi a) (psi b))ᴴ *
        T (S * ketbra (psi n) (psi m) * S)) =
      Matrix.trace ((T (S * ketbra (psi a) (psi b) * S))ᴴ * ketbra (psi n) (psi m))) :
    ∀ rho phi : Operator D, Matrix.trace (rhoᴴ * T (S * phi * S)) =
      Matrix.trace ((T (S * rho * S))ᴴ * phi) := by
  intro rho phi
  rw [basis_expansion psi hcomplete rho, basis_expansion psi hcomplete phi]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, map_sum, map_smul,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  rw [hbalanced]

theorem quantumDetailedBalanceCriterion : QuantumDetailedBalanceCriterion := by
  intro D T psi p horth hcomplete hp hsum hcriterion
  have hs := basis_density psi horth p hp hsum
  have hb : ∀ a b n m, Matrix.trace ((ketbra (psi a) (psi b))ᴴ *
        T.map (densSqrt (gibbsBasis psi p) * ketbra (psi n) (psi m) * densSqrt (gibbsBasis psi p))) =
      Matrix.trace ((T.map (densSqrt (gibbsBasis psi p) * ketbra (psi a) (psi b) * densSqrt (gibbsBasis psi p)))ᴴ *
        ketbra (psi n) (psi m)) := by
    intro a b n m
    simp only [basis_sandwich psi horth p hp hsum, map_smul, Matrix.conjTranspose_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [ketbra_star, trace_ketbra_mul, trace_mul_ketbra, ← channel_star, ketbra_star]
    simp only [Complex.star_def, Complex.conj_ofReal]
    exact hcriterion a b n m
  have hdb : QuantumDetailedBalance T.map (gibbsBasis psi p) :=
    balance_extension T.map (densSqrt (gibbsBasis psi p)) psi hcomplete hb
  exact ⟨hdb, quantumDetailedBalanceFixedPoint D T (gibbsBasis psi p) hs hdb⟩

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
