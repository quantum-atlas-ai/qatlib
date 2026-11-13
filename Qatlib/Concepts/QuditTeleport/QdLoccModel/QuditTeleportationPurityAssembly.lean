/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.QuditTeleportationInstrument
import Qatlib.Concepts.QuditTeleport.TeleportCore.CountedQuditTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.QdLoccModel.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditResourceMarginalConverse
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntCharacterization
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditMaxEntResourceTeleportation
import Qatlib.Concepts.QuditTeleport.ResourceIff.QuditPureResourceMaxEntForm
import Qatlib.Concepts.QuditTeleport.MessagingBounds.RedundantCodingReliability
import Qatlib.Concepts.QuditTeleport.CommLowerBound.CommBoundRestrictedTele
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationBranchMarginal
import Qatlib.Concepts.QuditTeleport.QdLoccModel.QuditTeleportationPurity

/-!
# Purity of perfect teleportation resources

The branch marginal is linear in the resource operator, so a square-root column decomposition
expands a mixed resource into pure-resource contributions. Perfect recovery makes every
resulting row Kraus operator proportional to its unitary correction's adjoint.

The theorem `g8p_mixed_purity` uses these constraints to show that a positive semidefinite
resource for a perfect protocol is the outer product of a normalized vector. These results
develop resource and communication properties of teleportation [BennettEtAl1993Teleportation].
Matrix positivity and finite-dimensional operator methods are treated in [Watrous2018].

## Main statements

* `g8p_row_scalar_all`: For a positive semidefinite resource in a perfect protocol with unitary
  corrections, every row Kraus operator of every square-root column is a scalar multiple of the
  corresponding correction's adjoint.
* `g8p_row_scalar_ne`: For a positive semidefinite resource enabling perfect recovery in nonzero
  dimension, any scalar representation of all square-root-column row Kraus operators has a
  nonzero coefficient.
* `g8p_mixed_purity`: A positive semidefinite resource enabling perfect teleportation with
  unitary corrections in nonzero dimension equals the outer product of a normalized vector
  [BennettEtAl1993Teleportation].

## References

* [Bennett et al., 1993][BennettEtAl1993Teleportation]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open Matrix
open scoped ComplexOrder

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QuditTeleport.QdLoccModel
open Matrix
open scoped BigOperators ComplexOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
open Matrix Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open Qatlib.Concepts.QuditTeleport.CommLowerBound
open Qatlib.Concepts.QuditTeleport.MessagingBounds
open Qatlib.Concepts.QuditTeleport.QdLoccModel
open Qatlib.Concepts.QuditTeleport.ResourceIff

/-- The branch marginal is additive in its resource operator. -/
theorem g8p_branch_add_res {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (ω₁ ω₂ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) :
    qdBranchMarginal K (ω₁ + ω₂) ρ
      = qdBranchMarginal K ω₁ ρ + qdBranchMarginal K ω₂ ρ := by
  simp only [qdBranchMarginal, TensorGate, Matrix.kronecker_add, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_add, Pi.add_apply,
    Matrix.mul_add, Matrix.add_mul, partialTrace_add]

/-- Scaling the resource operator by a complex scalar scales the branch marginal by the same
scalar. -/
theorem g8p_branch_smul_res {n : ℕ} (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (c : ℂ) (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) :
    qdBranchMarginal K (c • ω) ρ = c • qdBranchMarginal K ω ρ := by
  simp only [qdBranchMarginal, TensorGate, Matrix.kronecker_smul, relabelGate,
    Matrix.reindex_apply, Matrix.submatrix_smul, Pi.smul_apply,
    Matrix.mul_smul, Matrix.smul_mul, partialTrace_smul]

/-- The branch marginal of a finite sum of resource operators equals the sum of their branch
marginals. -/
theorem g8p_branch_sum_res {n : ℕ} {ι : Type} [Fintype ι]
    (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (t : ι → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (ρ : Operator n) :
    qdBranchMarginal K (∑ i, t i) ρ = ∑ i, qdBranchMarginal K (t i) ρ := by
  classical
  let F : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ →+ Operator n :=
    { toFun := fun ω => qdBranchMarginal K ω ρ
      map_zero' := by
        ext i j
        simp [qdBranchMarginal, TensorGate, relabelGate]
      map_add' := fun a b => g8p_branch_add_res K a b ρ }
  exact map_sum F t Finset.univ

/-- Conjugation by `U * B` is conjugation by `B` followed by conjugation by `U`. -/
theorem g8p_conjBranch_mul {n : ℕ} (U B : Operator n) (ρ : Operator n) :
    conjBranch (U * B) ρ = U * conjBranch B ρ * U.conjTranspose := by
  simp only [conjBranch_apply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Fixed left and right matrix factors can be moved outside a finite sum. -/
theorem g8p_sum_sandwich {n : ℕ} {ι : Type} [Fintype ι] (A B : Operator n)
    (T : ι → Operator n) :
    (∑ i, A * T i * B) = A * (∑ i, T i) * B := by
  have h1 : (∑ i, A * T i * B) = (∑ i, A * T i) * B := by rw [← Finset.sum_mul]
  have h2 : (∑ i, A * T i) = A * (∑ i, T i) := by rw [Finset.mul_sum]
  rw [h1, h2]

/-- Fixed left and right matrix factors can be moved outside a double finite sum. -/
theorem g8p_sum2_sandwich {n : ℕ} {ι σ : Type} [Fintype ι] [Fintype σ] (A B : Operator n)
    (T : ι → σ → Operator n) :
    (∑ i, ∑ j, A * T i j * B) = A * (∑ i, ∑ j, T i j) * B := by
  calc (∑ i, ∑ j, A * T i j * B) = ∑ i, A * (∑ j, T i j) * B :=
        Finset.sum_congr rfl (fun i _ => g8p_sum_sandwich A B (T i))
    _ = A * (∑ i, ∑ j, T i j) * B := g8p_sum_sandwich A B (fun i => ∑ j, T i j)

/-- For a positive semidefinite resource in a perfect protocol with unitary corrections, every
row Kraus operator of every square-root column is a scalar multiple of the corresponding
correction's adjoint. -/
theorem g8p_row_scalar_all {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω) :
    ∀ (k : κ) (s : Fin (n * n)) (u : Fin n × Fin n),
      ∃ z : ℂ, qdRowKraus (P.kraus k) (g8pCol ω s) u = z • (U k).conjTranspose := by
  classical
  set A : κ × Fin (n * n) × (Fin n × Fin n) → Operator n :=
    fun w => U w.1 * qdRowKraus (P.kraus w.1) (g8pCol ω w.2.1) w.2.2
  have hsum : ∀ ρ : Operator n,
      (∑ w : κ × Fin (n * n) × (Fin n × Fin n), conjBranch (A w) ρ) = (1 : ℂ) • ρ := by
    intro ρ
    rw [one_smul]
    have hbr : ∀ k : κ, qdBranchMarginal (P.kraus k) ω ρ
        = ∑ s : Fin (n * n), ∑ u : Fin n × Fin n,
            conjBranch (qdRowKraus (P.kraus k) (g8pCol ω s) u) ρ := by
      intro k
      have hstep : qdBranchMarginal (P.kraus k)
          (∑ s : Fin (n * n), outerProduct (g8pCol ω s)) ρ
          = ∑ s : Fin (n * n), ∑ u : Fin n × Fin n,
              conjBranch (qdRowKraus (P.kraus k) (g8pCol ω s) u) ρ := by
        rw [g8p_branch_sum_res]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        exact qdBranchMarginal_outerProduct_kraus (P.kraus k) (g8pCol ω s) ρ
      have hcast := congrArg
        (fun X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => qdBranchMarginal (P.kraus k) X ρ)
        (g8p_omega_sum_outerProduct ω hω)
      exact hcast.symm.trans hstep
    have hsplit : ∀ k : κ,
        (∑ s : Fin (n * n), ∑ u : Fin n × Fin n,
            conjBranch (U k * qdRowKraus (P.kraus k) (g8pCol ω s) u) ρ)
          = U k * qdBranchMarginal (P.kraus k) ω ρ * (U k).conjTranspose := by
      intro k
      have h1 : (∑ s : Fin (n * n), ∑ u : Fin n × Fin n,
          conjBranch (U k * qdRowKraus (P.kraus k) (g8pCol ω s) u) ρ)
          = ∑ s : Fin (n * n), ∑ u : Fin n × Fin n,
              U k * conjBranch (qdRowKraus (P.kraus k) (g8pCol ω s) u) ρ * (U k).conjTranspose :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun u _ => g8p_conjBranch_mul _ _ _))
      rw [h1, g8p_sum2_sandwich, hbr]
    calc (∑ w : κ × Fin (n * n) × (Fin n × Fin n), conjBranch (A w) ρ)
        = ∑ k : κ, ∑ s : Fin (n * n), ∑ u : Fin n × Fin n,
            conjBranch (U k * qdRowKraus (P.kraus k) (g8pCol ω s) u) ρ := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          show (∑ x : Fin (n * n) × (Fin n × Fin n),
              conjBranch (A (k, x)) ρ) = _
          rw [Fintype.sum_prod_type]
      _ = ∑ k : κ, U k * qdBranchMarginal (P.kraus k) ω ρ * (U k).conjTranspose :=
          Finset.sum_congr rfl (fun k _ => hsplit k)
      _ = ∑ k : κ, P.corr k (qdBranchMarginal (P.kraus k) ω ρ) :=
          Finset.sum_congr rfl (fun k _ => (hU.2 k _).symm)
      _ = ρ := hperf ρ
  have hsc := comm_kraus_scalar_of_identity A 1 hsum
  intro k s u
  obtain ⟨z, hz⟩ := hsc (k, s, u)
  have hkey : U k * qdRowKraus (P.kraus k) (g8pCol ω s) u = z • (1 : Operator n) := hz
  exact ⟨z, qdRowKraus_eq P U hU (g8pCol ω s) k u z hkey⟩

/-- For a positive semidefinite resource enabling perfect recovery in nonzero dimension, any
scalar representation of all square-root-column row Kraus operators has a nonzero
coefficient. -/
theorem g8p_row_scalar_ne {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (_hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω)
    (z : κ → Fin (n * n) → (Fin n × Fin n) → ℂ)
    (hz : ∀ (k : κ) (s : Fin (n * n)) (u : Fin n × Fin n),
      qdRowKraus (P.kraus k) (g8pCol ω s) u = z k s u • (U k).conjTranspose) :
    ∃ (k : κ) (s : Fin (n * n)) (u : Fin n × Fin n), z k s u ≠ 0 := by
  classical
  by_contra hc
  have hz0 : ∀ (k : κ) (s : Fin (n * n)) (u : Fin n × Fin n), z k s u = 0 := by
    intro k s u
    by_contra h
    exact hc ⟨k, s, u, h⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have hrow0 : ∀ (k : κ) (s : Fin (n * n)) (u : Fin n × Fin n),
      qdRowKraus (P.kraus k) (g8pCol ω s) u = 0 := by
    intro k s u
    rw [hz k s u, hz0 k s u, zero_smul]
  have hbr : ∀ (k : κ) (ρ : Operator n), qdBranchMarginal (P.kraus k) ω ρ = 0 := by
    intro k ρ
    have hstep : qdBranchMarginal (P.kraus k)
        (∑ s : Fin (n * n), outerProduct (g8pCol ω s)) ρ = 0 := by
      rw [g8p_branch_sum_res]
      apply Finset.sum_eq_zero
      intro s _
      rw [qdBranchMarginal_outerProduct_kraus]
      apply Finset.sum_eq_zero
      intro u _
      rw [hrow0]
      simp only [conjBranch_apply, Matrix.zero_mul, Matrix.mul_zero]
    have hcast := congrArg
      (fun X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ => qdBranchMarginal (P.kraus k) X ρ)
      (g8p_omega_sum_outerProduct ω hω)
    exact hcast.symm.trans hstep
  have hout : qdLoccOutput P ω (1 : Operator n) = 0 := by
    show (∑ k : κ, P.corr k (qdBranchMarginal (P.kraus k) ω (1 : Operator n))) = 0
    simp only [hbr, map_zero, Finset.sum_const_zero]
  have hone := hperf (1 : Operator n)
  rw [hout] at hone
  exact zero_ne_one hone

/-- A positive semidefinite resource enabling perfect teleportation with unitary corrections in
nonzero dimension equals the outer product of a normalized vector
[BennettEtAl1993Teleportation]. -/
theorem g8p_mixed_purity {n : ℕ} [NeZero n] {κ : Type} [Fintype κ]
    (P : QdLoccTeleport n κ) (U : κ → Operator n) (hU : QdLoccUnitaryCorr P U)
    (ω : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (hω : ω.PosSemidef)
    (hperf : QdLoccPerfect P ω) :
    ∃ Ψ : QState (Fin n × Fin n), Normalized Ψ ∧ ω = outerProduct Ψ := by
  classical
  choose z hz using g8p_row_scalar_all P U hU ω hω hperf
  obtain ⟨k0, s0, u0, hz0⟩ := g8p_row_scalar_ne P U hU ω hω hperf z hz
  set A0 : Matrix (Fin n) (Fin n) ℂ := qdMatA (P.kraus k0) u0
  have hprod : ∀ s : Fin (n * n),
      qdMatW (g8pCol ω s) * A0 = z k0 s u0 • (U k0).conjTranspose := by
    intro s
    exact hz k0 s u0
  have hu0 : (U k0).conjTranspose * U k0 = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff'.mp (hU.1 k0)
  have hdet1 : (U k0).conjTranspose.det * (U k0).det = 1 := by
    have h := congrArg Matrix.det hu0
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact h
  have hdetU : (U k0).det ≠ 0 := by
    intro hh
    rw [hh, mul_zero] at hdet1
    exact zero_ne_one hdet1
  have hdetU' : (U k0).conjTranspose.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.mpr hdetU
  have hdetP : ((z k0 s0 u0 • (U k0).conjTranspose : Operator n)).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz0) hdetU'
  have hdetProd : (qdMatW (g8pCol ω s0) * A0).det ≠ 0 := by
    rw [hprod s0]
    exact hdetP
  have hdetA0 : IsUnit A0.det := by
    rw [Matrix.det_mul] at hdetProd
    exact IsUnit.mk0 _ (right_ne_zero_of_mul hdetProd)
  set M : Matrix (Fin n) (Fin n) ℂ := (U k0).conjTranspose * A0⁻¹
  have hW : ∀ s : Fin (n * n), qdMatW (g8pCol ω s) = z k0 s u0 • M := by
    intro s
    have h2 : qdMatW (g8pCol ω s) = qdMatW (g8pCol ω s) * A0 * A0⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv A0 hdetA0, Matrix.mul_one]
    rw [h2, hprod s, Matrix.smul_mul]
  set v : QState (Fin n × Fin n) := fun p => M p.2 p.1
  have hcol : ∀ (s : Fin (n * n)) (p : Fin n × Fin n),
      g8pCol ω s p = z k0 s u0 * v p := by
    intro s p
    have h := congrArg (fun T : Matrix (Fin n) (Fin n) ℂ => T p.2 p.1) (hW s)
    simpa only [qdMatW, Matrix.smul_apply, smul_eq_mul, v] using h
  have hop : ∀ s : Fin (n * n),
      outerProduct (g8pCol ω s) = (z k0 s u0 * star (z k0 s u0)) • outerProduct v := by
    intro s
    ext i j
    simp only [outerProduct_apply, Matrix.smul_apply, smul_eq_mul, Complex.star_def]
    rw [hcol s i, hcol s j, map_mul]
    ring
  have homega : ω = (∑ s : Fin (n * n), z k0 s u0 * star (z k0 s u0)) • outerProduct v := by
    have hsum := g8p_omega_sum_outerProduct ω hω
    rw [← hsum, Finset.sum_smul]
    exact Finset.sum_congr rfl (fun s _ => hop s)
  have htr := g8p_trace_one P U hU ω hω hperf
  have hN' : (∑ p : Fin n × Fin n, (Complex.normSq (v p) : ℂ))
      = ∑ p : Fin n × Fin n, v p * star (v p) := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Complex.normSq_eq_conj_mul_self]
    exact mul_comm _ _
  set N : ℝ := ∑ p : Fin n × Fin n, Complex.normSq (v p)
  have hN0 : (N : ℂ) = ∑ p : Fin n × Fin n, v p * star (v p) := by
    simpa only [N, Complex.ofReal_sum] using hN'
  have htrv : Matrix.trace (outerProduct v) = ∑ p : Fin n × Fin n, v p * star (v p) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, outerProduct_apply, Complex.star_def]
  have hcn : (∑ s : Fin (n * n), z k0 s u0 * star (z k0 s u0)) * (N : ℂ) = 1 := by
    have h := congrArg Matrix.trace homega
    rw [Matrix.trace_smul, htrv, ← hN0] at h
    simp only [smul_eq_mul] at h
    rw [← h, htr]
  have hNge : 0 ≤ N :=
    Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg (v p))
  have hNpos : 0 < N := by
    by_contra hle
    have hNz : N = 0 := le_antisymm (not_lt.mp hle) hNge
    have hv0 : ∀ p : Fin n × Fin n, v p = 0 := by
      intro p
      have hle0 : Complex.normSq (v p) = 0 := by
        have h1 : Complex.normSq (v p) ≤ N :=
          Finset.single_le_sum (fun q _ => Complex.normSq_nonneg (v q)) (Finset.mem_univ p)
        have hnn : 0 ≤ Complex.normSq (v p) := Complex.normSq_nonneg (v p)
        linarith
      exact Complex.normSq_eq_zero.mp hle0
    have hv0m : outerProduct v = 0 := by
      ext i j
      simp only [outerProduct_apply, hv0, zero_mul, Matrix.zero_apply]
    rw [hv0m, smul_zero] at homega
    have htr0 : Matrix.trace ω = 0 := by rw [homega, Matrix.trace_zero]
    rw [htr0] at htr
    exact zero_ne_one htr
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  refine ⟨fun p => ((Real.sqrt N : ℂ))⁻¹ * v p, ?_, ?_⟩
  · have h1 : ∀ p : Fin n × Fin n,
        ‖((Real.sqrt N : ℂ))⁻¹ * v p‖ ^ 2 = (1 / N) * Complex.normSq (v p) := by
      intro p
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_inv,
        Complex.normSq_ofReal, Real.mul_self_sqrt (le_of_lt hNpos)]
      field_simp [ne_of_gt hNpos]
    show ∑ p : Fin n × Fin n, ‖((Real.sqrt N : ℂ))⁻¹ * v p‖ ^ 2 = 1
    rw [Finset.sum_congr rfl (fun p _ => h1 p), ← Finset.mul_sum]
    have hsum : (∑ p : Fin n × Fin n, Complex.normSq (v p)) = N := rfl
    rw [hsum]
    field_simp [ne_of_gt hNpos]
  · have hopΨ : outerProduct (fun p => ((Real.sqrt N : ℂ))⁻¹ * v p)
        = ((1 : ℂ) / N) • outerProduct v := by
      ext i j
      simp only [outerProduct_apply, Matrix.smul_apply, smul_eq_mul]
      have hconj : (starRingEnd ℂ) (((Real.sqrt N : ℂ))⁻¹ * v j)
          = ((Real.sqrt N : ℂ))⁻¹ * (starRingEnd ℂ) (v j) := by
        rw [map_mul, map_inv₀, Complex.conj_ofReal]
      rw [hconj]
      have hinv : ((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹ = (1 : ℂ) / N := by
        rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hNpos), one_div]
      have hs : ((Real.sqrt N : ℂ))⁻¹ * v i * (((Real.sqrt N : ℂ))⁻¹ * (starRingEnd ℂ) (v j))
          = (((Real.sqrt N : ℂ))⁻¹ * ((Real.sqrt N : ℂ))⁻¹) * (v i * (starRingEnd ℂ) (v j)) :=
        by ring
      rw [hs, hinv]
    rw [hopΨ, homega]
    have hc : (∑ s : Fin (n * n), z k0 s u0 * star (z k0 s u0)) = (1 : ℂ) / N := by
      apply (mul_right_cancel₀ hNne)
      rw [hcn, one_div_mul_cancel hNne]
    rw [hc]
end Qatlib.Concepts.QuditTeleport.QdLoccModel
