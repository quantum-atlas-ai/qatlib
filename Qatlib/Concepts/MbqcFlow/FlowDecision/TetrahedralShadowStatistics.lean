/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowInstrument
import Qatlib.Concepts.PauliClifford.ExactRank.PauliShadowStatistics

/-!
# Moments and concentration of tetrahedral shadows

`tetraStatistic` converts tetrahedral records into unbiased observable estimates with second
moments and variances bounded by nine times the squared spectral norm. Independent records are
realized by product density operators and Kraus operators, so their product law agrees with the
physical Born law.

Chebyshev's inequality and a finite union bound give a simultaneous accuracy bound for sample
means of a finite family of Hermitian observables. See [HuangKuengPreskill2020].

## Main statements

* `tetrahedral_observable_computed_second_moment_bound`: second-moment and variance bounds.
* `tetra_fresh_actual_born`: realization of fresh record probabilities by product-state
  measurements.
* `tetrahedral_many_observable_actual_mean_bound`: joint concentration for observable sample
  means.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder ComplexConjugate Kronecker

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- Negation preserves the spectral norm of a qubit operator. -/
theorem operatorSpectralNorm_neg (A : Operator 2) :
    OperatorSpectralNorm (-A) = OperatorSpectralNorm A := by
  rw [OperatorSpectralNorm, OperatorSpectralNorm, map_neg, norm_neg]

/-- For a Hermitian qubit operator, its quadratic form is real and is at most the spectral norm
times the vector's squared Euclidean norm. -/
theorem re_dotProduct_mulVec_le (A : Operator 2) (hA : A.IsHermitian) (x : Fin 2 → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).im = 0 ∧
      (star x ⬝ᵥ (A *ᵥ x)).re ≤ OperatorSpectralNorm A * (∑ i, ‖x i‖ ^ 2) := by
  have hnorm : ‖(star x ⬝ᵥ (A *ᵥ x) : ℂ)‖
      ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖
        * (OperatorSpectralNorm A * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖) := by
    calc ‖(star x ⬝ᵥ (A *ᵥ x) : ℂ)‖
        = ‖inner ℂ (WithLp.toLp 2 x)
            (Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 x))‖ := by
          rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp]
          show ‖∑ i, star (x i) * (A *ᵥ x) i‖
              = ‖∑ i, (A *ᵥ x) i * star (x i)‖
          exact congrArg _
            (Finset.sum_congr rfl fun i _ => mul_comm ((star x) i) ((A *ᵥ x) i))
      _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖
            * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A (WithLp.toLp 2 x)‖ := norm_inner_le_norm _ _
      _ ≤ ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖
            * (OperatorSpectralNorm A * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
  have hcs : (star x ⬝ᵥ (A *ᵥ x)).re ≤ OperatorSpectralNorm A * (∑ i, ‖x i‖ ^ 2) := by
    have hrele : ((star x ⬝ᵥ (A *ᵥ x) : ℂ)).re ≤ ‖(star x ⬝ᵥ (A *ᵥ x) : ℂ)‖ :=
      Complex.re_le_norm _
    have h3 : ‖(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ ^ 2 = (∑ i, ‖x i‖ ^ 2) := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [pow_two] at h3
    nlinarith [hrele, hnorm, h3, norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2)),
      operatorSpectralNorm_nonneg A]
  refine ⟨?_, hcs⟩
  have hconj : conj (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) := by
    have hsum : ∀ g : Fin 2 → ℂ, conj (∑ i, g i) = ∑ i, conj (g i) :=
      fun g => map_sum (starRingEnd ℂ) g Finset.univ
    have h1 : ∀ i : Fin 2, conj ((A *ᵥ x) i) = ∑ j, A j i * conj (x j) := by
      intro i
      show conj (∑ j, A i j * x j) = _
      rw [hsum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [map_mul]
        have hj : (starRingEnd ℂ) (A i j) = A j i := by
          have h2 := congrFun (congrFun hA j) i
          rw [Matrix.conjTranspose_apply] at h2
          exact h2
        rw [hj]
    have hL : conj (∑ i, conj (x i) * (A *ᵥ x) i)
        = ∑ p : Fin 2 × Fin 2, x p.1 * (A p.2 p.1 * conj (x p.2)) := by
      rw [hsum]
      have hexp : ∀ i : Fin 2, conj (conj (x i) * (A *ᵥ x) i)
          = ∑ j, x i * (A j i * conj (x j)) := by
        intro i
        rw [map_mul, h1 i]
        show star (star (x i)) * ∑ j, A j i * conj (x j) = _
        rw [star_star, Finset.mul_sum]
      calc ∑ i, conj (conj (x i) * (A *ᵥ x) i)
          = ∑ i, ∑ j, x i * (A j i * conj (x j)) :=
            Finset.sum_congr rfl fun i _ => hexp i
        _ = ∑ p : Fin 2 × Fin 2, x p.1 * (A p.2 p.1 * conj (x p.2)) := by
            rw [← Fintype.sum_prod_type
              (f := fun p : Fin 2 × Fin 2 => x p.1 * (A p.2 p.1 * conj (x p.2)))]
    have hR : (∑ i, conj (x i) * (A *ᵥ x) i)
        = ∑ p : Fin 2 × Fin 2, conj (x p.1) * (A p.1 p.2 * x p.2) := by
      rw [Fintype.sum_prod_type
        (f := fun p : Fin 2 × Fin 2 => conj (x p.1) * (A p.1 p.2 * x p.2))]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hmv : (A *ᵥ x) i = ∑ y, A i y * x y := rfl
      rw [hmv, Finset.mul_sum]
    show conj (∑ i, conj (x i) * (A *ᵥ x) i) = ∑ i, conj (x i) * (A *ᵥ x) i
    rw [hL]
    refine Eq.trans ?_ hR.symm
    rw [← Equiv.sum_comp (Equiv.prodComm (Fin 2) (Fin 2))
      (g := fun p : Fin 2 × Fin 2 => x p.1 * (A p.2 p.1 * conj (x p.2)))]
    exact Finset.sum_congr rfl fun p _ => by
      show x p.2 * (A p.1 p.2 * conj (x p.1))
          = conj (x p.1) * (A p.1 p.2 * x p.2)
      ring
  exact Complex.conj_eq_iff_im.mp hconj

/-- For a Hermitian qubit operator, its spectral norm times the identity minus the operator is
positive semidefinite. -/
theorem posSemidef_one_sub_of_isHermitian (A : Operator 2) (hA : A.IsHermitian) :
    (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A).PosSemidef := by
  have hherm : (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A).IsHermitian := by
    show ((((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A)ᴴ
        = ((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A)
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_ofReal, hA]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?_
  intro x
  obtain ⟨him, hbd⟩ := re_dotProduct_mulVec_le A hA x
  have hxx : star x ⬝ᵥ x = ((∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    show ∑ i, star (x i) * x i = _
    have hterm : ∀ i : Fin 2, star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Complex.ofReal_sum]
  have hexp : star x ⬝ᵥ
      ((((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A) *ᵥ x)
      = ((OperatorSpectralNorm A : ℝ) : ℂ) * (star x ⬝ᵥ x) - star x ⬝ᵥ (A *ᵥ x) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul]
    rfl
  rw [hexp, hxx, Complex.nonneg_iff]
  refine ⟨?_, ?_⟩
  · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    linarith

/-- The absolute real trace of a Hermitian operator against an orthogonal projector is bounded
by its spectral norm times the projector trace. -/
theorem abs_trace_re_le_of_isOrthogonalProjector (A Q : Operator 2)
    (hA : A.IsHermitian) (hQ : Q.PosSemidef) (hQQ : Q * Q = Q) :
    |(Matrix.trace (A * Q)).re| ≤ OperatorSpectralNorm A * (Matrix.trace Q).re := by
  have hQherm : Qᴴ = Q := hQ.isHermitian
  have hpsdm := posSemidef_one_sub_of_isHermitian A hA
  have hpsdp : (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) + A).PosSemidef := by
    have hneg : (-A).IsHermitian := by
      show (-A)ᴴ = -A
      rw [Matrix.conjTranspose_neg, hA]
    have h := posSemidef_one_sub_of_isHermitian (-A) hneg
    rw [operatorSpectralNorm_neg] at h
    rwa [sub_neg_eq_add] at h
  have hconjm : (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A) * Q).PosSemidef := by
    have h := hpsdm.conjTranspose_mul_mul_same Q
    rwa [hQherm] at h
  have hconjp : (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) + A) * Q).PosSemidef := by
    have h := hpsdp.conjTranspose_mul_mul_same Q
    rwa [hQherm] at h
  have htrQQ : Matrix.trace (Q * Q) = Matrix.trace Q := by rw [hQQ]
  have htrQAQ : Matrix.trace (Q * A * Q) = Matrix.trace (A * Q) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm (Q * Q) A, hQQ]

  have hupper : (Matrix.trace (A * Q)).re
      ≤ OperatorSpectralNorm A * (Matrix.trace Q).re := by
    have h0 : 0 ≤ (Matrix.trace
        (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A) * Q)).re :=
      (Complex.nonneg_iff.mp hconjm.trace_nonneg).1
    have hre : (Matrix.trace
          (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A) * Q)).re
        = OperatorSpectralNorm A * (Matrix.trace Q).re - (Matrix.trace (A * Q)).re := by
      have hexp : Matrix.trace
          (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) - A) * Q)
          = ((OperatorSpectralNorm A : ℝ) : ℂ) * Matrix.trace (Q * Q)
            - Matrix.trace (Q * A * Q) := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
      rw [hexp, htrQQ, htrQAQ]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre] at h0
    linarith

  have hlower : -(OperatorSpectralNorm A * (Matrix.trace Q).re)
      ≤ (Matrix.trace (A * Q)).re := by
    have h0 : 0 ≤ (Matrix.trace
        (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) + A) * Q)).re :=
      (Complex.nonneg_iff.mp hconjp.trace_nonneg).1
    have hre : (Matrix.trace
          (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) + A) * Q)).re
        = OperatorSpectralNorm A * (Matrix.trace Q).re + (Matrix.trace (A * Q)).re := by
      have hexp : Matrix.trace
          (Q * (((OperatorSpectralNorm A : ℝ) : ℂ) • (1 : Operator 2) + A) * Q)
          = ((OperatorSpectralNorm A : ℝ) : ℂ) * Matrix.trace (Q * Q)
            + Matrix.trace (Q * A * Q) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
          Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
      rw [hexp, htrQQ, htrQAQ]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      linarith
    rw [hre] at h0
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The real trace of an observable against the tetrahedral snapshot for a given outcome. -/
noncomputable def tetraStatistic (A : Operator 2) (a : Fin 4) : ℝ :=
  (Matrix.trace (A * tetraSnapshot a)).re

/-- The tetrahedral statistic is the real snapshot pairing, and its expectation equals the
observable's expectation in the input state. -/
theorem tetrahedral_observable_unbiased (ρ A : Operator 2) (hρ : IsDensityOperator ρ)
    (_hA : A.IsHermitian) :
    (∀ a, tetraStatistic A a = (Matrix.trace (A * tetraSnapshot a)).re) ∧
      (tetraRecordLaw ρ hρ).expect (tetraStatistic A) = (Matrix.trace (A*ρ)).re := by
  refine ⟨fun _ => rfl, ?_⟩
  have hg3 := tetrahedral_measurement_inverse_reconstructs.2 ρ hρ
  have hstep : Matrix.trace
      (A * ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ) • tetraSnapshot a)
      = ∑ a : Fin 4, (((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)
          * Matrix.trace (A * tetraSnapshot a) := by
    rw [Matrix.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have htr := congrArg (fun M : Operator 2 => Matrix.trace (A * M)) hg3
  (try simp only [] at htr)
  rw [hstep] at htr
  rw [← htr, Complex.re_sum]
  show ∑ a : Fin 4, (tetraRecordLaw ρ hρ).prob a * tetraStatistic A a = _
  refine Finset.sum_congr rfl fun a _ => ?_
  show (tetraRecordLaw ρ hρ).prob a * ((Matrix.trace (A * tetraSnapshot a)).re : ℝ)
      = ((((tetraRecordLaw ρ hρ).prob a : ℝ) : ℂ)
          * Matrix.trace (A * tetraSnapshot a)).re
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- For a Hermitian observable, both the second moment and the mean squared centered error are
at most nine times its squared spectral norm. -/
theorem tetrahedral_observable_computed_second_moment_bound (ρ A : Operator 2)
    (hρ : IsDensityOperator ρ) (hA : A.IsHermitian) :
    (tetraRecordLaw ρ hρ).expect (fun a => (tetraStatistic A a)^2)
        ≤ 9 * (OperatorSpectralNorm A)^2 ∧
      (tetraRecordLaw ρ hρ).expect
          (fun a => (tetraStatistic A a-(Matrix.trace (A*ρ)).re)^2)
        ≤ 9 * (OperatorSpectralNorm A)^2 := by

  have hpsdP : ∀ a : Fin 4, (tetraProjector a).PosSemidef := by
    intro a
    have h := Matrix.posSemidef_conjTranspose_mul_self (tetraProjector a)
    rwa [tetraProjector_conjTranspose, tetraProjector_mul_self] at h
  have hpsdQ : ∀ a : Fin 4, (1 - tetraProjector a).PosSemidef := by
    intro a
    have hidem : (1 - tetraProjector a)ᴴ * (1 - tetraProjector a)
        = 1 - tetraProjector a := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, tetraProjector_conjTranspose,
        sub_mul, one_mul, mul_sub, mul_one, tetraProjector_mul_self, sub_self, sub_zero]
    have h := Matrix.posSemidef_conjTranspose_mul_self ((1 : Operator 2) - tetraProjector a)
    rwa [hidem] at h
  have htraceP : ∀ a : Fin 4, (Matrix.trace (tetraProjector a)).re = 1 := by
    intro a
    rw [tetraProjector_trace]
    rfl
  have htraceQ : ∀ a : Fin 4, (Matrix.trace (1 - tetraProjector a)).re = 1 := by
    intro a
    have h : Matrix.trace (1 - tetraProjector a) = 1 := by
      rw [Matrix.trace_sub, Matrix.trace_one, tetraProjector_trace]
      norm_num
    rw [h]
    rfl
  have hidemQ : ∀ a : Fin 4, (1 - tetraProjector a) * (1 - tetraProjector a)
      = 1 - tetraProjector a := by
    intro a
    rw [sub_mul, one_mul, mul_sub, mul_one, tetraProjector_mul_self, sub_self, sub_zero]

  have hbound : ∀ a : Fin 4, |tetraStatistic A a| ≤ 3 * OperatorSpectralNorm A := by
    intro a
    have hdec : tetraSnapshot a
        = (2 : ℂ) • tetraProjector a - (1 - tetraProjector a) := by
      rw [tetraSnapshot]
      module
    have hexp : Matrix.trace (A * tetraSnapshot a)
        = (2:ℂ) * Matrix.trace (A * tetraProjector a)
          - Matrix.trace (A * (1 - tetraProjector a)) := by
      rw [hdec, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        smul_eq_mul]
    have hstat : tetraStatistic A a
        = 2 * (Matrix.trace (A * tetraProjector a)).re
          - (Matrix.trace (A * (1 - tetraProjector a))).re := by
      show (Matrix.trace (A * tetraSnapshot a)).re = _
      rw [hexp, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat]
      ring
    rw [hstat, abs_le]
    have h1 := abs_trace_re_le_of_isOrthogonalProjector A (tetraProjector a) hA (hpsdP a)
      (tetraProjector_mul_self a)
    rw [htraceP a, mul_one] at h1
    have h2 := abs_trace_re_le_of_isOrthogonalProjector A (1 - tetraProjector a) hA
      (hpsdQ a) (hidemQ a)
    rw [htraceQ a, mul_one] at h2
    rcases abs_le.mp h1 with ⟨hx1, hx2⟩
    rcases abs_le.mp h2 with ⟨hy1, hy2⟩
    constructor <;> linarith
  have hmain : (tetraRecordLaw ρ hρ).expect (fun a => (tetraStatistic A a)^2)
      ≤ 9 * (OperatorSpectralNorm A)^2 := by
    have hsq : ∀ a : Fin 4, (tetraStatistic A a)^2 ≤ (3 * OperatorSpectralNorm A)^2 := by
      intro a
      have hb := hbound a
      have habsnn : 0 ≤ |tetraStatistic A a| := abs_nonneg _
      have hsqnn : 0 ≤ (OperatorSpectralNorm A)^2 := sq_nonneg _
      nlinarith [sq_abs (tetraStatistic A a)]
    show (∑ a : Fin 4, (tetraRecordLaw ρ hρ).prob a * (tetraStatistic A a)^2) ≤ _
    calc ∑ a : Fin 4, (tetraRecordLaw ρ hρ).prob a * (tetraStatistic A a)^2
        ≤ ∑ a : Fin 4, (tetraRecordLaw ρ hρ).prob a * (3 * OperatorSpectralNorm A)^2 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hsq a)
            ((tetraRecordLaw ρ hρ).nonneg a)
      _ = 9 * (OperatorSpectralNorm A)^2 := by
          have hcomm : ∀ a : Fin 4, (tetraRecordLaw ρ hρ).prob a
                * (3 * OperatorSpectralNorm A)^2
              = (3 * OperatorSpectralNorm A)^2 * (tetraRecordLaw ρ hρ).prob a :=
            fun a => mul_comm _ _
          rw [Finset.sum_congr rfl (fun a _ => hcomm a), ← Finset.mul_sum,
            (tetraRecordLaw ρ hρ).sum_one, mul_one]
          ring
  refine ⟨hmain, ?_⟩
  rw [← (tetrahedral_observable_unbiased ρ A hρ hA).2]
  show (tetraRecordLaw ρ hρ).variance (tetraStatistic A) ≤ 9 * (OperatorSpectralNorm A)^2
  rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance_eq_expect_sq_sub]
  exact le_trans (sub_le_self _ (sq_nonneg _)) hmain

/-- The product distribution of `m` independent tetrahedral records from the same density
operator. -/
noncomputable def tetraFreshLaw (ρ : Operator 2) (hρ : IsDensityOperator ρ) (m : ℕ) :
    FinDist (Fin m → Fin 4) :=
  independentSampleLaw (fun _ : Fin m => tetraRecordLaw ρ hρ)

/-- The arithmetic mean of the tetrahedral observable statistics in a sample record. -/
noncomputable def tetraSampleMean (A : Operator 2) (m : ℕ) (ω : Fin m → Fin 4) : ℝ :=
  Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg (tetraStatistic A) ω

/-- Fresh record probabilities factor into single-record probabilities, and the sample mean is
the sum of its statistics divided by the sample count. -/
theorem tetrahedral_fresh_same_record_product (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (m : ℕ) (ω : Fin m → Fin 4) :
    (tetraFreshLaw ρ hρ m).prob ω = ∏ j, (tetraRecordLaw ρ hρ).prob (ω j) ∧
      ∀ A, tetraSampleMean A m ω = (∑ j, tetraStatistic A (ω j))/(m:ℝ) :=
  ⟨rfl, fun _ => rfl⟩

/-- The access-count triple `(m, m, m * K)` for fresh tetrahedral records and `K` observable
evaluations per record. -/
def tetraFreshAccessCounts (m K : ℕ) : ℕ × ℕ × ℕ := (m, m, m * K)

/-- The fresh tetrahedral access-count triple is `(m, m, m * K)`. -/
theorem tetra_fresh_access_counts (m K : ℕ) :
    tetraFreshAccessCounts m K = (m, m, m * K) := rfl

/-- Reindexing both matrix indices by an equivalence preserves the trace. -/
private theorem trace_submatrix_of_equiv_local {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (σ : ι ≃ κ) (M : Matrix κ κ ℂ) :
    Matrix.trace (M.submatrix σ σ) = Matrix.trace M := by
  show ∑ i, M (σ i) (σ i) = ∑ k, M k k
  exact Equiv.sum_comp σ (fun k => M k k)

/-- A product-entry matrix on `n + 1` qubits splits as the first `n` factors tensored with the
final factor, after register reindexing. -/
private theorem prodEntryMatrix_succ_local {n : ℕ} (M : Fin (n + 1) → Operator 2) :
    (Matrix.of fun x y => ∏ i, (M i) (boolEquivFin2 (x i)) (boolEquivFin2 (y i)) :
        Matrix (Reg (n + 1)) (Reg (n + 1)) ℂ)
      = (((Matrix.of fun x y => ∏ i, (M (Fin.castAdd 1 i)) (boolEquivFin2 (x i))
              (boolEquivFin2 (y i))) : Matrix (Reg n) (Reg n) ℂ) ⊗ₖ
          (M (Fin.natAdd n 0))).submatrix (regProdEquiv n) (regProdEquiv n) := by
  ext x y
  have hfst : ∀ i : Fin n, (regProdEquiv n x).1 i = x (Fin.castAdd 1 i) := fun i => rfl
  have hsnd : (regProdEquiv n x).2 = boolEquivFin2 (x (Fin.natAdd n 0)) := rfl
  have hfsty : ∀ i : Fin n, (regProdEquiv n y).1 i = y (Fin.castAdd 1 i) := fun i => rfl
  have hsndy : (regProdEquiv n y).2 = boolEquivFin2 (y (Fin.natAdd n 0)) := rfl
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.of_apply,
    hfst, hfsty, hsnd, hsndy]
  rw [Fin.prod_univ_add, Fin.prod_univ_one]

/-- The product of `n` copies of a qubit operator, indexed by Boolean registers. -/
noncomputable def tetraProductDensity {n : ℕ} (ρ : Operator 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => ∏ i, ρ (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

/-- The tensor product of the single-qubit tetrahedral Kraus operators specified by a record. -/
noncomputable def tetraProductRecordKraus {n : ℕ} (ρ : Operator 2) (ω : Fin n → Fin 4) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y =>
    ∏ i, (tetraKraus (ω i)) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

/-- The product density operator on zero qubits is the identity. -/
private theorem tetraProductDensity_zero (ρ : Operator 2) :
    tetraProductDensity (n := 0) ρ = 1 := by
  ext x y
  rw [show x = y from Subsingleton.elim x y]
  simp [tetraProductDensity, Matrix.one_apply_eq]

/-- The Kraus operator of an empty product record is the identity. -/
private theorem tetraProductRecordKraus_zero (ρ : Operator 2) (ω : Fin 0 → Fin 4) :
    tetraProductRecordKraus ρ ω = 1 := by
  ext x y
  rw [show x = y from Subsingleton.elim x y]
  simp [tetraProductRecordKraus, Matrix.one_apply_eq]

/-- The product density operator on `n + 1` qubits is the reindexed tensor product of the first
`n` copies and the final copy. -/
theorem tetraProductDensity_succ {n : ℕ} (ρ : Operator 2) :
    tetraProductDensity (n := n + 1) ρ
      = ((tetraProductDensity (n := n) ρ ⊗ₖ ρ)).submatrix (regProdEquiv n) (regProdEquiv n) :=
  prodEntryMatrix_succ_local (fun _ => ρ)

/-- A product-record Kraus operator splits into the Kraus operator for its first `n` outcomes
and the final single-qubit Kraus operator. -/
theorem tetraProductRecordKraus_succ {n : ℕ} (ρ : Operator 2) (ω : Fin (n + 1) → Fin 4) :
    tetraProductRecordKraus ρ ω
      = ((tetraProductRecordKraus (n := n) ρ (fun i => ω (Fin.castAdd 1 i)) ⊗ₖ
          tetraKraus (ω (Fin.natAdd n 0)))).submatrix (regProdEquiv n) (regProdEquiv n) :=
  prodEntryMatrix_succ_local (fun i => tetraKraus (ω i))

/-- The complex trace of a single tetrahedral branch equals its real Born probability embedded
in ℂ. -/
theorem trace_tetraRecord_single (σ : Operator 2) (hσ : IsDensityOperator σ) (a : Fin 4) :
    Matrix.trace (tetraKraus a * σ * (tetraKraus a)ᴴ)
      = (((tetraRecordLaw σ hσ).prob a : ℝ) : ℂ) := by
  have hpsd : (tetraKraus a * σ * (tetraKraus a)ᴴ).PosSemidef := by
    have h := (completelyPositive_conjBranch (tetraKraus a)).positive hσ.1
    rwa [conjBranch_apply] at h
  have him : (Matrix.trace (tetraKraus a * σ * (tetraKraus a)ᴴ)).im = 0 :=
    (RCLike.nonneg_iff.mp hpsd.trace_nonneg).2
  refine Complex.ext_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.ofReal_re]
    rfl
  · rw [him]
    rfl

/-- The real trace of a product-record branch equals the independent fresh-record probability. -/
theorem tetraProductRecordKraus_trace {n : ℕ} (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (ω : Fin n → Fin 4) :
    (Matrix.trace (tetraProductRecordKraus ρ ω * tetraProductDensity ρ
        * (tetraProductRecordKraus ρ ω)ᴴ)).re
      = (tetraFreshLaw ρ hρ n).prob ω := by
  induction n with
  | zero =>
    rw [tetraProductRecordKraus_zero ρ ω, tetraProductDensity_zero ρ, Matrix.one_mul,
      Matrix.conjTranspose_one, Matrix.mul_one]
    have hRHS : (tetraFreshLaw ρ hρ 0).prob ω = 1 := by
      show (∏ i : Fin 0, (tetraRecordLaw ρ hρ).prob (ω i)) = 1
      simp
    rw [hRHS]
    simp [Matrix.trace_one]
  | succ n ih =>
    rw [tetraProductRecordKraus_succ ρ ω, tetraProductDensity_succ ρ,
      Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
      Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      trace_submatrix_of_equiv_local, Matrix.trace_kronecker]
    have htail := ih (fun i => ω (Fin.castAdd 1 i))
    have hlast := trace_tetraRecord_single ρ hρ (ω (Fin.natAdd n 0))
    rw [hlast]
    rw [show ∀ (z : ℂ) (r : ℝ), (z * (r : ℂ)).re = z.re * r from fun z r => by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]]
    rw [htail]
    show (∏ i : Fin n, (tetraRecordLaw ρ hρ).prob (ω (Fin.castAdd 1 i))) *
        (tetraRecordLaw ρ hρ).prob (ω (Fin.natAdd n 0))
      = ∏ i : Fin (n + 1), (tetraRecordLaw ρ hρ).prob (ω i)
    rw [Fin.prod_univ_add, Fin.prod_univ_one]

/-- The tensor product of copies of a density operator is positive semidefinite and has trace
one. -/
theorem tetraProductDensity_isDensity {n : ℕ} (ρ : Operator 2) (hρ : IsDensityOperator ρ) :
    (tetraProductDensity (n := n) ρ).PosSemidef ∧
      Matrix.trace (tetraProductDensity (n := n) ρ) = 1 := by
  induction n with
  | zero =>
    rw [tetraProductDensity_zero ρ]
    exact ⟨Matrix.PosSemidef.one, by simp [Matrix.trace_one]⟩
  | succ n ih =>
    rw [tetraProductDensity_succ ρ]
    refine ⟨(Matrix.posSemidef_submatrix_equiv _).mpr
      (Matrix.PosSemidef.kronecker ih.1 hρ.1), ?_⟩
    rw [trace_submatrix_of_equiv_local (regProdEquiv n) _, Matrix.trace_kronecker
      (tetraProductDensity (n := n) ρ) ρ, ih.2, hρ.2, mul_one]

/-- The product input is a density operator, and its tetrahedral branch trace realizes the
fresh-record product law. -/
theorem tetra_fresh_actual_born {n : ℕ} (ρ : Operator 2) (hρ : IsDensityOperator ρ)
    (ω : Fin n → Fin 4) :
    (tetraProductDensity (n := n) ρ).PosSemidef ∧
      Matrix.trace (tetraProductDensity (n := n) ρ) = 1 ∧
      (Matrix.trace (tetraProductRecordKraus ρ ω * tetraProductDensity (n := n) ρ
          * (tetraProductRecordKraus ρ ω)ᴴ)).re = (tetraFreshLaw ρ hρ n).prob ω :=
  ⟨(tetraProductDensity_isDensity ρ hρ).1, (tetraProductDensity_isDensity ρ hρ).2,
    tetraProductRecordKraus_trace ρ hρ ω⟩

/-- For positive `ε`, the probability of deviation by at least `ε` from any center is at most
the mean squared deviation divided by `ε ^ 2`. -/
theorem chebyshev_single {X : Type*} [Fintype X] [DecidableEq X] (p : FinDist X)
    (f : X → ℝ) (μ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ε ≤ |f ω - μ|), p.prob ω)
      ≤ (∑ ω : X, p.prob ω * (f ω - μ)^2) / ε^2 := by
  have hstep1 : ∑ ω ∈ Finset.univ.filter (fun ω => ε ≤ |f ω - μ|), p.prob ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ε ≤ |f ω - μ|),
          p.prob ω * (f ω - μ)^2 / ε^2 := by
    refine Finset.sum_le_sum fun ω hω => ?_
    have hle : ε ≤ |f ω - μ| := (Finset.mem_filter.mp hω).2
    have hd : ε ^ 2 ≤ (f ω - μ)^2 := by
      nlinarith [hle, abs_nonneg (f ω - μ), sq_abs (f ω - μ)]
    calc p.prob ω = p.prob ω * 1 := by ring
      _ ≤ p.prob ω * ((f ω - μ)^2 / ε^2) := by
          refine mul_le_mul_of_nonneg_left ?_ (p.nonneg ω)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2), one_mul]
          exact hd
      _ = p.prob ω * (f ω - μ)^2 / ε^2 := by ring
  refine le_trans hstep1 ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun ω => ε ≤ |f ω - μ|) (Finset.univ : Finset X))
    (fun ω _ _ => div_nonneg (mul_nonneg (p.nonneg ω) (sq_nonneg _)) (sq_nonneg ε))

/-- The probability of a finite union of events is at most the sum of their probabilities. -/
theorem union_bound_single {X : Type*} [Fintype X] [DecidableEq X]
    (p : FinDist X) {Z : Type} [Fintype Z] (E : Z → X → Prop)
    [∀ z, DecidablePred (E z)] [DecidablePred (fun ω : X => ∃ z, E z ω)] :
    (∑ ω ∈ Finset.univ.filter (fun ω => ∃ z, E z ω), p.prob ω)
      ≤ ∑ z : Z, (∑ ω ∈ Finset.univ.filter (E z), p.prob ω) := by
  classical
  have hsplit : ∀ ω : X,
      p.prob ω * ∑ z : Z, (if E z ω then (1 : ℝ) else 0)
        = ∑ z : Z, p.prob ω * (if E z ω then (1 : ℝ) else 0) :=
        fun ω => Finset.mul_sum (Finset.univ : Finset Z)
          (fun z => if E z ω then (1 : ℝ) else 0) (p.prob ω)
  calc ∑ ω ∈ Finset.univ.filter (fun ω : X => ∃ z, E z ω), p.prob ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω : X => ∃ z, E z ω),
          ∑ z : Z, p.prob ω * (if E z ω then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun ω hω => ?_
        rw [← hsplit ω]
        obtain ⟨z₀, hz₀⟩ := (Finset.mem_filter.mp hω).2
        have h1 : (1 : ℝ) ≤ ∑ z : Z, if E z ω then (1 : ℝ) else 0 := by
          have hz₀' : (1 : ℝ) ≤ (if E z₀ ω then (1 : ℝ) else 0) := by
            rw [if_pos hz₀]
          exact hz₀'.trans (Finset.single_le_sum
            (f := fun z => if E z ω then (1 : ℝ) else 0)
            (fun z _ => by positivity) (Finset.mem_univ z₀))
        calc p.prob ω = p.prob ω * 1 := by ring
          _ ≤ p.prob ω * ∑ z : Z, if E z ω then (1 : ℝ) else 0 :=
              mul_le_mul_of_nonneg_left h1 (p.nonneg ω)
    _ ≤ ∑ ω : X, ∑ z : Z, p.prob ω * (if E z ω then (1 : ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => Finset.sum_nonneg fun z _ => mul_nonneg (p.nonneg ω) (by positivity))
    _ = ∑ z : Z, ∑ ω : X, p.prob ω * (if E z ω then 1 else 0) :=
        Finset.sum_comm
    _ = ∑ z : Z, (∑ ω ∈ Finset.univ.filter (E z), p.prob ω) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [show (∑ ω : X, p.prob ω * (if E z ω then 1 else 0))
            = ∑ ω ∈ Finset.univ.filter (E z), p.prob ω from by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun ω _ => by
            rw [mul_ite, mul_one, mul_zero]]

/-- For positive sample size and tolerance, the probability of any observable sample mean having
error at least `ε` is bounded by the sum of nine times the squared spectral norms divided by
`m * ε ^ 2`. -/
theorem tetrahedral_many_observable_actual_mean_bound {Z : Type} [Fintype Z] [DecidableEq Z]
    (ρ : Operator 2) (hρ : IsDensityOperator ρ) (A : Z → Operator 2) (m : ℕ) (ε : ℝ)
    (hm : 0 < m) (hε : 0 < ε) (hA : ∀ z, (A z).IsHermitian) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ∃ z, ε ≤ |tetraSampleMean (A z) m ω
          - (Matrix.trace (A z*ρ)).re|), (tetraFreshLaw ρ hρ m).prob ω)
      ≤ (∑ z, 9*(OperatorSpectralNorm (A z))^2)/((m:ℝ)*ε^2) := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hbudget : ∀ z : Z,
      (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin 4 => ε ≤ |tetraSampleMean (A z) m ω
            - (Matrix.trace (A z*ρ)).re|), (tetraFreshLaw ρ hρ m).prob ω)
        ≤ 9*(OperatorSpectralNorm (A z))^2/((m:ℝ)*ε^2) := by
    intro z
    have hmean : (tetraRecordLaw ρ hρ).expect (tetraStatistic (A z))
        = (Matrix.trace (A z * ρ)).re :=
      (tetrahedral_observable_unbiased ρ (A z) hρ (hA z)).2
    have hsecond := (tetrahedral_observable_computed_second_moment_bound ρ (A z) hρ (hA z)).1
    have havg : (∑ ω : Fin m → Fin 4, (tetraFreshLaw ρ hρ m).prob ω
          * (tetraSampleMean (A z) m ω
              - (tetraRecordLaw ρ hρ).expect (tetraStatistic (A z)))^2)
        = (tetraRecordLaw ρ hρ).variance (tetraStatistic (A z)) / m := by
      exact Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_avg_sub_sq
          (tetraRecordLaw ρ hρ) (tetraStatistic (A z)) hm
    rw [hmean] at havg
    have hvarle : (tetraRecordLaw ρ hρ).variance (tetraStatistic (A z))
        ≤ (tetraRecordLaw ρ hρ).expect (fun a => (tetraStatistic (A z) a)^2) := by
      rw [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.variance_eq_expect_sq_sub]
      exact sub_le_self _ (sq_nonneg _)
    have hstep := chebyshev_single (tetraFreshLaw ρ hρ m) (tetraSampleMean (A z) m)
      ((tetraRecordLaw ρ hρ).expect (tetraStatistic (A z))) ε hε
    rw [hmean] at hstep
    calc (∑ ω ∈ Finset.univ.filter (fun ω : Fin m → Fin 4 => ε ≤ |tetraSampleMean (A z) m ω
              - (Matrix.trace (A z*ρ)).re|), (tetraFreshLaw ρ hρ m).prob ω)
        ≤ (∑ ω : Fin m → Fin 4, (tetraFreshLaw ρ hρ m).prob ω
              * (tetraSampleMean (A z) m ω - (Matrix.trace (A z*ρ)).re)^2) / ε^2 := hstep
      _ = ((tetraRecordLaw ρ hρ).variance (tetraStatistic (A z)) / (m:ℝ)) / ε^2 := by
          rw [havg]
      _ ≤ 9 * (OperatorSpectralNorm (A z))^2 / ((m:ℝ) * ε^2) := by
          rw [div_div]
          exact div_le_div_of_nonneg_right (le_trans hvarle hsecond) (by positivity)
  refine le_trans (union_bound_single (tetraFreshLaw ρ hρ m)
    (fun (z : Z) (ω : Fin m → Fin 4) => ε ≤ |tetraSampleMean (A z) m ω
      - (Matrix.trace (A z*ρ)).re|)) ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun z _ => hbudget z

end Qatlib.Concepts.MbqcFlow.FlowDecision
