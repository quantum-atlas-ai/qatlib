/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.RootLaws.PhasePush
import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualBias
import Qatlib.Foundations.MatrixAlgebra.TorusMoments.RootMoments

/-!
# From source ensembles to weighted circuit densities

The matrix `sourceDensity` averages actual output outer products over a finite oracle ensemble.
Product and polynomial expectation identities identify the source densities with the weighted
phase model, transporting Born probabilities and the distinguishing lower bound. This
development supports the treatment in [TangWright2025].

## Main statements

* `sourceDensity_biased`: the biased source density equals the weighted circuit density.
* `sourceSuccess_eq_weighted`: equality of distinguishing success probabilities.
* `actual_source_query_lower_bound`: the source query lower bound at success `2/3`.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.RootLaws
open Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Foundations.MatrixAlgebra.TorusMoments
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination
set_option warningAsError false

/-- The ensemble average of the outer products of the actual forward-query output states. -/
def sourceDensity {d a : ℕ} {S : Type} [Fintype S] (p : FinDist (Fin d → S))
    (phi : S → ℂ) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  fun x y => ∑U,(p.prob U:ℂ)*(run phi Alg n U x*star (run phi Alg n U y))

/-- The Born mass of an ensemble-averaged density equals the ensemble-averaged Boolean output
probability. -/
theorem sourceDensity_born {d a : ℕ} {S : Type} [Fintype S] [DecidableEq S]
    (p : FinDist (Fin d → S)) (phi : S → ℂ) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (b : Bool) :
    bornMass (sourceDensity p phi Alg n) Alg.good b=distProb p phi Alg n b := by
  have hp (w : ℝ) (z : ℂ) : (((w:ℂ)*(z*star z))).re=w*‖z‖^2 := by
    have hc : z*star z=((‖z‖^2:ℝ):ℂ) := by
      rw [Complex.star_def,mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    rw [hc,← Complex.ofReal_mul,Complex.ofReal_re]
  simp only [bornMass,sourceDensity,Complex.re_sum,hp,distProb,FinDist.expect,outProb,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : Alg.good x=b <;> simp [h]

/-- A weighted product of polynomial evaluations expands as a double sum over monomial supports
and their weighted phase moments. -/
private theorem weighted_eval_expand {d : ℕ} {U : Type*} [Fintype U]
    (w : U → ℂ) (z : U → Fin d → ℂ) (P Q : MvPolynomial (Fin d) ℂ) :
    (∑u,w u*(MvPolynomial.eval (z u) P*star (MvPolynomial.eval (z u) Q))) =
      ∑h ∈ P.support,∑k ∈ Q.support,(P.coeff h*star (Q.coeff k)) *
        ∑u,w u*(monomialValue (z u) h*star (monomialValue (z u) k)) := by
  classical
  simp_rw [polynomial_density_expand,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- For `q > 1` and bias in `[0, 1]`, product observables have the same expectation in the
source mixture ensemble and the explicit weighted root ensemble. -/
theorem actual_product_phase_transport {d : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (f : Fin d → ℂ → ℂ) :
    (∑U : Fin d → Fin q ⊕ Fin (halfCount q),
      ((ensemble1 d q eps (by omega) he0 he1).prob U:ℂ) * ∏i,f i (phaseEps q (U i))) =
    ∑u : Fin d → Fin q,(phaseWeight eps q u:ℂ)*∏i,f i (phase q (u i)) := by
  simp only [ensemble1,independent,Complex.ofReal_prod,phaseWeight,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin d) (x : Fin q ⊕ Fin (halfCount q)) =>
      ((muEps eps q (by omega) he0 he1).prob x:ℂ)*f i (phaseEps q x)),
    ← Fintype.prod_sum (fun (i : Fin d) (g : Fin q) =>
      (muEpsWeight eps q g:ℂ)*f i (phase q g))]
  apply Finset.prod_congr rfl
  intro i _
  exact actual_muEps_expect eps q hq he0 he1 (f i)

/-- The source biased ensemble and the weighted root ensemble give the same expectation for a
polynomial evaluation times a conjugate polynomial evaluation. -/
theorem actual_polynomial_phase_transport {d : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (P Q : MvPolynomial (Fin d) ℂ) :
    (∑U : Fin d → Fin q ⊕ Fin (halfCount q),
      ((ensemble1 d q eps (by omega) he0 he1).prob U:ℂ) *
        (MvPolynomial.eval (fun i => phaseEps q (U i)) P *
          star (MvPolynomial.eval (fun i => phaseEps q (U i)) Q))) =
    ∑u : Fin d → Fin q,(phaseWeight eps q u:ℂ)*
      (MvPolynomial.eval (fun i => phase q (u i)) P *
        star (MvPolynomial.eval (fun i => phase q (u i)) Q)) := by
  rw [weighted_eval_expand,weighted_eval_expand]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  simpa only [monomialValue,star_prod,← Finset.prod_mul_distrib] using!
    actual_product_phase_transport eps q hq he0 he1 (fun i z => z^(h i)*star (z^(k i)))

/-- For `q > 1` and bias in `[0, 1]`, the actual biased source density equals
`weightedCircuitDensity` [TangWright2025]. -/
theorem sourceDensity_biased {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    sourceDensity (ensemble1 d q eps (by omega) he0 he1) (phaseEps q) Alg n=
      weightedCircuitDensity eps q Alg n := by
  ext x y
  simp only [sourceDensity,weightedCircuitDensity,Matrix.sum_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul]
  have h :=
      actual_polynomial_phase_transport eps q hq he0 he1 (queryPolynomial Alg n x)
      (queryPolynomial Alg n y)
  simpa only [queryPolynomial_eval] using! h

/-- For positive `q`, the uniform source density equals the zero-bias weighted circuit density. -/
theorem sourceDensity_unbiased {d a : ℕ} (q : ℕ) (hq : 0<q)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    sourceDensity (ensemble0 d q hq) (phase q) Alg n=weightedCircuitDensity 0 q Alg n := by
  ext x y
  simp [sourceDensity,weightedCircuitDensity,Matrix.sum_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul,ensemble0,independent,mu0,phaseWeight,muEpsWeight]

/-- For `q > 1` and bias in `[0, 1]`, actual ensemble-distinguishing success equals the weighted
circuit success [TangWright2025]. -/
theorem sourceSuccess_eq_weighted {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    successProb q (by omega) eps he0 he1 Alg n=weightedSuccess eps q Alg n := by
  rw [successProb,← sourceDensity_born,← sourceDensity_born,
    sourceDensity_unbiased,sourceDensity_biased eps q hq he0 he1]
  unfold weightedSuccess
  ring

/-- If `0 < eps < 1/2` and `q ≥ 1/eps^2`, then the root order `q` is greater than one. -/
theorem actual_q_order {eps : ℝ} {q : ℕ} (he0 : 0<eps) (he1 : eps<1/2)
    (hq : 1/eps^2≤(q:ℝ)) : 1<q := by
  have he2 : 0<eps^2 := sq_pos_of_pos he0
  have hqp : 1≤(q:ℝ)*eps^2 := (div_le_iff₀ he2).mp hq
  by_contra h
  have hqn : q≤1 := by omega
  have hqr : (q:ℝ)≤1 := by exact_mod_cast hqn
  nlinarith

/-- When `0 < eps < 1/2` and `q ≥ 1/eps^2`, actual source success at least `2/3` forces `n ≥
1/(12 * eps^2)`. -/
theorem actual_source_query_lower_bound {d a q : ℕ} (eps : ℝ) (he0 : 0<eps)
    (he1 : eps<1/2) (hq : 1/eps^2≤(q:ℝ)) (Alg : ForwardQueryAlgorithm d a) (n : ℕ)
    (hsucc : (2/3:ℝ)≤ successProb q (Nat.zero_lt_of_lt (actual_q_order he0 he1 hq))
      eps he0.le (by linarith) Alg n) : 1/(12*eps^2)≤(n:ℝ) := by
  rw [sourceSuccess_eq_weighted eps q (actual_q_order he0 he1 hq) he0.le (by linarith)] at hsucc
  exact actual_weighted_query_lower_bound eps he0 he1 hq Alg n hsucc

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
