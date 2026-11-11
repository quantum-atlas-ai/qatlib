/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.UStatBackend.OrderedHigherUStatistic
import Qatlib.Papers.ClassShadows20.HigherMoments.HigherPauliShadows

/-!
# Higher Pauli moment estimators

The module applies the ordered higher U-statistic to tensor Pauli snapshots and reconstructs the
real trace of each state power. It proves unbiasedness and an explicit deviation bound for the
rational estimator, and specializes the computation to order four with exact tuple and
local-record counts.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `higher_pauli_fresh_order_moment_and_tail`: gives the state-moment expectation and deviation
  bound.
* `higher_pauli_order_four_native_and_resources`: identifies the fourth-order rational evaluator
  and its counts.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Papers.ClassShadows20.HigherMoments
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- A fold multiplying tensor Pauli snapshots equals the initial operator times their ordered
list product. -/
private theorem higher_snapshot_fold_prod (n : ℕ) (xs : List (Fin n→Fin 3×Bool))
    (A : Operator (2^n)) :
    xs.foldl (fun U x=>U*tensorPauliSnapshot n x) A=
      A*(xs.map (tensorPauliSnapshot n)).prod := by
  induction xs generalizing A with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.map_cons,List.prod_cons,Matrix.mul_assoc]

/-- The independent order-`r` mean of the higher shadow kernel equals the real trace of `rho^r`. -/
theorem higherShadowKernel_mean (n r : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho) :
    higherUMean (tensorPauliLaw n rho hrho) r (higherShadowKernel n)=(Matrix.trace (rho^r)).re := by
  let p := tensorPauliLaw n rho hrho
  have hrec : (∑ a,(p.prob a:ℂ) • tensorPauliSnapshot n a)=rho :=
    tensor_pauli_snapshot_reconstructs_entangled_input n rho hrho
  have hmatrix (r : ℕ) :
      (∑ v : Fin r→(Fin n→Fin 3×Bool),(p.probOf v:ℂ) •
        ((List.ofFn v).map (tensorPauliSnapshot n)).prod)=rho^r := by
    induction r with
    | zero => simp [FinDist.probOf]
    | succ r ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (r+1)=>(Fin n→Fin 3×Bool))).sum_comp,Fintype.sum_prod_type]
      simp only [Fin.consEquiv_apply,FinDist.probOf,Fin.prod_univ_succ,Fin.cons_zero,
        Fin.cons_succ,List.ofFn_succ,List.map_cons,List.prod_cons]
      calc
        _ = (∑ a,(p.prob a:ℂ) • tensorPauliSnapshot n a)*
          (∑ v : Fin r→(Fin n→Fin 3×Bool),(p.probOf v:ℂ) •
            ((List.ofFn v).map (tensorPauliSnapshot n)).prod) := by
          simp only [FinDist.probOf,Matrix.sum_mul,Matrix.mul_sum,Matrix.smul_mul,Matrix.mul_smul,
            Finset.smul_sum,smul_smul,Complex.ofReal_mul,mul_comm]
          rw [Finset.sum_comm]
        _ = rho*rho^r := congrArg₂ (fun A B : Operator (2^n)=>A*B) hrec ih
        _ = rho^(r+1) := (pow_succ' rho r).symm
  have he := congrArg Matrix.trace (hmatrix r)
  simp only [Matrix.trace_sum,Matrix.trace_smul,smul_eq_mul] at he
  have hr := congrArg Complex.re he
  simpa only [higherUMean,higherShadowKernel,higher_snapshot_fold_prod,Matrix.one_mul,
    Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,p] using hr

/-- For `m > 0`, `r ≤ m`, and positive `eps`, the rational higher shadow estimator is unbiased
for the real trace of `rho^r`. Its deviation probability is at most `4 * r² * (2^n *
2^(n*r))² / (m * eps²)` [HuangKuengPreskill2020]. -/
theorem higher_pauli_fresh_order_moment_and_tail :
    ∀ (n m r : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho) (eps : ℝ),
    0 < m → r ≤ m → 0<eps →
    let p := tensorPauliLaw n rho hrho;
    (∑ ω : Fin m→(Fin n→Fin 3×Bool),p.probOf ω*
      ((higherUCountedQ m r (higherShadowKernelQ n) ω).1:ℝ))=(Matrix.trace (rho^r)).re ∧
    (∑ ω∈Finset.univ.filter (fun ω : Fin m→(Fin n→Fin 3×Bool)=>
      eps≤|((higherUCountedQ m r (higherShadowKernelQ n) ω).1:ℝ)-(Matrix.trace (rho^r)).re|),p.probOf ω)
      ≤4*(r:ℝ)^2*((2:ℝ)^n*(2:ℝ)^(n*r))^2/(m*eps^2) := by
  intro n m r rho hrho eps hm hr heps p
  have hc : (fun xs : List (Fin n→Fin 3×Bool)=>(higherShadowKernelQ n xs:ℝ))=higherShadowKernel n :=
    funext (higherShadowKernelQ_cast n)
  have hv (ω : Fin m→(Fin n→Fin 3×Bool)) :
      ((higherUCountedQ m r (higherShadowKernelQ n) ω).1:ℝ)=
        (higherUCounted m r (higherShadowKernel n) ω).1 := by
    simpa only [hc] using (higherUCountedQ_cast m r (higherShadowKernelQ n) ω).1
  have hmean : higherUMean p r (higherShadowKernel n)=(Matrix.trace (rho^r)).re :=
    higherShadowKernel_mean n r rho hrho
  constructor
  · simp_rw [hv]
    rw [(higher_u_asymmetric_unbiased_and_empty _ p m r (higherShadowKernel n) hr).1,hmean]
  · have hb (xs : List (Fin n→Fin 3×Bool)) (hl : xs.length=r) :
        |(higherShadowKernelQ n xs:ℝ)|≤(2:ℝ)^n*(2:ℝ)^(n*r) := by
      rw [higherShadowKernelQ_cast]
      simpa only [hl] using (higher_pauli_actual_gaussian_rational_trace n xs).2
    have ht := (higher_u_same_records_tail_and_rational_fold _ p m r (higherShadowKernelQ n)
      ((2:ℝ)^n*(2:ℝ)^(n*r)) eps hm hr (by positivity) heps hb).2
    simpa only [hc,hmean] using ht

/-- The fourth-order rational evaluator agrees with the real evaluator and counts
`m.descFactorial 4` ordered tuples. The tuple list has that length, and the sum of `m`
local-record sizes is `n * m`. -/
theorem higher_pauli_order_four_native_and_resources :
    ∀ (n m : ℕ) (omega : Fin m→Fin n→Fin 3×Bool),
    let z := higherUCountedQ m 4 (higherShadowKernelQ n) omega;
    z.2=m.descFactorial 4 ∧
    ((z.1:ℝ)=(higherUCounted m 4 (higherShadowKernel n) omega).1) ∧
    (higherUTuples m 4).length=m.descFactorial 4 ∧ (List.replicate m n).sum=n*m := by
  intro n m omega z
  have hc : (fun xs : List (Fin n→Fin 3×Bool)=>(higherShadowKernelQ n xs:ℝ))=higherShadowKernel n :=
    funext (higherShadowKernelQ_cast n)
  have he := higherUCountedQ_cast m 4 (higherShadowKernelQ n) omega
  refine ⟨he.2,?_,higherUTuples_length m 4,?_⟩
  · simpa only [hc] using he.1
  · simp [List.sum_replicate,Nat.mul_comm]

end Qatlib.Papers.ClassShadows20.HigherMoments
