/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualTensor
import Qatlib.Papers.AmpInvReqTang26.ForwardHist.ActualNorm
import Qatlib.Concepts.MixedFidelity.FidelityMetric.BornDomination
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
namespace Qatlib.Papers.AmpInvReqTang26.ForwardHist
open Qatlib.Papers.AmpInvReqTang26.AccessModel
open Qatlib.Papers.AmpInvReqTang26.BiasedFourier
open Qatlib.Foundations.MatrixAlgebra.FrameProject.Tensor
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Purification
open Qatlib.Concepts.MixedFidelity.FidelityMetric.Domination

def phaseWeight {d : ℕ} (eps : ℝ) (q : ℕ) (u : Fin d → Fin q) : ℝ :=
  ∏i,muEpsWeight eps q (u i)

def weightedCircuitDensity {d a : ℕ} (eps : ℝ) (q : ℕ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) : Matrix (Fin d × Fin a) (Fin d × Fin a) ℂ :=
  ∑u : Fin d → Fin q, (phaseWeight eps q u : ℂ) •
    Matrix.vecMulVec (run (phase q) Alg n u) (star (run (phase q) Alg n u))

theorem phaseWeight_sum {d : ℕ} (eps : ℝ) (q : ℕ) (hq : 0<q)
    (he0 : 0≤eps) (he1 : eps≤1) : ∑u : Fin d → Fin q,phaseWeight eps q u=1 := by
  simp only [phaseWeight]
  rw [← Fintype.prod_sum (fun (_ : Fin d) (v : Fin q) => muEpsWeight eps q v)]
  simp_rw [sum_muEpsWeight q hq eps he0 he1]
  simp

theorem phaseWeight_nonneg {d : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (u : Fin d → Fin q) : 0≤phaseWeight eps q u :=
  Finset.prod_nonneg (fun _ _ => muEpsWeight_nonneg q hq eps he0 he1 _)

theorem weightedCircuitDensity_posSemidef {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    (weightedCircuitDensity eps q Alg n).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro u _
  apply Matrix.PosSemidef.smul
  · exact Matrix.posSemidef_vecMulVec_self_star _
  · exact Complex.zero_le_real.mpr (phaseWeight_nonneg eps q hq he0 he1 u)

theorem weightedCircuitDensity_trace {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 0<q)
    (he0 : 0≤eps) (he1 : eps≤1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) :
    Matrix.trace (weightedCircuitDensity eps q Alg n)=1 := by
  have htrace (u : Fin d → Fin q) :
      Matrix.trace (Matrix.vecMulVec (run (phase q) Alg n u) (star (run (phase q) Alg n u)))=1 := by
    have hn := actual_run_normSq (phase q) (norm_phase q) Alg n u
    have hc (z : ℂ) : z*star z=((‖z‖^2:ℝ):ℂ) := by
      rw [Complex.star_def,mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.vecMulVec_apply,Pi.star_apply,hc,
      ← Complex.ofReal_sum,hn,Complex.ofReal_one]
  simp only [weightedCircuitDensity,Matrix.trace_sum,Matrix.trace_smul,htrace,smul_eq_mul,mul_one,
    ← Complex.ofReal_sum,phaseWeight_sum eps q hq he0 he1,Complex.ofReal_one]

def rawHistogramPurification {d a : ℕ} (eps : ℝ) (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) : Matrix (Fin d × Fin a) (Fin d → Fin q) ℂ :=
  pathCoefficient Alg n * columns (fourierUnitVec eps q) (pathHistogram Alg n q hn)

theorem rawHistogramPurification_entry {d a : ℕ} (eps : ℝ) (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) (x : Fin d × Fin a) (u : Fin d → Fin q) :
    rawHistogramPurification eps Alg n q hn x u =
      (∏i,(Real.sqrt (muEpsWeight eps q (u i)):ℂ)) * run (phase q) Alg n u x := by
  rw [actual_path_expansion (phase q) Alg n q hn u x]
  simp only [rawHistogramPurification,Matrix.mul_apply,columns,column,fourierUnitVec,
    Finset.prod_mul_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

theorem histogramPurification_gram_transport {d a : ℕ} (eps : ℝ) (Alg : ForwardQueryAlgorithm d a)
    (n q : ℕ) (hn : n<q) :
    reduced (histogramPurification1 eps Alg n q hn)=reduced (rawHistogramPurification eps Alg n q hn) := by
  apply reduced_gram_transport
  exact columns_gram_preserved (transformedColumn eps q) (fourierUnitVec eps q)
    (transformedColumn_gram eps q) (pathHistogram Alg n q hn)

theorem rawHistogramPurification_reduced {d a : ℕ} (eps : ℝ) (q : ℕ) (hq : 1<q)
    (he0 : 0≤eps) (he1 : eps≤1) (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (hn : n<q) :
    reduced (rawHistogramPurification eps Alg n q hn)=weightedCircuitDensity eps q Alg n := by
  have hs (g : Fin q) : (Real.sqrt (muEpsWeight eps q g):ℂ) *
      star (Real.sqrt (muEpsWeight eps q g):ℂ) = (muEpsWeight eps q g:ℂ) := by
    rw [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul]
    congr 1
    nlinarith [Real.sq_sqrt (muEpsWeight_nonneg q hq eps he0 he1 g)]
  have ht (u : Fin d → Fin q) :
      (∏i,(Real.sqrt (muEpsWeight eps q (u i)):ℂ)) *
        star (∏i,(Real.sqrt (muEpsWeight eps q (u i)):ℂ))=(phaseWeight eps q u:ℂ) := by
    rw [star_prod,← Finset.prod_mul_distrib]
    simp_rw [hs]
    simp only [phaseWeight,Complex.ofReal_prod]
  ext x y
  simp only [reduced,Matrix.mul_apply,Matrix.conjTranspose_apply,weightedCircuitDensity,
    Matrix.sum_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro u _
  rw [rawHistogramPurification_entry,rawHistogramPurification_entry,star_mul]
  calc
    _ = ((∏i,(Real.sqrt (muEpsWeight eps q (u i)):ℂ)) *
      star (∏i,(Real.sqrt (muEpsWeight eps q (u i)):ℂ))) *
        (run (phase q) Alg n u x * star (run (phase q) Alg n u y)) := by ring
    _ = _ := by rw [ht]

theorem weightedCircuitDensity_born {d a : ℕ} (eps : ℝ) (q : ℕ)
    (Alg : ForwardQueryAlgorithm d a) (n : ℕ) (b : Bool) :
    bornMass (weightedCircuitDensity eps q Alg n) Alg.good b =
      ∑u : Fin d → Fin q,phaseWeight eps q u * outProb (phase q) Alg n u b := by
  have hp (w : ℝ) (z : ℂ) : (((w:ℂ)*(z*star z))).re=w*‖z‖^2 := by
    have hc : z*star z=((‖z‖^2:ℝ):ℂ) := by
      rw [Complex.star_def,mul_comm,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    rw [hc,← Complex.ofReal_mul,Complex.ofReal_re]
  simp only [bornMass,weightedCircuitDensity,Matrix.sum_apply,Matrix.smul_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,smul_eq_mul,Complex.re_sum,hp,outProb,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : Alg.good x=b <;> simp [h]

end Qatlib.Papers.AmpInvReqTang26.ForwardHist
