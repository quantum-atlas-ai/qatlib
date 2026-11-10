/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.MatrixAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.RealDeriv
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false

noncomputable section
namespace CBMD
open Complex Metric Set Filter
open scoped Topology

section VectorSeries
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private def vectorSeries (c : ℕ → E) : FormalMultilinearSeries ℂ ℂ E :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)

omit [CompleteSpace E] in

private theorem vectorSeries_coeff (c : ℕ → E) (n : ℕ) :
    (vectorSeries c).coeff n = c n := by
  simp [vectorSeries, FormalMultilinearSeries.coeff]

private theorem vectorSeries_entire (c : ℕ → E)
    (hc : ∀ z : ℂ, Summable (fun n => z ^ n • c n)) :
    HasFPowerSeriesOnBall (fun z : ℂ => ∑' n, z ^ n • c n)
      (vectorSeries c) 0 ⊤ := by
  have hr : (vectorSeries c).radius = ⊤ := by
    apply ENNReal.eq_top_of_forall_nnreal_le
    intro r
    apply FormalMultilinearSeries.le_radius_of_tendsto (vectorSeries c) (l := 0)
    have ht := (hc (r : ℂ)).tendsto_atTop_zero.norm
    simpa [vectorSeries, norm_smul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg r.coe_nonneg, mul_comm] using ht
  have hh := (vectorSeries c).hasFPowerSeriesOnBall (by rw [hr]; exact ENNReal.zero_lt_top)
  rw [hr] at hh
  convert! hh using 1
  ext z
  simp [FormalMultilinearSeries.sum, vectorSeries_coeff]

private def univDerivSeries (p : FormalMultilinearSeries ℂ ℂ E) :
    FormalMultilinearSeries ℂ ℂ E :=
  (ContinuousLinearMap.apply ℂ E (1 : ℂ)).compFormalMultilinearSeries p.derivSeries

omit [CompleteSpace E] in

private theorem univDerivSeries_coeff (p : FormalMultilinearSeries ℂ ℂ E) (n : ℕ) :
    (univDerivSeries p).coeff n = (n + 1) • p.coeff (n + 1) := by
  change p.derivSeries.coeff n 1 = _
  exact p.derivSeries_coeff_one n

private theorem hasPowerSeries_deriv {f : ℂ → E} {p : FormalMultilinearSeries ℂ ℂ E}
    (h : HasFPowerSeriesOnBall f p 0 ⊤) :
    HasFPowerSeriesOnBall (deriv f) (univDerivSeries p) 0 ⊤ := by
  exact (ContinuousLinearMap.apply ℂ E (1 : ℂ)).comp_hasFPowerSeriesOnBall h.fderiv

private theorem vectorSeries_hasSum_second_deriv (c : ℕ → E)
    (hc : ∀ z : ℂ, Summable (fun n => z ^ n • c n)) (z : ℂ) :
    HasSum (fun n => z ^ n • ((n + 1) • ((n + 2) • c (n + 2))))
      (deriv (deriv (fun w : ℂ => ∑' n, w ^ n • c n)) z) := by
  have h := hasPowerSeries_deriv (hasPowerSeries_deriv (vectorSeries_entire c hc))
  have hs := h.hasSum (y := z) (by exact edist_lt_top _ _)
  simpa only [zero_add, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    univDerivSeries_coeff, vectorSeries_coeff, Nat.add_assoc] using hs

end VectorSeries
section Airy
variable {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]

def airyPropagator (A : E) (t : ℂ) : E :=
  ∑' n : ℕ, (airySeriesCoefficient n : ℂ) • (-(t ^ 3) • A) ^ n

private def airyTimeCoefficient (A : E) (n : ℕ) : E :=
  if n % 3 = 0 then (airySeriesCoefficient (n / 3) : ℂ) • (-A) ^ (n / 3) else 0

omit [CompleteSpace E] in

private theorem airyTimeCoefficient_mul (A : E) (n : ℕ) :
    airyTimeCoefficient A (3 * n) = (airySeriesCoefficient n : ℂ) • (-A) ^ n := by
  simp [airyTimeCoefficient]

omit [CompleteSpace E] in

private theorem airy_time_term (A : E) (t : ℂ) (n : ℕ) :
    t ^ (3 * n) • airyTimeCoefficient A (3 * n) =
      (airySeriesCoefficient n : ℂ) • (-(t ^ 3) • A) ^ n := by
  rw [airyTimeCoefficient_mul,
    show -(t ^ 3) • A = t ^ 3 • (-A) by simp,
    smul_pow, ← pow_mul, smul_comm]

private theorem airy_time_hasSum (A : E) (t : ℂ) :
    HasSum (fun n => t ^ n • airyTimeCoefficient A n) (airyPropagator A t) := by
  have hi : Function.Injective (fun n : ℕ => 3 * n) := by
    intro a b h
    change 3 * a = 3 * b at h
    omega
  apply (hi.hasSum_iff ?_).mp
  · change HasSum (fun n => t ^ (3 * n) • airyTimeCoefficient A (3 * n)) _
    simpa only [airy_time_term] using! (airy_series_summable A t).hasSum
  · intro n hn
    have hm : n % 3 ≠ 0 := by
      intro h
      apply hn
      exact ⟨n / 3, by change 3 * (n / 3) = n; omega⟩
    simp [airyTimeCoefficient, hm]

private theorem airyPropagator_timeSeries (A : E) :
    airyPropagator A = fun t => ∑' n, t ^ n • airyTimeCoefficient A n := by
  funext t
  exact (airy_time_hasSum A t).tsum_eq.symm

omit [CompleteSpace E] in

private theorem airyTimeCoefficient_step (A : E) (n : ℕ) :
    (n + 2) • ((n + 3) • airyTimeCoefficient A (n + 3)) =
      -A * airyTimeCoefficient A n := by
  by_cases hm : n % 3 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k := ⟨n / 3, by omega⟩
    rw [show 3 * k + 3 = 3 * (k + 1) by omega,
      airyTimeCoefficient_mul, airyTimeCoefficient_mul, pow_succ']
    have ha : ((3 * (k : ℝ) + 2) * (3 * (k : ℝ) + 3)) *
        airySeriesCoefficient (k + 1) = airySeriesCoefficient k := by
      rw [airySeriesCoefficient_step]
      have h2 : 3 * (k : ℝ) + 2 ≠ 0 := by positivity
      have h3 : 3 * (k : ℝ) + 3 ≠ 0 := by positivity
      field_simp
    have hac : ((3 * (k : ℂ) + 2) * (3 * (k : ℂ) + 3)) *
        (airySeriesCoefficient (k + 1) : ℂ) = (airySeriesCoefficient k : ℂ) := by
      exact_mod_cast ha
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, mul_smul_comm]
    rw [← mul_assoc]
    convert! congrArg (fun q : ℂ => q • (-A * (-A) ^ k)) hac using 1
    congr 2
    ring
  · simp [airyTimeCoefficient, hm]

theorem airyPropagator_analytic (A : E) (t : ℂ) : AnalyticAt ℂ (airyPropagator A) t := by
  rw [airyPropagator_timeSeries]
  exact (vectorSeries_entire (airyTimeCoefficient A)
    (fun z => (airy_time_hasSum A z).summable)).analyticAt_of_mem (edist_lt_top _ _)

omit [CompleteSpace E] in

@[simp] theorem airyPropagator_zero (A : E) : airyPropagator A 0 = 1 := by
  simp [airyPropagator, ← FormalMultilinearSeries.ofScalars_sum_eq]

theorem airyPropagator_hasDerivAt_zero (A : E) : HasDerivAt (airyPropagator A) 0 0 := by
  rw [airyPropagator_timeSeries]
  have h := (vectorSeries_entire (airyTimeCoefficient A)
    (fun z => (airy_time_hasSum A z).summable)).hasFPowerSeriesAt.hasDerivAt
  simpa [vectorSeries_coeff, airyTimeCoefficient] using h

@[simp] theorem airyPropagator_deriv_zero (A : E) : deriv (airyPropagator A) 0 = 0 :=
  (airyPropagator_hasDerivAt_zero A).deriv

theorem airyPropagator_ode (A : E) (t : ℂ) :
    deriv (deriv (airyPropagator A)) t + t • (A * airyPropagator A t) = 0 := by
  have hs := vectorSeries_hasSum_second_deriv (airyTimeCoefficient A)
    (fun z => (airy_time_hasSum A z).summable) t
  rw [← airyPropagator_timeSeries] at hs
  have ht : HasSum
      (fun n => t ^ (n + 1) • ((n + 2) • ((n + 3) • airyTimeCoefficient A (n + 3))))
      (t • (-A * airyPropagator A t)) := by
    convert! ((airy_time_hasSum A t).mul_left (-A)).const_smul t using 1
    funext n
    rw [airyTimeCoefficient_step]
    simp only [pow_succ, mul_smul_comm, smul_smul, mul_comm]
  have hf : HasSum
      (fun n => t ^ n • ((n + 1) • ((n + 2) • airyTimeCoefficient A (n + 2))))
      (t • (-A * airyPropagator A t)) := by
    have hh := (hasSum_nat_add_iff
      (f := fun n => t ^ n • ((n + 1) • ((n + 2) • airyTimeCoefficient A (n + 2))))
      (g := t • (-A * airyPropagator A t)) 1).mp (by
        simpa only [Nat.add_assoc] using ht)
    have hzero : airyTimeCoefficient A (0 + 2) = 0 := by simp [airyTimeCoefficient]
    simpa only [Finset.sum_range_one, hzero, smul_zero, add_zero] using hh
  rw [hs.unique hf]
  simp

theorem airyPropagator_hasDerivAt_deriv (A : E) (t : ℂ) :
    HasDerivAt (deriv (airyPropagator A)) (-(t • (A * airyPropagator A t))) t := by
  have h := (airyPropagator_analytic A t).deriv.differentiableAt.hasDerivAt
  convert! h using 1
  exact (eq_neg_of_add_eq_zero_left (airyPropagator_ode A t)).symm

section RealTime
variable [NormedSpace ℝ E]

omit [CompleteSpace E] in

private theorem vector_hasDerivAt_comp_ofReal {f : ℂ → E} {f' : E} {t : ℝ}
    (h : HasDerivAt f f' (t : ℂ)) :
    HasDerivAt (fun x : ℝ => f (x : ℂ)) f' t := by
  simpa using! ((h.hasFDerivAt.restrictScalars ℝ).comp t
    Complex.ofRealCLM.hasFDerivAt).hasDerivAt

theorem airyPropagator_real_deriv_eq (A : E) (t : ℝ) :
    deriv (fun x : ℝ => airyPropagator A (x : ℂ)) t =
      deriv (airyPropagator A) (t : ℂ) :=
  (vector_hasDerivAt_comp_ofReal
    (airyPropagator_analytic A (t : ℂ)).differentiableAt.hasDerivAt).deriv

theorem airyPropagator_real_hasDerivAt_zero (A : E) :
    HasDerivAt (fun x : ℝ => airyPropagator A (x : ℂ)) 0 0 := by
  exact vector_hasDerivAt_comp_ofReal (by simpa using airyPropagator_hasDerivAt_zero A)

theorem airyPropagator_real_hasDerivAt_deriv (A : E) (t : ℝ) :
    HasDerivAt (deriv (fun x : ℝ => airyPropagator A (x : ℂ)))
      (-(t • (A * airyPropagator A (t : ℂ)))) t := by
  have he : deriv (fun x : ℝ => airyPropagator A (x : ℂ)) =
      fun x : ℝ => deriv (airyPropagator A) (x : ℂ) :=
    funext (airyPropagator_real_deriv_eq A)
  rw [he]
  have h := vector_hasDerivAt_comp_ofReal (airyPropagator_hasDerivAt_deriv A (t : ℂ))
  simpa using h

theorem airyPropagator_real_ode (A : E) (t : ℝ) :
    deriv (deriv (fun x : ℝ => airyPropagator A (x : ℂ))) t +
      t • (A * airyPropagator A (t : ℂ)) = 0 := by
  rw [(airyPropagator_real_hasDerivAt_deriv A t).deriv]
  exact neg_add_cancel _

end RealTime
end Airy
section Matrices
open scoped Matrix.Norms.L2Operator
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_airy_initial_value_problem (A : Matrix n n ℂ) :
    let G : ℝ → Matrix n n ℂ := fun t => airyPropagator A (t : ℂ)
    G 0 = 1 ∧ HasDerivAt G 0 0 ∧
      ∀ t : ℝ, HasDerivAt (deriv G) (-(t • (A * G t))) t := by
  refine ⟨?_, airyPropagator_real_hasDerivAt_zero A,
    airyPropagator_real_hasDerivAt_deriv A⟩
  simp

end Matrices
end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
