/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowChannelSubgoalStat
import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleMeasurement
import Qatlib.Concepts.ShadowModels.ShadowChannel.PauliRealMoments
import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordShadowDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Concepts.ShadowModels.ShadowChannel
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem basis_shadow_expectation_bound {d : ℕ} (O ρ : Operator d) (hρ : IsDensityOperator ρ) :
    |(Matrix.trace (O*ρ)).re| ≤ ‖O‖ := abs_trace_density_le_norm O ρ hρ.1 hρ.2

theorem clifford_moment_forward_channel (d : ℕ) (hd : 2 ≤ d)
    (I : Type) [Fintype I] [DecidableEq I] (μ : FinDist I) (Uf : I → Operator d)
    (h35 : CliffordMomentHypothesis d I μ Uf) (ρ : Operator d) (hρ : IsDensityOperator ρ) :
    (∑ b : Fin d, ∑ i, (μ.prob i*(Matrix.trace (ρ*(Uf i*basisProjector b*(Uf i)ᴴ))).re) •
      ((Uf i)ᴴ*basisProjector b*Uf i)) =
      (1/((d : ℝ)+1)) • ρ+(1/((d : ℝ)+1)) • 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  have hterm (b : Fin d) := h35 (basisProjector b) (basisProjector_pure b) ρ
  simp only [hρ.2, Complex.one_re] at hterm
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_add, smul_smul]
  have he : (d : ℝ)*(1/((d : ℝ)*((d : ℝ)+1))) = 1/((d : ℝ)+1) := by
    field_simp
  rw [he, add_comm]

theorem clifford_basis_record_mass_one (d : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (hU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Operator d) (hρ : IsDensityOperator ρ) :
    (∑ b : Fin d, ∑ i, μ.prob i*(Matrix.trace (basisProjector b*(Uf i*ρ*(Uf i)ᴴ))).re) = 1 := by
  rw [Finset.sum_comm]
  have hb : ∑ b : Fin d, basisProjector b = 1 := by
    simp_rw [basisProjector_eq_projector]
    exact projectors_singleton_sum
  have he (i : I) : (∑ b : Fin d, μ.prob i*(Matrix.trace (basisProjector b*(Uf i*ρ*(Uf i)ᴴ))).re) = μ.prob i := by
    rw [← Finset.mul_sum, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hb,
        Matrix.one_mul]
    by_cases hp : 0 < μ.prob i
    · have hu : (Uf i)ᴴ*Uf i = 1 := by
        simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using! hU i hp
      have ht : Matrix.trace (Uf i*ρ*(Uf i)ᴴ) = 1 := by
        rw [Matrix.trace_mul_cycle, hu, Matrix.one_mul, hρ.2]
      rw [ht, Complex.one_re, mul_one]
    · have hz : μ.prob i = 0 := by have hn := μ.nonneg i; linarith
      simp [hz]
  simp_rw [he]
  exact μ.sum_one

theorem clifford_unbiased_of_actual_channel (d : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d)
    (hU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (ρ : Operator d) (hρ : IsDensityOperator ρ)
    (hc : (∑ b : Fin d, ∑ i,
      (μ.prob i*(Matrix.trace (basisProjector b*(Uf i*ρ*(Uf i)ᴴ))).re) •
        ((Uf i)ᴴ*basisProjector b*Uf i)) =
      (1/((d : ℝ)+1)) • ρ+(1/((d : ℝ)+1)) • 1) (O : Operator d) :
    (∑ b : Fin d, ∑ i,
      (μ.prob i*(Matrix.trace (basisProjector b*(Uf i*ρ*(Uf i)ᴴ))).re)*
        (Matrix.trace (O*(((d : ℝ)+1) • ((Uf i)ᴴ*basisProjector b*Uf i)-1))).re) =
      (Matrix.trace (O*ρ)).re := by
  let w := fun (b : Fin d) (i : I) => μ.prob i*(Matrix.trace (basisProjector b*(Uf i*ρ*(Uf i)ᴴ))).re
  let Q := fun (b : Fin d) (i : I) => (Uf i)ᴴ*basisProjector b*Uf i
  have hm : (∑ b, ∑ i, w b i) = 1 := clifford_basis_record_mass_one d I μ Uf hU ρ hρ
  have htrace : (∑ b, ∑ i, w b i*(Matrix.trace (O*Q b i)).re) =
      1/((d : ℝ)+1)*((Matrix.trace (O*ρ)).re+(Matrix.trace O).re) := by
    have h := congrArg (fun A : Operator d => (Matrix.trace (O*A)).re) hc
    simpa only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul,
      Matrix.trace_smul, Complex.smul_re, Matrix.mul_add, Matrix.trace_add,
      Complex.add_re, Matrix.mul_one, mul_add] using! h
  change (∑ b, ∑ i, w b i*(Matrix.trace (O*(((d : ℝ)+1) • Q b i-1))).re) = _
  simp only [Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
    Complex.sub_re, Complex.smul_re, smul_eq_mul, Matrix.mul_one, mul_sub]
  simp only [Finset.sum_sub_distrib]
  have hfirst : (∑ b, ∑ i, w b i*(((d : ℝ)+1)*(Matrix.trace (O*Q b i)).re)) =
      ((d : ℝ)+1)*(∑ b, ∑ i, w b i*(Matrix.trace (O*Q b i)).re) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro i _; ring
  have hsecond : (∑ b, ∑ i, w b i*(Matrix.trace O).re) = (Matrix.trace O).re := by
    simp_rw [← Finset.sum_mul]
    rw [hm, one_mul]
  rw [hfirst, hsecond, htrace]
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

private def orientationCycle : Operator 3 := fun i j => if i.val = (j.val+1)%3 then 1 else 0

theorem clifford_pointwise_orientation_obstruction :
    ∃ (U ρ : Operator 3), U ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ IsPureDensityOperator ρ ∧
      Matrix.trace (basisProjector (0 : Fin 3)*(U*ρ*Uᴴ)) ≠
        Matrix.trace (ρ*(U*basisProjector (0 : Fin 3)*Uᴴ)) := by
  have hU : orientationCycle ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [orientationCycle, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply]
  have hactual : Matrix.trace (basisProjector (0 : Fin 3)*
      (orientationCycle*basisProjector (1 : Fin 3)*orientationCycleᴴ)) = 0 := by
    norm_num [orientationCycle, basisProjector, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply]
  have hmoment : Matrix.trace (basisProjector (1 : Fin 3)*
      (orientationCycle*basisProjector (0 : Fin 3)*orientationCycleᴴ)) = 1 := by
    norm_num [orientationCycle, basisProjector, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.conjTranspose_apply]
  refine ⟨orientationCycle, basisProjector (1 : Fin 3), hU, basisProjector_pure _, ?_⟩
  rw [hactual, hmoment]
  norm_num

theorem clifford_actual_channel (d : ℕ) (hd : 2 ≤ d)
    (I : Type) [Fintype I] [DecidableEq I] (μ : FinDist I) (Uf : I → Operator d)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf) (ρ : Operator d) (hρ : IsDensityOperator ρ) :
    (∑ b : Fin d, ∑ i, (μ.prob i*(Matrix.trace (basisProjector b*(Uf i*ρ*(Uf i)ᴴ))).re) •
      ((Uf i)ᴴ*basisProjector b*Uf i)) =
      (1/((d : ℝ)+1)) • ρ+(1/((d : ℝ)+1)) • 1 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hterm (b : Fin d) := h35 (basisProjector b) (basisProjector_pure b) ρ hρ.1.isHermitian
  simp only [hρ.2, Complex.one_re] at hterm
  simp_rw [basis_born_trace_cycle, hterm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  simp only [smul_add, smul_smul]
  have he : (d : ℝ)*(1/((d : ℝ)*((d : ℝ)+1))) = 1/((d : ℝ)+1) := by
    field_simp
  rw [he, add_comm]

theorem cliffordBasisShadowChannelSubgoal : CliffordBasisShadowChannelSubgoal := by
  intro d hd I _ _ μ Uf hU h35
  refine ⟨?_, ?_⟩
  · intro ρ hρ
    exact clifford_actual_channel d hd I μ Uf h35 ρ hρ
  · intro ρ hρ O
    exact clifford_unbiased_of_actual_channel d I μ Uf hU ρ hρ
      (clifford_actual_channel d hd I μ Uf h35 ρ hρ) O

end Qatlib.Concepts.ShadowModels.ShadowChannel
